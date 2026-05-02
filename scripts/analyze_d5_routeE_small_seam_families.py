#!/usr/bin/env python3
"""Analyze candidate residue families in the D5 even Route-E small-seam table.

This is a research aid, not a proof.  It reads the recorded
`SMALL_SEAM_CASES` from `verify_d5_even_routeE.py`, normalizes every schedule
to E-slot zero, and checks whether the finite data are compatible with simple
affine count formulas on residue classes modulo selected periods.
"""
from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from fractions import Fraction
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import verify_d5_even_routeE as route_e

CountVec = Tuple[int, int, int, int, int]


DEFAULT_PERIODS = (4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30)


def frac_json(q: Fraction) -> dict:
    return {"num": q.numerator, "den": q.denominator}


def frac_text(q: Fraction) -> str:
    if q.denominator == 1:
        return str(q.numerator)
    return f"{q.numerator}/{q.denominator}"


def affine_text(a: Fraction, b: Fraction) -> str:
    if a == 0:
        return frac_text(b)
    slope = "m" if a == 1 else f"{frac_text(a)}*m"
    if b == 0:
        return slope
    sign = "+" if b > 0 else "-"
    return f"{slope} {sign} {frac_text(abs(b))}"


def case_rows(normalized: bool) -> List[dict]:
    rows = []
    for m, data in sorted(route_e.SMALL_SEAM_CASES.items()):
        counts = data["counts"]
        norm = route_e.normalize_counts_to_slot0(data["slot"], counts)
        vector = norm if normalized else counts
        rows.append(
            {
                "m": m,
                "slot": data["slot"],
                "counts": counts,
                "normalized_counts_slot0": norm,
                "fit_vector": vector,
                "zero_positions": [i for i, n in enumerate(vector) if n == 0],
                "support": [i for i, n in enumerate(vector) if n != 0],
            }
        )
    return rows


def as_count_vec(value: Sequence[int]) -> CountVec:
    vec = tuple(int(item) for item in value)
    if len(vec) != 5:
        raise ValueError(f"expected a 5-count vector, got {value!r}")
    return vec  # type: ignore[return-value]


def ordered_unique(values: Iterable[Tuple[int, ...]]) -> List[Tuple[int, ...]]:
    seen = set()
    result = []
    for value in values:
        if value not in seen:
            seen.add(value)
            result.append(value)
    return result


def counter_items(counter: Counter[Tuple[int, ...]], key_name: str) -> List[dict]:
    return [
        {key_name: list(key), "count": count}
        for key, count in sorted(counter.items(), key=lambda item: (item[0], item[1]))
    ]


def summarize_count_scan_case(item: dict) -> dict:
    hits = item.get("first_hits", [])
    normalized_vectors = [
        as_count_vec(hit["normalized_counts_slot0"]) for hit in hits
    ]
    distinct_vectors = ordered_unique(normalized_vectors)
    open_vectors = ordered_unique(
        vec
        for vec, hit in zip(normalized_vectors, hits)
        if hit.get("open_port_normal_form", False)
    )
    known_value = item.get("known_normalized_counts_slot0")
    known_vec = as_count_vec(known_value) if known_value is not None else None
    known_present = (
        known_vec in distinct_vectors
        if known_vec is not None
        else any(hit.get("matches_known_normalized", False) for hit in hits)
    )
    alternative_vectors = [
        vec for vec in distinct_vectors if known_vec is None or vec != known_vec
    ]
    zero_counter: Counter[Tuple[int, ...]] = Counter(
        tuple(hit.get("normalized_zero_positions", [])) for hit in hits
    )
    support_counter: Counter[Tuple[int, ...]] = Counter(
        tuple(hit.get("normalized_support", [])) for hit in hits
    )
    return {
        "m": item["m"],
        "checked": item.get("checked"),
        "first_hit_count": len(hits),
        "reported_hit_count": item.get("hit_count"),
        "ok": item.get("ok", bool(hits)),
        "known_normalized_counts_slot0": known_vec,
        "known_present": known_present,
        "known_hit_count": sum(
            1
            for vec, hit in zip(normalized_vectors, hits)
            if (known_vec is not None and vec == known_vec)
            or hit.get("matches_known_normalized", False)
        ),
        "distinct_normalized_count": len(distinct_vectors),
        "distinct_normalized_hits": distinct_vectors,
        "alternative_distinct_count": len(alternative_vectors),
        "alternative_normalized_hits": alternative_vectors,
        "open_port_hit_count": sum(
            1 for hit in hits if hit.get("open_port_normal_form", False)
        ),
        "open_port_distinct_count": len(open_vectors),
        "open_port_normalized_hits": open_vectors,
        "zero_position_classes": counter_items(zero_counter, "zero_positions"),
        "support_classes": counter_items(support_counter, "support"),
    }


def count_scan_distinct_hit_rows(item: dict) -> List[dict]:
    seen = set()
    rows = []
    for hit in item.get("first_hits", []):
        vec = as_count_vec(hit["normalized_counts_slot0"])
        if vec in seen:
            continue
        seen.add(vec)
        rows.append(
            {
                "m": item["m"],
                "slot": hit["slot"],
                "counts": as_count_vec(hit["counts"]),
                "normalized_counts_slot0": vec,
                "open_port_normal_form": hit.get("open_port_normal_form", False),
                "support": list(hit.get("normalized_support", [])),
                "zero_positions": list(hit.get("normalized_zero_positions", [])),
                "matches_known_normalized": hit.get(
                    "matches_known_normalized", False
                ),
            }
        )
    return rows


def score_count_scan_hit(row: dict) -> dict:
    result = route_e.verify_small_seam_case(
        row["m"], row["slot"], row["counts"]
    )
    blocks = result.get("translation_blocks", [])
    return {
        "normalized_counts_slot0": row["normalized_counts_slot0"],
        "slot": row["slot"],
        "counts": row["counts"],
        "open_port_normal_form": row["open_port_normal_form"],
        "support_count": len(row["support"]),
        "support": row["support"],
        "zero_positions": row["zero_positions"],
        "matches_known_normalized": row["matches_known_normalized"],
        "small_seam_ok": result["ok"],
        "block_count": result["translation_block_count"],
        "max_block_length": max((block["length"] for block in blocks), default=0),
        "translation_blocks_prefix": blocks[:8],
    }


def best_candidates(scored: Sequence[dict], top: int) -> dict:
    good = [item for item in scored if item["small_seam_ok"]]
    by_min_block = sorted(
        good,
        key=lambda item: (
            item["block_count"],
            -item["max_block_length"],
            item["support_count"],
            not item["open_port_normal_form"],
            item["normalized_counts_slot0"],
        ),
    )
    by_open_first = sorted(
        good,
        key=lambda item: (
            not item["open_port_normal_form"],
            item["block_count"],
            item["support_count"],
            item["normalized_counts_slot0"],
        ),
    )
    by_low_support = sorted(
        good,
        key=lambda item: (
            item["support_count"],
            item["block_count"],
            not item["open_port_normal_form"],
            item["normalized_counts_slot0"],
        ),
    )
    return {
        "min_block": by_min_block[:top],
        "open_first": by_open_first[:top],
        "low_support": by_low_support[:top],
    }


def score_count_scan_summary(summary: dict, payload: dict, top: int) -> None:
    scan_by_m = {
        item["m"]: item
        for item in payload.get("one_e_full_count_scan", [])
        if isinstance(item, dict)
    }
    for case in summary["cases"]:
        item = scan_by_m[case["m"]]
        scored = [
            score_count_scan_hit(row)
            for row in count_scan_distinct_hit_rows(item)
        ]
        case["scored_distinct_hits"] = scored
        case["best_scored_candidates"] = best_candidates(scored, top)


def summarize_count_scan_json(path: Path, score_small_seam: bool, top: int) -> dict:
    payload = json.loads(path.read_text())
    scan = payload.get("one_e_full_count_scan")
    if not isinstance(scan, list):
        raise ValueError("expected verifier JSON with one_e_full_count_scan")
    cases = [summarize_count_scan_case(item) for item in scan]
    summary = {
        "source": str(path),
        "schema": "d5_routeE_one_e_full_count_scan_summary_v1",
        "case_count": len(cases),
        "moduli": [case["m"] for case in cases],
        "known_present_moduli": [
            case["m"] for case in cases if case["known_present"]
        ],
        "alternative_present_moduli": [
            case["m"]
            for case in cases
            if case["alternative_distinct_count"] > 0
        ],
        "open_port_present_moduli": [
            case["m"] for case in cases if case["open_port_hit_count"] > 0
        ],
        "cases": cases,
    }
    if score_small_seam:
        score_count_scan_summary(summary, payload, top)
    return summary


def fit_affine_coordinate(points: Sequence[Tuple[int, int]]):
    if len(points) == 1:
        return {
            "status": "singleton",
            "formula": str(points[0][1]),
            "slope": frac_json(Fraction(0)),
            "intercept": frac_json(Fraction(points[0][1])),
        }
    x0, y0 = points[0]
    x1, y1 = points[-1]
    if x0 == x1:
        return {"status": "bad", "reason": "duplicate modulus"}
    slope = Fraction(y1 - y0, x1 - x0)
    intercept = Fraction(y0) - slope * x0
    for x, y in points:
        if slope * x + intercept != y:
            return {
                "status": "bad",
                "reason": "non_affine",
                "slope": frac_json(slope),
                "intercept": frac_json(intercept),
                "first_bad": {"m": x, "expected": frac_text(slope * x + intercept), "got": y},
            }
    return {
        "status": "ok",
        "formula": affine_text(slope, intercept),
        "slope": frac_json(slope),
        "intercept": frac_json(intercept),
    }


def fit_affine_vector(rows: Sequence[dict]) -> dict:
    fits = []
    ok = True
    singleton = len(rows) == 1
    for i in range(5):
        points = [(row["m"], row["fit_vector"][i]) for row in rows]
        fit = fit_affine_coordinate(points)
        fits.append(fit)
        ok = ok and fit["status"] in {"ok", "singleton"}
    return {
        "status": "singleton" if singleton else ("ok" if ok else "bad"),
        "formulas": [fit.get("formula") for fit in fits],
        "coordinate_fits": fits,
    }


def analyze_period(period: int, rows: Sequence[dict]) -> dict:
    groups: Dict[int, List[dict]] = defaultdict(list)
    for row in rows:
        groups[row["m"] % period].append(row)

    classes = []
    for residue, group in sorted(groups.items()):
        group = sorted(group, key=lambda row: row["m"])
        fit = fit_affine_vector(group)
        classes.append(
            {
                "residue": residue,
                "sample_count": len(group),
                "moduli": [row["m"] for row in group],
                "slots": [row["slot"] for row in group],
                "zero_positions": [row["zero_positions"] for row in group],
                "fit": fit,
            }
        )

    sample_counts = [item["sample_count"] for item in classes]
    bad = [item["residue"] for item in classes if item["fit"]["status"] == "bad"]
    robust = [
        item["residue"]
        for item in classes
        if item["sample_count"] >= 3 and item["fit"]["status"] == "ok"
    ]
    return {
        "period": period,
        "class_count": len(classes),
        "min_sample_count": min(sample_counts),
        "max_sample_count": max(sample_counts),
        "bad_residues": bad,
        "all_non_singleton_affine": not bad,
        "robust_affine_residues": robust,
        "singleton_residues": [
            item["residue"] for item in classes if item["fit"]["status"] == "singleton"
        ],
        "classes": classes,
    }


def parse_periods(text: str) -> List[int]:
    return [int(part) for part in text.split(",") if part.strip()]


def print_summary(results: Sequence[dict]) -> None:
    print("period classes min max bad robust singleton")
    for result in results:
        print(
            result["period"],
            result["class_count"],
            result["min_sample_count"],
            result["max_sample_count"],
            len(result["bad_residues"]),
            len(result["robust_affine_residues"]),
            len(result["singleton_residues"]),
        )


def print_count_scan_summary(summary: dict) -> None:
    print("count_scan m first_hits distinct open_hits open_distinct known_present alternatives zero_classes")
    for case in summary["cases"]:
        print(
            case["m"],
            case["first_hit_count"],
            case["distinct_normalized_count"],
            case["open_port_hit_count"],
            case["open_port_distinct_count"],
            case["known_present"],
            case["alternative_distinct_count"],
            len(case["zero_position_classes"]),
        )
        best = case.get("best_scored_candidates")
        if best is not None:
            for name in ["min_block", "open_first", "low_support"]:
                compact = [
                    {
                        "counts": item["normalized_counts_slot0"],
                        "blocks": item["block_count"],
                        "max": item["max_block_length"],
                        "support": item["support_count"],
                        "open": item["open_port_normal_form"],
                        "known": item["matches_known_normalized"],
                    }
                    for item in best[name]
                ]
                print("count_scan_best", case["m"], name, json.dumps(compact))


def compact_manifest(output: dict) -> dict:
    period_summaries = []
    for result in output["results"]:
        period_summaries.append(
            {
                "period": result["period"],
                "class_count": result["class_count"],
                "min_sample_count": result["min_sample_count"],
                "max_sample_count": result["max_sample_count"],
                "bad_residue_count": len(result["bad_residues"]),
                "bad_residues": result["bad_residues"],
                "all_non_singleton_affine": result["all_non_singleton_affine"],
                "robust_affine_residues": result["robust_affine_residues"],
                "singleton_residues": result["singleton_residues"],
            }
        )
    return {
        "schema": "d5_routeE_small_seam_family_scan_manifest_v1",
        "source": output["source"],
        "normalized_slot_zero": output["normalized_slot_zero"],
        "case_count": output["case_count"],
        "moduli": output["moduli"],
        "periods": [item["period"] for item in period_summaries],
        "bad_periods": [
            item["period"]
            for item in period_summaries
            if item["bad_residue_count"] != 0
        ],
        "nonrobust_affine_periods": [
            item["period"]
            for item in period_summaries
            if item["bad_residue_count"] == 0
            and not item["robust_affine_residues"]
        ],
        "robust_affine_periods": [
            item["period"]
            for item in period_summaries
            if item["robust_affine_residues"]
        ],
        "period_summaries": period_summaries,
    }


def compare_manifest(expected: dict, actual: dict) -> dict:
    keys = sorted(set(expected) | set(actual))
    mismatches = [key for key in keys if expected.get(key) != actual.get(key)]
    return {"ok": not mismatches, "mismatches": mismatches}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--periods",
        default=",".join(str(p) for p in DEFAULT_PERIODS),
        help="comma-separated residue periods to test",
    )
    parser.add_argument(
        "--raw-counts",
        action="store_true",
        help="fit raw slot/count vectors instead of normalized slot-zero vectors",
    )
    parser.add_argument("--json-out")
    parser.add_argument("--write-manifest", type=Path)
    parser.add_argument("--manifest", type=Path)
    parser.add_argument(
        "--count-scan-json",
        type=Path,
        help="summarize verifier JSON from verify_d5_even_routeE.py --count-scan-moduli",
    )
    parser.add_argument(
        "--score-count-scan-small-seam",
        action="store_true",
        help="score distinct count-scan hits by the small-seam block verifier",
    )
    parser.add_argument(
        "--count-scan-top",
        type=int,
        default=5,
        help="number of scored candidates to retain per objective",
    )
    args = parser.parse_args()

    rows = case_rows(normalized=not args.raw_counts)
    periods = parse_periods(args.periods)
    output = {
        "source": "verify_d5_even_routeE.SMALL_SEAM_CASES",
        "normalized_slot_zero": not args.raw_counts,
        "case_count": len(rows),
        "moduli": [row["m"] for row in rows],
        "results": [analyze_period(period, rows) for period in periods],
    }
    print_summary(output["results"])
    if args.count_scan_json is not None:
        output["count_scan_summary"] = summarize_count_scan_json(
            args.count_scan_json,
            score_small_seam=args.score_count_scan_small_seam,
            top=args.count_scan_top,
        )
        print_count_scan_summary(output["count_scan_summary"])
    manifest_check = None
    if args.write_manifest is not None:
        manifest = compact_manifest(output)
        args.write_manifest.parent.mkdir(parents=True, exist_ok=True)
        args.write_manifest.write_text(
            json.dumps(manifest, indent=2, sort_keys=True) + "\n"
        )
        print(f"wrote {args.write_manifest}")
    if args.manifest is not None:
        expected = json.loads(args.manifest.read_text())
        actual = compact_manifest(output)
        manifest_check = compare_manifest(expected, actual)
        output["manifest_check"] = manifest_check
        print("manifest_ok", manifest_check["ok"], "mismatches", manifest_check["mismatches"])
    if args.json_out:
        Path(args.json_out).write_text(json.dumps(output, indent=2) + "\n")
    if manifest_check is not None and not manifest_check["ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
