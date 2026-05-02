#!/usr/bin/env python3
"""Summarize D5 Route-E small-seam translation-block traces.

The full verifier records, for each even m in the absorbed small-seam table,
the first-return map on the seam parameter a=1..m-1.  This script compresses
those traces into proof-facing block statistics: maximal intervals on which
V(a)-a is constant, low-complexity cases, and block-length fingerprints.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from fractions import Fraction
from pathlib import Path

import verify_d5_even_routeE as route_e


def load_or_compute(path: Path | None) -> list[dict]:
    if path is not None:
        payload = json.loads(path.read_text())
        if isinstance(payload, dict) and "small_seam" in payload:
            return payload["small_seam"]
        if isinstance(payload, list):
            return payload
        raise ValueError("expected a verifier JSON object with small_seam or a result list")
    return route_e.verify_small_seam_cases(sorted(route_e.SMALL_SEAM_CASES))


def case_summary(case: dict) -> dict:
    m = case["m"]
    blocks = case.get("translation_blocks", [])
    lengths = [block["length"] for block in blocks]
    deltas = [block["delta"] for block in blocks]
    length_hist = Counter(lengths)
    delta_hist = Counter(deltas)
    long_blocks = [
        block for block in blocks if block["length"] >= max(2, (m - 1 + 3) // 4)
    ]
    normalized = route_e.normalize_counts_to_slot0(case["slot"], tuple(case["counts"]))
    return {
        "m": m,
        "ok": case.get("ok", False),
        "slot": case.get("slot"),
        "counts": case.get("counts"),
        "normalized_counts_slot0": normalized,
        "zero_positions": [i for i, count in enumerate(normalized) if count == 0],
        "support": [i for i, count in enumerate(normalized) if count != 0],
        "seam_size": case.get("seam_size"),
        "return_time_sum": case.get("return_time_sum"),
        "expected_return_time_sum": case.get("expected_return_time_sum"),
        "block_count": len(blocks),
        "max_block_length": max(lengths) if lengths else 0,
        "singleton_blocks": length_hist.get(1, 0),
        "non_singleton_blocks": len(blocks) - length_hist.get(1, 0),
        "length_histogram": dict(sorted(length_hist.items())),
        "delta_histogram_top": [
            {"delta": delta, "count": count}
            for delta, count in delta_hist.most_common(8)
        ],
        "long_blocks": long_blocks,
        "orbit_prefix_from_1": case.get("orbit_prefix_from_1", []),
    }


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


def fit_affine_coordinate(points: list[tuple[int, int]]) -> dict:
    if len(points) == 1:
        value = points[0][1]
        return {
            "status": "singleton",
            "formula": str(value),
            "slope": frac_json(Fraction(0)),
            "intercept": frac_json(Fraction(value)),
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
                "first_bad": {
                    "m": x,
                    "expected": frac_text(slope * x + intercept),
                    "got": y,
                },
            }
    return {
        "status": "ok",
        "formula": affine_text(slope, intercept),
        "slope": frac_json(slope),
        "intercept": frac_json(intercept),
    }


def fit_affine_counts(items: list[dict]) -> dict:
    ordered = sorted(items, key=lambda item: item["m"])
    fits = []
    ok = True
    for i in range(5):
      points = [
          (item["m"], item["normalized_counts_slot0"][i]) for item in ordered
      ]
      fit = fit_affine_coordinate(points)
      fits.append(fit)
      ok = ok and fit["status"] in {"ok", "singleton"}
    return {
        "status": "singleton" if len(ordered) == 1 else ("ok" if ok else "bad"),
        "formulas": [fit.get("formula") for fit in fits],
        "coordinate_fits": fits,
    }


def cluster_by_key(items: list[dict], key_name: str) -> list[dict]:
    groups: dict[tuple[int, ...], list[dict]] = {}
    for item in items:
        key = tuple(item[key_name])
        groups.setdefault(key, []).append(item)
    clusters = []
    for key, group in sorted(groups.items(), key=lambda pair: (pair[0], pair[1][0]["m"])):
        low = [item["m"] for item in group if item["block_count"] <= 10]
        long = [
            item["m"]
            for item in group
            if item["max_block_length"] >= item["m"] // 4
        ]
        affine_fit = fit_affine_counts(group)
        clusters.append(
            {
                key_name: list(key),
                "sample_count": len(group),
                "moduli": [item["m"] for item in group],
                "block_counts": [item["block_count"] for item in group],
                "max_block_lengths": [item["max_block_length"] for item in group],
                "low_block_moduli": low,
                "long_block_moduli": long,
                "robust_affine": len(group) >= 3 and affine_fit["status"] == "ok",
                "affine_fit": affine_fit,
            }
        )
    return clusters


def summarize(cases: list[dict]) -> dict:
    summaries = [case_summary(case) for case in sorted(cases, key=lambda c: c["m"])]
    low_block_cases = [
        item for item in summaries if item["ok"] and item["block_count"] <= 10
    ]
    long_block_cases = [
        item for item in summaries if item["ok"] and item["max_block_length"] >= item["m"] // 4
    ]
    mostly_singleton_cases = [
        item
        for item in summaries
        if item["ok"] and item["singleton_blocks"] * 2 >= item["block_count"]
    ]
    zero_clusters = cluster_by_key(summaries, "zero_positions")
    support_clusters = cluster_by_key(summaries, "support")
    return {
        "source": "verify_d5_even_routeE.SMALL_SEAM_CASES",
        "case_count": len(summaries),
        "all_ok": all(item["ok"] for item in summaries),
        "return_sums_ok": all(
            item["return_time_sum"] == item["expected_return_time_sum"]
            for item in summaries
        ),
        "moduli": [item["m"] for item in summaries],
        "block_count_by_m": {
            str(item["m"]): item["block_count"] for item in summaries
        },
        "low_block_cases": [
            {
                "m": item["m"],
                "block_count": item["block_count"],
                "max_block_length": item["max_block_length"],
                "normalized_counts_slot0": item["normalized_counts_slot0"],
                "long_blocks": item["long_blocks"],
            }
            for item in low_block_cases
        ],
        "long_block_cases": [
            {
                "m": item["m"],
                "block_count": item["block_count"],
                "max_block_length": item["max_block_length"],
                "long_blocks": item["long_blocks"],
            }
            for item in long_block_cases
        ],
        "mostly_singleton_moduli": [item["m"] for item in mostly_singleton_cases],
        "zero_position_clusters": zero_clusters,
        "support_clusters": support_clusters,
        "robust_affine_zero_position_clusters": [
            cluster for cluster in zero_clusters if cluster["robust_affine"]
        ],
        "robust_affine_support_clusters": [
            cluster for cluster in support_clusters if cluster["robust_affine"]
        ],
        "cases": summaries,
    }


def print_text(summary: dict) -> None:
    print(
        "cases",
        summary["case_count"],
        "all_ok",
        summary["all_ok"],
        "return_sums_ok",
        summary["return_sums_ok"],
    )
    print("m block_count max_block singleton non_singleton")
    for item in summary["cases"]:
        print(
            item["m"],
            item["block_count"],
            item["max_block_length"],
            item["singleton_blocks"],
            item["non_singleton_blocks"],
        )
    print("low_block_moduli", [item["m"] for item in summary["low_block_cases"]])
    print("long_block_moduli", [item["m"] for item in summary["long_block_cases"]])
    print(
        "robust_affine_zero_position_clusters",
        [
            cluster["zero_positions"]
            for cluster in summary["robust_affine_zero_position_clusters"]
        ],
    )
    print(
        "robust_affine_support_clusters",
        [cluster["support"] for cluster in summary["robust_affine_support_clusters"]],
    )
    print("zero_position_clusters")
    for cluster in summary["zero_position_clusters"]:
        print(
            cluster["zero_positions"],
            "moduli",
            cluster["moduli"],
            "fit",
            cluster["affine_fit"]["status"],
        )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--verify-json",
        type=Path,
        help="reuse JSON emitted by verify_d5_even_routeE.py --small-seam-moduli",
    )
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    summary = summarize(load_or_compute(args.verify_json))
    print_text(summary)
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
