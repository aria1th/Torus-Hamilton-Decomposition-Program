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
from collections import defaultdict
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
    if args.json_out:
        Path(args.json_out).write_text(json.dumps(output, indent=2) + "\n")


if __name__ == "__main__":
    main()
