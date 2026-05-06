#!/usr/bin/env python3
"""Fit simple residue-wise formulas in the Route-E all-pair portfolio.

The portfolio samples are not proofs, but residue classes whose parameters fit
small affine laws are better candidates for symbolic branch promotion.  This
script groups samples by `m mod 48` and fits `x`, `z`, and `nodes` as affine
functions of `q = (m - residue) / 48`.
"""

from __future__ import annotations

import argparse
import json
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SOURCE = ROOT / "certs" / "routeE_allpair_portfolio_samples_v1_1.json"
DEFAULT_COVERAGE = ROOT / "certs" / "routeE_typeA_residue_coverage.json"


def frac_json(value: Fraction) -> dict[str, int]:
    return {"num": value.numerator, "den": value.denominator}


def frac_text(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def affine_text(slope: Fraction, intercept: Fraction, variable: str = "q") -> str:
    if slope == 0:
        return frac_text(intercept)
    if slope == 1:
        head = variable
    elif slope == -1:
        head = f"-{variable}"
    else:
        head = f"{frac_text(slope)}*{variable}"
    if intercept == 0:
        return head
    sign = "+" if intercept > 0 else "-"
    return f"{head} {sign} {frac_text(abs(intercept))}"


def fit_affine(rows: list[dict[str, Any]], key: str) -> dict[str, Any]:
    if len(rows) == 1:
        value = Fraction(int(rows[0][key]))
        return {
            "status": "singleton",
            "formula": frac_text(value),
            "slope": frac_json(Fraction(0)),
            "intercept": frac_json(value),
        }
    first = rows[0]
    last = rows[-1]
    q0, y0 = int(first["q"]), int(first[key])
    q1, y1 = int(last["q"]), int(last[key])
    if q0 == q1:
        return {"status": "bad", "reason": "duplicate q"}
    slope = Fraction(y1 - y0, q1 - q0)
    intercept = Fraction(y0) - slope * q0
    for row in rows:
        q = int(row["q"])
        y = int(row[key])
        expected = slope * q + intercept
        if expected != y:
            return {
                "status": "bad",
                "reason": "non_affine",
                "formula_from_endpoints": affine_text(slope, intercept),
                "slope": frac_json(slope),
                "intercept": frac_json(intercept),
                "first_bad": {
                    "q": q,
                    "m": int(row["m"]),
                    "expected": frac_text(expected),
                    "got": y,
                },
            }
    return {
        "status": "ok",
        "formula": affine_text(slope, intercept),
        "slope": frac_json(slope),
        "intercept": frac_json(intercept),
    }


def summarize(source: Path, coverage_path: Path, modulus: int) -> dict[str, Any]:
    payload = json.loads(source.read_text())
    coverage = json.loads(coverage_path.read_text()) if coverage_path.exists() else {}
    proof_facing = sorted(int(x) for x in coverage.get("covered_residues_mod_48", []))

    by_residue: dict[int, list[dict[str, Any]]] = defaultdict(list)
    for sample in payload.get("samples", []):
        m = int(sample["m"])
        residue = m % modulus
        row = {
            **sample,
            "m": m,
            "residue": residue,
            "q": (m - residue) // modulus,
            "x": int(sample["x"]),
            "z": int(sample["z"]),
            "nodes": int(sample["nodes"]),
            "time_sum_target": int(sample["time_sum_target"]),
            "count_admissible": str(sample.get("count_admissible")) in {"1", "true", "True"},
        }
        by_residue[residue].append(row)

    rows = []
    for residue in sorted(by_residue):
        group = sorted(by_residue[residue], key=lambda row: row["q"])
        fit_x = fit_affine(group, "x")
        fit_z = fit_affine(group, "z")
        fit_nodes = fit_affine(group, "nodes")
        row = {
            "residue": residue,
            "sample_count": len(group),
            "moduli": [item["m"] for item in group],
            "q_values": [item["q"] for item in group],
            "tags": sorted({str(item.get("tag")) for item in group}),
            "proof_facing": residue in set(proof_facing),
            "all_count_admissible": all(item["count_admissible"] for item in group),
            "fit_x": fit_x,
            "fit_z": fit_z,
            "fit_nodes": fit_nodes,
            "xz_affine": fit_x["status"] == "ok" and fit_z["status"] == "ok",
            "samples": [
                {
                    "m": item["m"],
                    "q": item["q"],
                    "x": item["x"],
                    "z": item["z"],
                    "tag": item.get("tag"),
                    "nodes": item["nodes"],
                }
                for item in group
            ],
        }
        rows.append(row)

    affine_xz = [row["residue"] for row in rows if row["xz_affine"]]
    portfolio_only_affine_xz = [
        row["residue"] for row in rows if row["xz_affine"] and not row["proof_facing"]
    ]
    return {
        "schema": "routeE_allpair_portfolio_fit_summary_v1",
        "source": str(source),
        "residue_modulus": modulus,
        "sample_count": len(payload.get("samples", [])),
        "residue_count": len(rows),
        "proof_facing_typeA_residues": proof_facing,
        "affine_xz_residues": affine_xz,
        "portfolio_only_affine_xz_residues": portfolio_only_affine_xz,
        "next_symbolic_candidate": (
            portfolio_only_affine_xz[0] if portfolio_only_affine_xz else None
        ),
        "rows": rows,
        "interpretation": (
            "Residues with xz_affine=true have sample parameters compatible "
            "with a simple affine x/z law.  They still need branch formulas, "
            "first-return equations, no-early proofs, and time identities."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, default=DEFAULT_SOURCE)
    parser.add_argument("--coverage", type=Path, default=DEFAULT_COVERAGE)
    parser.add_argument("--modulus", type=int, default=48)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    summary = summarize(args.source, args.coverage, args.modulus)
    print(
        "residues",
        summary["residue_count"],
        "affine_xz",
        summary["affine_xz_residues"],
        "portfolio_only_affine_xz",
        summary["portfolio_only_affine_xz_residues"],
    )
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
