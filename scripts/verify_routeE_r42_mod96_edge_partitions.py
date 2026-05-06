#!/usr/bin/env python3
"""Verify the R42 mod-96 edge-partition diagnostic.

This intentionally verifies only diagnostic invariants.  The artifact is not a
pointwise first-return theorem: target and time formulas are allowed to remain
incomplete, and the promotion impact must say so.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SUMMARY = ROOT / "certs" / "routeE_r42_mod96_edge_partitions.json"
FORMULA_RE = re.compile(r"^\s*([+-]?\d+)?\*?s(?:\s*([+-])\s*(\d+))?\s*$")


def eval_formula(expr: str | None, s: int) -> int | None:
    if expr is None:
        return None
    expr = str(expr).strip()
    if "s" not in expr:
        return int(expr)
    if expr == "s":
        return s
    match = FORMULA_RE.match(expr)
    if match is None:
        raise ValueError(f"unsupported formula: {expr!r}")
    coeff = match.group(1)
    slope = int(coeff) if coeff not in {None, "", "+"} else 1
    value = slope * s
    if match.group(2):
        term = int(match.group(3))
        value += term if match.group(2) == "+" else -term
    return value


def check_branch(branch: dict[str, Any], errors: list[dict[str, Any]]) -> None:
    for row in branch.get("edge_partition_formulas", []):
        for key, field in [
            ("count_formula", "count"),
            ("min_formula", "min"),
            ("max_formula", "max"),
            ("interval_count_formula", "interval_count"),
        ]:
            formula = row.get(key)
            if formula is None:
                errors.append(
                    {
                        "branch": branch.get("name"),
                        "src": row.get("src"),
                        "dst": row.get("dst"),
                        "missing_formula": key,
                    }
                )
                continue
            for sample in branch.get("sample_s_values", []):
                # The per-row artifact stores formulas but not every sampled
                # condition value again; this check keeps formula syntax live.
                try:
                    eval_formula(formula, int(sample))
                except Exception as exc:  # pragma: no cover - diagnostic path
                    errors.append(
                        {
                            "branch": branch.get("name"),
                            "src": row.get("src"),
                            "dst": row.get("dst"),
                            "formula": key,
                            "sample_s": sample,
                            "error": str(exc),
                        }
                    )
        if row.get("qsteps_slope_formula") is not None:
            for sample in branch.get("sample_s_values", []):
                eval_formula(row.get("qsteps_slope_formula"), int(sample))
        if row.get("qsteps_intercept_formula") is not None:
            for sample in branch.get("sample_s_values", []):
                eval_formula(row.get("qsteps_intercept_formula"), int(sample))


def build_verification(summary_path: Path) -> dict[str, Any]:
    data = json.loads(summary_path.read_text())
    errors: list[dict[str, Any]] = []
    for branch in data.get("generic_subbranches", []):
        check_branch(branch, errors)

    branches = {branch.get("name"): branch for branch in data.get("generic_subbranches", [])}
    even = branches.get("R42-even-q", {})
    odd = branches.get("R42-odd-q", {})
    summary = data.get("summary", {})
    ok = (
        data.get("schema") == "routeE_r42_mod96_edge_partitions_v1"
        and summary.get("q_values") == [2, 3, 4, 5, 6]
        and summary.get("all_samples_ok") is True
        and summary.get("all_branch_edge_counts_69") is True
        and summary.get("all_count_formulas_affine_in_s") is True
        and summary.get("all_condition_bounds_affine_in_s") is True
        and summary.get("all_qsteps_affine_coeffs_affine_in_s") is True
        and summary.get("all_target_affine_maps_stable") is False
        and summary.get("all_target_affine_coeffs_affine_in_s") is False
        and summary.get("all_qtime_affine_maps_stable") is False
        and summary.get("all_qtime_affine_coeffs_affine_in_s") is False
        and summary.get("all_qsteps_affine_maps_stable") is False
        and even.get("edge_count") == 69
        and odd.get("edge_count") == 69
        and even.get("sample_q_values") == [2, 4, 6]
        and odd.get("sample_q_values") == [3, 5]
        and even.get("diagnostic_counts", {}).get("target_coeffs_nonaffine_edges") == 7
        and odd.get("diagnostic_counts", {}).get("target_coeffs_nonaffine_edges") == 0
        and even.get("diagnostic_counts", {}).get("qtime_coeffs_missing_edges") == 22
        and odd.get("diagnostic_counts", {}).get("qtime_coeffs_missing_edges") == 22
        and data.get("promotion_impact", {}).get("closes_residue") is False
        and data.get("promotion_impact", {}).get("pointwise_equations_closed") is False
        and data.get("promotion_impact", {}).get("no_early_closed") is False
        and not errors
    )
    return {
        "schema": "routeE_r42_mod96_edge_partitions_verification_v1",
        "summary": str(summary_path),
        "ok": ok,
        "q_values": summary.get("q_values"),
        "branch_edge_counts": {
            name: branch.get("edge_count") for name, branch in branches.items()
        },
        "diagnostic_counts": {
            name: branch.get("diagnostic_counts") for name, branch in branches.items()
        },
        "error_count": len(errors),
        "errors": errors[:20],
        "promotion_impact": data.get("promotion_impact"),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--summary", type=Path, default=DEFAULT_SUMMARY)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    payload = build_verification(args.summary)
    print("schema", payload["schema"])
    print("ok", payload["ok"])
    print("q_values", payload["q_values"])
    print("error_count", payload["error_count"])
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")
    if not payload["ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
