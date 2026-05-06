#!/usr/bin/env python3
"""Verify the R42 boundary block-transducer diagnostic artifact."""

from __future__ import annotations

import argparse
import json
import re
from fractions import Fraction
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SUMMARY = ROOT / "certs" / "routeE_r42_boundary_block_transducer.json"
FORMULA_RE = re.compile(r"^\s*([+-]?\d+)\*q(?:\s*([+-])\s*(\d+))?\s*$")


def eval_formula(expr: str | None, q: int) -> int | None:
    if expr is None:
        return None
    expr = str(expr)
    if "*q" not in expr:
        return int(expr)
    match = FORMULA_RE.match(expr)
    if match is None:
        raise ValueError(f"unsupported formula: {expr!r}")
    value = int(match.group(1)) * q
    if match.group(2):
        term = int(match.group(3))
        value += term if match.group(2) == "+" else -term
    return value


def eval_piecewise(spec: dict[str, Any], q: int) -> int | None:
    kind = spec.get("kind")
    if kind == "affine":
        return eval_rational_fit(spec, q)
    if kind == "residue_affine":
        modulus = int(spec["modulus"])
        fit = spec.get("residue_formulas", {}).get(str(q % modulus))
        return eval_rational_fit(fit, q)
    return None


def eval_rational_fit(fit: dict[str, Any] | None, q: int) -> int | None:
    if not fit:
        return None
    value = Fraction(fit.get("slope", "0")) * q + Fraction(
        fit.get("intercept", "0")
    )
    if value.denominator != 1:
        return None
    return value.numerator


def build_verification(summary_path: Path) -> dict[str, Any]:
    data = json.loads(summary_path.read_text())
    samples = data.get("samples", [])
    generic = [sample for sample in samples if sample.get("q", 0) >= 2]
    edge_fit_errors = []
    piecewise_fit_errors = []
    for fit in data.get("q_ge_2_edge_count_fits", []):
        for q, actual in fit.get("sample_points", []):
            expected = eval_formula(fit.get("formula"), int(q))
            if fit.get("formula") is not None and expected != actual:
                edge_fit_errors.append(
                    {
                        "src": fit.get("src"),
                        "dst": fit.get("dst"),
                        "q": q,
                        "formula": fit.get("formula"),
                        "expected": expected,
                        "actual": actual,
                    }
                )
            piecewise_expected = eval_piecewise(
                fit.get("piecewise_formula", {}), int(q)
            )
            if piecewise_expected != actual:
                piecewise_fit_errors.append(
                    {
                        "src": fit.get("src"),
                        "dst": fit.get("dst"),
                        "q": q,
                        "piecewise_formula": fit.get("piecewise_formula"),
                        "expected": piecewise_expected,
                        "actual": actual,
                    }
                )
    per_sample_checks = []
    for sample in samples:
        target_block_total = sum(sample.get("target_histogram", {}).values())
        per_sample_checks.append(
            {
                "q": sample.get("q"),
                "ok": sample.get("ok") is True,
                "block_count_ok": sample.get("block_count") == 29,
                "assignment_ok": sample.get("assignment_ok") is True,
                "boundary_single_cycle": sample.get("boundary_single_cycle") is True,
                "target_histogram_total_ok": target_block_total == 29,
                "support_strongly_connected": sample.get("support_strongly_connected")
                is True,
            }
        )
    generic_supports = [
        {(edge["src"], edge["dst"]) for edge in sample.get("edge_counts", [])}
        for sample in generic
    ]
    support_stable = bool(generic_supports) and all(
        support == generic_supports[0] for support in generic_supports
    )
    edge_fit_ok = (
        data.get("summary", {}).get("edge_count_fits_all_affine") is True
        and not edge_fit_errors
    ) or (
        data.get("summary", {}).get("edge_count_fits_all_piecewise_affine") is True
        and data.get("summary", {}).get("edge_count_piecewise_moduli") == [2]
        and not piecewise_fit_errors
    )
    ok = (
        data.get("schema") == "routeE_r42_boundary_block_transducer_v1"
        and all(all(check.values()) for check in per_sample_checks)
        and data.get("summary", {}).get("q_ge_2_support_stable") is True
        and support_stable
        and data.get("summary", {}).get("q_ge_2_edge_count") == 69
        and data.get("summary", {}).get("q_ge_2_support_strongly_connected")
        is True
        and edge_fit_ok
        and data.get("promotion_impact", {}).get("pointwise_equations_closed")
        is False
        and data.get("promotion_impact", {}).get("no_early_closed") is False
    )
    return {
        "schema": "routeE_r42_boundary_block_transducer_verification_v1",
        "summary": str(summary_path),
        "ok": ok,
        "sample_count": len(samples),
        "q_values": [sample.get("q") for sample in samples],
        "per_sample_checks": per_sample_checks,
        "edge_fit_error_count": len(edge_fit_errors),
        "edge_fit_errors": edge_fit_errors[:20],
        "piecewise_fit_error_count": len(piecewise_fit_errors),
        "piecewise_fit_errors": piecewise_fit_errors[:20],
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
    print("sample_count", payload["sample_count"])
    print("edge_fit_error_count", payload["edge_fit_error_count"])
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")
    if not payload["ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
