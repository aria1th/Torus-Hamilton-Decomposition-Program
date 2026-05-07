#!/usr/bin/env python3
"""Record the R42 branch in the natural c-parameter.

R42 was found as m=48*q+42, x=z=6*q+5.  Setting c=6*q+5 gives
m=8*c+2 and x=z=c.  This script rewrites the coarse boundary transition
counts into the simpler 5c/3c/2c skeleton and records the modular inverse
identities used by the proposed clock-carry refinement.
"""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_BOUNDARY = ROOT / "certs" / "routeE_r42_boundary_quotient_summary.json"

FORMULA_RE = re.compile(r"^\s*(?:(-?\d+)\*?q)?(?:\s*([+-])\s*(\d+))?\s*$")


@dataclass(frozen=True)
class LinearQ:
    slope: int
    intercept: int

    def at_q(self, q: int) -> int:
        return self.slope * q + self.intercept


@dataclass(frozen=True)
class LinearC:
    slope: int
    intercept: int

    def formula(self) -> str:
        if self.slope == 0:
            return str(self.intercept)
        term = "c" if self.slope == 1 else f"{self.slope}*c"
        if self.intercept == 0:
            return term
        sign = "+" if self.intercept > 0 else "-"
        return f"{term} {sign} {abs(self.intercept)}"

    def at_c(self, c: int) -> int:
        return self.slope * c + self.intercept


def parse_q_formula(text: str) -> LinearQ:
    text = str(text).strip()
    if text == "q":
        return LinearQ(1, 0)
    if "q" not in text:
        return LinearQ(0, int(text))
    match = FORMULA_RE.match(text)
    if match is None:
        raise ValueError(f"unsupported q formula: {text!r}")
    slope = int(match.group(1) or 1)
    intercept = 0
    if match.group(2):
        value = int(match.group(3))
        intercept = value if match.group(2) == "+" else -value
    return LinearQ(slope, intercept)


def convert_q_to_c(formula: str) -> LinearC | None:
    q = parse_q_formula(formula)
    # c=6q+5, so aq+b = (a/6)c + (b - 5a/6).  We keep only integral
    # c-linear laws here; those are exactly the clean skeleton laws.
    if q.slope % 6:
        return None
    slope = q.slope // 6
    intercept = q.intercept - 5 * slope
    return LinearC(slope, intercept)


EXPECTED_C_FORMULAS = {
    ("03", "03"): "1",
    ("03", "04"): "5*c",
    ("03", "34"): "3*c",
    ("03", "Z"): "0",
    ("04", "03"): "5*c - 1",
    ("04", "04"): "0",
    ("04", "34"): "3*c + 1",
    ("04", "Z"): "1",
    ("34", "03"): "3*c",
    ("34", "04"): "3*c + 1",
    ("34", "34"): "2*c",
    ("34", "Z"): "0",
    ("Z", "03"): "1",
    ("Z", "04"): "0",
    ("Z", "34"): "0",
    ("Z", "Z"): "0",
}


def build_summary(boundary_path: Path) -> dict[str, Any]:
    boundary = json.loads(boundary_path.read_text())
    q_fits = boundary.get("q_ge_1_transition_count_fits", {})
    rows = []
    errors = []
    for src in ["03", "04", "34", "Z"]:
        for dst in ["03", "04", "34", "Z"]:
            q_formula = q_fits.get(src, {}).get(dst)
            converted = convert_q_to_c(q_formula) if q_formula is not None else None
            c_formula = converted.formula() if converted is not None else None
            expected = EXPECTED_C_FORMULAS[(src, dst)]
            ok = c_formula == expected
            if not ok:
                errors.append(
                    {
                        "src": src,
                        "dst": dst,
                        "q_formula": q_formula,
                        "c_formula": c_formula,
                        "expected": expected,
                    }
                )
            rows.append(
                {
                    "src": src,
                    "dst": dst,
                    "q_formula": q_formula,
                    "c_formula": c_formula,
                    "expected_c_formula": expected,
                    "ok": ok,
                }
            )
    row_sum_formulas = {
        "03": "1 + 5*c + 3*c = 8*c + 1 = m - 1",
        "04": "(5*c - 1) + (3*c + 1) + 1 = 8*c + 1 = m - 1",
        "34": "3*c + (3*c + 1) + 2*c = 8*c + 1 = m - 1",
        "Z": "1",
    }
    return {
        "schema": "routeE_r42_c_skeleton_v1",
        "source": str(boundary_path),
        "branch": "R42",
        "parameters": {
            "old": "m = 48*q + 42, x = z = 6*q + 5",
            "new": "c = 6*q + 5, m = 8*c + 2, x = z = c",
            "c_congruence": "c ≡ 5 mod 6",
        },
        "transition_rows": rows,
        "row_sum_formulas": row_sum_formulas,
        "modular_inverse_identities": [
            {
                "unit": "c",
                "inverse_mod_m": "4*c - 3",
                "identity": "c*(4*c - 3) - 1 = ((c - 1)/2)*(8*c + 2)",
                "side_condition": "c is odd",
            },
            {
                "unit": "6*c + 1",
                "inverse_mod_m": "4*c - 1",
                "identity": "(6*c + 1)*(4*c - 1) - 1 = (3*c - 1)*(8*c + 2)",
                "side_condition": "none beyond m=8*c+2",
            },
        ],
        "coarse_skeleton": {
            "03": {"04": "5*c", "34": "3*c", "self_or_Z": "1"},
            "04": {"03": "5*c - 1", "34": "3*c + 1", "Z": "1"},
            "34": {"03": "3*c", "04": "3*c + 1", "34": "2*c"},
        },
        "clock_carry_hint": {
            "source_coordinate_decomposition": "a = j*c + u",
            "band_count": "8 full c-bands plus endpoint correction since m = 8*c + 2",
            "expected_refined_state": [
                "boundary block",
                "c-band j",
                "zero-clock winner",
                "wrap/carry residue",
            ],
            "prototype_edge": {
                "edge": "25 -> 3",
                "interval_count": "m/6 = (4*c + 1)/3",
                "member_count": "(m - 2)/4 = 2*c",
                "diagnosis": "balanced Beatty/rotation-carry interval word, not simple ordinal order",
            },
        },
        "checks": {
            "all_transition_formulas_match_expected_c_skeleton": not errors,
            "error_count": len(errors),
            "errors": errors,
        },
        "promotion_impact": {
            "closes_residue": False,
            "pointwise_equations_closed": False,
            "no_early_closed": False,
            "diagnosis": (
                "This records the natural c-parameter skeleton for R42.  It "
                "explains the coarse transition ratios but does not prove the "
                "clock-carry qtime grammar."
            ),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--boundary", type=Path, default=DEFAULT_BOUNDARY)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    payload = build_summary(args.boundary)
    print("schema", payload["schema"])
    print(
        "all_transition_formulas_match_expected_c_skeleton",
        payload["checks"]["all_transition_formulas_match_expected_c_skeleton"],
    )
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
