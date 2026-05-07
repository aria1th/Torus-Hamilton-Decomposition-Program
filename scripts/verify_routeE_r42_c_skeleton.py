#!/usr/bin/env python3
"""Verify the R42 c-parameter skeleton artifact."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SKELETON = ROOT / "certs" / "routeE_r42_c_skeleton.json"

EXPECTED_ROWS = {
    ("03", "03"): ("1", "1"),
    ("03", "04"): ("30*q + 25", "5*c"),
    ("03", "34"): ("18*q + 15", "3*c"),
    ("03", "Z"): ("0", "0"),
    ("04", "03"): ("30*q + 24", "5*c - 1"),
    ("04", "04"): ("0", "0"),
    ("04", "34"): ("18*q + 16", "3*c + 1"),
    ("04", "Z"): ("1", "1"),
    ("34", "03"): ("18*q + 15", "3*c"),
    ("34", "04"): ("18*q + 16", "3*c + 1"),
    ("34", "34"): ("12*q + 10", "2*c"),
    ("34", "Z"): ("0", "0"),
    ("Z", "03"): ("1", "1"),
    ("Z", "04"): ("0", "0"),
    ("Z", "34"): ("0", "0"),
    ("Z", "Z"): ("0", "0"),
}

EXPECTED_ROW_SUMS = {
    "03": "1 + 5*c + 3*c = 8*c + 1 = m - 1",
    "04": "(5*c - 1) + (3*c + 1) + 1 = 8*c + 1 = m - 1",
    "34": "3*c + (3*c + 1) + 2*c = 8*c + 1 = m - 1",
    "Z": "1",
}


def build_verification(skeleton_path: Path) -> dict[str, Any]:
    data = json.loads(skeleton_path.read_text())
    errors: list[dict[str, Any]] = []
    rows = {
        (row.get("src"), row.get("dst")): row
        for row in data.get("transition_rows", [])
    }
    for key, (q_formula, c_formula) in EXPECTED_ROWS.items():
        row = rows.get(key)
        if row is None:
            errors.append({"missing_row": key})
            continue
        actual = (row.get("q_formula"), row.get("c_formula"), row.get("ok"))
        expected = (q_formula, c_formula, True)
        if actual != expected:
            errors.append({"row": key, "expected": expected, "actual": actual})

    inverse_units = {
        item.get("unit"): item for item in data.get("modular_inverse_identities", [])
    }
    expected_inverses = {
        "c": {
            "inverse_mod_m": "4*c - 3",
            "identity": "c*(4*c - 3) - 1 = ((c - 1)/2)*(8*c + 2)",
        },
        "6*c + 1": {
            "inverse_mod_m": "4*c - 1",
            "identity": "(6*c + 1)*(4*c - 1) - 1 = (3*c - 1)*(8*c + 2)",
        },
    }
    for unit, expected in expected_inverses.items():
        actual = inverse_units.get(unit)
        if actual is None:
            errors.append({"missing_inverse_identity": unit})
            continue
        for field, value in expected.items():
            if actual.get(field) != value:
                errors.append(
                    {
                        "unit": unit,
                        "field": field,
                        "expected": value,
                        "actual": actual.get(field),
                    }
                )

    hint = data.get("clock_carry_hint", {})
    ok = (
        data.get("schema") == "routeE_r42_c_skeleton_v1"
        and data.get("branch") == "R42"
        and data.get("parameters", {}).get("old")
        == "m = 48*q + 42, x = z = 6*q + 5"
        and data.get("parameters", {}).get("new")
        == "c = 6*q + 5, m = 8*c + 2, x = z = c"
        and data.get("parameters", {}).get("c_congruence") == "c \u2261 5 mod 6"
        and data.get("checks", {}).get(
            "all_transition_formulas_match_expected_c_skeleton"
        )
        is True
        and data.get("checks", {}).get("error_count") == 0
        and data.get("row_sum_formulas") == EXPECTED_ROW_SUMS
        and hint.get("source_coordinate_decomposition") == "a = j*c + u"
        and hint.get("prototype_edge", {}).get("edge") == "25 -> 3"
        and hint.get("prototype_edge", {}).get("interval_count")
        == "m/6 = (4*c + 1)/3"
        and hint.get("prototype_edge", {}).get("member_count")
        == "(m - 2)/4 = 2*c"
        and data.get("promotion_impact", {}).get("closes_residue") is False
        and data.get("promotion_impact", {}).get("pointwise_equations_closed")
        is False
        and data.get("promotion_impact", {}).get("no_early_closed") is False
        and not errors
    )
    return {
        "schema": "routeE_r42_c_skeleton_verification_v1",
        "skeleton": str(skeleton_path),
        "ok": ok,
        "transition_row_count": len(data.get("transition_rows", [])),
        "error_count": len(errors),
        "errors": errors[:20],
        "promotion_impact": data.get("promotion_impact"),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--skeleton", type=Path, default=DEFAULT_SKELETON)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    payload = build_verification(args.skeleton)
    print("schema", payload["schema"])
    print("ok", payload["ok"])
    print("transition_row_count", payload["transition_row_count"])
    print("error_count", payload["error_count"])
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")
    if not payload["ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
