#!/usr/bin/env python3
"""Verify the R42 c-band qtime-atom fit diagnostic.

The current diagnostic is intentionally partial/negative: qtime slopes fit on
all sampled support atoms, but the first intercept model still fails on exactly
nine atoms in each parity branch.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_QTIME_ATOMS = ROOT / "certs" / "routeE_r42_carry_qtime_atoms.json"


def build_verification(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text())
    errors: list[dict[str, Any]] = []
    for branch in data.get("generic_subbranches", []):
        if branch.get("atom_key_count") != 116:
            errors.append({"branch": branch.get("name"), "bad_atom_key_count": branch.get("atom_key_count")})
        if branch.get("all_qtime_slopes_affine_in_s") is not True:
            errors.append({"branch": branch.get("name"), "bad_slope_atoms": branch.get("bad_slope_atoms")})
        if branch.get("all_qtime_intercepts_quadratic_s_linear_j") is not False:
            errors.append({"branch": branch.get("name"), "unexpected_intercept_success": True})
        if len(branch.get("bad_intercept_atoms", [])) != 9:
            errors.append({"branch": branch.get("name"), "bad_intercept_count": len(branch.get("bad_intercept_atoms", []))})
        for atom in branch.get("atoms", []):
            if atom.get("qtime_slope_formula") is None:
                errors.append({"branch": branch.get("name"), "atom": atom.get("atom"), "missing_slope_formula": True})
    ok = (
        data.get("schema") == "routeE_r42_carry_qtime_atoms_v1"
        and data.get("q_values") == [6, 7, 8, 9]
        and data.get("summary", {}).get("row_count") == 2988
        and data.get("summary", {}).get("all_branch_qtime_slopes_affine") is True
        and data.get("summary", {}).get("all_branch_qtime_intercepts_fit") is False
        and data.get("summary", {}).get("branch_atom_key_counts")
        == {"R42-even-q": 116, "R42-odd-q": 116}
        and data.get("promotion_impact", {}).get("closes_residue") is False
        and data.get("promotion_impact", {}).get("pointwise_equations_closed") is False
        and data.get("promotion_impact", {}).get("no_early_closed") is False
        and not errors
    )
    return {
        "schema": "routeE_r42_carry_qtime_atoms_verification_v1",
        "qtime_atoms": str(path),
        "ok": ok,
        "diagnostic_result": {
            "all_slopes_fit": data.get("summary", {}).get("all_branch_qtime_slopes_affine"),
            "intercept_model_fails_as_expected": data.get("summary", {}).get(
                "all_branch_qtime_intercepts_fit"
            )
            is False,
            "bad_intercept_atom_counts": {
                branch.get("name"): len(branch.get("bad_intercept_atoms", []))
                for branch in data.get("generic_subbranches", [])
            },
        },
        "q_values": data.get("q_values"),
        "row_count": data.get("summary", {}).get("row_count"),
        "branch_atom_key_counts": data.get("summary", {}).get("branch_atom_key_counts"),
        "error_count": len(errors),
        "errors": errors[:20],
        "promotion_impact": data.get("promotion_impact"),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--qtime-atoms", type=Path, default=DEFAULT_QTIME_ATOMS)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    payload = build_verification(args.qtime_atoms)
    print("schema", payload["schema"])
    print("ok", payload["ok"])
    print("q_values", payload["q_values"])
    print("row_count", payload["row_count"])
    print("branch_atom_key_counts", payload["branch_atom_key_counts"])
    print("error_count", payload["error_count"])
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")
    if not payload["ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
