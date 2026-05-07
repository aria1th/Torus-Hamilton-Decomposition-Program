#!/usr/bin/env python3
"""Verify the R42 c-band support-atom diagnostic."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_ATOMS = ROOT / "certs" / "routeE_r42_carry_support_atoms.json"


def build_verification(atoms_path: Path) -> dict[str, Any]:
    data = json.loads(atoms_path.read_text())
    errors: list[dict[str, Any]] = []
    expected_nonaffine = {str(q): 22 for q in [6, 7, 8, 9]}
    for sample in data.get("samples", []):
        q = sample.get("q")
        c = sample.get("c")
        if c != 6 * q + 5:
            errors.append({"q": q, "bad_c": c})
        if sample.get("m") != 8 * c + 2:
            errors.append({"q": q, "bad_m": sample.get("m")})
        if sample.get("nonaffine_edge_count") != 22:
            errors.append(
                {"q": q, "bad_nonaffine_edge_count": sample.get("nonaffine_edge_count")}
            )
    for branch in data.get("generic_subbranches", []):
        if branch.get("missing_atom_sample_count") != 0:
            errors.append(
                {
                    "branch": branch.get("name"),
                    "missing_atom_sample_count": branch.get("missing_atom_sample_count"),
                }
            )
        if branch.get("all_atom_counts_affine_in_s") is not True:
            errors.append({"branch": branch.get("name"), "atom_counts_not_affine": True})
        if branch.get("all_j_ranges_affine_in_s") is not True:
            errors.append({"branch": branch.get("name"), "j_ranges_not_affine": True})
        for atom in branch.get("atoms", []):
            if atom.get("count_formula") is None:
                errors.append({"branch": branch.get("name"), "atom": atom.get("atom"), "missing_count_formula": True})
            if atom.get("min_j_formula") is None or atom.get("max_j_formula") is None:
                errors.append({"branch": branch.get("name"), "atom": atom.get("atom"), "missing_j_formula": True})
    ok = (
        data.get("schema") == "routeE_r42_carry_support_atoms_v1"
        and data.get("q_values") == [6, 7, 8, 9]
        and data.get("summary", {}).get("all_samples_ok") is True
        and data.get("summary", {}).get("nonaffine_edge_counts") == expected_nonaffine
        and data.get("summary", {}).get("all_branch_atom_counts_affine") is True
        and data.get("summary", {}).get("all_branch_j_ranges_affine") is True
        and data.get("summary", {}).get("missing_atom_sample_counts")
        == {"R42-even-q": 0, "R42-odd-q": 0}
        and data.get("promotion_impact", {}).get("closes_residue") is False
        and data.get("promotion_impact", {}).get("pointwise_equations_closed") is False
        and data.get("promotion_impact", {}).get("no_early_closed") is False
        and not errors
    )
    return {
        "schema": "routeE_r42_carry_support_atoms_verification_v1",
        "atoms": str(atoms_path),
        "ok": ok,
        "q_values": data.get("q_values"),
        "branch_atom_key_counts": {
            branch.get("name"): branch.get("atom_key_count")
            for branch in data.get("generic_subbranches", [])
        },
        "error_count": len(errors),
        "errors": errors[:20],
        "promotion_impact": data.get("promotion_impact"),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--atoms", type=Path, default=DEFAULT_ATOMS)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    payload = build_verification(args.atoms)
    print("schema", payload["schema"])
    print("ok", payload["ok"])
    print("q_values", payload["q_values"])
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
