#!/usr/bin/env python3
"""Verify the extended R42 bad-intercept carry-split stress artifacts.

The first bad-intercept split diagnostic used two samples in each q-parity
branch and found an apparently small refinement: eight one-feature atoms and
one two-feature atom.  This verifier records the next stress test with three
samples per parity.  The result is intentionally negative: the simple
one/two-feature refinement does not remain stable once q=10 and q=11 are
included.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_EVEN = (
    ROOT / "certs" / "routeE_r42_bad_intercept_carry_split_even_q6_8_10.json"
)
DEFAULT_ODD = (
    ROOT / "certs" / "routeE_r42_bad_intercept_carry_split_odd_q7_9_11.json"
)
UNRESOLVED_ATOM = "20->26|L1|B7:7|R0:0"
NEW_TWO_FEATURE_ATOM = "13->4|L1|B6:6|R0:0"


def load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text())


def branch(payload: dict[str, Any], name: str) -> dict[str, Any]:
    for entry in payload.get("generic_subbranches", []):
        if entry.get("name") == name:
            return entry
    return {}


def atom_summary(branch_payload: dict[str, Any], atom: str) -> dict[str, Any]:
    for entry in branch_payload.get("atom_summaries", []):
        if entry.get("atom") == atom:
            return entry
    return {}


def verify_branch(
    payload: dict[str, Any],
    name: str,
    q_values: list[int],
    expected_rows: int,
    errors: list[dict[str, Any]],
) -> dict[str, Any]:
    br = branch(payload, name)
    if payload.get("schema") != "routeE_r42_bad_intercept_carry_split_v1":
        errors.append({"branch": name, "bad_schema": payload.get("schema")})
    if payload.get("q_values") != q_values:
        errors.append({"branch": name, "bad_q_values": payload.get("q_values")})
    if payload.get("bad_atom_count") != 9:
        errors.append({"branch": name, "bad_atom_count": payload.get("bad_atom_count")})
    if br.get("rows") != expected_rows:
        errors.append({"branch": name, "bad_row_count": br.get("rows")})
    if br.get("bad_atom_count") != 9:
        errors.append({"branch": name, "bad_branch_atom_count": br.get("bad_atom_count")})
    if br.get("atoms_with_one_feature_hit") != 7:
        errors.append({"branch": name, "bad_one_feature_count": br.get("atoms_with_one_feature_hit")})
    if br.get("atoms_with_two_feature_hit") != 1:
        errors.append({"branch": name, "bad_two_feature_count": br.get("atoms_with_two_feature_hit")})

    unresolved = atom_summary(br, UNRESOLVED_ATOM)
    if unresolved.get("one_feature_hit_count") != 0 or unresolved.get("two_feature_hit_count") != 0:
        errors.append(
            {
                "branch": name,
                "atom": UNRESOLVED_ATOM,
                "expected_unresolved": True,
                "one": unresolved.get("one_feature_hit_count"),
                "two": unresolved.get("two_feature_hit_count"),
            }
        )
    two_feature = atom_summary(br, NEW_TWO_FEATURE_ATOM)
    if two_feature.get("one_feature_hit_count") != 0 or two_feature.get("two_feature_hit_count", 0) < 1:
        errors.append(
            {
                "branch": name,
                "atom": NEW_TWO_FEATURE_ATOM,
                "expected_two_feature": True,
                "one": two_feature.get("one_feature_hit_count"),
                "two": two_feature.get("two_feature_hit_count"),
            }
        )
    return {
        "branch": name,
        "q_values": payload.get("q_values"),
        "rows": br.get("rows"),
        "atoms_with_one_feature_hit": br.get("atoms_with_one_feature_hit"),
        "atoms_with_two_feature_hit": br.get("atoms_with_two_feature_hit"),
        "unresolved_atom": UNRESOLVED_ATOM,
        "unresolved_j_values": unresolved.get("j_values"),
        "new_two_feature_atom": NEW_TWO_FEATURE_ATOM,
        "new_two_feature_j_values": two_feature.get("j_values"),
    }


def build_verification(even_path: Path, odd_path: Path) -> dict[str, Any]:
    errors: list[dict[str, Any]] = []
    even = load(even_path)
    odd = load(odd_path)
    even_summary = verify_branch(even, "R42-even-q", [6, 8, 10], 222, errors)
    odd_summary = verify_branch(odd, "R42-odd-q", [7, 9, 11], 246, errors)
    return {
        "schema": "routeE_r42_bad_intercept_carry_split_stress_verification_v1",
        "even_artifact": str(even_path),
        "odd_artifact": str(odd_path),
        "ok": not errors,
        "branch_summaries": [even_summary, odd_summary],
        "diagnostic_result": {
            "simple_one_or_two_feature_schema_stable": False,
            "bad_atom_count_per_branch": 9,
            "one_feature_hits_per_branch": {"R42-even-q": 7, "R42-odd-q": 7},
            "two_feature_hits_per_branch": {"R42-even-q": 1, "R42-odd-q": 1},
            "unresolved_atom": UNRESOLVED_ATOM,
            "new_two_feature_atom": NEW_TWO_FEATURE_ATOM,
        },
        "error_count": len(errors),
        "errors": errors[:20],
        "promotion_impact": {
            "closes_residue": False,
            "pointwise_equations_closed": False,
            "no_early_closed": False,
            "refutes_simple_one_step_carry_split": True,
            "diagnosis": (
                "Adding q=10 and q=11 breaks the apparent two-sample split: "
                "one atom remains unresolved even with all tested one/two "
                "features.  R42 may still have a deeper clock-carry structure, "
                "but the one-step carry split is not a branch theorem."
            ),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--even", type=Path, default=DEFAULT_EVEN)
    parser.add_argument("--odd", type=Path, default=DEFAULT_ODD)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    payload = build_verification(args.even, args.odd)
    print("schema", payload["schema"])
    print("ok", payload["ok"])
    print("diagnostic_result", payload["diagnostic_result"])
    print("error_count", payload["error_count"])
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")
    if not payload["ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
