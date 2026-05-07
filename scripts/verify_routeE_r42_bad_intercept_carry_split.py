#!/usr/bin/env python3
"""Verify the R42 bad-intercept carry-split diagnostic artifacts."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_EVEN = ROOT / "certs" / "routeE_r42_bad_intercept_carry_split_even_q6_8.json"
DEFAULT_ODD = ROOT / "certs" / "routeE_r42_bad_intercept_carry_split_odd_q7_9.json"
TWO_FEATURE_ATOM = "20->26|L1|B7:7|R0:0"
TWO_FEATURE_SET = ["m*1[j%5=0]", "m*1[j%6=5]"]


def load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text())


def branch(payload: dict[str, Any], name: str) -> dict[str, Any]:
    for entry in payload.get("generic_subbranches", []):
        if entry.get("name") == name:
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
    if br.get("atoms_with_one_feature_hit") != 8:
        errors.append({"branch": name, "bad_one_feature_count": br.get("atoms_with_one_feature_hit")})
    if br.get("atoms_with_two_feature_hit") != 1:
        errors.append({"branch": name, "bad_two_feature_count": br.get("atoms_with_two_feature_hit")})

    atom_summaries = br.get("atom_summaries", [])
    two_feature_atoms = [
        item for item in atom_summaries if item.get("two_feature_hit_count", 0) > 0
    ]
    if [item.get("atom") for item in two_feature_atoms] != [TWO_FEATURE_ATOM]:
        errors.append(
            {
                "branch": name,
                "bad_two_feature_atoms": [item.get("atom") for item in two_feature_atoms],
            }
        )
    elif two_feature_atoms:
        features = two_feature_atoms[0].get("two_feature_hits", [{}])[0].get("features")
        if features != TWO_FEATURE_SET:
            errors.append({"branch": name, "bad_two_feature_set": features})
    for item in atom_summaries:
        if item.get("sample_count", 0) == 0:
            continue
        if item.get("atom") == TWO_FEATURE_ATOM:
            if item.get("one_feature_hit_count") != 0 or item.get("two_feature_hit_count", 0) < 1:
                errors.append({"branch": name, "atom": item.get("atom"), "expected_two_feature_only": True})
        elif item.get("one_feature_hit_count", 0) < 1:
            errors.append({"branch": name, "atom": item.get("atom"), "missing_one_feature_hit": True})
    return {
        "branch": name,
        "q_values": payload.get("q_values"),
        "rows": br.get("rows"),
        "atoms_with_one_feature_hit": br.get("atoms_with_one_feature_hit"),
        "atoms_with_two_feature_hit": br.get("atoms_with_two_feature_hit"),
        "two_feature_atom": TWO_FEATURE_ATOM,
        "two_feature_set": TWO_FEATURE_SET,
    }


def build_verification(even_path: Path, odd_path: Path) -> dict[str, Any]:
    errors: list[dict[str, Any]] = []
    even = load(even_path)
    odd = load(odd_path)
    even_summary = verify_branch(even, "R42-even-q", [6, 8], 131, errors)
    odd_summary = verify_branch(odd, "R42-odd-q", [7, 9], 147, errors)
    return {
        "schema": "routeE_r42_bad_intercept_carry_split_verification_v1",
        "even_artifact": str(even_path),
        "odd_artifact": str(odd_path),
        "ok": not errors,
        "branch_summaries": [even_summary, odd_summary],
        "diagnostic_result": {
            "bad_atom_count_per_branch": 9,
            "one_feature_hits_per_branch": {"R42-even-q": 8, "R42-odd-q": 8},
            "two_feature_hits_per_branch": {"R42-even-q": 1, "R42-odd-q": 1},
            "two_feature_atom": TWO_FEATURE_ATOM,
            "two_feature_set": TWO_FEATURE_SET,
        },
        "error_count": len(errors),
        "errors": errors[:20],
        "promotion_impact": {
            "closes_residue": False,
            "pointwise_equations_closed": False,
            "no_early_closed": False,
            "diagnosis": (
                "On q=6,8 and q=7,9, the nine bad qtime-intercept atoms "
                "split further into eight one-threshold carry atoms and one "
                "two-residue carry atom.  This identifies the next finite "
                "state refinement, but it is still not a no-early proof."
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
