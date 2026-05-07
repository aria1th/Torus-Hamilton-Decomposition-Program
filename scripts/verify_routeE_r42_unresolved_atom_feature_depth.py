#!/usr/bin/env python3
"""Verify the R42 unresolved-atom feature-depth probe artifacts."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_EVEN = (
    ROOT / "certs" / "routeE_r42_unresolved_atom_20_feature_depth_even_q6_8_10.json"
)
DEFAULT_ODD = (
    ROOT / "certs" / "routeE_r42_unresolved_atom_20_feature_depth_odd_q7_9_11.json"
)
ATOM = "20->26|L1|B7:7|R0:0"


def load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text())


def branch(payload: dict[str, Any], name: str) -> dict[str, Any]:
    for entry in payload.get("generic_subbranches", []):
        if entry.get("name") == name:
            return entry
    return {}


def build_verification(even_path: Path, odd_path: Path) -> dict[str, Any]:
    errors: list[dict[str, Any]] = []
    even = load(even_path)
    odd = load(odd_path)
    even_branch = branch(even, "R42-even-q")
    odd_branch = branch(odd, "R42-odd-q")
    if even.get("schema") != "routeE_r42_unresolved_atom_feature_depth_v1":
        errors.append({"artifact": "even", "bad_schema": even.get("schema")})
    if odd.get("schema") != "routeE_r42_unresolved_atom_feature_depth_v1":
        errors.append({"artifact": "odd", "bad_schema": odd.get("schema")})
    if even.get("atom") != ATOM or odd.get("atom") != ATOM:
        errors.append({"bad_atom": [even.get("atom"), odd.get("atom")]})
    if even.get("q_values") != [6, 8, 10]:
        errors.append({"artifact": "even", "bad_q_values": even.get("q_values")})
    if odd.get("q_values") != [7, 9, 11]:
        errors.append({"artifact": "odd", "bad_q_values": odd.get("q_values")})
    if even_branch.get("rows") != 27 or even_branch.get("minimal_depth") != 3:
        errors.append(
            {
                "artifact": "even",
                "rows": even_branch.get("rows"),
                "minimal_depth": even_branch.get("minimal_depth"),
            }
        )
    if odd_branch.get("rows") != 30 or odd_branch.get("minimal_depth") is not None:
        errors.append(
            {
                "artifact": "odd",
                "rows": odd_branch.get("rows"),
                "minimal_depth": odd_branch.get("minimal_depth"),
            }
        )
    even_hits = even_branch.get("hits", [])
    if not even_hits or even_hits[0].get("features") != [
        "m*1[j>s+4]",
        "m*1[j%5=0]",
        "m*1[j%6=5]",
    ]:
        errors.append({"artifact": "even", "bad_first_hit": even_hits[:1]})
    if odd_branch.get("hits") != []:
        errors.append({"artifact": "odd", "unexpected_hits": odd_branch.get("hits")})
    return {
        "schema": "routeE_r42_unresolved_atom_feature_depth_verification_v1",
        "even_artifact": str(even_path),
        "odd_artifact": str(odd_path),
        "ok": not errors,
        "diagnostic_result": {
            "atom": ATOM,
            "even_minimal_depth": even_branch.get("minimal_depth"),
            "odd_minimal_depth": odd_branch.get("minimal_depth"),
            "even_rows": even_branch.get("rows"),
            "odd_rows": odd_branch.get("rows"),
            "interpretation": (
                "The even parity sample is rescued by three tested carry "
                "features, but the odd parity sample is not rescued up to "
                "depth three.  This weakens the simple finite-depth carry "
                "ansatz and points to a deeper or different state variable."
            ),
        },
        "error_count": len(errors),
        "errors": errors[:20],
        "promotion_impact": {
            "closes_residue": False,
            "pointwise_equations_closed": False,
            "no_early_closed": False,
            "refutes_depth_three_uniformity": True,
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
