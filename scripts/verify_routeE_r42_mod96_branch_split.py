#!/usr/bin/env python3
"""Verify the R42 mod-96 branch split record."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SPLIT = ROOT / "certs" / "routeE_r42_mod96_branch_split.json"


def build_verification(split_path: Path) -> dict[str, Any]:
    data = json.loads(split_path.read_text())
    branches = {branch["name"]: branch for branch in data.get("generic_subbranches", [])}
    finite_ms = [case.get("m") for case in data.get("finite_boundary_cases", [])]
    ok = (
        data.get("schema") == "routeE_r42_mod96_branch_split_v1"
        and finite_ms == [42, 90]
        and set(branches) == {"R42-even-q", "R42-odd-q"}
        and branches["R42-even-q"].get("modulus_family") == "m = 96*s + 42"
        and branches["R42-even-q"].get("sample_q_values") == [2, 4, 6]
        and branches["R42-even-q"].get("sample_m_values") == [138, 234, 330]
        and branches["R42-odd-q"].get("modulus_family") == "m = 96*s + 90"
        and branches["R42-odd-q"].get("sample_q_values") == [3, 5]
        and branches["R42-odd-q"].get("sample_m_values") == [186, 282]
        and data.get("checks", {}).get("q_ge_2_support_stable") is True
        and data.get("checks", {}).get("q_ge_2_edge_count") == 69
        and data.get("checks", {}).get("edge_count_piecewise_moduli") == [2]
        and data.get("promotion_impact", {}).get("closes_residue") is False
    )
    return {
        "schema": "routeE_r42_mod96_branch_split_verification_v1",
        "split": str(split_path),
        "ok": ok,
        "finite_boundary_cases": finite_ms,
        "generic_subbranches": {
            name: {
                "modulus_family": branch.get("modulus_family"),
                "sample_q_values": branch.get("sample_q_values"),
                "sample_m_values": branch.get("sample_m_values"),
            }
            for name, branch in sorted(branches.items())
        },
        "promotion_impact": data.get("promotion_impact"),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--split", type=Path, default=DEFAULT_SPLIT)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    payload = build_verification(args.split)
    print("schema", payload["schema"])
    print("ok", payload["ok"])
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")
    if not payload["ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
