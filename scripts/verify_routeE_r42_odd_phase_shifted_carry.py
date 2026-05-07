#!/usr/bin/env python3
"""Verify the R42-odd phase-shifted carry screen artifact."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_INPUT = ROOT / "certs" / "routeE_r42_odd_phase_shifted_carry.json"


def build_verification(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text())
    search = data.get("search_space", {})
    checks = [
        data.get("schema") == "routeE_r42_odd_phase_shifted_carry_v1",
        data.get("atom") == "20->26|L1|B7:7|R0:0",
        data.get("sample_count") == 30,
        data.get("q_values") == [7, 9, 11],
        search.get("threshold_feature_count") == 84,
        search.get("mod5_feature_count") == 50,
        search.get("mod6_feature_count") == 72,
        search.get("depth_three_candidate_count") == 302400,
        search.get("checked_candidate_count") == 302400,
        search.get("modular_survivor_count") == 0,
        data.get("hit_count") == 0,
    ]
    return {
        "schema": "routeE_r42_odd_phase_shifted_carry_verification_v1",
        "source_artifact": str(path),
        "ok": all(checks),
        "checks": {
            "schema": checks[0],
            "atom": checks[1],
            "sample_count": checks[2],
            "q_values": checks[3],
            "feature_counts": all(checks[4:7]),
            "candidate_count": checks[7],
            "checked_candidate_count": checks[8],
            "no_modular_survivors": checks[9],
            "no_exact_hits_after_screen": checks[10],
        },
        "interpretation": (
            "The natural R42-odd phase-shifted depth-three screen has no "
            "two-prime modular survivors on the unresolved atom.  This is a "
            "screened failure of that grammar, not a theorem excluding every "
            "possible R42-odd carry state."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    payload = build_verification(args.input)
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
