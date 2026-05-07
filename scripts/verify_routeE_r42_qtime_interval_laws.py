#!/usr/bin/env python3
"""Verify the R42 qtime start/end interval-law diagnostic."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_LAWS = ROOT / "certs" / "routeE_r42_qtime_interval_laws.json"


def build_verification(laws_path: Path) -> dict:
    data = json.loads(laws_path.read_text())
    ok = (
        data.get("schema") == "routeE_r42_qtime_interval_laws_v1"
        and data.get("q_values") == [6, 7, 8, 9, 10, 11]
        and data.get("occurrence_count") == 5022
        and data.get("group_count") == 4068
        and data.get("repeated_group_count") == 3348
        and data.get("singleton_group_count") == 720
        and data.get("repeated_bad_group_count") == 2266
        and data.get("uncovered_occurrence_count") == 2758
        and data.get("summary", {}).get("all_repeated_groups_affine") is False
        and data.get("summary", {}).get(
            "all_occurrences_covered_by_start_or_end_affine_group"
        )
        is False
        and data.get("summary", {}).get("branch_occurrence_counts")
        == {"R42-even-q": 2376, "R42-odd-q": 2646}
        and data.get("promotion_impact", {}).get("closes_residue") is False
        and data.get("promotion_impact", {}).get("pointwise_equations_closed") is False
        and data.get("promotion_impact", {}).get("no_early_closed") is False
    )
    return {
        "schema": "routeE_r42_qtime_interval_laws_verification_v1",
        "laws": str(laws_path),
        "ok": ok,
        "q_values": data.get("q_values"),
        "occurrence_count": data.get("occurrence_count"),
        "repeated_bad_group_count": data.get("repeated_bad_group_count"),
        "uncovered_occurrence_count": data.get("uncovered_occurrence_count"),
        "promotion_impact": data.get("promotion_impact"),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--laws", type=Path, default=DEFAULT_LAWS)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    payload = build_verification(args.laws)
    print("schema", payload["schema"])
    print("ok", payload["ok"])
    print("occurrence_count", payload["occurrence_count"])
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")
    if not payload["ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
