#!/usr/bin/env python3
"""Verify the R42 qtime interval-profile diagnostic."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PROFILES = ROOT / "certs" / "routeE_r42_qtime_interval_profiles.json"


def build_verification(profiles_path: Path) -> dict[str, Any]:
    data = json.loads(profiles_path.read_text())
    errors = []
    expected_counts = {"6": 22, "7": 22, "8": 22, "9": 22}
    for sample in data.get("samples", []):
        q = str(sample.get("q"))
        if sample.get("nonaffine_edge_count") != expected_counts.get(q):
            errors.append(
                {
                    "q": sample.get("q"),
                    "expected_nonaffine_edge_count": expected_counts.get(q),
                    "actual": sample.get("nonaffine_edge_count"),
                }
            )
        if sample.get("bad_interval_count") != 0:
            errors.append(
                {
                    "q": sample.get("q"),
                    "bad_interval_count": sample.get("bad_interval_count"),
                }
            )
    ok = (
        data.get("schema") == "routeE_r42_qtime_interval_profiles_v1"
        and data.get("q_values") == [6, 7, 8, 9]
        and data.get("summary", {}).get("all_samples_ok") is True
        and data.get("summary", {}).get("all_nonaffine_edges_interval_affine") is True
        and data.get("summary", {}).get("nonaffine_edge_counts") == expected_counts
        and data.get("summary", {}).get("bad_interval_counts")
        == {"6": 0, "7": 0, "8": 0, "9": 0}
        and data.get("promotion_impact", {}).get("closes_residue") is False
        and data.get("promotion_impact", {}).get("pointwise_equations_closed") is False
        and data.get("promotion_impact", {}).get("no_early_closed") is False
        and not errors
    )
    return {
        "schema": "routeE_r42_qtime_interval_profiles_verification_v1",
        "profiles": str(profiles_path),
        "ok": ok,
        "q_values": data.get("q_values"),
        "error_count": len(errors),
        "errors": errors[:20],
        "promotion_impact": data.get("promotion_impact"),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--profiles", type=Path, default=DEFAULT_PROFILES)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    payload = build_verification(args.profiles)
    print("schema", payload["schema"])
    print("ok", payload["ok"])
    print("q_values", payload["q_values"])
    print("error_count", payload["error_count"])
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")
    if not payload["ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
