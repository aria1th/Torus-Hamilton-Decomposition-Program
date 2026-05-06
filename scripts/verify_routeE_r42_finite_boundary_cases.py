#!/usr/bin/env python3
"""Verify the R42 finite boundary case summary."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SUMMARY = ROOT / "certs" / "routeE_r42_finite_boundary_cases.json"


def build_verification(summary_path: Path) -> dict:
    data = json.loads(summary_path.read_text())
    cases = data.get("finite_cases", [])
    ok = (
        data.get("schema") == "routeE_r42_finite_boundary_cases_v1"
        and [case.get("m") for case in cases] == [42, 90]
        and data.get("summary", {}).get("all_cases_pass_allpair_checker") is True
        and data.get("summary", {}).get("all_cases_single_cycle") is True
        and data.get("summary", {}).get("all_cases_time_sum_m4") is True
        and data.get("summary", {}).get("all_cases_color_sign_vector_ok") is True
        and data.get("promotion_impact", {}).get("finite_cases_recorded") is True
    )
    return {
        "schema": "routeE_r42_finite_boundary_cases_verification_v1",
        "summary": str(summary_path),
        "ok": ok,
        "case_moduli": [case.get("m") for case in cases],
        "promotion_impact": data.get("promotion_impact"),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--summary", type=Path, default=DEFAULT_SUMMARY)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    payload = build_verification(args.summary)
    print("schema", payload["schema"])
    print("ok", payload["ok"])
    print("case_moduli", payload["case_moduli"])
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")
    if not payload["ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
