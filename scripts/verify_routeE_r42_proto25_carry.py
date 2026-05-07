#!/usr/bin/env python3
"""Verify the R42 25->3 c-band carry diagnostic."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PROTO = ROOT / "certs" / "routeE_r42_proto25_carry.json"


def build_verification(proto_path: Path) -> dict[str, Any]:
    data = json.loads(proto_path.read_text())
    errors: list[dict[str, Any]] = []
    for sample in data.get("samples", []):
        q = sample.get("q")
        c = sample.get("c")
        if c != 6 * q + 5:
            errors.append({"q": q, "bad_c": c})
            continue
        if sample.get("m") != 8 * c + 2:
            errors.append({"q": q, "bad_m": sample.get("m")})
        if sample.get("member_count") != 2 * c:
            errors.append({"q": q, "bad_member_count": sample.get("member_count")})
        if sample.get("interval_count") != (4 * c + 1) // 3:
            errors.append({"q": q, "bad_interval_count": sample.get("interval_count")})
        if sample.get("length_counts") != {
            "1": (2 * c + 2) // 3,
            "2": (2 * c - 1) // 3,
        }:
            errors.append({"q": q, "bad_length_counts": sample.get("length_counts")})
        if sample.get("type_counts") != {
            "double_1mod3": (2 * c - 1) // 3,
            "single_2c1_6j": (c + 1) // 3,
            "single_2c3_6j": (c - 2) // 3,
            "single_endpoint_4c": 1,
        }:
            errors.append({"q": q, "bad_type_counts": sample.get("type_counts")})
        if sample.get("qtime_slope_values") != [0, 4 * c + 3, 12 * c + 5]:
            errors.append(
                {
                    "q": q,
                    "bad_qtime_slope_values": sample.get("qtime_slope_values"),
                }
            )
        if sample.get("qtime_coeffs_match_carry_formula") is not True:
            errors.append(
                {
                    "q": q,
                    "bad_qtime_coeffs": sample.get("qtime_coeff_mismatches"),
                }
            )
        for flag in [
            "support_matches_carry_grammar",
            "all_intervals_qtime_affine",
            "qtime_slopes_within_expected_alphabet",
            "qtime_coeffs_match_carry_formula",
        ]:
            if sample.get(flag) is not True:
                errors.append({"q": q, "flag": flag, "actual": sample.get(flag)})

    ok = (
        data.get("schema") == "routeE_r42_proto25_carry_v1"
        and data.get("q_values") == [6, 7, 8, 9]
        and data.get("summary", {}).get("all_samples_ok") is True
        and data.get("summary", {}).get("all_support_matches_carry_grammar")
        is True
        and data.get("summary", {}).get("all_intervals_qtime_affine") is True
        and data.get("summary", {}).get("all_qtime_slopes_within_expected_alphabet")
        is True
        and data.get("summary", {}).get("all_qtime_coeffs_match_carry_formula")
        is True
        and data.get("promotion_impact", {}).get("closes_residue") is False
        and data.get("promotion_impact", {}).get("pointwise_equations_closed")
        is False
        and data.get("promotion_impact", {}).get("no_early_closed") is False
        and not errors
    )
    return {
        "schema": "routeE_r42_proto25_carry_verification_v1",
        "proto": str(proto_path),
        "ok": ok,
        "q_values": data.get("q_values"),
        "sample_count": len(data.get("samples", [])),
        "error_count": len(errors),
        "errors": errors[:20],
        "promotion_impact": data.get("promotion_impact"),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--proto", type=Path, default=DEFAULT_PROTO)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    payload = build_verification(args.proto)
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
