#!/usr/bin/env python3
"""Summarize the finite R42 boundary cases created by the mod-96 split."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SAMPLES = ROOT / "certs" / "routeE_r42_affine_samples_verification.json"
DEFAULT_SIGN = ROOT / "certs" / "routeE_color_sign_screen_audit.json"
DEFAULT_SPLIT = ROOT / "certs" / "routeE_r42_mod96_branch_split.json"


def build_summary(samples_path: Path, sign_path: Path, split_path: Path) -> dict[str, Any]:
    samples = json.loads(samples_path.read_text())
    signs = json.loads(sign_path.read_text())
    split = json.loads(split_path.read_text())
    finite_ms = {case["m"] for case in split.get("finite_boundary_cases", [])}
    sign_by_m = {
        record["m"]: record
        for record in signs.get("one_lambda_E_branch_records", [])
        if record.get("name") == "R42"
    }
    cases = []
    for sample in samples.get("samples", []):
        if sample.get("m") not in finite_ms:
            continue
        checker = sample.get("checker", {})
        sign_record = sign_by_m.get(sample["m"], {})
        cases.append(
            {
                "q": sample.get("q"),
                "m": sample.get("m"),
                "x": sample.get("x"),
                "z": sample.get("z"),
                "allpair_passed": sample.get("passed"),
                "single_cycle": checker.get("single_cycle"),
                "sum_ok": checker.get("sum_ok"),
                "ok_returns": checker.get("ok_returns"),
                "count_admissible": checker.get("count_admissible"),
                "unit_pair": checker.get("unit_pair"),
                "time_sum": checker.get("time_sum"),
                "m4": checker.get("m4"),
                "color_sign_vector": sign_record.get("color_sign_vector_symbols"),
                "color_sign_vector_ok": sign_record.get("color_sign_vector_ok"),
            }
        )
    return {
        "schema": "routeE_r42_finite_boundary_cases_v1",
        "branch": "R42",
        "source_samples": str(samples_path),
        "source_sign_screen": str(sign_path),
        "source_split": str(split_path),
        "finite_cases": sorted(cases, key=lambda row: row["m"]),
        "summary": {
            "case_moduli": sorted(row["m"] for row in cases),
            "all_cases_pass_allpair_checker": all(row["allpair_passed"] for row in cases),
            "all_cases_single_cycle": all(row["single_cycle"] for row in cases),
            "all_cases_time_sum_m4": all(row["time_sum"] == row["m4"] for row in cases),
            "all_cases_color_sign_vector_ok": all(
                row["color_sign_vector_ok"] for row in cases
            ),
        },
        "promotion_impact": {
            "finite_cases_recorded": True,
            "closes_generic_subbranches": False,
            "pointwise_equations_closed": False,
            "no_early_closed": False,
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=Path, default=DEFAULT_SAMPLES)
    parser.add_argument("--sign", type=Path, default=DEFAULT_SIGN)
    parser.add_argument("--split", type=Path, default=DEFAULT_SPLIT)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    payload = build_summary(args.samples, args.sign, args.split)
    print("schema", payload["schema"])
    print("case_moduli", payload["summary"]["case_moduli"])
    print("all_cases_single_cycle", payload["summary"]["all_cases_single_cycle"])
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
