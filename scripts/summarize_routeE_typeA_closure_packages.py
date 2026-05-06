#!/usr/bin/env python3
"""Summarize Route-E Type-A branch closure package outputs.

This script reads the B16/R14e closure zip packages and extracts a compact,
machine-readable summary of the proof-facing evidence.  It deliberately avoids
committing raw all-pair CSV tables.

The resulting summary is evidence, not a theorem: it records finite complete
case checks, symbolic polynomial totals, macro/boundary one-cycle checks, and
the remaining Lean-facing open status.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import zipfile
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_B16 = ROOT.parent / "RouteE" / "B16_closure_package_20260506.zip"
DEFAULT_R14E = ROOT.parent / "RouteE" / "R14e_closure_package_20260506.zip"


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def read_zip_json(path: Path, suffix: str) -> dict[str, Any]:
    with zipfile.ZipFile(path) as zf:
        matches = [name for name in zf.namelist() if name.endswith(suffix)]
        if len(matches) != 1:
            raise ValueError(f"expected one {suffix} in {path}, found {matches}")
        return json.loads(zf.read(matches[0]).decode())


def summarize_b16(path: Path) -> dict[str, Any]:
    data = read_zip_json(path, "b16_complete_verifier_output.json")
    macro_checks = data.get("macro_R_checks", [])
    applicable = [x for x in macro_checks if x.get("applicable")]
    macro_bad = [
        x
        for x in applicable
        if x.get("bad_count")
        or not x.get("pred_R_one_cycle")
        or not x.get("length_sum_equals_boundary_size")
    ]
    case_summary = data.get("complete_case_summary", [])
    return {
        "source": str(path),
        "sha256": sha256_file(path),
        "schema": data.get("schema"),
        "family": data.get("family"),
        "case_count": len(case_summary),
        "moduli": [case["m"] for case in case_summary],
        "all_complete": all(case.get("complete") for case in case_summary),
        "all_section_single_cycle": all(case.get("section_single_cycle") for case in case_summary),
        "all_total_equals_m4": all(case.get("total_equals_m4") for case in case_summary),
        "all_boundary_formula_ok": all(case.get("boundary_bad_count") == 0 for case in case_summary),
        "macro_applicable_count": len(applicable),
        "macro_all_ok": not macro_bad,
        "macro_bad_examples": macro_bad[:5],
        "poly_bad_count": data.get("poly_bad_count"),
        "label_total_equals_m4": data.get("label_total_equals_m4"),
        "label_dst_total_equals_m4": data.get("label_dst_total_equals_m4"),
        "open_status": (
            "proof-facing branch; still needs concrete Lean first-return/"
            "minimality instance, not closed as a theorem"
        ),
    }


def b16_symbolic_skeleton(path: Path) -> dict[str, Any]:
    data = read_zip_json(path, "b16_complete_verifier_output.json")
    return {
        "source": str(path),
        "sha256": sha256_file(path),
        "schema": data.get("schema"),
        "family": data.get("family"),
        "parameter": "m = 24*q + 16",
        "sample_moduli": [case["m"] for case in data.get("complete_case_summary", [])],
        "label_sum_polynomials": data.get("label_sum_polynomials"),
        "label_dst_sum_polynomials": data.get("label_dst_sum_polynomials"),
        "total_poly_from_labels": data.get("total_poly_from_labels"),
        "total_poly_from_label_dst": data.get("total_poly_from_label_dst"),
        "m4_poly": data.get("m4_poly"),
        "label_total_equals_m4": data.get("label_total_equals_m4"),
        "label_dst_total_equals_m4": data.get("label_dst_total_equals_m4"),
        "macro_checked_q_range": "0..200",
        "macro_formula_status": (
            "The package verifier records Q_formula/pred_R/pred_len in "
            "b16_complete_verifier.py and checks them on q=0..200; this "
            "skeleton preserves the polynomial mass identities."
        ),
    }


def summarize_r14e(path: Path) -> dict[str, Any]:
    data = read_zip_json(path, "r14e_complete_verifier_output.json")
    insertion = read_zip_json(path, "r14e_insertion_macro_verifier_output.json")
    case_summary = data.get("complete_case_summary", [])
    comparisons = insertion.get("bylabel_expected_comparisons", [])
    return {
        "source": str(path),
        "sha256": sha256_file(path),
        "schema": data.get("schema"),
        "family": data.get("family"),
        "case_count": len(case_summary),
        "moduli": [case["m"] for case in case_summary],
        "used_k_values": data.get("used_k_values"),
        "all_complete": all(case.get("complete") for case in case_summary),
        "all_section_single_cycle": all(case.get("single_cycle") for case in case_summary),
        "all_total_equals_m4": all(case.get("total_equals_m4") for case in case_summary),
        "all_boundary_step_sum_ok": all(case.get("boundary_step_sum_ok") for case in case_summary),
        "expected_insertion_weighted_equals_allpair_size": data.get(
            "expected_insertion_weighted_equals_allpair_size"
        ),
        "label_total_equals_m4": data.get("label_total_equals_m4"),
        "label_dst_total_equals_m4": data.get("label_dst_total_equals_m4"),
        "label_dst_count_equals_allpair_size": data.get(
            "label_dst_count_equals_allpair_size"
        ),
        "insertion_macro_schema": insertion.get("schema"),
        "insertion_comparison_count": len(comparisons),
        "insertion_comparisons_all_ok": all(
            item.get("matches_expected") is not False for item in comparisons
        ),
        "symbolic_boundary_count": insertion.get("symbolic_boundary_count"),
        "symbolic_boundary_size": insertion.get("symbolic_boundary_size"),
        "symbolic_weighted_steps": insertion.get("symbolic_weighted_steps"),
        "symbolic_allpair_size": insertion.get("symbolic_allpair_size"),
        "open_status": (
            "proof-facing branch; still needs concrete Lean first-return/"
            "minimality instance, not closed as a theorem"
        ),
    }


def r14e_symbolic_skeleton(path: Path) -> dict[str, Any]:
    data = read_zip_json(path, "r14e_complete_verifier_output.json")
    insertion = read_zip_json(path, "r14e_insertion_macro_verifier_output.json")
    return {
        "source": str(path),
        "sha256": sha256_file(path),
        "schema": data.get("schema"),
        "family": data.get("family"),
        "parameter": "m = 48*k + 14",
        "sample_moduli": [case["m"] for case in data.get("complete_case_summary", [])],
        "used_k_values": data.get("used_k_values"),
        "label_sum_polynomials": data.get("label_sum_polynomials"),
        "label_dst_sum_polynomials": data.get("label_dst_sum_polynomials"),
        "expected_insertion_bylabel": data.get("expected_insertion_bylabel"),
        "expected_insertion_boundary_count": data.get("expected_insertion_boundary_count"),
        "expected_boundary_size": data.get("expected_boundary_size"),
        "expected_insertion_weighted_sum": data.get("expected_insertion_weighted_sum"),
        "expected_allpair_size": data.get("expected_allpair_size"),
        "expected_insertion_weighted_equals_allpair_size": data.get(
            "expected_insertion_weighted_equals_allpair_size"
        ),
        "total_poly_from_labels": data.get("total_poly_from_labels"),
        "total_poly_from_label_dst": data.get("total_poly_from_label_dst"),
        "m4_poly": data.get("m4_poly"),
        "label_total_equals_m4": data.get("label_total_equals_m4"),
        "label_dst_total_equals_m4": data.get("label_dst_total_equals_m4"),
        "label_dst_count_total": data.get("label_dst_count_total"),
        "label_dst_count_equals_allpair_size": data.get(
            "label_dst_count_equals_allpair_size"
        ),
        "insertion_macro_schema": insertion.get("schema"),
        "insertion_macro_symbolic": {
            "boundary_count": insertion.get("symbolic_boundary_count"),
            "boundary_size": insertion.get("symbolic_boundary_size"),
            "weighted_steps": insertion.get("symbolic_weighted_steps"),
            "allpair_size": insertion.get("symbolic_allpair_size"),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--b16-package", type=Path, default=DEFAULT_B16)
    parser.add_argument("--r14e-package", type=Path, default=DEFAULT_R14E)
    parser.add_argument("--json-out", type=Path)
    parser.add_argument("--symbolic-out", type=Path)
    args = parser.parse_args()

    payload = {
        "schema": "routeE_typeA_closure_package_summary_v1",
        "b16": summarize_b16(args.b16_package),
        "r14e": summarize_r14e(args.r14e_package),
    }
    payload["all_recorded_flags_ok"] = (
        payload["b16"]["all_complete"]
        and payload["b16"]["all_section_single_cycle"]
        and payload["b16"]["all_total_equals_m4"]
        and payload["b16"]["all_boundary_formula_ok"]
        and payload["b16"]["macro_all_ok"]
        and payload["b16"]["poly_bad_count"] == 0
        and payload["b16"]["label_total_equals_m4"]
        and payload["b16"]["label_dst_total_equals_m4"]
        and payload["r14e"]["all_complete"]
        and payload["r14e"]["all_section_single_cycle"]
        and payload["r14e"]["all_total_equals_m4"]
        and payload["r14e"]["all_boundary_step_sum_ok"]
        and payload["r14e"]["expected_insertion_weighted_equals_allpair_size"]
        and payload["r14e"]["label_total_equals_m4"]
        and payload["r14e"]["label_dst_total_equals_m4"]
        and payload["r14e"]["label_dst_count_equals_allpair_size"]
        and payload["r14e"]["insertion_comparisons_all_ok"]
    )

    print(
        "b16",
        payload["b16"]["moduli"],
        "macro_all_ok",
        payload["b16"]["macro_all_ok"],
        "r14e",
        payload["r14e"]["moduli"],
        "all_recorded_flags_ok",
        payload["all_recorded_flags_ok"],
    )
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")
    if args.symbolic_out is not None:
        symbolic = {
            "schema": "routeE_typeA_symbolic_skeleton_v1",
            "b16": b16_symbolic_skeleton(args.b16_package),
            "r14e": r14e_symbolic_skeleton(args.r14e_package),
            "status": (
                "Symbolic mass/insertion skeleton extracted from package "
                "verifier outputs.  This is still not a Lean theorem."
            ),
        }
        args.symbolic_out.parent.mkdir(parents=True, exist_ok=True)
        args.symbolic_out.write_text(
            json.dumps(symbolic, indent=2, sort_keys=True) + "\n"
        )
        print(f"wrote {args.symbolic_out}")
    if not payload["all_recorded_flags_ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
