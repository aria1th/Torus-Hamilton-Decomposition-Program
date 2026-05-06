#!/usr/bin/env python3
"""Initialize the Route-E R42 affine branch record.

The all-pair portfolio fit scan identifies residue 42 mod 48 as the only
portfolio-only residue whose samples fit a simple symmetric affine law.  This
record fixes the observed law and the proof obligations required before the
residue can be promoted to Type-A proof-facing coverage.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_FITS = ROOT / "certs" / "routeE_allpair_portfolio_fit_summary.json"
DEFAULT_COVERAGE = ROOT / "certs" / "routeE_typeA_residue_coverage.json"
DEFAULT_SAMPLE_VERIFICATION = (
    ROOT / "certs" / "routeE_r42_affine_samples_verification.json"
)
DEFAULT_BOUNDARY_SUMMARY = ROOT / "certs" / "routeE_r42_boundary_quotient_summary.json"
DEFAULT_BOUNDARY_VERIFICATION = (
    ROOT / "certs" / "routeE_r42_boundary_summary_verification.json"
)
DEFAULT_BLOCK_REGENERATION_VERIFICATION = (
    ROOT / "certs" / "routeE_r42_block_formula_regeneration_verification.json"
)
DEFAULT_COLOR_SIGN_SCREEN = ROOT / "certs" / "routeE_color_sign_screen_audit.json"


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text())


def build_record(
    fits_path: Path,
    coverage_path: Path,
    sample_verification_path: Path,
    boundary_summary_path: Path,
    boundary_verification_path: Path,
    block_regeneration_verification_path: Path,
    color_sign_screen_path: Path,
) -> dict[str, Any]:
    fits = load_json(fits_path)
    coverage = load_json(coverage_path) if coverage_path.exists() else {}
    sample_verification = (
        load_json(sample_verification_path)
        if sample_verification_path.exists()
        else {}
    )
    boundary_summary = (
        load_json(boundary_summary_path) if boundary_summary_path.exists() else {}
    )
    boundary_verification = (
        load_json(boundary_verification_path)
        if boundary_verification_path.exists()
        else {}
    )
    block_regeneration_verification = (
        load_json(block_regeneration_verification_path)
        if block_regeneration_verification_path.exists()
        else {}
    )
    color_sign_screen = (
        load_json(color_sign_screen_path) if color_sign_screen_path.exists() else {}
    )
    rows = {int(row["residue"]): row for row in fits.get("rows", [])}
    row = rows[42]
    verified_samples = [
        sample
        for sample in sample_verification.get("samples", [])
        if sample.get("passed")
    ]
    r42_color_sign_records = [
        record
        for record in color_sign_screen.get("one_lambda_E_branch_records", [])
        if record.get("name") == "R42"
    ]
    return {
        "schema": "routeE_r42_affine_branch_record_v1",
        "branch": "R42",
        "status": "sample_verified_open_symbolic_candidate",
        "modulus_family": "m == 42 mod 48",
        "parameter": "m = 48*q + 42",
        "observed_law": {
            "x": row["fit_x"].get("formula"),
            "z": row["fit_z"].get("formula"),
            "nodes": row["fit_nodes"].get("formula"),
            "symmetric": row["fit_x"].get("formula") == row["fit_z"].get("formula"),
        },
        "sample_moduli": [sample.get("m") for sample in verified_samples]
        or row.get("moduli"),
        "samples": row.get("samples"),
        "source_artifacts": {
            "portfolio_fits": str(fits_path),
            "portfolio_samples": "certs/routeE_allpair_portfolio_samples_v1_1.json",
            "sample_verification": str(sample_verification_path),
            "boundary_summary": str(boundary_summary_path),
            "boundary_verification": str(boundary_verification_path),
            "block_regeneration_verification": str(
                block_regeneration_verification_path
            ),
            "color_sign_screen": str(color_sign_screen_path),
            "typeA_coverage": str(coverage_path),
        },
        "sample_verification_summary": {
            "schema": sample_verification.get("schema"),
            "all_passed": sample_verification.get("all_passed"),
            "source_checker": sample_verification.get("source_checker"),
            "verified_q_values": [
                sample.get("q")
                for sample in sample_verification.get("samples", [])
                if sample.get("passed")
            ],
        },
        "boundary_summary": {
            "schema": boundary_summary.get("schema"),
            "status": boundary_summary.get("status"),
            "raw_csv_preserved": boundary_summary.get("raw_csv_preserved"),
            "q_ge_1_stability": boundary_summary.get("q_ge_1_stability"),
            "q_ge_1_transition_count_fits": boundary_summary.get(
                "q_ge_1_transition_count_fits"
            ),
            "q_ge_1_block_formula_fits_summary": {
                "stable_structural_keys": boundary_summary.get(
                    "q_ge_1_block_formula_fits", {}
                ).get("stable_structural_keys"),
                "block_count": boundary_summary.get(
                    "q_ge_1_block_formula_fits", {}
                ).get("block_count"),
                "fit_block_count": len(
                    boundary_summary.get("q_ge_1_block_formula_fits", {}).get(
                        "blocks", []
                    )
                ),
                "block24_q_ge_2_tail": {
                    "terminal_affine_alpha_q_ge_2": (
                        boundary_summary.get("q_ge_1_block_formula_fits", {})
                        .get("blocks", [{}] * 25)[24]
                        .get("terminal_affine_alpha_q_ge_2")
                        if len(
                            boundary_summary.get(
                                "q_ge_1_block_formula_fits", {}
                            ).get("blocks", [])
                        )
                        > 24
                        else None
                    ),
                    "terminal_affine_beta_q_ge_2": (
                        boundary_summary.get("q_ge_1_block_formula_fits", {})
                        .get("blocks", [{}] * 25)[24]
                        .get("terminal_affine_beta_q_ge_2")
                        if len(
                            boundary_summary.get(
                                "q_ge_1_block_formula_fits", {}
                            ).get("blocks", [])
                        )
                        > 24
                        else None
                    ),
                },
            },
        },
        "boundary_verification_summary": {
            "schema": boundary_verification.get("schema"),
            "ok": boundary_verification.get("ok"),
            "summary": boundary_verification.get("summary"),
        },
        "block_regeneration_verification_summary": {
            "schema": block_regeneration_verification.get("schema"),
            "ok": block_regeneration_verification.get("ok"),
            "summary": block_regeneration_verification.get("summary"),
        },
        "color_sign_screen_summary": {
            "schema": color_sign_screen.get("schema"),
            "r42_record_count": len(r42_color_sign_records),
            "all_r42_color_sign_vectors_ok": bool(r42_color_sign_records)
            and all(record.get("color_sign_vector_ok") for record in r42_color_sign_records),
            "r42_moduli": [record.get("m") for record in r42_color_sign_records],
        },
        "coverage_snapshot": {
            "proof_facing_typeA_residues_mod_48": coverage.get(
                "covered_residues_mod_48", []
            ),
            "open_residues_mod_48": coverage.get("open_residues_mod_48", []),
            "r42_is_open": 42 in coverage.get("open_residues_mod_48", []),
        },
        "required_branch_data": [
            "closed count/packet law for all q >= 0",
            "RF1/RF2 one-layer validity or an adapter to existing all-pair data",
            "color sign vector proof Omega_kappa = -1 for all five colors",
            "repeated-block screen if the branch schedule has block-power form",
            "pointwise first-return equations",
            "no-early/minimality proof",
            "quotient or splice one-cycle proof",
            "sum tau = m^4 time identity",
            "finite boundary case q = 0 integration",
            "Lean-facing theorem endpoint and theorem-name synchronization",
        ],
        "interpretation": (
            "R42 is the next simple symbolic-promotion target.  The q=0..4 "
            "samples have reproducible all-pair checker verification, pass the "
            "color sign vector screen, and have an internally verified compact "
            "boundary summary.  This is still evidence only and does not close "
            "the residue until the required symbolic branch data are proved."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--fits", type=Path, default=DEFAULT_FITS)
    parser.add_argument("--coverage", type=Path, default=DEFAULT_COVERAGE)
    parser.add_argument(
        "--sample-verification", type=Path, default=DEFAULT_SAMPLE_VERIFICATION
    )
    parser.add_argument("--boundary-summary", type=Path, default=DEFAULT_BOUNDARY_SUMMARY)
    parser.add_argument(
        "--boundary-verification", type=Path, default=DEFAULT_BOUNDARY_VERIFICATION
    )
    parser.add_argument(
        "--block-regeneration-verification",
        type=Path,
        default=DEFAULT_BLOCK_REGENERATION_VERIFICATION,
    )
    parser.add_argument("--color-sign-screen", type=Path, default=DEFAULT_COLOR_SIGN_SCREEN)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    record = build_record(
        args.fits,
        args.coverage,
        args.sample_verification,
        args.boundary_summary,
        args.boundary_verification,
        args.block_regeneration_verification,
        args.color_sign_screen,
    )
    print(
        "branch",
        record["branch"],
        "status",
        record["status"],
        "law",
        record["observed_law"],
    )
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
