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


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text())


def build_record(
    fits_path: Path,
    coverage_path: Path,
    sample_verification_path: Path,
    boundary_summary_path: Path,
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
    rows = {int(row["residue"]): row for row in fits.get("rows", [])}
    row = rows[42]
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
        "sample_moduli": row.get("moduli"),
        "samples": row.get("samples"),
        "source_artifacts": {
            "portfolio_fits": str(fits_path),
            "portfolio_samples": "certs/routeE_allpair_portfolio_samples_v1_1.json",
            "sample_verification": str(sample_verification_path),
            "boundary_summary": str(boundary_summary_path),
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
            "product_t Lambda_t = -1 sign proof",
            "pointwise first-return equations",
            "no-early/minimality proof",
            "quotient or splice one-cycle proof",
            "sum tau = m^4 time identity",
            "finite boundary case q = 0 integration",
            "Lean-facing theorem endpoint and theorem-name synchronization",
        ],
        "interpretation": (
            "R42 is the next simple symbolic-promotion target.  The q=0..4 "
            "samples now have reproducible all-pair checker verification, but "
            "this is still evidence only and does not close the residue until "
            "the required symbolic branch data are proved."
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
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    record = build_record(
        args.fits, args.coverage, args.sample_verification, args.boundary_summary
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
