#!/usr/bin/env python3
"""Summarize the corrected Route-E open-residue promotion queue."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_COVERAGE = ROOT / "certs" / "routeE_typeA_residue_coverage.json"
DEFAULT_PORTFOLIO_FITS = ROOT / "certs" / "routeE_allpair_portfolio_fit_summary.json"
DEFAULT_R38 = ROOT / "certs" / "routeE_r38_gate_transducer_branch_record.json"
DEFAULT_R42 = ROOT / "certs" / "routeE_r42_promotion_audit.json"


def load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text()) if path.exists() else {}


def classify_row(
    row: dict[str, Any],
    covered: set[int],
    r38_targets: set[int],
    r42_audit: dict[str, Any],
) -> tuple[str, str]:
    residue = int(row["residue"])
    if residue in covered:
        return "proof_facing", "Already covered by Type-A proof-facing artifacts."
    if residue == 42:
        missing = [
            item["name"]
            for item in r42_audit.get("required_theorem_items_missing", [])
        ]
        return (
            "active_promotion_target",
            "Simple affine R42 family; missing " + "; ".join(missing) + ".",
        )
    if residue in r38_targets:
        return (
            "gate_transducer_target",
            "R38 has positive/negative symmetric probes; needs gate-transducer invariant.",
        )
    if row.get("xz_affine"):
        return (
            "affine_candidate_not_promoted",
            "Affine x/z fit exists but no branch record is promoted yet.",
        )
    tags = ",".join(row.get("tags", []))
    if tags == "sym":
        return (
            "portfolio_only_symmetric_nonaffine",
            "Portfolio samples are symmetric but x=z is not affine across q.",
        )
    return (
        "portfolio_only_nonaffine",
        "Portfolio samples exist but no simple affine x/z law is recorded.",
    )


def build_queue(
    coverage_path: Path,
    portfolio_fits_path: Path,
    r38_path: Path,
    r42_path: Path,
) -> dict[str, Any]:
    coverage = load(coverage_path)
    portfolio = load(portfolio_fits_path)
    r38 = load(r38_path)
    r42 = load(r42_path)
    covered = {int(residue) for residue in coverage.get("covered_residues_mod_48", [])}
    open_residues = {int(residue) for residue in coverage.get("open_residues_mod_48", [])}
    r38_targets = {int(residue) for residue in r38.get("target_residues_mod_48", [])}
    rows = []
    for row in portfolio.get("rows", []):
        residue = int(row["residue"])
        status, action = classify_row(row, covered, r38_targets, r42)
        rows.append(
            {
                "residue": residue,
                "status": status,
                "open_in_typeA_coverage": residue in open_residues,
                "proof_facing": residue in covered,
                "sample_count": row.get("sample_count"),
                "moduli": row.get("moduli"),
                "q_values": row.get("q_values"),
                "tags": row.get("tags"),
                "xz_affine": row.get("xz_affine"),
                "fit_x_status": row.get("fit_x", {}).get("status"),
                "fit_z_status": row.get("fit_z", {}).get("status"),
                "fit_nodes_formula": row.get("fit_nodes", {}).get("formula"),
                "recommended_next_action": action,
            }
        )
    rows.sort(key=lambda item: item["residue"])
    by_status: dict[str, list[int]] = {}
    for row in rows:
        by_status.setdefault(row["status"], []).append(row["residue"])
    return {
        "schema": "routeE_open_residue_queue_v1",
        "source_artifacts": {
            "coverage": str(coverage_path),
            "portfolio_fits": str(portfolio_fits_path),
            "r38_record": str(r38_path),
            "r42_promotion_audit": str(r42_path),
        },
        "residue_modulus": 48,
        "rows": rows,
        "summary": {
            "proof_facing_residues": sorted(covered),
            "open_residues": sorted(open_residues),
            "status_counts": {status: len(residues) for status, residues in by_status.items()},
            "residues_by_status": by_status,
            "recommended_order": [
                "42: active affine promotion target",
                "38: gate-transducer target",
                "remaining nonaffine portfolio-only residues: need new law mining",
            ],
            "coverage_complete": coverage.get("coverage_complete"),
        },
        "warning": (
            "This queue ranks proof-promotion work. It does not promote any "
            "residue by itself."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--coverage", type=Path, default=DEFAULT_COVERAGE)
    parser.add_argument("--portfolio-fits", type=Path, default=DEFAULT_PORTFOLIO_FITS)
    parser.add_argument("--r38", type=Path, default=DEFAULT_R38)
    parser.add_argument("--r42", type=Path, default=DEFAULT_R42)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    payload = build_queue(args.coverage, args.portfolio_fits, args.r38, args.r42)
    print("schema", payload["schema"])
    print("coverage_complete", payload["summary"]["coverage_complete"])
    print("status_counts", payload["summary"]["status_counts"])
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
