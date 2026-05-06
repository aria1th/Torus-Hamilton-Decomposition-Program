#!/usr/bin/env python3
"""Summarize proof-facing Route-E Type-A residue coverage.

The corrected even D5 dispatcher is not closed.  This script records which
even residue classes modulo 48 are currently represented by promoted Type-A
proof-facing branches, and which residue classes remain open.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_B20_CERT = ROOT / "certs" / "d5_routeE_b20_branch_verify_m20_44_68.json"
DEFAULT_TYPEA_CERT = ROOT / "certs" / "routeE_typeA_closure_package_summary.json"


def residues(moduli: list[int], modulus: int = 48) -> list[int]:
    return sorted({m % modulus for m in moduli})


def branch_record(name: str, moduli: list[int], status: str) -> dict[str, Any]:
    return {
        "name": name,
        "sample_moduli": moduli,
        "residues_mod_48": residues(moduli),
        "status": status,
    }


def build_summary(b20_path: Path, typea_path: Path) -> dict[str, Any]:
    b20 = json.loads(b20_path.read_text()) if b20_path.exists() else {}
    typea = json.loads(typea_path.read_text()) if typea_path.exists() else {}

    branches = [
        branch_record(
            "B20",
            b20.get("moduli", []),
            "proof-facing evidence; pointwise first-return/minimality still open",
        )
    ]
    if typea:
        branches.extend(
            [
                branch_record(
                    "B16",
                    typea.get("b16", {}).get("moduli", []),
                    "proof-facing package evidence; Lean branch theorem still open",
                ),
                branch_record(
                    "R14e",
                    typea.get("r14e", {}).get("moduli", []),
                    "proof-facing package evidence; Lean branch theorem still open",
                ),
            ]
        )

    even_residues = list(range(0, 48, 2))
    covered = sorted({r for br in branches for r in br["residues_mod_48"]})
    open_residues = [r for r in even_residues if r not in covered]
    return {
        "schema": "routeE_typeA_residue_coverage_v1",
        "modulus": 48,
        "branches": branches,
        "covered_residues_mod_48": covered,
        "open_residues_mod_48": open_residues,
        "coverage_count": len(covered),
        "even_residue_count": len(even_residues),
        "coverage_complete": len(open_residues) == 0,
        "next_target": {
            "name": "R42 affine all-pair/boundary family",
            "target_residues_mod_48": [42],
            "reason": (
                "The portfolio fit scan identifies 42 mod 48 as the only "
                "portfolio-only residue with a simple affine x=z law.  The "
                "R42 artifacts now include q=0..4 all-pair verification, a "
                "q>=1 stable 29-block boundary quotient summary, and a compact "
                "boundary-summary verifier.  It remains open because pointwise "
                "first-return/no-early formulas and the full branch theorem are "
                "not proved."
            ),
        },
        "secondary_targets": [
            {
                "name": "R38 / gate-transducer family",
                "target_residues_mod_48": [38],
                "reason": (
                    "R38 remains useful evidence, but the naive symmetric "
                    "theorem has negative controls; it should stay a "
                    "gate-transducer target until a primitiveity invariant is "
                    "found."
                ),
            }
        ],
        "warning": (
            "Residue coverage is only a branch-planning artifact.  Covered "
            "residues are proof-facing evidence, not closed Lean theorems."
        ),
    }


def markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# Route-E Type-A Residue Coverage",
        "",
        "| branch | residues mod 48 | samples | status |",
        "| --- | --- | --- | --- |",
    ]
    for br in summary["branches"]:
        lines.append(
            "| "
            + " | ".join(
                [
                    br["name"],
                    ",".join(map(str, br["residues_mod_48"])),
                    ",".join(map(str, br["sample_moduli"])),
                    br["status"],
                ]
            )
            + " |"
        )
    lines.extend(
        [
            "",
            f"Covered residues: {summary['covered_residues_mod_48']}",
            f"Open residues: {summary['open_residues_mod_48']}",
            "",
            "Next target:",
            "",
            f"- {summary['next_target']['name']}: residues {summary['next_target']['target_residues_mod_48']}",
        ]
    )
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--b20-cert", type=Path, default=DEFAULT_B20_CERT)
    parser.add_argument("--typea-cert", type=Path, default=DEFAULT_TYPEA_CERT)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    summary = build_summary(args.b20_cert, args.typea_cert)
    print(markdown(summary))
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
