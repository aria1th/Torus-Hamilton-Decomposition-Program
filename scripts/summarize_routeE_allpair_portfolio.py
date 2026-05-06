#!/usr/bin/env python3
"""Summarize Route-E all-pair portfolio sample coverage.

The v3.6 Route-E proof bundle contains zero-event checked all-pair candidate
samples for every even residue class mod 48.  These samples are useful search
evidence, but they are not symbolic branch theorems.  This script records that
distinction explicitly.
"""

from __future__ import annotations

import argparse
import json
from collections import defaultdict
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SOURCE = ROOT / "certs" / "routeE_allpair_portfolio_samples_v1_1.json"
DEFAULT_COVERAGE = ROOT / "certs" / "routeE_typeA_residue_coverage.json"


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text())


def summarize(source: Path, coverage_path: Path, modulus: int) -> dict[str, Any]:
    payload = load_json(source)
    coverage = load_json(coverage_path) if coverage_path.exists() else {}
    samples = payload.get("samples", [])
    by_residue: dict[int, list[dict[str, Any]]] = defaultdict(list)
    for sample in samples:
        m = int(sample["m"])
        by_residue[m % modulus].append(sample)

    residue_rows = []
    for residue in sorted(by_residue):
        rows = sorted(by_residue[residue], key=lambda item: int(item["m"]))
        residue_rows.append(
            {
                "residue": residue,
                "sample_count": len(rows),
                "moduli": [int(item["m"]) for item in rows],
                "tags": sorted({str(item.get("tag")) for item in rows}),
                "count_admissible_all": all(
                    str(item.get("count_admissible")) in {"1", "True", "true"}
                    for item in rows
                ),
                "time_sum_targets": [int(item["time_sum_target"]) for item in rows],
            }
        )

    even_residues = list(range(0, modulus, 2))
    covered_residues = sorted(by_residue)
    proof_facing = sorted(int(x) for x in coverage.get("covered_residues_mod_48", []))
    portfolio_only = [
        residue for residue in covered_residues if residue not in set(proof_facing)
    ]
    return {
        "schema": "routeE_allpair_portfolio_summary_v1",
        "source": str(source),
        "upstream_schema": payload.get("schema"),
        "scope": payload.get("scope"),
        "sample_count": len(samples),
        "residue_modulus": modulus,
        "even_residue_count": len(even_residues),
        "covered_residue_count": len(covered_residues),
        "all_even_residues_covered_by_samples": covered_residues == even_residues,
        "covered_residues": covered_residues,
        "proof_facing_typeA_residues": proof_facing,
        "portfolio_only_residues": portfolio_only,
        "portfolio_only_count": len(portfolio_only),
        "residue_rows": residue_rows,
        "interpretation": (
            "The portfolio gives zero-event checked all-pair candidates across "
            "all even residues mod 48.  It is search evidence only; residues "
            "outside proof_facing_typeA_residues still need symbolic formulas, "
            "no-early proofs, time identities, and Lean-facing branch records."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, default=DEFAULT_SOURCE)
    parser.add_argument("--coverage", type=Path, default=DEFAULT_COVERAGE)
    parser.add_argument("--modulus", type=int, default=48)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    summary = summarize(args.source, args.coverage, args.modulus)
    print(
        "samples",
        summary["sample_count"],
        "covered_residues",
        summary["covered_residue_count"],
        "all_even",
        summary["all_even_residues_covered_by_samples"],
        "portfolio_only",
        summary["portfolio_only_count"],
    )
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
