#!/usr/bin/env python3
"""Initialize the R38 Route-E gate-transducer branch record.

The R38 residue is the next Type-A mining target after B20/B16/R14e.  Existing
evidence shows that a naive fixed symmetric law is too small, so this script
creates a proof-facing branch record for a future gate/transducer family rather
than a theorem claim.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_COVERAGE = ROOT / "certs" / "routeE_typeA_residue_coverage.json"
DEFAULT_SYMMETRIC = ROOT / "certs" / "routeE_r38_symmetric_probe_summary.json"
DEFAULT_CPP_TIMEOUT = ROOT / "certs" / "routeE_r38_m182_cpp_screen_timeout.json"


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text()) if path.exists() else {}


def build_record(coverage_path: Path, symmetric_path: Path, cpp_timeout_path: Path) -> dict:
    coverage = load_json(coverage_path)
    symmetric = load_json(symmetric_path)
    cpp_timeout = load_json(cpp_timeout_path)
    target_residues = (
        coverage.get("next_target", {}).get("target_residues_mod_48") or [38]
    )
    open_residues = coverage.get("open_residues_mod_48", [])
    return {
        "schema": "routeE_r38_gate_transducer_branch_record_v1",
        "branch": "R38",
        "status": "open_gate_transducer_target",
        "modulus_family": "m == 38 mod 48",
        "target_residues_mod_48": target_residues,
        "target_residues_are_open": all(r in open_residues for r in target_residues),
        "source_artifacts": {
            "coverage": str(coverage_path),
            "symmetric_probe": str(symmetric_path),
            "cpp_timeout_screen": str(cpp_timeout_path),
        },
        "positive_seed_evidence": symmetric.get("hits", {}),
        "negative_controls": [
            {
                "name": "naive symmetric continuation fails",
                "evidence": (
                    "The symmetric probe records m=134,x=23 with time sum m^4 "
                    "but section cycle split 38,38,57."
                ),
            },
            {
                "name": "m=182 one-cycle-looking symmetric candidates fail time exhaustion",
                "evidence": (
                    "The probe records m=182,x=21 and x=63 with one section "
                    "cycle [181] but return-time sum far below m^4."
                ),
            },
            {
                "name": "short C++ support-pattern screen is timeout-heavy",
                "evidence": (
                    "The m=182 screen over patterns 0,1,3 / 0,3,4 / 1,3,4 / "
                    "0,1,4 / 2,3,4 timed out with no partial hits at 8s."
                ),
            },
        ],
        "required_branch_data": [
            "closed packet/count formula, not a fixed x=z law",
            "finite gate state set and transition formula",
            "boundary or macro section definition",
            "section return map formula",
            "section one-cycle proof",
            "no-early/minimality proof",
            "insertion distribution from boundary/macro section to all-pair section",
            "label or label-destination time mass polynomials",
            "sum tau = m^4 identity",
            "finite boundary cases",
        ],
        "proof_style": (
            "Type-A all-pair/boundary/macro quotient certificate, unless a "
            "different full-layered parity-changing template is discovered."
        ),
        "search_guidance": [
            "Do not promote a symmetric x=z streak directly.",
            "Prefer outputs that expose a finite gate graph and insertion lengths.",
            "Use timeout-safe search runs and preserve compact summaries, not raw massive maps.",
            "A candidate is not proof-facing until it supplies return equations, no-early facts, and time exhaustion.",
        ],
        "coverage_snapshot": {
            "covered_typeA_residues_mod_48": coverage.get("covered_residues_mod_48"),
            "open_residues_mod_48": open_residues,
        },
        "cpp_timeout_snapshot": {
            "timeout_seconds": cpp_timeout.get("timeout_seconds"),
            "patterns": cpp_timeout.get("patterns"),
            "all_timed_out": bool(cpp_timeout)
            and all(result.get("timeout") for result in cpp_timeout.get("results", [])),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--coverage", type=Path, default=DEFAULT_COVERAGE)
    parser.add_argument("--symmetric", type=Path, default=DEFAULT_SYMMETRIC)
    parser.add_argument("--cpp-timeout", type=Path, default=DEFAULT_CPP_TIMEOUT)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    record = build_record(args.coverage, args.symmetric, args.cpp_timeout)
    print("branch", record["branch"], "status", record["status"])
    print("target residues", record["target_residues_mod_48"])
    print("positive seeds", record["positive_seed_evidence"])
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
