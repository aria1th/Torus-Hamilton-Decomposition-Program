#!/usr/bin/env python3
"""Record the R42 q-parity split suggested by the block transducer."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_TRANSDUCER = ROOT / "certs" / "routeE_r42_boundary_block_transducer.json"
DEFAULT_PROMOTION = ROOT / "certs" / "routeE_r42_promotion_audit.json"


def build_summary(transducer_path: Path, promotion_path: Path) -> dict[str, Any]:
    transducer = json.loads(transducer_path.read_text())
    promotion = json.loads(promotion_path.read_text()) if promotion_path.exists() else {}
    summary = transducer.get("summary", {})
    q_values = summary.get("q_values", [])
    q1_missing = summary.get("q1_missing_q_ge_2_edges", [])
    piecewise_moduli = summary.get("edge_count_piecewise_moduli", [])
    q_ge_2_samples = [q for q in q_values if q >= 2]
    even_q_samples = [q for q in q_ge_2_samples if q % 2 == 0]
    odd_q_samples = [q for q in q_ge_2_samples if q % 2 == 1]
    return {
        "schema": "routeE_r42_mod96_branch_split_v1",
        "branch": "R42",
        "source_transducer": str(transducer_path),
        "source_promotion_audit": str(promotion_path),
        "reason": (
            "The q>=2 29-block transducer support is stable, but edge counts "
            "are piecewise rational-affine by q mod 2.  Therefore the symbolic "
            "promotion should split R42 into two mod-96 generic subbranches."
        ),
        "parent_family": "m = 48*q + 42, x = z = 6*q + 5",
        "finite_boundary_cases": [
            {
                "q": 0,
                "m": 42,
                "reason": "portfolio/all-pair sample case outside the q>=1 boundary block profile",
            },
            {
                "q": 1,
                "m": 90,
                "reason": "boundary block support has one missing q>=2 edge",
                "q1_missing_q_ge_2_edges": q1_missing,
            },
        ],
        "generic_subbranches": [
            {
                "name": "R42-even-q",
                "condition": "q = 2*s, s >= 1",
                "modulus_family": "m = 96*s + 42",
                "x_z_law": "x = z = 12*s + 5",
                "sample_q_values": even_q_samples,
                "sample_m_values": [48 * q + 42 for q in even_q_samples],
            },
            {
                "name": "R42-odd-q",
                "condition": "q = 2*s + 1, s >= 1",
                "modulus_family": "m = 96*s + 90",
                "x_z_law": "x = z = 12*s + 11",
                "sample_q_values": odd_q_samples,
                "sample_m_values": [48 * q + 42 for q in odd_q_samples],
            },
        ],
        "checks": {
            "q_ge_2_support_stable": summary.get("q_ge_2_support_stable"),
            "q_ge_2_edge_count": summary.get("q_ge_2_edge_count"),
            "q_ge_2_support_strongly_connected": summary.get(
                "q_ge_2_support_strongly_connected"
            ),
            "edge_count_fits_all_piecewise_affine": summary.get(
                "edge_count_fits_all_piecewise_affine"
            ),
            "edge_count_piecewise_moduli": piecewise_moduli,
            "promotion_ready": promotion.get("promotion_ready"),
            "required_theorem_item_count": len(
                promotion.get("required_theorem_items_missing", [])
            ),
        },
        "promotion_impact": {
            "closes_residue": False,
            "pointwise_equations_closed": False,
            "no_early_closed": False,
            "next_symbolic_target": (
                "Prove separate boundary/transducer pointwise and no-early "
                "laws for m=96*s+42 and m=96*s+90, plus finite cases m=42,90."
            ),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--transducer", type=Path, default=DEFAULT_TRANSDUCER)
    parser.add_argument("--promotion", type=Path, default=DEFAULT_PROMOTION)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    payload = build_summary(args.transducer, args.promotion)
    print("schema", payload["schema"])
    print("finite_cases", [case["m"] for case in payload["finite_boundary_cases"]])
    print(
        "generic_subbranches",
        [branch["modulus_family"] for branch in payload["generic_subbranches"]],
    )
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
