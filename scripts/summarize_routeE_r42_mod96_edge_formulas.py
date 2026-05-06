#!/usr/bin/env python3
"""Convert R42 q-parity block-transducer counts into mod-96 branch formulas."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_TRANSDUCER = ROOT / "certs" / "routeE_r42_boundary_block_transducer.json"
DEFAULT_SPLIT = ROOT / "certs" / "routeE_r42_mod96_branch_split.json"


def affine_formula(points: list[tuple[int, int]], variable: str = "s") -> str | None:
    if not points:
        return None
    if len(points) == 1:
        return str(points[0][1])
    s0, v0 = points[0]
    s1, v1 = points[1]
    if s1 == s0:
        return None
    num = v1 - v0
    den = s1 - s0
    if num % den:
        return None
    slope = num // den
    intercept = v0 - slope * s0
    if any(slope * s + intercept != value for s, value in points):
        return None
    if slope == 0:
        return str(intercept)
    if intercept == 0:
        return variable if slope == 1 else f"{slope}*{variable}"
    sign = "+" if intercept > 0 else "-"
    qterm = variable if slope == 1 else f"{slope}*{variable}"
    return f"{qterm} {sign} {abs(intercept)}"


def build_summary(transducer_path: Path, split_path: Path) -> dict[str, Any]:
    transducer = json.loads(transducer_path.read_text())
    split = json.loads(split_path.read_text()) if split_path.exists() else {}
    edge_rows = []
    even_ok = True
    odd_ok = True
    for row in transducer.get("q_ge_2_edge_count_fits", []):
        samples = [(int(q), int(value)) for q, value in row.get("sample_points", [])]
        even_points = [(q // 2, value) for q, value in samples if q % 2 == 0]
        odd_points = [((q - 1) // 2, value) for q, value in samples if q % 2 == 1 and q >= 3]
        even_formula = affine_formula(even_points)
        odd_formula = affine_formula(odd_points)
        even_ok = even_ok and even_formula is not None
        odd_ok = odd_ok and odd_formula is not None
        edge_rows.append(
            {
                "src": row["src"],
                "dst": row["dst"],
                "even_q_branch": {
                    "branch": "m = 96*s + 42",
                    "sample_points_s": even_points,
                    "formula": even_formula,
                },
                "odd_q_branch": {
                    "branch": "m = 96*s + 90",
                    "sample_points_s": odd_points,
                    "formula": odd_formula,
                },
            }
        )
    return {
        "schema": "routeE_r42_mod96_edge_formulas_v1",
        "branch": "R42",
        "source_transducer": str(transducer_path),
        "source_split": str(split_path),
        "generic_subbranches": split.get("generic_subbranches"),
        "edge_count": len(edge_rows),
        "edge_formulas": edge_rows,
        "summary": {
            "edge_count": len(edge_rows),
            "even_q_branch": "m = 96*s + 42, s >= 1",
            "odd_q_branch": "m = 96*s + 90, s >= 1",
            "all_even_branch_formulas_affine_in_s": even_ok,
            "all_odd_branch_formulas_affine_in_s": odd_ok,
            "even_sample_s_values": sorted(
                {
                    point[0]
                    for row in edge_rows
                    for point in row["even_q_branch"]["sample_points_s"]
                }
            ),
            "odd_sample_s_values": sorted(
                {
                    point[0]
                    for row in edge_rows
                    for point in row["odd_q_branch"]["sample_points_s"]
                }
            ),
        },
        "promotion_impact": {
            "closes_residue": False,
            "pointwise_equations_closed": False,
            "no_early_closed": False,
            "diagnosis": (
                "The q-parity split turns the stable R42 block-transducer edge "
                "counts into affine-in-s tables on both mod-96 subbranches. "
                "This is still a block-count artifact, not pointwise/no-early."
            ),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--transducer", type=Path, default=DEFAULT_TRANSDUCER)
    parser.add_argument("--split", type=Path, default=DEFAULT_SPLIT)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    payload = build_summary(args.transducer, args.split)
    print("schema", payload["schema"])
    print("edge_count", payload["edge_count"])
    print(
        "all_even_branch_formulas_affine_in_s",
        payload["summary"]["all_even_branch_formulas_affine_in_s"],
    )
    print(
        "all_odd_branch_formulas_affine_in_s",
        payload["summary"]["all_odd_branch_formulas_affine_in_s"],
    )
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
