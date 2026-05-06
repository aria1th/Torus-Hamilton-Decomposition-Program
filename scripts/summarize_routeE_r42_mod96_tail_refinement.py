#!/usr/bin/env python3
"""Summarize tail refinements in the R42 mod-96 edge-partition diagnostic."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PARTITIONS = ROOT / "certs" / "routeE_r42_mod96_edge_partitions.json"


def affine_coeffs(values: list[tuple[int, list[int] | None]]) -> bool:
    if len(values) < 2:
        return False
    if any(coeffs is None for _, coeffs in values):
        return False
    for index in [0, 1]:
        x0, y0 = values[0][0], values[0][1][index]  # type: ignore[index]
        x1, y1 = values[1][0], values[1][1][index]  # type: ignore[index]
        if x1 == x0 or (y1 - y0) % (x1 - x0):
            return False
        slope = (y1 - y0) // (x1 - x0)
        intercept = y0 - slope * x0
        for x, coeffs in values:
            if slope * x + intercept != coeffs[index]:  # type: ignore[index]
                return False
    return True


def bad_edges_for_drop(branch: dict[str, Any], drop: int) -> dict[str, Any]:
    target_bad = []
    qtime_bad = []
    qtime_missing = []
    qtime_nonaffine = []
    qsteps_bad = []
    tail_q_values = []
    finite_q_values = []
    for row in branch.get("edge_partition_formulas", []):
        stats = row.get("sample_stats", [])
        if not finite_q_values:
            finite_q_values = [sample["q"] for sample in stats[:drop]]
            tail_q_values = [sample["q"] for sample in stats[drop:]]
        target_values = [
            (sample["s"], sample.get("target_affine_mod_m"))
            for sample in stats[drop:]
        ]
        qtime_values = [
            (sample["s"], sample.get("qtime_affine_coeffs"))
            for sample in stats[drop:]
        ]
        qsteps_values = [
            (sample["s"], sample.get("qsteps_affine_coeffs"))
            for sample in stats[drop:]
        ]
        edge = {"src": row["src"], "dst": row["dst"]}
        if not affine_coeffs(target_values):
            target_bad.append(edge)
        if not affine_coeffs(qtime_values):
            qtime_bad.append(edge)
            if any(coeffs is None for _, coeffs in qtime_values):
                qtime_missing.append(edge)
            else:
                qtime_nonaffine.append(edge)
        if not affine_coeffs(qsteps_values):
            qsteps_bad.append(edge)
    return {
        "drop_first_sample_count": drop,
        "finite_q_values_before_tail": finite_q_values,
        "finite_m_values_before_tail": [48 * q + 42 for q in finite_q_values],
        "tail_q_values": tail_q_values,
        "tail_m_values": [48 * q + 42 for q in tail_q_values],
        "target_bad_edge_count": len(target_bad),
        "qtime_bad_edge_count": len(qtime_bad),
        "qtime_missing_edge_count": len(qtime_missing),
        "qtime_nonaffine_edge_count": len(qtime_nonaffine),
        "qsteps_bad_edge_count": len(qsteps_bad),
        "target_bad_edges": target_bad,
        "qtime_missing_edges": qtime_missing,
        "qtime_nonaffine_edges": qtime_nonaffine,
        "qsteps_bad_edges": qsteps_bad,
    }


def build_summary(partitions_path: Path) -> dict[str, Any]:
    data = json.loads(partitions_path.read_text())
    branches = []
    for branch in data.get("generic_subbranches", []):
        tails = [bad_edges_for_drop(branch, drop) for drop in [0, 1, 2]]
        branches.append(
            {
                "name": branch.get("name"),
                "sample_q_values": branch.get("sample_q_values"),
                "tail_refinements": tails,
            }
        )
    return {
        "schema": "routeE_r42_mod96_tail_refinement_v1",
        "source": str(partitions_path),
        "q_values": data.get("summary", {}).get("q_values"),
        "branches": branches,
        "conclusion": {
            "target_coefficients_affine_after_dropping_first_generic_sample": all(
                tail["target_bad_edge_count"] == 0
                for branch in branches
                for tail in branch["tail_refinements"]
                if tail["drop_first_sample_count"] == 1
            ),
            "qtime_nonaffine_edges_removed_after_dropping_first_two_generic_samples": all(
                tail["qtime_nonaffine_edge_count"] == 0
                for branch in branches
                for tail in branch["tail_refinements"]
                if tail["drop_first_sample_count"] == 2
            ),
            "remaining_qtime_missing_edges_after_two_drops": {
                branch["name"]: next(
                    tail["qtime_missing_edge_count"]
                    for tail in branch["tail_refinements"]
                    if tail["drop_first_sample_count"] == 2
                )
                for branch in branches
            },
        },
        "promotion_impact": {
            "closes_residue": False,
            "pointwise_equations_closed": False,
            "no_early_closed": False,
            "diagnosis": (
                "Tail refinement localizes the non-affine target/time behavior "
                "to early generic samples and to 22 qtime-missing edges, but it "
                "does not prove pointwise first-return or no-early."
            ),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--partitions", type=Path, default=DEFAULT_PARTITIONS)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    payload = build_summary(args.partitions)
    print("schema", payload["schema"])
    print("q_values", payload["q_values"])
    print(
        "target_tail_ok",
        payload["conclusion"][
            "target_coefficients_affine_after_dropping_first_generic_sample"
        ],
    )
    print(
        "qtime_tail_nonaffine_removed",
        payload["conclusion"][
            "qtime_nonaffine_edges_removed_after_dropping_first_two_generic_samples"
        ],
    )
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
