#!/usr/bin/env python3
"""Probe feature depth for unresolved R42 bad-intercept atoms.

This is a targeted stress tool for the atom that survives the one/two-feature
carry split.  It regenerates sampled rows, then searches exact linear models
using the same base intercept features plus one-, two-, and three-feature carry
corrections.  A positive hit is still only qtime evidence; a miss is evidence
that the proposed finite state is continuing to split.
"""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path
from typing import Any

import summarize_routeE_r42_bad_intercept_carry_split as split


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_ATOM = "20->26|L1|B7:7|R0:0"
DEFAULT_BINARY = split.DEFAULT_BIN
DEFAULT_QTIME_ATOMS = split.DEFAULT_QTIME_ATOMS


def feature_values(row: dict[str, Any], features: list[split.Feature]) -> list[int]:
    return [fn(row) for _, fn in features]


def fit_atom(
    rows: list[dict[str, Any]],
    features: list[split.Feature],
    max_depth: int,
    max_hits: int,
) -> dict[str, Any]:
    base_names = ["1", "s", "s^2", "j", "s*j"]
    base_points = [
        (split.base_features(row), row["qtime_intercept"])
        for row in rows
    ]
    base_fit = split.solve_linear(base_points)
    if base_fit is not None:
        return {
            "base_fit": True,
            "minimal_depth": 0,
            "hits": [{"features": [], "formula": split.format_linear(base_fit, base_names)}],
        }

    names = [name for name, _ in features]
    values = [feature_values(row, features) for row in rows]
    for depth in range(1, max_depth + 1):
        hits = []
        for combo in itertools.combinations(range(len(features)), depth):
            fit = split.solve_linear(
                [
                    (
                        split.base_features(row) + [values[i][j] for j in combo],
                        row["qtime_intercept"],
                    )
                    for i, row in enumerate(rows)
                ]
            )
            if fit is None:
                continue
            combo_names = [names[j] for j in combo]
            hits.append(
                {
                    "features": combo_names,
                    "formula": split.format_linear(fit, base_names + combo_names),
                }
            )
            if len(hits) >= max_hits:
                break
        if hits:
            return {
                "base_fit": False,
                "minimal_depth": depth,
                "hits": hits,
            }
    return {
        "base_fit": False,
        "minimal_depth": None,
        "hits": [],
    }


def build_summary(
    q_values: list[int],
    atom: str,
    binary: Path,
    compile_binary: bool,
    max_depth: int,
    max_hits: int,
) -> dict[str, Any]:
    rows = split.collect_bad_rows(
        q_values=q_values,
        binary=binary,
        bad_atoms={atom},
        compile_binary=compile_binary,
    )
    rows = [row for row in rows if row["atom"] == atom]
    branches = []
    features = split.candidate_features()
    for branch_name in ("R42-even-q", "R42-odd-q"):
        branch_rows = [row for row in rows if row["branch"] == branch_name]
        fit = fit_atom(branch_rows, features, max_depth=max_depth, max_hits=max_hits)
        branches.append(
            {
                "name": branch_name,
                "rows": len(branch_rows),
                "q_values": sorted({row["q"] for row in branch_rows}),
                "j_values": sorted({row["j"] for row in branch_rows}),
                "qj_points": [
                    {
                        "q": row["q"],
                        "s": row["s"],
                        "j": row["j"],
                        "qtime_intercept": row["qtime_intercept"],
                    }
                    for row in branch_rows[:200]
                ],
                **fit,
            }
        )
    return {
        "schema": "routeE_r42_unresolved_atom_feature_depth_v1",
        "family": "R42, c=6*q+5, m=8*c+2, x=z=c",
        "atom": atom,
        "q_values": q_values,
        "max_depth": max_depth,
        "candidate_feature_count": len(features),
        "generic_subbranches": branches,
        "summary": {
            "minimal_depth_by_branch": {
                branch["name"]: branch["minimal_depth"] for branch in branches
            },
            "all_nonempty_branches_hit": all(
                branch["rows"] == 0 or branch["minimal_depth"] is not None
                for branch in branches
            ),
        },
        "promotion_impact": {
            "closes_residue": False,
            "pointwise_equations_closed": False,
            "no_early_closed": False,
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--q-values", default="6,8,10")
    parser.add_argument("--atom", default=DEFAULT_ATOM)
    parser.add_argument("--binary", type=Path, default=DEFAULT_BINARY)
    parser.add_argument("--max-depth", type=int, default=3)
    parser.add_argument("--max-hits", type=int, default=8)
    parser.add_argument("--no-compile", action="store_true")
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    payload = build_summary(
        q_values=split.parse_q_values(args.q_values),
        atom=args.atom,
        binary=args.binary,
        compile_binary=not args.no_compile,
        max_depth=args.max_depth,
        max_hits=args.max_hits,
    )
    print("schema", payload["schema"])
    print("atom", payload["atom"])
    print("q_values", payload["q_values"])
    print("summary", payload["summary"])
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
