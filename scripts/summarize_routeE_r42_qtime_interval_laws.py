#!/usr/bin/env python3
"""Mine start/end ordinal laws for R42 qtime interval profiles."""

from __future__ import annotations

import argparse
import json
import tempfile
from pathlib import Path
from typing import Any

import summarize_routeE_r42_boundary_quotient as r42
import summarize_routeE_r42_boundary_block_transducer as bt
from summarize_routeE_r42_mod96_edge_partitions import affine_coeffs, intervals
from summarize_routeE_r42_qtime_interval_profiles import affine_formula


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_BIN = Path(tempfile.gettempdir()) / "routeE_allpair_cpp_v1_2"


def parse_range(text: str) -> list[int]:
    if ":" in text:
        start, end = [int(part) for part in text.split(":", 1)]
        return list(range(start, end + 1))
    return [int(part) for part in text.split(",") if part]


def interval_occurrences(binary: Path, q: int, workdir: Path) -> list[dict[str, Any]]:
    m = 48 * q + 42
    x = 6 * q + 5
    z = x
    cap = max(10_000, 10 * m * m)
    csv_path = workdir / f"r42_interval_laws_q{q}.csv"
    proc = r42.subprocess.run(
        [str(binary), "dump-csv", str(m), str(x), str(z), str(cap), str(csv_path)],
        cwd=r42.REPO,
        text=True,
        stdout=r42.subprocess.PIPE,
        stderr=r42.subprocess.PIPE,
        check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr)
    rows = r42.load_rows(csv_path)
    blocks = bt.block_rows(r42.boundary_return_rows(rows), m)
    by_node: dict[tuple[str, int], int] = {}
    by_member: dict[tuple[str, int], dict[str, Any]] = {}
    for index, block in enumerate(blocks):
        for member in block["_members"]:
            key = (member["src_label"], member["src_a"])
            by_node[key] = index
            by_member[key] = member
    groups: dict[tuple[int, int], list[dict[str, Any]]] = {}
    for key, member in by_member.items():
        src_block = by_node[key]
        dst_block = by_node[(member["dst_label"], member["dst_a"])]
        groups.setdefault((src_block, dst_block), []).append(member)

    out = []
    for (src, dst), members in sorted(groups.items()):
        members = sorted(members, key=lambda row: row["src_a"])
        if affine_coeffs([(member["src_a"], member["qtime"]) for member in members]):
            continue
        edge_intervals = []
        for lo, hi in intervals([member["src_a"] for member in members]):
            sub = [member for member in members if lo <= member["src_a"] <= hi]
            coeffs = affine_coeffs([(member["src_a"], member["qtime"]) for member in sub])
            if coeffs is None:
                raise AssertionError((q, src, dst, lo, hi))
            edge_intervals.append((lo, hi, len(sub), coeffs[0], coeffs[1]))
        total = len(edge_intervals)
        s = q // 2 if q % 2 == 0 else (q - 1) // 2
        branch = "R42-even-q" if q % 2 == 0 else "R42-odd-q"
        for ordinal, (lo, hi, length, slope, intercept) in enumerate(edge_intervals):
            out.append(
                {
                    "branch": branch,
                    "q": q,
                    "s": s,
                    "src": src,
                    "dst": dst,
                    "ordinal_start": ordinal,
                    "ordinal_end": total - 1 - ordinal,
                    "lo": lo,
                    "hi": hi,
                    "length": length,
                    "qtime_slope": slope,
                    "qtime_intercept": intercept,
                }
            )
    return out


def formula_group(rows: list[dict[str, Any]], mode: str) -> dict[str, Any]:
    sample_points = sorted(
        [
            {
                "q": row["q"],
                "s": row["s"],
                "lo": row["lo"],
                "hi": row["hi"],
                "length": row["length"],
                "qtime_slope": row["qtime_slope"],
                "qtime_intercept": row["qtime_intercept"],
            }
            for row in rows
        ],
        key=lambda row: row["s"],
    )
    def fit(field: str) -> str | None:
        return affine_formula([(row["s"], row[field]) for row in sample_points], "s")

    formulas = {
        "lo": fit("lo"),
        "hi": fit("hi"),
        "length": fit("length"),
        "qtime_slope": fit("qtime_slope"),
        "qtime_intercept": fit("qtime_intercept"),
    }
    return {
        "branch": rows[0]["branch"],
        "src": rows[0]["src"],
        "dst": rows[0]["dst"],
        "mode": mode,
        "ordinal": rows[0]["ordinal_start"] if mode == "start" else rows[0]["ordinal_end"],
        "sample_count": len(rows),
        "sample_s_values": [row["s"] for row in sample_points],
        "formulas": formulas,
        "all_formulas_affine": all(value is not None for value in formulas.values()),
    }


def build_summary(q_values: list[int], binary: Path, compile_binary: bool) -> dict[str, Any]:
    if compile_binary:
        r42.compile_checker(binary)
    with tempfile.TemporaryDirectory(prefix="routeE-r42-interval-laws-") as tmp:
        occurrences = [
            occurrence
            for q in q_values
            for occurrence in interval_occurrences(binary, q, Path(tmp))
        ]
    grouped: dict[tuple[str, int, int, str, int], list[dict[str, Any]]] = {}
    for occurrence in occurrences:
        for mode, ordinal_key in [
            ("start", occurrence["ordinal_start"]),
            ("end", occurrence["ordinal_end"]),
        ]:
            grouped.setdefault(
                (
                    occurrence["branch"],
                    occurrence["src"],
                    occurrence["dst"],
                    mode,
                    ordinal_key,
                ),
                [],
            ).append(occurrence)
    groups = [formula_group(rows, key[3]) for key, rows in sorted(grouped.items())]
    good_keys = {
        (group["branch"], group["src"], group["dst"], group["mode"], group["ordinal"])
        for group in groups
        if group["sample_count"] >= 2 and group["all_formulas_affine"]
    }
    uncovered = []
    for occurrence in occurrences:
        start_key = (
            occurrence["branch"],
            occurrence["src"],
            occurrence["dst"],
            "start",
            occurrence["ordinal_start"],
        )
        end_key = (
            occurrence["branch"],
            occurrence["src"],
            occurrence["dst"],
            "end",
            occurrence["ordinal_end"],
        )
        if start_key not in good_keys and end_key not in good_keys:
            uncovered.append(occurrence)
    repeated_bad = [
        group
        for group in groups
        if group["sample_count"] >= 2 and not group["all_formulas_affine"]
    ]
    singleton_groups = [group for group in groups if group["sample_count"] == 1]
    return {
        "schema": "routeE_r42_qtime_interval_laws_v1",
        "q_values": q_values,
        "occurrence_count": len(occurrences),
        "group_count": len(groups),
        "repeated_group_count": len(groups) - len(singleton_groups),
        "singleton_group_count": len(singleton_groups),
        "repeated_bad_group_count": len(repeated_bad),
        "uncovered_occurrence_count": len(uncovered),
        "summary": {
            "all_repeated_groups_affine": not repeated_bad,
            "all_occurrences_covered_by_start_or_end_affine_group": not uncovered,
            "branch_occurrence_counts": {
                branch: sum(1 for row in occurrences if row["branch"] == branch)
                for branch in ["R42-even-q", "R42-odd-q"]
            },
        },
        "sample_group_formulas": groups[:80],
        "repeated_bad_groups": repeated_bad[:40],
        "uncovered_occurrences": uncovered[:40],
        "promotion_impact": {
            "closes_residue": False,
            "pointwise_equations_closed": False,
            "no_early_closed": False,
            "diagnosis": (
                "This tests the simple start/end ordinal qtime interval-law "
                "hypothesis.  The summary records whether repeated ordinal "
                "groups are affine and whether sampled occurrences are covered. "
                "A failure is useful negative evidence for the next grammar."
            ),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--q-values", default="6:11")
    parser.add_argument("--binary", type=Path, default=DEFAULT_BIN)
    parser.add_argument("--no-compile", action="store_true")
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    payload = build_summary(parse_range(args.q_values), args.binary, not args.no_compile)
    print("schema", payload["schema"])
    print("occurrence_count", payload["occurrence_count"])
    print("repeated_bad_group_count", payload["repeated_bad_group_count"])
    print("uncovered_occurrence_count", payload["uncovered_occurrence_count"])
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
