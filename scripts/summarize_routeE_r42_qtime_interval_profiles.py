#!/usr/bin/env python3
"""Summarize interval-level qtime profiles for R42 tail samples.

The mod-96 edge-partition diagnostic leaves 22 qtime-missing edges on each
tail branch.  This checker asks a narrower question: for those edge groups, is
qtime affine on each contiguous source-a interval in each sampled witness?
"""

from __future__ import annotations

import argparse
import json
import tempfile
from pathlib import Path
from typing import Any

import summarize_routeE_r42_boundary_quotient as r42
import summarize_routeE_r42_boundary_block_transducer as bt
from summarize_routeE_r42_mod96_edge_partitions import affine_coeffs, intervals


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_BIN = Path(tempfile.gettempdir()) / "routeE_allpair_cpp_v1_2"


def affine_formula(points: list[tuple[int, int]], var: str) -> str | None:
    if not points:
        return None
    if len(points) == 1:
        return str(points[0][1])
    x0, y0 = points[0]
    x1, y1 = points[1]
    if x1 == x0:
        return None
    num = y1 - y0
    den = x1 - x0
    if num % den:
        return None
    slope = num // den
    intercept = y0 - slope * x0
    if any(slope * x + intercept != y for x, y in points):
        return None
    if slope == 0:
        return str(intercept)
    term = var if slope == 1 else f"{slope}*{var}"
    if intercept == 0:
        return term
    sign = "+" if intercept > 0 else "-"
    return f"{term} {sign} {abs(intercept)}"


def parse_range(text: str) -> list[int]:
    if ":" in text:
        start, end = [int(part) for part in text.split(":", 1)]
        return list(range(start, end + 1))
    return [int(part) for part in text.split(",") if part]


def summarize_sample(binary: Path, q: int, workdir: Path) -> dict[str, Any]:
    m = 48 * q + 42
    x = 6 * q + 5
    z = x
    cap = max(10_000, 10 * m * m)
    csv_path = workdir / f"r42_qtime_intervals_q{q}.csv"
    proc = r42.subprocess.run(
        [str(binary), "dump-csv", str(m), str(x), str(z), str(cap), str(csv_path)],
        cwd=r42.REPO,
        text=True,
        stdout=r42.subprocess.PIPE,
        stderr=r42.subprocess.PIPE,
        check=False,
    )
    if proc.returncode != 0:
        return {
            "q": q,
            "m": m,
            "ok": False,
            "returncode": proc.returncode,
            "stderr_tail": proc.stderr.strip().splitlines()[-5:],
        }

    rows = r42.load_rows(csv_path)
    boundary = r42.boundary_return_rows(rows)
    blocks = bt.block_rows(boundary, m)
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

    nonaffine_edges = []
    interval_bad_total = 0
    interval_total = 0
    for (src, dst), members in sorted(groups.items()):
        members = sorted(members, key=lambda row: row["src_a"])
        if affine_coeffs([(member["src_a"], member["qtime"]) for member in members]):
            continue
        edge_interval_count = 0
        edge_bad_intervals = []
        for lo, hi in intervals([member["src_a"] for member in members]):
            sub = [member for member in members if lo <= member["src_a"] <= hi]
            coeffs = affine_coeffs([(member["src_a"], member["qtime"]) for member in sub])
            edge_interval_count += 1
            interval_total += 1
            if coeffs is None:
                interval_bad_total += 1
                edge_bad_intervals.append([lo, hi, len(sub)])
        nonaffine_edges.append(
            {
                "src": src,
                "dst": dst,
                "member_count": len(members),
                "interval_count": edge_interval_count,
                "bad_interval_count": len(edge_bad_intervals),
                "bad_intervals": edge_bad_intervals[:10],
            }
        )
    return {
        "q": q,
        "m": m,
        "ok": True,
        "nonaffine_edge_count": len(nonaffine_edges),
        "interval_count": interval_total,
        "bad_interval_count": interval_bad_total,
        "all_nonaffine_edges_interval_affine": interval_bad_total == 0,
        "nonaffine_edges": nonaffine_edges,
    }


def branch_formula_summary(samples: list[dict[str, Any]], parity: int) -> dict[str, Any]:
    name = "R42-even-q" if parity == 0 else "R42-odd-q"
    selected = [
        sample
        for sample in samples
        if sample.get("ok") and sample["q"] % 2 == parity
    ]
    edge_keys = sorted(
        {
            (edge["src"], edge["dst"])
            for sample in selected
            for edge in sample.get("nonaffine_edges", [])
        }
    )
    rows = []
    all_interval_counts_affine = True
    all_member_counts_affine = True
    for src, dst in edge_keys:
        per_sample = []
        for sample in selected:
            edge = next(
                edge
                for edge in sample.get("nonaffine_edges", [])
                if edge["src"] == src and edge["dst"] == dst
            )
            s = sample["q"] // 2 if parity == 0 else (sample["q"] - 1) // 2
            per_sample.append((s, sample, edge))
        interval_formula = affine_formula(
            [(s, edge["interval_count"]) for s, _, edge in per_sample], "s"
        )
        member_formula = affine_formula(
            [(s, edge["member_count"]) for s, _, edge in per_sample], "s"
        )
        all_interval_counts_affine = (
            all_interval_counts_affine and interval_formula is not None
        )
        all_member_counts_affine = all_member_counts_affine and member_formula is not None
        rows.append(
            {
                "src": src,
                "dst": dst,
                "interval_count_formula": interval_formula,
                "member_count_formula": member_formula,
                "has_multi_point_intervals": any(
                    edge["member_count"] != edge["interval_count"]
                    for _, _, edge in per_sample
                ),
                "sample_points": [
                    {
                        "s": s,
                        "q": sample["q"],
                        "interval_count": edge["interval_count"],
                        "member_count": edge["member_count"],
                    }
                    for s, sample, edge in per_sample
                ],
            }
        )
    return {
        "name": name,
        "parity": parity,
        "sample_q_values": [sample["q"] for sample in selected],
        "sample_s_values": [
            sample["q"] // 2 if parity == 0 else (sample["q"] - 1) // 2
            for sample in selected
        ],
        "edge_count": len(edge_keys),
        "all_interval_counts_affine_in_s": all_interval_counts_affine,
        "all_member_counts_affine_in_s": all_member_counts_affine,
        "multi_point_interval_edge_count": sum(
            1 for row in rows if row["has_multi_point_intervals"]
        ),
        "edge_interval_formulas": rows,
    }


def build_summary(q_values: list[int], binary: Path, compile_binary: bool) -> dict[str, Any]:
    if compile_binary:
        r42.compile_checker(binary)
    with tempfile.TemporaryDirectory(prefix="routeE-r42-qtime-intervals-") as tmp:
        samples = [summarize_sample(binary, q, Path(tmp)) for q in q_values]
    branch_formulas = [
        branch_formula_summary(samples, 0),
        branch_formula_summary(samples, 1),
    ]
    return {
        "schema": "routeE_r42_qtime_interval_profiles_v1",
        "family": "R42, m=48*q+42, x=z=6*q+5",
        "q_values": q_values,
        "samples": samples,
        "generic_subbranches": branch_formulas,
        "summary": {
            "all_samples_ok": all(sample.get("ok") for sample in samples),
            "all_nonaffine_edges_interval_affine": all(
                sample.get("all_nonaffine_edges_interval_affine") for sample in samples
            ),
            "all_interval_counts_affine_in_s": all(
                branch.get("all_interval_counts_affine_in_s") for branch in branch_formulas
            ),
            "all_member_counts_affine_in_s": all(
                branch.get("all_member_counts_affine_in_s") for branch in branch_formulas
            ),
            "branch_multi_point_interval_edge_counts": {
                branch["name"]: branch["multi_point_interval_edge_count"]
                for branch in branch_formulas
            },
            "nonaffine_edge_counts": {
                str(sample.get("q")): sample.get("nonaffine_edge_count")
                for sample in samples
            },
            "bad_interval_counts": {
                str(sample.get("q")): sample.get("bad_interval_count")
                for sample in samples
            },
        },
        "promotion_impact": {
            "closes_residue": False,
            "pointwise_equations_closed": False,
            "no_early_closed": False,
            "diagnosis": (
                "The remaining qtime-missing edge groups are interval-affine "
                "on sampled tail witnesses.  This suggests an interval grammar "
                "for time equations, but it is still sampled evidence."
            ),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--q-values", default="6:9")
    parser.add_argument("--binary", type=Path, default=DEFAULT_BIN)
    parser.add_argument("--no-compile", action="store_true")
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    payload = build_summary(parse_range(args.q_values), args.binary, not args.no_compile)
    print("schema", payload["schema"])
    print("all_samples_ok", payload["summary"]["all_samples_ok"])
    print(
        "all_nonaffine_edges_interval_affine",
        payload["summary"]["all_nonaffine_edges_interval_affine"],
    )
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
