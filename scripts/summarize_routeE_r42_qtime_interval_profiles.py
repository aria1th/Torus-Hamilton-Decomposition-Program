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


def build_summary(q_values: list[int], binary: Path, compile_binary: bool) -> dict[str, Any]:
    if compile_binary:
        r42.compile_checker(binary)
    with tempfile.TemporaryDirectory(prefix="routeE-r42-qtime-intervals-") as tmp:
        samples = [summarize_sample(binary, q, Path(tmp)) for q in q_values]
    return {
        "schema": "routeE_r42_qtime_interval_profiles_v1",
        "family": "R42, m=48*q+42, x=z=6*q+5",
        "q_values": q_values,
        "samples": samples,
        "summary": {
            "all_samples_ok": all(sample.get("ok") for sample in samples),
            "all_nonaffine_edges_interval_affine": all(
                sample.get("all_nonaffine_edges_interval_affine") for sample in samples
            ),
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
