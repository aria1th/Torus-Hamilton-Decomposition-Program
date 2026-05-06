#!/usr/bin/env python3
"""Summarize R42 mod-96 block-edge point partitions.

This is one step finer than edge-count formulas: for each stable 29-block edge,
and separately on the two generic mod-96 branches, it records whether the
points taking that edge have affine-in-s counts and affine target/time maps
on the sampled witnesses.

It is still not a no-early proof, but it is closer to a pointwise
first-return table than aggregate edge counts.
"""

from __future__ import annotations

import argparse
import json
import tempfile
from pathlib import Path
from typing import Any

import summarize_routeE_r42_boundary_quotient as r42
import summarize_routeE_r42_boundary_block_transducer as bt


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_BIN = Path(tempfile.gettempdir()) / "routeE_allpair_cpp_v1_2"
DEFAULT_EDGE_FORMULAS = ROOT / "certs" / "routeE_r42_mod96_edge_formulas.json"


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


def affine_coeffs(points: list[tuple[int, int]]) -> tuple[int, int] | None:
    if not points:
        return None
    if len(points) == 1:
        return (0, points[0][1])
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
    return (slope, intercept)


def affine_mod(points: list[tuple[int, int]], m: int) -> tuple[int, int] | None:
    return r42.affine_mod(points, m)


def intervals(values: list[int]) -> list[list[int]]:
    if not values:
        return []
    out = []
    start = prev = values[0]
    for value in values[1:]:
        if value == prev + 1:
            prev = value
            continue
        out.append([start, prev])
        start = prev = value
    out.append([start, prev])
    return out


def condition_stats(members: list[dict[str, Any]]) -> dict[str, Any]:
    values = sorted(member["src_a"] for member in members)
    ivals = intervals(values)
    return {
        "count": len(values),
        "min": values[0] if values else None,
        "max": values[-1] if values else None,
        "interval_count": len(ivals),
        "first_intervals": ivals[:4],
        "last_intervals": ivals[-3:],
    }


def summarize_sample(binary: Path, q: int, workdir: Path) -> dict[str, Any]:
    m = 48 * q + 42
    x = 6 * q + 5
    z = x
    cap = max(10_000, 10 * m * m)
    csv_path = workdir / f"r42_edge_partition_q{q}.csv"
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
    edge_rows = []
    for (src, dst), members in sorted(groups.items()):
        members = sorted(members, key=lambda row: row["src_a"])
        target_affine = affine_mod(
            [(member["src_a"], member["dst_a"]) for member in members], m
        )
        qtime_affine = affine_formula(
            [(member["src_a"], member["qtime"]) for member in members], "a"
        )
        qtime_coeffs = affine_coeffs(
            [(member["src_a"], member["qtime"]) for member in members]
        )
        qsteps_affine = affine_formula(
            [(member["src_a"], member["qsteps"]) for member in members], "a"
        )
        qsteps_coeffs = affine_coeffs(
            [(member["src_a"], member["qsteps"]) for member in members]
        )
        edge_rows.append(
            {
                "src": src,
                "dst": dst,
                "condition": condition_stats(members),
                "target_affine_mod_m": list(target_affine) if target_affine else None,
                "qtime_affine_in_a": qtime_affine,
                "qtime_affine_coeffs": list(qtime_coeffs) if qtime_coeffs else None,
                "qsteps_affine_in_a": qsteps_affine,
                "qsteps_affine_coeffs": list(qsteps_coeffs) if qsteps_coeffs else None,
            }
        )
    return {
        "q": q,
        "m": m,
        "ok": True,
        "edge_count": len(edge_rows),
        "edge_partitions": edge_rows,
    }


def branch_samples(samples: list[dict[str, Any]], parity: int) -> list[dict[str, Any]]:
    return [sample for sample in samples if sample.get("ok") and sample["q"] >= 2 and sample["q"] % 2 == parity]


def summarize_branch(samples: list[dict[str, Any]], parity: int) -> dict[str, Any]:
    selected = branch_samples(samples, parity)
    branch_name = "R42-even-q" if parity == 0 else "R42-odd-q"
    edge_support = sorted(
        {
            (edge["src"], edge["dst"])
            for sample in selected
            for edge in sample["edge_partitions"]
        }
    )
    rows = []
    all_count_affine = True
    all_condition_bounds_affine = True
    all_target_affine_stable = True
    all_target_coeffs_affine = True
    all_qtime_affine = True
    all_qtime_coeffs_affine = True
    all_qsteps_affine = True
    all_qsteps_coeffs_affine = True
    target_coeffs_missing_edges = 0
    qtime_coeffs_missing_edges = 0
    qsteps_coeffs_missing_edges = 0
    target_coeffs_nonaffine_edges = 0
    qtime_coeffs_nonaffine_edges = 0
    qsteps_coeffs_nonaffine_edges = 0
    for src, dst in edge_support:
        per_sample = []
        for sample in selected:
            edge = next(
                edge
                for edge in sample["edge_partitions"]
                if edge["src"] == src and edge["dst"] == dst
            )
            s = sample["q"] // 2 if parity == 0 else (sample["q"] - 1) // 2
            per_sample.append((s, sample, edge))
        count_formula = affine_formula(
            [(s, edge["condition"]["count"]) for s, _, edge in per_sample], "s"
        )
        min_formula = affine_formula(
            [(s, edge["condition"]["min"]) for s, _, edge in per_sample], "s"
        )
        max_formula = affine_formula(
            [(s, edge["condition"]["max"]) for s, _, edge in per_sample], "s"
        )
        interval_count_formula = affine_formula(
            [(s, edge["condition"]["interval_count"]) for s, _, edge in per_sample],
            "s",
        )
        target_coeff_list = [
            (s, edge.get("target_affine_mod_m")) for s, _, edge in per_sample
        ]
        target_values = {
            tuple(coeffs) if coeffs is not None else None
            for _, coeffs in target_coeff_list
        }
        target_missing = sum(1 for _, coeffs in target_coeff_list if coeffs is None)
        if target_missing:
            target_coeffs_missing_edges += 1
            target_alpha_formula = None
            target_beta_formula = None
        else:
            target_alpha_formula = affine_formula(
                [(s, coeffs[0]) for s, coeffs in target_coeff_list if coeffs is not None],
                "s",
            )
            target_beta_formula = affine_formula(
                [(s, coeffs[1]) for s, coeffs in target_coeff_list if coeffs is not None],
                "s",
            )
            if target_alpha_formula is None or target_beta_formula is None:
                target_coeffs_nonaffine_edges += 1
        qtime_values = {edge["qtime_affine_in_a"] for _, _, edge in per_sample}
        qtime_coeff_list = [
            (s, edge.get("qtime_affine_coeffs")) for s, _, edge in per_sample
        ]
        qtime_missing = sum(1 for _, coeffs in qtime_coeff_list if coeffs is None)
        if qtime_missing:
            qtime_coeffs_missing_edges += 1
            qtime_slope_formula = None
            qtime_intercept_formula = None
        else:
            qtime_slope_formula = affine_formula(
                [(s, coeffs[0]) for s, coeffs in qtime_coeff_list if coeffs is not None],
                "s",
            )
            qtime_intercept_formula = affine_formula(
                [(s, coeffs[1]) for s, coeffs in qtime_coeff_list if coeffs is not None],
                "s",
            )
            if qtime_slope_formula is None or qtime_intercept_formula is None:
                qtime_coeffs_nonaffine_edges += 1
        qsteps_values = {edge["qsteps_affine_in_a"] for _, _, edge in per_sample}
        qsteps_coeff_list = [
            (s, edge.get("qsteps_affine_coeffs")) for s, _, edge in per_sample
        ]
        qsteps_missing = sum(1 for _, coeffs in qsteps_coeff_list if coeffs is None)
        if qsteps_missing:
            qsteps_coeffs_missing_edges += 1
            qsteps_slope_formula = None
            qsteps_intercept_formula = None
        else:
            qsteps_slope_formula = affine_formula(
                [(s, coeffs[0]) for s, coeffs in qsteps_coeff_list if coeffs is not None],
                "s",
            )
            qsteps_intercept_formula = affine_formula(
                [(s, coeffs[1]) for s, coeffs in qsteps_coeff_list if coeffs is not None],
                "s",
            )
            if qsteps_slope_formula is None or qsteps_intercept_formula is None:
                qsteps_coeffs_nonaffine_edges += 1
        all_count_affine = all_count_affine and count_formula is not None
        all_condition_bounds_affine = all_condition_bounds_affine and all(
            value is not None
            for value in [min_formula, max_formula, interval_count_formula]
        )
        all_target_affine_stable = (
            all_target_affine_stable and len(target_values) == 1 and None not in target_values
        )
        all_target_coeffs_affine = all_target_coeffs_affine and all(
            value is not None for value in [target_alpha_formula, target_beta_formula]
        )
        all_qtime_affine = all_qtime_affine and len(qtime_values) == 1 and None not in qtime_values
        all_qtime_coeffs_affine = all_qtime_coeffs_affine and all(
            value is not None for value in [qtime_slope_formula, qtime_intercept_formula]
        )
        all_qsteps_affine = (
            all_qsteps_affine and len(qsteps_values) == 1 and None not in qsteps_values
        )
        all_qsteps_coeffs_affine = all_qsteps_coeffs_affine and all(
            value is not None for value in [qsteps_slope_formula, qsteps_intercept_formula]
        )
        rows.append(
            {
                "src": src,
                "dst": dst,
                "count_formula": count_formula,
                "min_formula": min_formula,
                "max_formula": max_formula,
                "interval_count_formula": interval_count_formula,
                "target_affine_mod_m_stable": list(next(iter(target_values)))
                if len(target_values) == 1 and None not in target_values
                else None,
                "target_affine_alpha_formula": target_alpha_formula,
                "target_affine_beta_formula": target_beta_formula,
                "target_affine_coeffs_missing_sample_count": target_missing,
                "qtime_affine_in_a_stable": next(iter(qtime_values))
                if len(qtime_values) == 1 and None not in qtime_values
                else None,
                "qtime_slope_formula": qtime_slope_formula,
                "qtime_intercept_formula": qtime_intercept_formula,
                "qtime_affine_coeffs_missing_sample_count": qtime_missing,
                "qsteps_affine_in_a_stable": next(iter(qsteps_values))
                if len(qsteps_values) == 1 and None not in qsteps_values
                else None,
                "qsteps_slope_formula": qsteps_slope_formula,
                "qsteps_intercept_formula": qsteps_intercept_formula,
                "qsteps_affine_coeffs_missing_sample_count": qsteps_missing,
                "sample_s_values": [s for s, _, _ in per_sample],
            }
        )
    return {
        "name": branch_name,
        "parity": parity,
        "sample_q_values": [sample["q"] for sample in selected],
        "sample_s_values": [
            sample["q"] // 2 if parity == 0 else (sample["q"] - 1) // 2
            for sample in selected
        ],
        "edge_count": len(edge_support),
        "all_count_formulas_affine_in_s": all_count_affine,
        "all_condition_bounds_affine_in_s": all_condition_bounds_affine,
        "all_target_affine_maps_stable": all_target_affine_stable,
        "all_target_affine_coeffs_affine_in_s": all_target_coeffs_affine,
        "all_qtime_affine_maps_stable": all_qtime_affine,
        "all_qtime_affine_coeffs_affine_in_s": all_qtime_coeffs_affine,
        "all_qsteps_affine_maps_stable": all_qsteps_affine,
        "all_qsteps_affine_coeffs_affine_in_s": all_qsteps_coeffs_affine,
        "diagnostic_counts": {
            "target_coeffs_missing_edges": target_coeffs_missing_edges,
            "target_coeffs_nonaffine_edges": target_coeffs_nonaffine_edges,
            "qtime_coeffs_missing_edges": qtime_coeffs_missing_edges,
            "qtime_coeffs_nonaffine_edges": qtime_coeffs_nonaffine_edges,
            "qsteps_coeffs_missing_edges": qsteps_coeffs_missing_edges,
            "qsteps_coeffs_nonaffine_edges": qsteps_coeffs_nonaffine_edges,
        },
        "edge_partition_formulas": rows,
    }


def build_summary(q_values: list[int], binary: Path, compile_binary: bool) -> dict[str, Any]:
    if compile_binary:
        r42.compile_checker(binary)
    with tempfile.TemporaryDirectory(prefix="routeE-r42-edge-partitions-") as tmp:
        samples = [summarize_sample(binary, q, Path(tmp)) for q in q_values]
    branches = [summarize_branch(samples, 0), summarize_branch(samples, 1)]
    sample_overviews = [
        {
            "q": sample.get("q"),
            "m": sample.get("m"),
            "ok": sample.get("ok"),
            "edge_count": len(sample.get("edge_partitions", []))
            if sample.get("ok")
            else None,
            "returncode": sample.get("returncode"),
        }
        for sample in samples
    ]
    return {
        "schema": "routeE_r42_mod96_edge_partitions_v1",
        "branch": "R42",
        "family": "m = 48*q + 42, split by q parity",
        "samples": sample_overviews,
        "generic_subbranches": branches,
        "summary": {
            "q_values": q_values,
            "all_samples_ok": all(sample.get("ok") for sample in samples),
            "all_branch_edge_counts_69": all(
                branch["edge_count"] == 69 for branch in branches
            ),
            "all_count_formulas_affine_in_s": all(
                branch["all_count_formulas_affine_in_s"] for branch in branches
            ),
            "all_condition_bounds_affine_in_s": all(
                branch["all_condition_bounds_affine_in_s"] for branch in branches
            ),
            "all_target_affine_maps_stable": all(
                branch["all_target_affine_maps_stable"] for branch in branches
            ),
            "all_target_affine_coeffs_affine_in_s": all(
                branch["all_target_affine_coeffs_affine_in_s"]
                for branch in branches
            ),
            "all_qtime_affine_maps_stable": all(
                branch["all_qtime_affine_maps_stable"] for branch in branches
            ),
            "all_qtime_affine_coeffs_affine_in_s": all(
                branch["all_qtime_affine_coeffs_affine_in_s"]
                for branch in branches
            ),
            "all_qsteps_affine_maps_stable": all(
                branch["all_qsteps_affine_maps_stable"] for branch in branches
            ),
            "all_qsteps_affine_coeffs_affine_in_s": all(
                branch["all_qsteps_affine_coeffs_affine_in_s"]
                for branch in branches
            ),
        },
        "promotion_impact": {
            "closes_residue": False,
            "pointwise_equations_closed": False,
            "no_early_closed": False,
            "diagnosis": (
                "This records candidate per-edge source-condition and target/time "
                "maps on the two mod-96 R42 subbranches.  It is still sampled "
                "symbolic evidence and does not prove no-early."
            ),
        },
    }


def parse_range(text: str) -> list[int]:
    if ":" in text:
        start, end = [int(part) for part in text.split(":", 1)]
        return list(range(start, end + 1))
    return [int(part) for part in text.split(",") if part]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--q-values", default="2:6")
    parser.add_argument("--binary", type=Path, default=DEFAULT_BIN)
    parser.add_argument("--no-compile", action="store_true")
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    payload = build_summary(parse_range(args.q_values), args.binary, not args.no_compile)
    print("schema", payload["schema"])
    print("all_samples_ok", payload["summary"]["all_samples_ok"])
    print("all_branch_edge_counts_69", payload["summary"]["all_branch_edge_counts_69"])
    print(
        "all_count_formulas_affine_in_s",
        payload["summary"]["all_count_formulas_affine_in_s"],
    )
    print(
        "all_target_affine_maps_stable",
        payload["summary"]["all_target_affine_maps_stable"],
    )
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
