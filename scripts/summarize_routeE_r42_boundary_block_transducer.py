#!/usr/bin/env python3
"""Summarize the R42 boundary quotient as a 29-block transducer.

The R42 boundary quotient summary already records 29 run-normalized boundary
blocks and aggregate transition counts.  This diagnostic regenerates finite
witnesses and records the finer block-to-block transition support induced by
those 29 blocks.

This is not a proof of the R42 residue.  It is a proof-planning artifact:
it checks whether the boundary/transducer route has a stable finite block graph
worth promoting into symbolic pointwise/no-early formulas.
"""

from __future__ import annotations

import argparse
import json
import tempfile
from collections import Counter
from fractions import Fraction
from pathlib import Path
from typing import Any

import summarize_routeE_r42_boundary_quotient as r42


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_BIN = Path(tempfile.gettempdir()) / "routeE_allpair_cpp_v1_2"
BOUNDARY_LABELS = ["Z", "03", "04", "34"]


def affine_formula(points: list[tuple[int, int]]) -> str | None:
    if not points:
        return None
    if len(points) == 1:
        return str(points[0][1])
    q0, v0 = points[0]
    q1, v1 = points[1]
    if q1 == q0:
        return None
    num = v1 - v0
    den = q1 - q0
    if num % den:
        return None
    slope = num // den
    intercept = v0 - slope * q0
    if any(slope * q + intercept != value for q, value in points):
        return None
    if slope == 0:
        return str(intercept)
    if intercept == 0:
        return f"{slope}*q"
    sign = "+" if intercept > 0 else "-"
    return f"{slope}*q {sign} {abs(intercept)}"


def rational_formula_text(slope: Fraction, intercept: Fraction) -> str:
    def coeff_text(value: Fraction) -> str:
        if value.denominator == 1:
            return str(value.numerator)
        return f"{value.numerator}/{value.denominator}"

    if slope == 0:
        return coeff_text(intercept)
    q_term = "q" if slope == 1 else f"{coeff_text(slope)}*q"
    if intercept == 0:
        return q_term
    sign = "+" if intercept > 0 else "-"
    return f"{q_term} {sign} {coeff_text(abs(intercept))}"


def rational_affine_fit(points: list[tuple[int, int]]) -> dict[str, Any] | None:
    if not points:
        return None
    if len(points) == 1:
        return {
            "slope": "0",
            "intercept": str(points[0][1]),
            "formula": str(points[0][1]),
        }
    q0, v0 = points[0]
    q1, v1 = points[1]
    if q1 == q0:
        return None
    slope = Fraction(v1 - v0, q1 - q0)
    intercept = Fraction(v0) - slope * q0
    if any(slope * q + intercept != value for q, value in points):
        return None
    return {
        "slope": str(slope),
        "intercept": str(intercept),
        "formula": rational_formula_text(slope, intercept),
    }


def piecewise_formula(points: list[tuple[int, int]]) -> dict[str, Any]:
    formula = affine_formula(points)
    if formula is not None:
        fit = rational_affine_fit(points)
        return {"kind": "affine", **(fit or {"formula": formula})}
    for modulus in [2, 3, 4]:
        residues: dict[int, list[tuple[int, int]]] = {}
        for q, value in points:
            residues.setdefault(q % modulus, []).append((q, value))
        fits = {
            residue: rational_affine_fit(part)
            for residue, part in sorted(residues.items())
        }
        if all(fit is not None for fit in fits.values()):
            return {
                "kind": "residue_affine",
                "modulus": modulus,
                "residue_formulas": {
                    str(residue): fit for residue, fit in fits.items()
                },
            }
    return {"kind": "unfit", "formula": None}


def block_rows(rows: list[dict[str, Any]], m: int) -> list[dict[str, Any]]:
    """Return the same block order as r42.block_table, retaining memberships."""

    out: list[dict[str, Any]] = []

    def append_block(group: list[dict[str, Any]], extra: dict[str, Any]) -> None:
        details = r42.block_detail(group, m, extra)
        if len(details) == 1:
            row = dict(details[0])
            row["_members"] = [
                {
                    "src_label": item["src_label"],
                    "src_a": item["src_a"],
                    "dst_label": item["dst_label"],
                    "dst_a": item["dst_a"],
                    "path": item["path"],
                }
                for item in group
            ]
            out.append(row)
            return

        unused = list(group)
        for detail in details:
            members: list[dict[str, Any]] = []
            for item in list(unused):
                if not condition_contains(detail.get("condition", {}), item["src_a"]):
                    continue
                terminal = detail.get("terminal") or {}
                if terminal.get("dst_label") != item["dst_label"]:
                    continue
                members.append(item)
                unused.remove(item)
            row = dict(detail)
            row["_members"] = [
                {
                    "src_label": item["src_label"],
                    "src_a": item["src_a"],
                    "dst_label": item["dst_label"],
                    "dst_a": item["dst_a"],
                    "path": item["path"],
                }
                for item in members
            ]
            out.append(row)
        if unused:
            raise RuntimeError(f"unassigned block members: {unused[:3]}")

    for src_label in BOUNDARY_LABELS:
        sub = [row for row in rows if row["src_label"] == src_label]
        if src_label == "Z":
            groups: dict[str, list[dict[str, Any]]] = {}
            for row in sub:
                groups.setdefault(row["path"], []).append(row)
            for path, group in sorted(groups.items()):
                append_block(group, {"src_label": src_label, "path": path})
            continue
        groups: dict[tuple[str, str], list[dict[str, Any]]] = {}
        for row in sub:
            groups.setdefault((row["dst_label"], row["path"]), []).append(row)
        for (dst_label, path), group in sorted(
            groups.items(), key=lambda item: (r42.BOUNDARY_ORDER[item[0][0]], item[0][1])
        ):
            append_block(
                group,
                {"src_label": src_label, "dst_label_group": dst_label, "path": path},
            )
    return out


def condition_contains(condition: dict[str, Any], value: int) -> bool:
    if "mod" in condition and value % int(condition["mod"]) != int(condition["residue"]):
        return False
    if "intervals" in condition:
        return any(lo <= value <= hi for lo, hi in condition["intervals"])
    if "first_intervals" in condition or "last_intervals" in condition:
        intervals = list(condition.get("first_intervals", [])) + list(
            condition.get("last_intervals", [])
        )
        if any(lo <= value <= hi for lo, hi in intervals):
            return True
        return int(condition["min"]) <= value <= int(condition["max"])
    return int(condition.get("min", value)) <= value <= int(condition.get("max", value))


def reachable(edges: set[tuple[int, int]], start: int, reverse: bool = False) -> set[int]:
    graph: dict[int, set[int]] = {}
    for src, dst in edges:
        a, b = (dst, src) if reverse else (src, dst)
        graph.setdefault(a, set()).add(b)
        graph.setdefault(b, set())
    seen = {start}
    stack = [start]
    while stack:
        src = stack.pop()
        for dst in graph.get(src, set()):
            if dst not in seen:
                seen.add(dst)
                stack.append(dst)
    return seen


def strongly_connected(edges: set[tuple[int, int]], n: int) -> bool:
    if not edges or n == 0:
        return False
    return reachable(edges, 0) == set(range(n)) and reachable(edges, 0, True) == set(
        range(n)
    )


def summarize_sample(binary: Path, q: int, workdir: Path) -> dict[str, Any]:
    m = 48 * q + 42
    x = 6 * q + 5
    z = x
    cap = max(10_000, 10 * m * m)
    csv_path = workdir / f"r42_block_transducer_q{q}.csv"
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
    blocks = block_rows(boundary, m)
    by_node: dict[tuple[str, int], int] = {}
    assignment_ok = True
    for index, block in enumerate(blocks):
        for member in block["_members"]:
            key = (member["src_label"], member["src_a"])
            if key in by_node:
                assignment_ok = False
            by_node[key] = index
    edge_counts: Counter[tuple[int, int]] = Counter()
    for index, block in enumerate(blocks):
        for member in block["_members"]:
            target = (member["dst_label"], member["dst_a"])
            if target not in by_node:
                assignment_ok = False
                continue
            edge_counts[(index, by_node[target])] += 1
    target_sets = {
        index: sorted({dst for (src, dst), count in edge_counts.items() if src == index and count})
        for index in range(len(blocks))
    }
    target_hist = Counter(len(targets) for targets in target_sets.values())
    support = set(edge_counts)
    return {
        "q": q,
        "m": m,
        "ok": True,
        "block_count": len(blocks),
        "boundary_nodes": len(boundary),
        "boundary_single_cycle": r42.cycle_lengths(boundary) == [len(boundary)],
        "assignment_ok": assignment_ok and len(by_node) == len(boundary),
        "edge_count": len(edge_counts),
        "max_targets_per_block": max((len(targets) for targets in target_sets.values()), default=0),
        "target_histogram": {str(key): value for key, value in sorted(target_hist.items())},
        "split_blocks": [
            {"block": index, "targets": targets}
            for index, targets in target_sets.items()
            if len(targets) > 1
        ],
        "edge_counts": [
            {"src": src, "dst": dst, "count": count}
            for (src, dst), count in sorted(edge_counts.items())
        ],
        "support_strongly_connected": strongly_connected(support, len(blocks)),
        "stderr_tail": proc.stderr.strip().splitlines()[-3:],
    }


def build_summary(
    q_values: list[int],
    binary: Path,
    compile_binary: bool,
) -> dict[str, Any]:
    if compile_binary:
        r42.compile_checker(binary)
    with tempfile.TemporaryDirectory(prefix="routeE-r42-block-transducer-") as tmp:
        samples = [summarize_sample(binary, q, Path(tmp)) for q in q_values]
    generic = [sample for sample in samples if sample.get("ok") and sample["q"] >= 2]
    supports = [
        {(edge["src"], edge["dst"]) for edge in sample["edge_counts"]}
        for sample in generic
    ]
    stable_support = bool(supports) and all(support == supports[0] for support in supports)
    support = sorted(supports[0]) if stable_support else sorted(set().union(*supports))
    edge_count_fits = []
    for src, dst in support:
        points = []
        for sample in generic:
            counts = {
                (edge["src"], edge["dst"]): edge["count"]
                for edge in sample["edge_counts"]
            }
            points.append((sample["q"], counts.get((src, dst), 0)))
        edge_count_fits.append(
            {
                "src": src,
                "dst": dst,
                "formula": affine_formula(points),
                "piecewise_formula": piecewise_formula(points),
                "sample_points": points,
            }
        )
    q1 = next((sample for sample in samples if sample.get("q") == 1), None)
    q_ge_2_support = set(support)
    q1_support = (
        {(edge["src"], edge["dst"]) for edge in q1["edge_counts"]}
        if q1 is not None and q1.get("ok")
        else set()
    )
    return {
        "schema": "routeE_r42_boundary_block_transducer_v1",
        "branch": "R42",
        "family": "m = 48*q + 42, x = z = 6*q + 5",
        "source_checker": str(r42.CPP.relative_to(ROOT)),
        "samples": samples,
        "summary": {
            "q_values": q_values,
            "all_samples_ok": all(sample.get("ok") for sample in samples),
            "all_assignments_ok": all(sample.get("assignment_ok") for sample in samples),
            "all_boundary_single_cycle": all(
                sample.get("boundary_single_cycle") for sample in samples
            ),
            "q_ge_2_support_stable": stable_support,
            "q_ge_2_edge_count": len(support),
            "q_ge_2_support_strongly_connected": strongly_connected(
                q_ge_2_support, 29
            ),
            "q1_edge_count": len(q1_support),
            "q1_missing_q_ge_2_edges": [
                {"src": src, "dst": dst} for src, dst in sorted(q_ge_2_support - q1_support)
            ],
            "q1_extra_edges": [
                {"src": src, "dst": dst} for src, dst in sorted(q1_support - q_ge_2_support)
            ],
            "max_targets_per_block_q_ge_2": max(
                (sample.get("max_targets_per_block", 0) for sample in generic),
                default=0,
            ),
            "split_block_count_q_ge_2": max(
                (len(sample.get("split_blocks", [])) for sample in generic),
                default=0,
            ),
            "edge_count_fits_all_affine": all(
                row.get("formula") is not None for row in edge_count_fits
            ),
            "edge_count_fits_all_piecewise_affine": all(
                row.get("piecewise_formula", {}).get("kind") != "unfit"
                for row in edge_count_fits
            ),
            "edge_count_piecewise_moduli": sorted(
                {
                    row.get("piecewise_formula", {}).get("modulus")
                    for row in edge_count_fits
                    if row.get("piecewise_formula", {}).get("kind")
                    == "residue_affine"
                }
            ),
        },
        "q_ge_2_edge_count_fits": edge_count_fits,
        "promotion_impact": {
            "supports_boundary_transducer_route": True,
            "pointwise_equations_closed": False,
            "no_early_closed": False,
            "diagnosis": (
                "The 29-block boundary graph has stable q>=2 support, but many "
                "blocks split across several target blocks.  This is a finite "
                "transducer skeleton, not a pointwise/no-early proof."
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
    parser.add_argument("--q-values", default="1:6")
    parser.add_argument("--binary", type=Path, default=DEFAULT_BIN)
    parser.add_argument("--no-compile", action="store_true")
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    payload = build_summary(parse_range(args.q_values), args.binary, not args.no_compile)
    print("schema", payload["schema"])
    print("all_samples_ok", payload["summary"]["all_samples_ok"])
    print("q_ge_2_support_stable", payload["summary"]["q_ge_2_support_stable"])
    print("q_ge_2_edge_count", payload["summary"]["q_ge_2_edge_count"])
    print("edge_count_fits_all_affine", payload["summary"]["edge_count_fits_all_affine"])
    print(
        "edge_count_fits_all_piecewise_affine",
        payload["summary"]["edge_count_fits_all_piecewise_affine"],
    )
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
