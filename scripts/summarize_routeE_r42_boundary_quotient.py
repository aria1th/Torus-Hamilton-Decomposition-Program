#!/usr/bin/env python3
"""Summarize R42 boundary quotients without preserving raw all-pair CSV.

The R42 affine samples pass the all-pair section check.  This script takes the
next compression step: it dumps the all-pair first-return map to a temporary
CSV, computes the return to the boundary labels {Z,03,04,34}, mines a compact
piecewise-affine block count, and records only summary data.

The output is evidence for symbolic promotion, not a branch proof.
"""

from __future__ import annotations

import argparse
import csv
import json
import subprocess
import tempfile
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any


REPO = Path(__file__).resolve().parents[1]
CPP = REPO / "scripts" / "routeE_allpair_cpp_v1_2.cpp"
BOUNDARY = {"Z", "03", "04", "34"}
BOUNDARY_ORDER = {"Z": 0, "03": 1, "04": 2, "34": 3}
DEFAULT_BIN = Path(tempfile.gettempdir()) / "routeE_allpair_cpp_v1_2"


def compile_checker(binary: Path) -> None:
    subprocess.run(
        ["g++", "-O3", "-std=c++17", str(CPP), "-o", str(binary)],
        cwd=REPO,
        check=True,
    )


def parse_range(text: str) -> list[int]:
    if ":" not in text:
        return [int(part) for part in text.split(",") if part.strip()]
    parts = [int(part) for part in text.split(":")]
    if len(parts) == 2:
        start, stop = parts
        step = 1
    elif len(parts) == 3:
        start, stop, step = parts
    else:
        raise ValueError("range syntax is start:stop[:step]")
    return list(range(start, stop + 1, step))


def load_rows(path: Path) -> list[dict[str, Any]]:
    rows = []
    with path.open() as handle:
        for row in csv.DictReader(handle):
            rows.append(
                {
                    key: int(value)
                    if key in {
                        "idx",
                        "src_a",
                        "dst_idx",
                        "dst_a",
                        "time",
                        "events",
                    }
                    else value
                    for key, value in row.items()
                }
            )
    return rows


def boundary_return_rows(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    by_idx = {row["idx"]: row for row in rows}
    out = []
    for row in rows:
        if row["src_label"] not in BOUNDARY:
            continue
        cur = row["idx"]
        total_time = 0
        qsteps = 0
        path = []
        while True:
            rr = by_idx[cur]
            total_time += rr["time"]
            qsteps += 1
            path.append(rr["src_label"])
            cur = rr["dst_idx"]
            if by_idx[cur]["src_label"] in BOUNDARY:
                dst = by_idx[cur]
                out.append(
                    {
                        "src_label": row["src_label"],
                        "src_a": row["src_a"],
                        "dst_label": dst["src_label"],
                        "dst_a": dst["src_a"],
                        "qtime": total_time,
                        "qsteps": qsteps,
                        "path": ">".join(path),
                    }
                )
                break
            if qsteps > len(rows) + 5:
                raise RuntimeError("no boundary return")
    return sorted(
        out, key=lambda item: (BOUNDARY_ORDER[item["src_label"]], item["src_a"])
    )


def cycle_lengths(rows: list[dict[str, Any]]) -> list[int]:
    nxt = {
        (row["src_label"], row["src_a"]): (row["dst_label"], row["dst_a"])
        for row in rows
    }
    seen: set[tuple[str, int]] = set()
    lengths = []
    for start in nxt:
        if start in seen:
            continue
        cur = start
        count = 0
        while cur not in seen:
            seen.add(cur)
            count += 1
            cur = nxt[cur]
        lengths.append(count)
    return sorted(lengths, reverse=True)


def affine_mod(points: list[tuple[int, int]], m: int) -> tuple[int, int] | None:
    if not points:
        return None
    a0, b0 = points[0]
    for alpha in range(m):
        beta = (b0 - alpha * a0) % m
        if all((alpha * a + beta) % m == b % m for a, b in points):
            return alpha, beta
    return None


def terminal(group: list[dict[str, Any]], m: int) -> tuple[str, tuple[int, int]] | None:
    if not group or len({row["dst_label"] for row in group}) != 1:
        return None
    affine = affine_mod([(row["src_a"], row["dst_a"]) for row in group], m)
    if affine is None:
        return None
    return group[0]["dst_label"], affine


def split_blocks(group: list[dict[str, Any]], m: int) -> int:
    if terminal(group, m) is not None:
        return 1
    for modulus in [2, 3, 4, 5, 6, 8, 10, 12, 16, 24, 32]:
        classes: dict[int, list[dict[str, Any]]] = defaultdict(list)
        for row in group:
            classes[row["src_a"] % modulus].append(row)
        if len(classes) <= 1:
            continue
        if all(terminal(rows, m) is not None for rows in classes.values()):
            return len(classes)
    blocks = 0
    run: list[dict[str, Any]] = []
    for row in sorted(group, key=lambda item: item["src_a"]):
        candidate = run + [row]
        if not run or terminal(candidate, m) is not None:
            run = candidate
        else:
            blocks += 1 if terminal(run, m) is not None else len(run)
            run = [row]
    if run:
        blocks += 1 if terminal(run, m) is not None else len(run)
    return blocks


def block_counts(rows: list[dict[str, Any]], m: int) -> dict[str, int]:
    counts: Counter[str] = Counter()
    for src_label in ["Z", "03", "04", "34"]:
        sub = [row for row in rows if row["src_label"] == src_label]
        if src_label == "Z":
            counts[src_label] += split_blocks(sub, m)
            continue
        groups: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)
        for row in sub:
            groups[(row["dst_label"], row["path"])].append(row)
        for group in groups.values():
            counts[src_label] += split_blocks(group, m)
    return dict(counts)


def transition_counts(rows: list[dict[str, Any]]) -> dict[str, dict[str, int]]:
    counts: dict[str, Counter[str]] = {
        label: Counter() for label in ["Z", "03", "04", "34"]
    }
    for row in rows:
        counts[row["src_label"]][row["dst_label"]] += 1
    return {
        src: {dst: counts[src][dst] for dst in ["Z", "03", "04", "34"]}
        for src in ["Z", "03", "04", "34"]
    }


def affine_formula(points: list[tuple[int, int]]) -> str | None:
    if not points:
        return None
    if len(points) == 1:
        return str(points[0][1])
    q0, v0 = points[0]
    q1, v1 = points[1]
    den = q1 - q0
    num = v1 - v0
    if den == 0 or num % den != 0:
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


def transition_count_fits(samples: list[dict[str, Any]]) -> dict[str, dict[str, str | None]]:
    generic = [sample for sample in samples if sample.get("q", 0) >= 1]
    fits: dict[str, dict[str, str | None]] = {}
    for src in ["Z", "03", "04", "34"]:
        fits[src] = {}
        for dst in ["Z", "03", "04", "34"]:
            points = [
                (
                    int(sample["q"]),
                    int(sample["boundary_transition_counts"][src][dst]),
                )
                for sample in generic
            ]
            fits[src][dst] = affine_formula(points)
    return fits


def summarize_sample(binary: Path, q: int, workdir: Path) -> dict[str, Any]:
    m = 48 * q + 42
    x = 6 * q + 5
    z = x
    cap = max(10_000, 10 * m * m)
    csv_path = workdir / f"r42_q{q}.csv"
    proc = subprocess.run(
        [str(binary), "dump-csv", str(m), str(x), str(z), str(cap), str(csv_path)],
        cwd=REPO,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if proc.returncode != 0:
        return {
            "q": q,
            "m": m,
            "x": x,
            "z": z,
            "cap_events": cap,
            "returncode": proc.returncode,
            "stderr_tail": proc.stderr.strip().splitlines()[-5:],
            "ok": False,
        }
    rows = load_rows(csv_path)
    boundary = boundary_return_rows(rows)
    lengths = cycle_lengths(boundary)
    by_label = block_counts(boundary, m)
    block_count = sum(by_label.values())
    transitions = transition_counts(boundary)
    return {
        "q": q,
        "m": m,
        "x": x,
        "z": z,
        "cap_events": cap,
        "allpair_nodes": len(rows),
        "boundary_nodes": len(boundary),
        "boundary_nodes_formula_ok": len(boundary) == 3 * m - 2,
        "boundary_cycle_lengths": lengths,
        "boundary_single_cycle": lengths == [len(boundary)],
        "block_count": block_count,
        "block_count_by_label": by_label,
        "boundary_transition_counts": transitions,
        "returncode": proc.returncode,
        "stderr_tail": proc.stderr.strip().splitlines()[-3:],
        "ok": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--q-values", default="0:4")
    parser.add_argument("--binary", type=Path, default=DEFAULT_BIN)
    parser.add_argument("--no-compile", action="store_true")
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    if not args.no_compile:
        compile_checker(args.binary)

    q_values = parse_range(args.q_values)
    with tempfile.TemporaryDirectory(prefix="routeE-r42-boundary-") as tmp:
        samples = [summarize_sample(args.binary, q, Path(tmp)) for q in q_values]

    generic = [sample for sample in samples if sample.get("q", 0) >= 1]
    stable_counts = len({json.dumps(s.get("block_count_by_label"), sort_keys=True) for s in generic}) == 1
    stable_block_count = len({s.get("block_count") for s in generic}) == 1
    payload = {
        "schema": "routeE_r42_boundary_quotient_summary_v1",
        "branch": "R42",
        "status": "boundary_summary_not_symbolic_proof",
        "family": "m = 48*q + 42, x = z = 6*q + 5",
        "source_checker": str(CPP.relative_to(REPO)),
        "raw_csv_preserved": False,
        "samples": samples,
        "q_ge_1_stability": {
            "sample_q_values": [sample.get("q") for sample in generic],
            "stable_block_count": stable_block_count,
            "stable_block_count_by_label": stable_counts,
            "all_boundary_single_cycle": all(
                sample.get("boundary_single_cycle") for sample in generic
            ),
            "all_boundary_nodes_formula_ok": all(
                sample.get("boundary_nodes_formula_ok") for sample in generic
            ),
            "block_count": generic[0].get("block_count") if generic else None,
            "block_count_by_label": generic[0].get("block_count_by_label")
            if generic
            else None,
        },
        "q_ge_1_transition_count_fits": transition_count_fits(samples),
        "interpretation": (
            "The boundary quotient is a single cycle for the checked R42 "
            "samples and has stable block counts for q>=1.  This is a "
            "symbolic-promotion guide, not a proof of the R42 residue."
        ),
    }
    text = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    print(text, end="")
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(text)

    if not all(sample.get("ok") for sample in samples):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
