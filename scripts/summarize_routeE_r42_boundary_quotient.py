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


def condition_summary(group: list[dict[str, Any]]) -> dict[str, Any]:
    values = sorted(row["src_a"] for row in group)
    if not values:
        return {"count": 0}
    intervals = []
    start = prev = values[0]
    for value in values[1:]:
        if value == prev + 1:
            prev = value
            continue
        intervals.append([start, prev])
        start = prev = value
    intervals.append([start, prev])

    out: dict[str, Any] = {
        "count": len(values),
        "min": values[0],
        "max": values[-1],
    }
    if len(intervals) <= 8:
        out["intervals"] = intervals
    else:
        out["interval_count"] = len(intervals)
        out["first_intervals"] = intervals[:4]
        out["last_intervals"] = intervals[-3:]

    hints = []
    for modulus in [2, 3, 4, 5, 6, 8, 10, 12, 16, 24, 32]:
        residues = sorted({value % modulus for value in values})
        if len(residues) <= 4:
            hints.append({"mod": modulus, "residues": residues})
    if hints:
        out["residue_hints"] = hints[:6]
    return out


def terminal_dict(group: list[dict[str, Any]], m: int) -> dict[str, Any] | None:
    result = terminal(group, m)
    if result is None:
        return None
    dst_label, affine = result
    return {"dst_label": dst_label, "affine_mod": list(affine)}


def block_detail(group: list[dict[str, Any]], m: int, extra: dict[str, Any]) -> list[dict[str, Any]]:
    term = terminal_dict(group, m)
    if term is not None:
        return [{"condition": condition_summary(group), "terminal": term, **extra}]

    for modulus in [2, 3, 4, 5, 6, 8, 10, 12, 16, 24, 32]:
        classes: dict[int, list[dict[str, Any]]] = defaultdict(list)
        for row in group:
            classes[row["src_a"] % modulus].append(row)
        if len(classes) <= 1:
            continue
        if all(terminal(rows, m) is not None for rows in classes.values()):
            out = []
            for residue, rows in sorted(classes.items()):
                condition = condition_summary(rows)
                condition["mod"] = modulus
                condition["residue"] = residue
                out.append({"condition": condition, "terminal": terminal_dict(rows, m), **extra})
            return out

    out = []
    run: list[dict[str, Any]] = []

    def flush(rows: list[dict[str, Any]]) -> None:
        if not rows:
            return
        term = terminal_dict(rows, m)
        if term is not None:
            out.append({"condition": condition_summary(rows), "terminal": term, **extra})
        else:
            for row in rows:
                out.append(
                    {
                        "condition": condition_summary([row]),
                        "terminal": terminal_dict([row], m),
                        "fallback": "singleton",
                        **extra,
                    }
                )

    for row in sorted(group, key=lambda item: item["src_a"]):
        candidate = run + [row]
        if not run or terminal(candidate, m) is not None:
            run = candidate
        else:
            flush(run)
            run = [row]
    flush(run)
    return out


def block_table(rows: list[dict[str, Any]], m: int) -> list[dict[str, Any]]:
    table = []
    for src_label in ["Z", "03", "04", "34"]:
        sub = [row for row in rows if row["src_label"] == src_label]
        if src_label == "Z":
            table.extend(block_detail(sub, m, {"src_label": src_label, "path": "Z"}))
            continue
        groups: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)
        for row in sub:
            groups[(row["dst_label"], row["path"])].append(row)
        for (dst_label, path), group in sorted(
            groups.items(), key=lambda item: (BOUNDARY_ORDER[item[0][0]], item[0][1])
        ):
            table.extend(
                block_detail(
                    group,
                    m,
                    {"src_label": src_label, "dst_label_group": dst_label, "path": path},
                )
            )
    return table


def condition_shape(condition: dict[str, Any]) -> dict[str, Any]:
    shape = {"count": condition.get("count")}
    if "mod" in condition:
        shape["mod"] = condition.get("mod")
        shape["residue"] = condition.get("residue")
    if "interval_count" in condition:
        shape["interval_count"] = condition.get("interval_count")
    elif "intervals" in condition:
        shape["intervals_len"] = len(condition.get("intervals", []))
    return shape


def block_signature(blocks: list[dict[str, Any]] | None) -> list[dict[str, Any]] | None:
    if blocks is None:
        return None
    out = []
    for block in blocks:
        terminal = block.get("terminal") or {}
        out.append(
            {
                "src_label": block.get("src_label"),
                "dst_label_group": block.get("dst_label_group"),
                "path": block.get("path"),
                "fallback": block.get("fallback"),
                "terminal_dst_label": terminal.get("dst_label"),
                "condition_shape": condition_shape(block.get("condition", {})),
            }
        )
    return out


def structural_block_key(block: dict[str, Any]) -> dict[str, Any]:
    terminal = block.get("terminal") or {}
    condition = block.get("condition") or {}
    return {
        "src_label": block.get("src_label"),
        "dst_label_group": block.get("dst_label_group"),
        "path_shape": path_shape(block.get("path")),
        "fallback": block.get("fallback"),
        "terminal_dst_label": terminal.get("dst_label"),
        "condition_mod": condition.get("mod"),
        "condition_residue": condition.get("residue"),
    }


def compressed_path(path: str | None) -> list[dict[str, Any]]:
    if not path:
        return []
    labels = path.split(">")
    runs = []
    cur = labels[0]
    count = 1
    for label in labels[1:]:
        if label == cur:
            count += 1
        else:
            runs.append({"label": cur, "count": count})
            cur = label
            count = 1
    runs.append({"label": cur, "count": count})
    return runs


def path_shape(path: str | None) -> list[str]:
    return [run["label"] for run in compressed_path(path)]


def fit_path_runs(blocks_by_q: dict[int, list[dict[str, Any]]], index: int) -> list[dict[str, Any]]:
    by_q = {
        q: compressed_path(blocks[index].get("path"))
        for q, blocks in sorted(blocks_by_q.items())
    }
    if not by_q:
        return []
    shapes = [[run["label"] for run in runs] for runs in by_q.values()]
    if any(shape != shapes[0] for shape in shapes[1:]):
        return []
    out = []
    for run_index, label in enumerate(shapes[0]):
        points = [(q, runs[run_index]["count"]) for q, runs in by_q.items()]
        out.append({"label": label, "count": affine_formula(points)})
    return out


def fit_field(
    blocks_by_q: dict[int, list[dict[str, Any]]],
    index: int,
    path: list[Any],
    min_q: int = 1,
) -> str | None:
    points = []
    for q, blocks in sorted(blocks_by_q.items()):
        if q < min_q:
            continue
        value: Any = blocks[index]
        for key in path:
            if value is None:
                return None
            if isinstance(value, dict):
                value = value.get(key)
            elif isinstance(value, list) and isinstance(key, int) and 0 <= key < len(value):
                value = value[key]
            else:
                return None
        if not isinstance(value, int):
            return None
        points.append((q, value))
    return affine_formula(points)


def tail_formula_fields(
    blocks_by_q: dict[int, list[dict[str, Any]]],
    index: int,
    path: list[Any],
    field: str,
) -> dict[str, str]:
    q_values = sorted(blocks_by_q)
    out: dict[str, str] = {}
    for min_q in q_values:
        if min_q < 2:
            continue
        points = []
        ok = True
        for q in q_values:
            if q < min_q:
                continue
            value: Any = blocks_by_q[q][index]
            for key in path:
                if value is None:
                    ok = False
                    break
                if isinstance(value, dict):
                    value = value.get(key)
                elif isinstance(value, list) and isinstance(key, int) and 0 <= key < len(value):
                    value = value[key]
                else:
                    ok = False
                    break
            if not ok or not isinstance(value, int):
                ok = False
                break
            points.append((q, value))
        if ok and len(points) >= 2:
            formula = affine_formula(points)
            if formula is not None:
                out[f"{field}_q_ge_{min_q}"] = formula
                break
    return out


def q_ge_1_block_formula_fits(blocks_by_q: dict[int, list[dict[str, Any]]]) -> dict[str, Any]:
    if not blocks_by_q:
        return {"stable_structural_keys": False, "blocks": []}
    key_lists = [
        [structural_block_key(block) for block in blocks]
        for _, blocks in sorted(blocks_by_q.items())
    ]
    stable_keys = all(keys == key_lists[0] for keys in key_lists[1:])
    out = []
    if stable_keys:
        for index, key in enumerate(key_lists[0]):
            alpha = fit_field(blocks_by_q, index, ["terminal", "affine_mod", 0])
            beta = fit_field(blocks_by_q, index, ["terminal", "affine_mod", 1])
            condition_interval_count = fit_field(
                blocks_by_q, index, ["condition", "interval_count"]
            )
            block = {
                "index": index,
                "key": key,
                "condition_count": fit_field(blocks_by_q, index, ["condition", "count"]),
                "condition_min": fit_field(blocks_by_q, index, ["condition", "min"]),
                "condition_max": fit_field(blocks_by_q, index, ["condition", "max"]),
                "condition_interval_count": condition_interval_count,
                "path_run_counts": fit_path_runs(blocks_by_q, index),
                "terminal_affine_alpha": alpha,
                "terminal_affine_beta": beta,
                "terminal_affine_alpha_q_ge_2": None
                if alpha is not None
                else fit_field(
                    blocks_by_q, index, ["terminal", "affine_mod", 0], min_q=2
                ),
                "terminal_affine_beta_q_ge_2": None
                if beta is not None
                else fit_field(
                    blocks_by_q, index, ["terminal", "affine_mod", 1], min_q=2
                ),
            }
            if condition_interval_count is None:
                block.update(
                    tail_formula_fields(
                        blocks_by_q,
                        index,
                        ["condition", "interval_count"],
                        "condition_interval_count",
                    )
                )
            out.append(block)
    return {
        "stable_structural_keys": stable_keys,
        "q_values": sorted(blocks_by_q),
        "block_count": len(key_lists[0]) if key_lists else 0,
        "blocks": out,
    }


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
    blocks = block_table(boundary, m) if q >= 1 else None
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
        "block_signature": block_signature(blocks) if blocks is not None else None,
        "representative_block_table": blocks if q == 1 else None,
        "_block_table_for_fit": blocks,
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
    representative_q1_block_table = next(
        (
            sample.pop("representative_block_table")
            for sample in samples
            if sample.get("q") == 1
        ),
        None,
    )
    for sample in samples:
        sample.pop("representative_block_table", None)
    blocks_by_q = {
        int(sample["q"]): sample["_block_table_for_fit"]
        for sample in samples
        if sample.get("q", 0) >= 1 and sample.get("_block_table_for_fit") is not None
    }
    block_formula_fits = q_ge_1_block_formula_fits(blocks_by_q)
    for sample in samples:
        sample.pop("_block_table_for_fit", None)

    generic = [sample for sample in samples if sample.get("q", 0) >= 1]
    stable_counts = len({json.dumps(s.get("block_count_by_label"), sort_keys=True) for s in generic}) == 1
    stable_block_count = len({s.get("block_count") for s in generic}) == 1
    stable_block_signature = (
        len({json.dumps(s.get("block_signature"), sort_keys=True) for s in generic})
        == 1
    )
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
            "stable_block_signature": stable_block_signature,
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
        "q_ge_1_block_formula_fits": block_formula_fits,
        "representative_q1_block_table": representative_q1_block_table,
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
