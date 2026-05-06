#!/usr/bin/env python3
"""Mine naive pointwise laws for the R42 all-pair first-return map.

This script is intentionally diagnostic.  The existing R42 artifacts verify
aggregate time and transition polynomial fits.  Promotion to a branch theorem
still needs pointwise first-return equations and no-early/minimality proofs.

The most direct first attempt is to partition each source label fiber by the
source parameter `a` into consecutive intervals on which

  dst_label, dst_a, time, events

are affine functions of `a`.  If this partition is small and stable, it is a
candidate formula table.  If it is large, the artifact records that a stronger
trace-level grammar is needed.
"""

from __future__ import annotations

import argparse
import json
import tempfile
from pathlib import Path
from typing import Any

import summarize_routeE_r42_boundary_quotient as r42
from summarize_routeE_r42_allpair_time_fits import (
    LABELS,
    cycle_lengths,
    fit_polynomial,
    parse_range,
)


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_BIN = Path(tempfile.gettempdir()) / "routeE_allpair_cpp_v1_2"
FIELDS = ["dst_a", "time", "events"]
GLOBAL_FIELDS = ["dst_idx", "time", "events"]
RESIDUE_MODULI = [2, 3, 4, 5, 6, 8, 10, 12, 16, 24, 32, 48]


def is_affine_on_a(rows: list[dict[str, Any]], field: str) -> bool:
    if len(rows) <= 2:
        return True
    differences = [
        rows[i + 1][field] - rows[i][field]
        for i in range(len(rows) - 1)
    ]
    return len(set(differences)) == 1


def is_affine_on_sparse_a(rows: list[dict[str, Any]], field: str) -> bool:
    if len(rows) <= 2:
        return True
    ordered = sorted(rows, key=lambda row: row["src_a"])
    a0 = ordered[0]["src_a"]
    v0 = ordered[0][field]
    a1 = ordered[1]["src_a"]
    v1 = ordered[1][field]
    da0 = a1 - a0
    dv0 = v1 - v0
    for row in ordered[2:]:
        da = row["src_a"] - a0
        dv = row[field] - v0
        if dv * da0 != dv0 * da:
            return False
    return True


def affine_formula(
    rows: list[dict[str, Any]],
    field: str,
    variable: str = "src_a",
) -> dict[str, Any]:
    if len(rows) == 1:
        return {
            "kind": "constant_singleton",
            "value": rows[0][field],
            "formula": str(rows[0][field]),
        }
    slope = rows[1][field] - rows[0][field]
    intercept = rows[0][field] - slope * rows[0][variable]
    if slope == 0:
        text = str(intercept)
    elif intercept == 0:
        text = f"{slope}*{variable}"
    elif intercept > 0:
        text = f"{slope}*{variable} + {intercept}"
    else:
        text = f"{slope}*{variable} - {-intercept}"
    return {
        "kind": f"affine_in_{variable}",
        "slope": slope,
        "intercept": intercept,
        "formula": text,
    }


def partition_label(rows: list[dict[str, Any]]) -> list[list[dict[str, Any]]]:
    ordered = sorted(rows, key=lambda row: row["src_a"])
    blocks: list[list[dict[str, Any]]] = []
    current: list[dict[str, Any]] = []
    for row in ordered:
        candidate = current + [row]
        ok = True
        if current and row["src_a"] != current[-1]["src_a"] + 1:
            ok = False
        if len({item["dst_label"] for item in candidate}) > 1:
            ok = False
        for field in FIELDS:
            if not is_affine_on_a(candidate, field):
                ok = False
                break
        if ok:
            current = candidate
        else:
            blocks.append(current)
            current = [row]
    if current:
        blocks.append(current)
    return blocks


def is_affine_on_index(rows: list[dict[str, Any]], field: str) -> bool:
    if len(rows) <= 2:
        return True
    differences = [
        rows[i + 1][field] - rows[i][field]
        for i in range(len(rows) - 1)
    ]
    return len(set(differences)) == 1


def partition_global_index(rows: list[dict[str, Any]]) -> list[list[dict[str, Any]]]:
    ordered = sorted(rows, key=lambda row: row["idx"])
    blocks: list[list[dict[str, Any]]] = []
    current: list[dict[str, Any]] = []
    for row in ordered:
        candidate = current + [row]
        ok = True
        if current and row["idx"] != current[-1]["idx"] + 1:
            ok = False
        for field in GLOBAL_FIELDS:
            if not is_affine_on_index(candidate, field):
                ok = False
                break
        if ok:
            current = candidate
        else:
            blocks.append(current)
            current = [row]
    if current:
        blocks.append(current)
    return blocks


def block_summary(block: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "src_a_start": block[0]["src_a"],
        "src_a_end": block[-1]["src_a"],
        "length": len(block),
        "dst_label": block[0]["dst_label"],
        "dst_a": affine_formula(block, "dst_a"),
        "time": affine_formula(block, "time"),
        "events": affine_formula(block, "events"),
    }


def global_block_summary(block: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "idx_start": block[0]["idx"],
        "idx_end": block[-1]["idx"],
        "length": len(block),
        "src_label_start": block[0]["src_label"],
        "src_label_end": block[-1]["src_label"],
        "dst_idx": affine_formula(block, "dst_idx", "idx"),
        "time": affine_formula(block, "time", "idx"),
        "events": affine_formula(block, "events", "idx"),
    }


def residue_affine_test(rows: list[dict[str, Any]], modulus: int) -> bool:
    classes: dict[int, list[dict[str, Any]]] = {}
    for row in rows:
        classes.setdefault(row["src_a"] % modulus, []).append(row)
    for part in classes.values():
        if len({row["dst_label"] for row in part}) > 1:
            return False
        for field in FIELDS:
            if not is_affine_on_sparse_a(part, field):
                return False
    return True


def residue_affine_tests_by_label(
    by_label: dict[str, list[dict[str, Any]]]
) -> dict[str, Any]:
    out = {}
    for label in LABELS:
        passing = [
            modulus
            for modulus in RESIDUE_MODULI
            if residue_affine_test(by_label[label], modulus)
        ]
        out[label] = {
            "passing_moduli": passing,
            "first_passing_modulus": passing[0] if passing else None,
        }
    return out


def summarize_q(binary: Path, q: int, workdir: Path, preview_limit: int) -> dict[str, Any]:
    m = 48 * q + 42
    x = 6 * q + 5
    z = x
    cap = max(10_000, 10 * m * m)
    csv_path = workdir / f"r42_pointwise_q{q}.csv"
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
            "x": x,
            "z": z,
            "ok": False,
            "returncode": proc.returncode,
            "stderr_tail": proc.stderr.strip().splitlines()[-5:],
        }
    rows = r42.load_rows(csv_path)
    by_label: dict[str, list[dict[str, Any]]] = {label: [] for label in LABELS}
    for row in rows:
        by_label[row["src_label"]].append(row)
    blocks_by_label: dict[str, list[list[dict[str, Any]]]] = {
        label: partition_label(by_label[label])
        for label in LABELS
    }
    global_blocks = partition_global_index(rows)
    residue_tests = residue_affine_tests_by_label(by_label)
    block_counts = {
        label: len(blocks_by_label[label])
        for label in LABELS
    }
    singleton_counts = {
        label: sum(1 for block in blocks_by_label[label] if len(block) == 1)
        for label in LABELS
    }
    max_block_lengths = {
        label: max((len(block) for block in blocks_by_label[label]), default=0)
        for label in LABELS
    }
    preview = {
        label: [block_summary(block) for block in blocks_by_label[label][:preview_limit]]
        for label in LABELS
        if blocks_by_label[label]
    }
    total_time = sum(row["time"] for row in rows)
    lengths = cycle_lengths(rows)
    return {
        "q": q,
        "m": m,
        "x": x,
        "z": z,
        "ok": True,
        "allpair_nodes": len(rows),
        "expected_nodes": 10 * (m - 1) + 1,
        "node_count_ok": len(rows) == 10 * (m - 1) + 1,
        "single_cycle": lengths == [len(rows)],
        "cycle_lengths": lengths[:8],
        "time_total": total_time,
        "m4": m**4,
        "time_total_ok": total_time == m**4,
        "total_blocks": sum(block_counts.values()),
        "total_singleton_blocks": sum(singleton_counts.values()),
        "max_block_length": max(max_block_lengths.values()),
        "block_counts_by_label": block_counts,
        "singleton_blocks_by_label": singleton_counts,
        "max_block_length_by_label": max_block_lengths,
        "rows_by_label": {label: len(by_label[label]) for label in LABELS},
        "residue_affine_tests_by_label": residue_tests,
        "preview_blocks_by_label": preview,
        "global_idx_affine_blocks": {
            "block_count": len(global_blocks),
            "singleton_count": sum(1 for block in global_blocks if len(block) == 1),
            "max_block_length": max((len(block) for block in global_blocks), default=0),
            "preview": [
                global_block_summary(block)
                for block in global_blocks[:preview_limit]
            ],
        },
        "stderr_tail": proc.stderr.strip().splitlines()[-3:],
    }


def fit_by_label(samples: list[dict[str, Any]], key: str) -> dict[str, Any]:
    out = {}
    for label in LABELS:
        points = [
            (sample["q"], sample[key][label])
            for sample in samples
            if sample.get("ok")
        ]
        out[label] = fit_polynomial(points)
    return out


def build_summary(
    q_values: list[int],
    binary: Path,
    compile_binary: bool,
    preview_limit: int,
) -> dict[str, Any]:
    if compile_binary:
        r42.compile_checker(binary)
    with tempfile.TemporaryDirectory(prefix="routeE-r42-pointwise-law-") as tmp:
        samples = [
            summarize_q(binary, q, Path(tmp), preview_limit)
            for q in q_values
        ]
    ok_samples = [sample for sample in samples if sample.get("ok")]
    total_block_points = [
        (sample["q"], sample["total_blocks"])
        for sample in ok_samples
    ]
    singleton_points = [
        (sample["q"], sample["total_singleton_blocks"])
        for sample in ok_samples
    ]
    global_block_points = [
        (sample["q"], sample["global_idx_affine_blocks"]["block_count"])
        for sample in ok_samples
    ]
    global_singleton_points = [
        (sample["q"], sample["global_idx_affine_blocks"]["singleton_count"])
        for sample in ok_samples
    ]
    global_max_block_points = [
        (sample["q"], sample["global_idx_affine_blocks"]["max_block_length"])
        for sample in ok_samples
    ]
    uniform_residue_moduli_by_label = {}
    for label in LABELS:
        passing_sets = [
            set(sample["residue_affine_tests_by_label"][label]["passing_moduli"])
            for sample in ok_samples
        ]
        common = sorted(set.intersection(*passing_sets)) if passing_sets else []
        uniform_residue_moduli_by_label[label] = {
            "common_passing_moduli": common,
            "first_common_passing_modulus": common[0] if common else None,
        }
    return {
        "schema": "routeE_r42_pointwise_law_mining_v1",
        "branch": "R42",
        "family": "m = 48*q + 42, x = z = 6*q + 5",
        "source_checker": str(r42.CPP.relative_to(ROOT)),
        "raw_csv_preserved": False,
        "partition_rule": (
            "For each source label, split consecutive src_a runs maximally "
            "so dst_label is constant and dst_a/time/events are affine in src_a."
        ),
        "samples": samples,
        "fits": {
            "total_blocks": fit_polynomial(total_block_points),
            "total_singleton_blocks": fit_polynomial(singleton_points),
            "global_idx_block_count": fit_polynomial(global_block_points),
            "global_idx_singleton_count": fit_polynomial(global_singleton_points),
            "global_idx_max_block_length": fit_polynomial(global_max_block_points),
            "block_counts_by_label": fit_by_label(ok_samples, "block_counts_by_label"),
            "singleton_blocks_by_label": fit_by_label(
                ok_samples, "singleton_blocks_by_label"
            ),
            "max_block_length_by_label": fit_by_label(
                ok_samples, "max_block_length_by_label"
            ),
        },
        "summary": {
            "q_values": q_values,
            "all_samples_ok": all(sample.get("ok") for sample in samples),
            "all_single_cycle": all(sample.get("single_cycle") for sample in samples),
            "all_time_total_ok": all(sample.get("time_total_ok") for sample in samples),
            "all_node_count_ok": all(sample.get("node_count_ok") for sample in samples),
            "total_block_formula": fit_polynomial(total_block_points).get("formula"),
            "total_singleton_block_formula": fit_polynomial(singleton_points).get(
                "formula"
            ),
            "global_idx_block_formula": fit_polynomial(global_block_points).get(
                "formula"
            ),
            "global_idx_singleton_formula": fit_polynomial(
                global_singleton_points
            ).get("formula"),
            "global_idx_max_block_length_formula": fit_polynomial(
                global_max_block_points
            ).get("formula"),
            "max_total_blocks": max(
                (sample["total_blocks"] for sample in ok_samples), default=0
            ),
            "max_singleton_blocks": max(
                (sample["total_singleton_blocks"] for sample in ok_samples), default=0
            ),
            "max_global_idx_blocks": max(
                (
                    sample["global_idx_affine_blocks"]["block_count"]
                    for sample in ok_samples
                ),
                default=0,
            ),
            "representative_q": ok_samples[1]["q"] if len(ok_samples) > 1 else None,
            "uniform_residue_moduli_by_label": uniform_residue_moduli_by_label,
            "labels_without_uniform_residue_modulus": [
                label
                for label, info in uniform_residue_moduli_by_label.items()
                if not info["common_passing_moduli"]
            ],
        },
        "promotion_impact": {
            "pointwise_equations_closed": False,
            "no_early_closed": False,
            "diagnosis": (
                "The naive source-label/src_a interval-affine partition is "
                "only a formula-mining diagnostic.  It does not prove the "
                "first-return equation or no-early condition."
            ),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--q-values", default="0:4")
    parser.add_argument("--binary", type=Path, default=DEFAULT_BIN)
    parser.add_argument("--no-compile", action="store_true")
    parser.add_argument("--preview-limit", type=int, default=8)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    payload = build_summary(
        parse_range(args.q_values),
        args.binary,
        not args.no_compile,
        args.preview_limit,
    )
    print("schema", payload["schema"])
    print("all_samples_ok", payload["summary"]["all_samples_ok"])
    print("all_single_cycle", payload["summary"]["all_single_cycle"])
    print("total_block_formula", payload["summary"]["total_block_formula"])
    print("max_total_blocks", payload["summary"]["max_total_blocks"])
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
