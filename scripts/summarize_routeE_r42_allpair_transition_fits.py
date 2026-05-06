#!/usr/bin/env python3
"""Summarize R42 all-pair transition count/time polynomial evidence."""

from __future__ import annotations

import argparse
import json
import tempfile
from collections import Counter, defaultdict
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


def summarize_q(binary: Path, q: int, workdir: Path) -> dict[str, Any]:
    m = 48 * q + 42
    x = 6 * q + 5
    z = x
    cap = max(10_000, 10 * m * m)
    csv_path = workdir / f"r42_allpair_transition_q{q}.csv"
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
    counts: dict[str, Counter[str]] = {label: Counter() for label in LABELS}
    times: dict[str, dict[str, int]] = {
        src: defaultdict(int) for src in LABELS
    }
    label_count = Counter(row["src_label"] for row in rows)
    dst_count = Counter(row["dst_label"] for row in rows)
    label_time: dict[str, int] = defaultdict(int)
    dst_time: dict[str, int] = defaultdict(int)
    for row in rows:
        src = row["src_label"]
        dst = row["dst_label"]
        counts[src][dst] += 1
        times[src][dst] += row["time"]
        label_time[src] += row["time"]
        dst_time[dst] += row["time"]
    total_time = sum(row["time"] for row in rows)
    return {
        "q": q,
        "m": m,
        "x": x,
        "z": z,
        "allpair_nodes": len(rows),
        "expected_nodes": 10 * (m - 1) + 1,
        "node_count_ok": len(rows) == 10 * (m - 1) + 1,
        "cycle_lengths": cycle_lengths(rows),
        "single_cycle": cycle_lengths(rows) == [len(rows)],
        "time_total": total_time,
        "m4": m**4,
        "time_total_ok": total_time == m**4,
        "label_count": {label: label_count[label] for label in LABELS},
        "dst_count": {label: dst_count[label] for label in LABELS},
        "label_time": {label: label_time[label] for label in LABELS},
        "dst_time": {label: dst_time[label] for label in LABELS},
        "transition_count": {
            src: {dst: counts[src][dst] for dst in LABELS} for src in LABELS
        },
        "transition_time": {
            src: {dst: times[src][dst] for dst in LABELS} for src in LABELS
        },
        "max_return_time": max(row["time"] for row in rows),
        "max_events": max(row["events"] for row in rows),
        "stderr_tail": proc.stderr.strip().splitlines()[-3:],
        "ok": True,
    }


def fit_matrix(samples: list[dict[str, Any]], key: str) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    for src in LABELS:
        row = {}
        for dst in LABELS:
            points = [
                (sample["q"], sample[key][src][dst])
                for sample in samples
            ]
            row[dst] = fit_polynomial(points)
        out[src] = row
    return out


def support_edges(matrix: dict[str, dict[str, Any]]) -> list[list[str]]:
    edges = []
    for src in LABELS:
        for dst in LABELS:
            coeffs = matrix.get(src, {}).get(dst, {}).get("coefficients_ascending", [])
            if any(str(coeff) != "0" for coeff in coeffs):
                edges.append([src, dst])
    return edges


def build_summary(q_values: list[int], binary: Path, compile_binary: bool) -> dict[str, Any]:
    if compile_binary:
        r42.compile_checker(binary)
    with tempfile.TemporaryDirectory(prefix="routeE-r42-allpair-transition-") as tmp:
        samples = [summarize_q(binary, q, Path(tmp)) for q in q_values]
    ok_samples = [sample for sample in samples if sample.get("ok")]
    count_fits = fit_matrix(ok_samples, "transition_count")
    time_fits = fit_matrix(ok_samples, "transition_time")
    return {
        "schema": "routeE_r42_allpair_transition_fit_summary_v1",
        "branch": "R42",
        "family": "m = 48*q + 42, x = z = 6*q + 5",
        "source_checker": str(r42.CPP.relative_to(ROOT)),
        "raw_csv_preserved": False,
        "samples": samples,
        "fits": {
            "transition_count": count_fits,
            "transition_time": time_fits,
        },
        "summary": {
            "q_values": q_values,
            "all_samples_ok": all(sample.get("ok") for sample in samples),
            "all_single_cycle": all(sample.get("single_cycle") for sample in samples),
            "all_time_total_ok": all(sample.get("time_total_ok") for sample in samples),
            "transition_count_nonzero_edge_count": len(support_edges(count_fits)),
            "transition_time_nonzero_edge_count": len(support_edges(time_fits)),
        },
        "warning": (
            "Transition fits are sample-derived.  They support the R42 proof "
            "plan but do not replace the pointwise first-return/no-early proof."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--q-values", default="0:6")
    parser.add_argument("--binary", type=Path, default=DEFAULT_BIN)
    parser.add_argument("--no-compile", action="store_true")
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    payload = build_summary(parse_range(args.q_values), args.binary, not args.no_compile)
    print("schema", payload["schema"])
    print("all_samples_ok", payload["summary"]["all_samples_ok"])
    print("all_single_cycle", payload["summary"]["all_single_cycle"])
    print("transition_count_nonzero_edge_count", payload["summary"]["transition_count_nonzero_edge_count"])
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
