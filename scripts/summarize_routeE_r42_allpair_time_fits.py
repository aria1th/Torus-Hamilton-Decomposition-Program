#!/usr/bin/env python3
"""Summarize R42 all-pair return time polynomial evidence.

This script regenerates temporary all-pair CSV witnesses for
`m = 48*q + 42, x = z = 6*q + 5`, checks the all-pair section cycle and
`sum tau = m^4`, and records compact polynomial fits for label-wise time
totals.  It is evidence for the R42 Type-A promotion target, not a symbolic
no-early proof.
"""

from __future__ import annotations

import argparse
import json
import tempfile
from collections import Counter, defaultdict
from fractions import Fraction
from pathlib import Path
from typing import Any

import summarize_routeE_r42_boundary_quotient as r42


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_BIN = Path(tempfile.gettempdir()) / "routeE_allpair_cpp_v1_2"
LABELS = ["Z", "01", "02", "03", "04", "12", "13", "14", "23", "24", "34"]


def parse_range(text: str) -> list[int]:
    return r42.parse_range(text)


def cycle_lengths(rows: list[dict[str, Any]]) -> list[int]:
    nxt = {row["idx"]: row["dst_idx"] for row in rows}
    seen: set[int] = set()
    lengths = []
    for start in sorted(nxt):
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


def solve_linear(matrix: list[list[Fraction]], rhs: list[Fraction]) -> list[Fraction] | None:
    n = len(rhs)
    aug = [row[:] + [rhs[i]] for i, row in enumerate(matrix)]
    for col in range(n):
        pivot = next((row for row in range(col, n) if aug[row][col] != 0), None)
        if pivot is None:
            return None
        aug[col], aug[pivot] = aug[pivot], aug[col]
        div = aug[col][col]
        aug[col] = [value / div for value in aug[col]]
        for row in range(n):
            if row == col or aug[row][col] == 0:
                continue
            factor = aug[row][col]
            aug[row] = [aug[row][i] - factor * aug[col][i] for i in range(n + 1)]
    return [aug[i][-1] for i in range(n)]


def fit_polynomial(points: list[tuple[int, int]], max_degree: int = 6) -> dict[str, Any]:
    if not points:
        return {"status": "empty"}
    for degree in range(min(max_degree, len(points) - 1) + 1):
        xs = [Fraction(q) for q, _ in points[: degree + 1]]
        matrix = [[x**power for power in range(degree + 1)] for x in xs]
        rhs = [Fraction(value) for _, value in points[: degree + 1]]
        coeffs = solve_linear(matrix, rhs)
        if coeffs is None:
            continue
        if all(sum(coeffs[p] * Fraction(q) ** p for p in range(degree + 1)) == value for q, value in points):
            return {
                "status": "polynomial_fit",
                "degree": degree,
                "coefficients_ascending": [str(coeff) for coeff in coeffs],
                "formula": polynomial_text(coeffs),
            }
    return {"status": "no_fit"}


def polynomial_text(coeffs: list[Fraction]) -> str:
    parts: list[str] = []
    for power, coeff in enumerate(coeffs):
        if coeff == 0:
            continue
        sign = "-" if coeff < 0 else "+"
        abs_coeff = -coeff if coeff < 0 else coeff
        if abs_coeff.denominator == 1:
            coeff_text = str(abs_coeff.numerator)
        else:
            coeff_text = f"({abs_coeff.numerator}/{abs_coeff.denominator})"
        if power == 0:
            term = coeff_text
        elif power == 1:
            term = "q" if abs_coeff == 1 else f"{coeff_text}*q"
        else:
            term = f"q^{power}" if abs_coeff == 1 else f"{coeff_text}*q^{power}"
        if not parts:
            parts.append(term if sign == "+" else f"-{term}")
        else:
            parts.append(f"{sign} {term}")
    return " ".join(parts) if parts else "0"


def summarize_q(binary: Path, q: int, workdir: Path) -> dict[str, Any]:
    m = 48 * q + 42
    x = 6 * q + 5
    z = x
    cap = max(10_000, 10 * m * m)
    csv_path = workdir / f"r42_allpair_q{q}.csv"
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
    label_count = Counter(row["src_label"] for row in rows)
    label_time: dict[str, int] = defaultdict(int)
    dst_count = Counter(row["dst_label"] for row in rows)
    dst_time: dict[str, int] = defaultdict(int)
    for row in rows:
        label_time[row["src_label"]] += row["time"]
        dst_time[row["dst_label"]] += row["time"]
    total_time = sum(row["time"] for row in rows)
    lengths = cycle_lengths(rows)
    return {
        "q": q,
        "m": m,
        "x": x,
        "z": z,
        "allpair_nodes": len(rows),
        "expected_nodes": 10 * (m - 1) + 1,
        "node_count_ok": len(rows) == 10 * (m - 1) + 1,
        "cycle_lengths": lengths,
        "single_cycle": lengths == [len(rows)],
        "time_total": total_time,
        "m4": m**4,
        "time_total_ok": total_time == m**4,
        "label_count": {label: label_count[label] for label in LABELS},
        "label_time": {label: label_time[label] for label in LABELS},
        "dst_count": {label: dst_count[label] for label in LABELS},
        "dst_time": {label: dst_time[label] for label in LABELS},
        "max_return_time": max(row["time"] for row in rows),
        "max_events": max(row["events"] for row in rows),
        "stderr_tail": proc.stderr.strip().splitlines()[-3:],
        "ok": True,
    }


def fit_table(samples: list[dict[str, Any]], key: str) -> dict[str, Any]:
    out = {}
    for label in LABELS:
        points = [(sample["q"], sample[key][label]) for sample in samples]
        out[label] = fit_polynomial(points)
    return out


def build_summary(q_values: list[int], binary: Path, compile_binary: bool) -> dict[str, Any]:
    if compile_binary:
        r42.compile_checker(binary)
    with tempfile.TemporaryDirectory(prefix="routeE-r42-allpair-time-") as tmp:
        samples = [summarize_q(binary, q, Path(tmp)) for q in q_values]
    ok_samples = [sample for sample in samples if sample.get("ok")]
    total_points = [(sample["q"], sample["time_total"]) for sample in ok_samples]
    return {
        "schema": "routeE_r42_allpair_time_fit_summary_v1",
        "branch": "R42",
        "family": "m = 48*q + 42, x = z = 6*q + 5",
        "source_checker": str(r42.CPP.relative_to(ROOT)),
        "raw_csv_preserved": False,
        "samples": samples,
        "fits": {
            "time_total": fit_polynomial(total_points),
            "label_count": fit_table(ok_samples, "label_count"),
            "label_time": fit_table(ok_samples, "label_time"),
            "dst_count": fit_table(ok_samples, "dst_count"),
            "dst_time": fit_table(ok_samples, "dst_time"),
        },
        "summary": {
            "q_values": q_values,
            "all_samples_ok": all(sample.get("ok") for sample in samples),
            "all_single_cycle": all(sample.get("single_cycle") for sample in samples),
            "all_time_total_ok": all(sample.get("time_total_ok") for sample in samples),
            "all_node_count_ok": all(sample.get("node_count_ok") for sample in samples),
            "time_total_formula": fit_polynomial(total_points).get("formula"),
            "time_total_degree": fit_polynomial(total_points).get("degree"),
        },
        "warning": (
            "Polynomial fits are sample-derived.  They support the R42 proof "
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
    print("all_time_total_ok", payload["summary"]["all_time_total_ok"])
    print("time_total_formula", payload["summary"]["time_total_formula"])
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
