#!/usr/bin/env python3
"""Verify the compact R42 all-pair transition-fit summary."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path
from typing import Any

from summarize_routeE_r42_allpair_time_fits import LABELS
from verify_routeE_r42_allpair_time_fits import expected_m4_coeffs, expected_node_count_coeffs


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CERT = ROOT / "certs" / "routeE_r42_allpair_transition_fit_summary.json"


def parse_coeffs(coeffs: list[str]) -> list[Fraction]:
    return [Fraction(coeff) for coeff in coeffs]


def coeffs_to_strings(coeffs: list[Fraction]) -> list[str]:
    while len(coeffs) > 1 and coeffs[-1] == 0:
        coeffs.pop()
    return [str(coeff.numerator) if coeff.denominator == 1 else str(coeff) for coeff in coeffs]


def eval_coeffs(coeffs: list[str], q: int) -> int:
    value = sum(Fraction(coeff) * Fraction(q) ** power for power, coeff in enumerate(coeffs))
    if value.denominator != 1:
        raise ValueError(f"nonintegral polynomial value at q={q}: {value}")
    return value.numerator


def add_coeff_lists(rows: list[list[str]]) -> list[str]:
    parsed = [parse_coeffs(row) for row in rows]
    max_len = max((len(row) for row in parsed), default=1)
    total = [Fraction(0) for _ in range(max_len)]
    for row in parsed:
        for index, coeff in enumerate(row):
            total[index] += coeff
    return coeffs_to_strings(total)


def matrix_coeffs(fits: dict[str, Any], src: str, dst: str) -> list[str]:
    fit = fits.get(src, {}).get(dst, {})
    if fit.get("status") != "polynomial_fit":
        return ["0"]
    return fit.get("coefficients_ascending", ["0"])


def verify_matrix_values(samples: list[dict[str, Any]], fits: dict[str, Any], key: str) -> list[dict[str, Any]]:
    bad = []
    for sample in samples:
        q = int(sample["q"])
        matrix = sample.get(key, {})
        for src in LABELS:
            for dst in LABELS:
                expected = eval_coeffs(matrix_coeffs(fits, src, dst), q)
                actual = matrix.get(src, {}).get(dst)
                if expected != actual:
                    bad.append(
                        {
                            "check": "matrix_value",
                            "key": key,
                            "q": q,
                            "src": src,
                            "dst": dst,
                            "expected": expected,
                            "actual": actual,
                        }
                    )
    return bad


def fit_row_sum(fits: dict[str, Any], src: str) -> list[str]:
    return add_coeff_lists([matrix_coeffs(fits, src, dst) for dst in LABELS])


def fit_col_sum(fits: dict[str, Any], dst: str) -> list[str]:
    return add_coeff_lists([matrix_coeffs(fits, src, dst) for src in LABELS])


def fit_total(fits: dict[str, Any]) -> list[str]:
    return add_coeff_lists([matrix_coeffs(fits, src, dst) for src in LABELS for dst in LABELS])


def strongly_connected(edges: set[tuple[str, str]]) -> bool:
    if not edges:
        return False
    graph = {label: set() for label in LABELS}
    rev = {label: set() for label in LABELS}
    for src, dst in edges:
        graph[src].add(dst)
        rev[dst].add(src)

    def reach(adjacency: dict[str, set[str]]) -> set[str]:
        start = LABELS[0]
        seen = {start}
        stack = [start]
        while stack:
            cur = stack.pop()
            for nxt in adjacency[cur]:
                if nxt not in seen:
                    seen.add(nxt)
                    stack.append(nxt)
        return seen

    return reach(graph) == set(LABELS) and reach(rev) == set(LABELS)


def nonzero_edges(fits: dict[str, Any]) -> set[tuple[str, str]]:
    out = set()
    for src in LABELS:
        for dst in LABELS:
            if any(coeff != "0" for coeff in matrix_coeffs(fits, src, dst)):
                out.add((src, dst))
    return out


def build_verification(cert: Path) -> dict[str, Any]:
    data = json.loads(cert.read_text())
    samples = data.get("samples", [])
    count_fits = data.get("fits", {}).get("transition_count", {})
    time_fits = data.get("fits", {}).get("transition_time", {})
    bad = []
    if data.get("schema") != "routeE_r42_allpair_transition_fit_summary_v1":
        bad.append({"check": "schema", "actual": data.get("schema")})
    bad.extend(verify_matrix_values(samples, count_fits, "transition_count"))
    bad.extend(verify_matrix_values(samples, time_fits, "transition_time"))
    count_row_ok = True
    count_col_ok = True
    time_row_ok = True
    time_col_ok = True
    for label in LABELS:
        expected_count = ["1"] if label == "Z" else ["41", "48"]
        if fit_row_sum(count_fits, label) != expected_count:
            count_row_ok = False
            bad.append({"check": "count_row_sum", "label": label, "actual": fit_row_sum(count_fits, label)})
        if fit_col_sum(count_fits, label) != expected_count:
            count_col_ok = False
            bad.append({"check": "count_col_sum", "label": label, "actual": fit_col_sum(count_fits, label)})
    count_total = fit_total(count_fits)
    time_total = fit_total(time_fits)
    if count_total != expected_node_count_coeffs():
        bad.append({"check": "count_total", "expected": expected_node_count_coeffs(), "actual": count_total})
    if time_total != expected_m4_coeffs():
        bad.append({"check": "time_total", "expected": expected_m4_coeffs(), "actual": time_total})
    for sample in samples:
        q = int(sample["q"])
        for label in LABELS:
            row_time = sum(sample.get("transition_time", {}).get(label, {}).values())
            if row_time != sample.get("label_time", {}).get(label):
                time_row_ok = False
                bad.append({"check": "sample_time_row", "q": q, "label": label})
            col_time = sum(sample.get("transition_time", {}).get(src, {}).get(label, 0) for src in LABELS)
            if col_time != sample.get("dst_time", {}).get(label):
                time_col_ok = False
                bad.append({"check": "sample_time_col", "q": q, "label": label})
    count_edges = nonzero_edges(count_fits)
    time_edges = nonzero_edges(time_fits)
    return {
        "schema": "routeE_r42_allpair_transition_fit_verification_v1",
        "source": str(cert),
        "ok": not bad,
        "bad_examples": bad[:20],
        "summary": {
            "sample_q_values": [sample.get("q") for sample in samples],
            "transition_count_values_verified": not verify_matrix_values(samples, count_fits, "transition_count"),
            "transition_time_values_verified": not verify_matrix_values(samples, time_fits, "transition_time"),
            "count_row_sums_match_label_counts": count_row_ok,
            "count_column_sums_match_dst_counts": count_col_ok,
            "count_total_is_node_count": count_total == expected_node_count_coeffs(),
            "time_row_sums_match_label_times_on_samples": time_row_ok,
            "time_column_sums_match_dst_times_on_samples": time_col_ok,
            "time_total_is_m4": time_total == expected_m4_coeffs(),
            "transition_count_nonzero_edge_count": len(count_edges),
            "transition_time_nonzero_edge_count": len(time_edges),
            "transition_count_support_strongly_connected": strongly_connected(count_edges),
            "transition_time_support_strongly_connected": strongly_connected(time_edges),
        },
        "warning": (
            "This verifies the committed transition-fit artifact. It does not "
            "regenerate CSV witnesses and does not prove no-early returns."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cert", type=Path, default=DEFAULT_CERT)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    payload = build_verification(args.cert)
    print("schema", payload["schema"])
    print("ok", payload["ok"])
    print("sample_q_values", payload["summary"]["sample_q_values"])
    print("count_edges", payload["summary"]["transition_count_nonzero_edge_count"])
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")
    if not payload["ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
