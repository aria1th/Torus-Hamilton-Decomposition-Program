#!/usr/bin/env python3
"""Verify the compact R42 boundary quotient summary.

This verifier is intentionally lightweight: it does not preserve or regenerate
the raw all-pair CSV.  Instead it checks that the committed compact R42 summary
is internally consistent:

* q>=1 transition-count affine fits reproduce every sampled transition table;
* boundary sizes match 3*m-2 and the boundary quotient is one cycle in samples;
* the q=1 representative 29-block table agrees with the run-normalized block
  formula fits at q=1;
* the block-count by source label matches the stable advertised profile.

This is still not a symbolic R42 theorem.  It is an integrity verifier for the
proof-promotion artifact.
"""

from __future__ import annotations

import argparse
import json
import re
from collections import Counter
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CERT = ROOT / "certs" / "routeE_r42_boundary_quotient_summary.json"


FORMULA_RE = re.compile(r"^\s*([+-]?\d+)\*q(?:\s*([+-])\s*(\d+))?\s*$")
LABELS = ["Z", "03", "04", "34"]


def eval_formula(expr: str | None, q: int) -> int | None:
    if expr is None:
        return None
    expr = str(expr).strip()
    if "*q" not in expr:
        return int(expr)
    match = FORMULA_RE.match(expr)
    if match is None:
        raise ValueError(f"unsupported affine formula: {expr!r}")
    slope = int(match.group(1))
    value = slope * q
    if match.group(2) is not None:
        term = int(match.group(3))
        value += term if match.group(2) == "+" else -term
    return value


def affine_coeffs(expr: str | None) -> tuple[int, int] | None:
    if expr is None:
        return None
    expr = str(expr).strip()
    if "*q" not in expr:
        return (0, int(expr))
    match = FORMULA_RE.match(expr)
    if match is None:
        raise ValueError(f"unsupported affine formula: {expr!r}")
    slope = int(match.group(1))
    intercept = 0
    if match.group(2) is not None:
        term = int(match.group(3))
        intercept = term if match.group(2) == "+" else -term
    return (slope, intercept)


def add_coeffs(values: list[tuple[int, int]]) -> tuple[int, int]:
    return (sum(a for a, _ in values), sum(b for _, b in values))


def formula_text(coeffs: tuple[int, int]) -> str:
    slope, intercept = coeffs
    if slope == 0:
        return str(intercept)
    if intercept == 0:
        return f"{slope}*q"
    sign = "+" if intercept > 0 else "-"
    return f"{slope}*q {sign} {abs(intercept)}"


def tail_formula(block: dict[str, Any], field: str, q: int | None = None) -> tuple[str | None, str | None]:
    prefix = f"{field}_q_ge_"
    candidates = sorted(
        (
            (int(key[len(prefix):]), key)
            for key in block
            if key.startswith(prefix) and key[len(prefix):].isdigit()
        ),
        reverse=True,
    )
    for threshold, key in candidates:
        if q is None or q >= threshold:
            value = block.get(key)
            if value is not None:
                return value, key
    return None, None


def path_run_counts(path: str | None) -> list[dict[str, int | str]]:
    if not path:
        return []
    labels = path.split(">")
    out: list[dict[str, int | str]] = []
    current = labels[0]
    count = 1
    for label in labels[1:]:
        if label == current:
            count += 1
            continue
        out.append({"label": current, "count": count})
        current = label
        count = 1
    out.append({"label": current, "count": count})
    return out


def structural_key(block: dict[str, Any]) -> dict[str, Any]:
    terminal = block.get("terminal") or {}
    condition = block.get("condition") or {}
    return {
        "src_label": block.get("src_label"),
        "dst_label_group": block.get("dst_label_group"),
        "path_shape": [run["label"] for run in path_run_counts(block.get("path"))],
        "fallback": block.get("fallback"),
        "terminal_dst_label": terminal.get("dst_label"),
        "condition_mod": condition.get("mod"),
        "condition_residue": condition.get("residue"),
    }


def verify_transition_fits(data: dict[str, Any]) -> list[dict[str, Any]]:
    fits = data.get("q_ge_1_transition_count_fits", {})
    bad = []
    for sample in data.get("samples", []):
        q = int(sample["q"])
        if q < 1:
            continue
        got = sample.get("boundary_transition_counts", {})
        for src, row in fits.items():
            for dst, formula in row.items():
                expected = eval_formula(formula, q)
                actual = got.get(src, {}).get(dst)
                if expected != actual:
                    bad.append(
                        {
                            "q": q,
                            "src": src,
                            "dst": dst,
                            "formula": formula,
                            "expected": expected,
                            "actual": actual,
                        }
                    )
    return bad


def strongly_connected(edges: set[tuple[str, str]]) -> bool:
    if not edges:
        return False
    adjacency = {label: set() for label in LABELS}
    reverse = {label: set() for label in LABELS}
    for src, dst in edges:
        adjacency[src].add(dst)
        reverse[dst].add(src)

    def reach(graph: dict[str, set[str]], start: str) -> set[str]:
        seen = {start}
        stack = [start]
        while stack:
            src = stack.pop()
            for dst in graph[src]:
                if dst not in seen:
                    seen.add(dst)
                    stack.append(dst)
        return seen

    return reach(adjacency, LABELS[0]) == set(LABELS) and reach(reverse, LABELS[0]) == set(LABELS)


def verify_transition_symbolics(data: dict[str, Any]) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    fits = data.get("q_ge_1_transition_count_fits", {})
    bad = []
    expected_label_count = {
        "Z": (0, 1),
        "03": (48, 41),
        "04": (48, 41),
        "34": (48, 41),
    }
    row_totals: dict[str, tuple[int, int]] = {}
    col_totals: dict[str, tuple[int, int]] = {}
    positive_edges: set[tuple[str, str]] = set()
    nonnegative_for_q_ge_1 = True
    for src in LABELS:
        coeffs = []
        for dst in LABELS:
            value = affine_coeffs(fits.get(src, {}).get(dst))
            if value is None:
                bad.append({"check": "missing_transition_fit", "src": src, "dst": dst})
                value = (0, 0)
            if value[0] + value[1] < 0 or value[0] < 0:
                nonnegative_for_q_ge_1 = False
                bad.append({"check": "negative_for_q_ge_1", "src": src, "dst": dst, "coeffs": value})
            if value[0] + value[1] > 0:
                positive_edges.add((src, dst))
            coeffs.append(value)
        row_totals[src] = add_coeffs(coeffs)
    for dst in LABELS:
        col_totals[dst] = add_coeffs(
            [affine_coeffs(fits.get(src, {}).get(dst)) or (0, 0) for src in LABELS]
        )
    for label in LABELS:
        if row_totals[label] != expected_label_count[label]:
            bad.append(
                {
                    "check": "row_total",
                    "label": label,
                    "expected": expected_label_count[label],
                    "actual": row_totals[label],
                }
            )
        if col_totals[label] != expected_label_count[label]:
            bad.append(
                {
                    "check": "column_total",
                    "label": label,
                    "expected": expected_label_count[label],
                    "actual": col_totals[label],
                }
            )
    total = add_coeffs(list(row_totals.values()))
    expected_total = (144, 124)
    if total != expected_total:
        bad.append({"check": "total", "expected": expected_total, "actual": total})
    if not strongly_connected(positive_edges):
        bad.append({"check": "positive_edge_support_strongly_connected", "edges": sorted(positive_edges)})
    summary = {
        "row_totals": {label: formula_text(value) for label, value in row_totals.items()},
        "column_totals": {label: formula_text(value) for label, value in col_totals.items()},
        "expected_label_counts": {
            label: formula_text(value) for label, value in expected_label_count.items()
        },
        "total": formula_text(total),
        "expected_total": "144*q + 124",
        "m_family": "m = 48*q + 42",
        "total_equals_3m_minus_2": total == expected_total,
        "nonnegative_for_q_ge_1": nonnegative_for_q_ge_1,
        "positive_edges": sorted([list(edge) for edge in positive_edges]),
        "positive_edge_support_strongly_connected": strongly_connected(positive_edges),
    }
    return bad, summary


def coeffs_equal_text(left: tuple[int, int], right: tuple[int, int]) -> bool:
    return left == right


def nonnegative_affine_for_q_ge_1(coeffs: tuple[int, int]) -> bool:
    slope, intercept = coeffs
    return slope >= 0 and slope + intercept >= 0


def verify_block_formula_symbolics(data: dict[str, Any]) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    fits = data.get("q_ge_1_block_formula_fits", {})
    blocks = fits.get("blocks", [])
    transitions = data.get("q_ge_1_transition_count_fits", {})
    stability = data.get("q_ge_1_stability", {})
    bad = []
    by_src: dict[str, tuple[int, int]] = {label: (0, 0) for label in LABELS}
    by_transition: dict[tuple[str, str], tuple[int, int]] = {
        (src, dst): (0, 0) for src in LABELS for dst in LABELS
    }
    block_count_by_src = Counter()
    missing_terminal_fields = []
    for block in blocks:
        index = block.get("index")
        key = block.get("key") or {}
        src = key.get("src_label")
        dst = key.get("terminal_dst_label")
        count = affine_coeffs(block.get("condition_count"))
        if src not in LABELS or dst not in LABELS or count is None:
            bad.append({"index": index, "check": "bad_block_key_or_count", "block": block})
            continue
        if not nonnegative_affine_for_q_ge_1(count):
            bad.append({"index": index, "check": "negative_condition_count", "count": count})
        by_src[src] = add_coeffs([by_src[src], count])
        by_transition[(src, dst)] = add_coeffs([by_transition[(src, dst)], count])
        block_count_by_src[src] += 1
        for field in ["terminal_affine_alpha", "terminal_affine_beta"]:
            if block.get(field) is None:
                tail, _ = tail_formula(block, field)
                if tail is None:
                    missing_terminal_fields.append({"index": index, "field": field})
    for src in LABELS:
        expected_src = add_coeffs(
            [affine_coeffs(transitions.get(src, {}).get(dst)) or (0, 0) for dst in LABELS]
        )
        if by_src[src] != expected_src:
            bad.append(
                {
                    "check": "src_block_mass",
                    "src": src,
                    "expected": expected_src,
                    "actual": by_src[src],
                }
            )
        for dst in LABELS:
            expected = affine_coeffs(transitions.get(src, {}).get(dst)) or (0, 0)
            actual = by_transition[(src, dst)]
            if actual != expected:
                bad.append(
                    {
                        "check": "transition_block_mass",
                        "src": src,
                        "dst": dst,
                        "expected": expected,
                        "actual": actual,
                    }
                )
    expected_block_counts = stability.get("block_count_by_label") or {}
    if dict(block_count_by_src) != expected_block_counts:
        bad.append(
            {
                "check": "block_count_by_src",
                "expected": expected_block_counts,
                "actual": dict(block_count_by_src),
            }
        )
    if missing_terminal_fields:
        bad.append({"check": "missing_terminal_tail_fields", "items": missing_terminal_fields})
    summary = {
        "block_count": len(blocks),
        "block_count_by_src": dict(block_count_by_src),
        "src_masses": {src: formula_text(value) for src, value in by_src.items()},
        "transition_masses": {
            src: {
                dst: formula_text(by_transition[(src, dst)])
                for dst in LABELS
                if by_transition[(src, dst)] != (0, 0)
            }
            for src in LABELS
        },
        "block_masses_match_transition_fits": not bad,
        "all_null_terminal_fields_have_q_ge_2_tails": not missing_terminal_fields,
    }
    return bad, summary


def verify_sample_flags(data: dict[str, Any]) -> list[dict[str, Any]]:
    bad = []
    for sample in data.get("samples", []):
        q = int(sample["q"])
        m = int(sample["m"])
        checks = {
            "ok": sample.get("ok") is True,
            "boundary_nodes_formula_ok": sample.get("boundary_nodes_formula_ok") is True,
            "boundary_nodes_value": sample.get("boundary_nodes") == 3 * m - 2,
            "boundary_single_cycle": sample.get("boundary_single_cycle") is True,
            "x_law": sample.get("x") == 6 * q + 5,
            "z_law": sample.get("z") == 6 * q + 5,
            "m_law": m == 48 * q + 42,
        }
        for name, ok in checks.items():
            if not ok:
                bad.append({"q": q, "m": m, "check": name, "sample": sample})
    return bad


def verify_representative_blocks(data: dict[str, Any]) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    blocks = data.get("representative_q1_block_table") or []
    fits = data.get("q_ge_1_block_formula_fits", {})
    formulas = fits.get("blocks", [])
    bad = []
    null_fields = []
    if fits.get("stable_structural_keys") is not True:
        bad.append({"check": "stable_structural_keys", "actual": fits.get("stable_structural_keys")})
    if fits.get("block_count") != 29 or len(formulas) != 29 or len(blocks) != 29:
        bad.append(
            {
                "check": "block_count",
                "fit_block_count": fits.get("block_count"),
                "formula_len": len(formulas),
                "representative_len": len(blocks),
            }
        )
        return bad
    for index, (block, formula) in enumerate(zip(blocks, formulas, strict=True)):
        q = 1
        key = structural_key(block)
        if formula.get("key") != key:
            bad.append({"index": index, "check": "key", "expected": formula.get("key"), "actual": key})
        condition = block.get("condition") or {}
        terminal = block.get("terminal") or {}
        comparisons = [
            ("condition_count", condition.get("count")),
            ("condition_min", condition.get("min")),
            ("condition_max", condition.get("max")),
            ("condition_interval_count", condition.get("interval_count")),
            ("terminal_affine_alpha", (terminal.get("affine_mod") or [None, None])[0]),
            ("terminal_affine_beta", (terminal.get("affine_mod") or [None, None])[1]),
        ]
        for field, actual in comparisons:
            if formula.get(field) is None:
                if actual is not None:
                    _, tail_key = tail_formula(formula, field)
                    null_fields.append(
                        {
                            "index": index,
                            "field": field,
                            "actual_q1": actual,
                            "tail_formula_key": tail_key,
                            "tail_formula": formula.get(tail_key)
                            if tail_key is not None
                            else None,
                        }
                    )
                continue
            expected = eval_formula(formula.get(field), q)
            if expected != actual:
                bad.append(
                    {
                        "index": index,
                        "check": field,
                        "formula": formula.get(field),
                        "expected": expected,
                        "actual": actual,
                    }
                )
        actual_runs = path_run_counts(block.get("path"))
        expected_runs = [
            {"label": run["label"], "count": eval_formula(run["count"], q)}
            for run in formula.get("path_run_counts", [])
        ]
        if actual_runs != expected_runs:
            bad.append(
                {
                    "index": index,
                    "check": "path_run_counts",
                    "expected": expected_runs,
                    "actual": actual_runs,
                }
            )
    return bad, null_fields


def verify_stability(data: dict[str, Any]) -> list[dict[str, Any]]:
    stability = data.get("q_ge_1_stability", {})
    bad = []
    expected_flags = {
        "stable_block_count": True,
        "stable_block_count_by_label": True,
        "all_boundary_single_cycle": True,
        "all_boundary_nodes_formula_ok": True,
    }
    for field, expected in expected_flags.items():
        if stability.get(field) is not expected:
            bad.append({"check": field, "expected": expected, "actual": stability.get(field)})
    if stability.get("block_count") != 29:
        bad.append({"check": "block_count", "expected": 29, "actual": stability.get("block_count")})
    if stability.get("block_count_by_label") != {"03": 7, "04": 13, "34": 8, "Z": 1}:
        bad.append(
            {
                "check": "block_count_by_label",
                "expected": {"03": 7, "04": 13, "34": 8, "Z": 1},
                "actual": stability.get("block_count_by_label"),
            }
        )
    samples = [sample for sample in data.get("samples", []) if int(sample.get("q", 0)) >= 1]
    for sample in samples:
        if sum((sample.get("block_count_by_label") or {}).values()) != sample.get("block_count"):
            bad.append({"q": sample.get("q"), "check": "sample_block_count_sum"})
        if sample.get("block_count_by_label") != stability.get("block_count_by_label"):
            bad.append({"q": sample.get("q"), "check": "sample_stable_block_count_by_label"})
        transitions = sample.get("boundary_transition_counts", {})
        src_totals = {src: sum(row.values()) for src, row in transitions.items()}
        src_boundary_counts = Counter(row.get("src_label") for row in data.get("representative_q1_block_table", []))
        if int(sample.get("q")) == 1:
            # The q=1 representative block table is grouped by blocks, not by
            # nodes, so compare only the preserved block count by label.
            if dict(src_boundary_counts) != stability.get("block_count_by_label"):
                bad.append({"q": 1, "check": "representative_source_block_counts"})
        if sum(src_totals.values()) != sample.get("boundary_nodes"):
            bad.append({"q": sample.get("q"), "check": "transition_total_equals_boundary_nodes"})
    return bad


def build_verification(cert: Path) -> dict[str, Any]:
    data = json.loads(cert.read_text())
    representative_errors, representative_null_fields = verify_representative_blocks(data)
    transition_symbolic_errors, transition_symbolic_summary = verify_transition_symbolics(data)
    block_formula_errors, block_formula_summary = verify_block_formula_symbolics(data)
    checks = {
        "schema_ok": data.get("schema") == "routeE_r42_boundary_quotient_summary_v1",
        "raw_csv_not_preserved": data.get("raw_csv_preserved") is False,
        "sample_flag_errors": verify_sample_flags(data),
        "transition_fit_errors": verify_transition_fits(data),
        "transition_symbolic_errors": transition_symbolic_errors,
        "transition_symbolic_summary": transition_symbolic_summary,
        "block_formula_symbolic_errors": block_formula_errors,
        "block_formula_symbolic_summary": block_formula_summary,
        "representative_block_errors": representative_errors,
        "representative_block_null_formula_fields": representative_null_fields,
        "stability_errors": verify_stability(data),
    }
    ok = (
        checks["schema_ok"]
        and checks["raw_csv_not_preserved"]
        and not checks["sample_flag_errors"]
        and not checks["transition_fit_errors"]
        and not checks["transition_symbolic_errors"]
        and not checks["block_formula_symbolic_errors"]
        and not checks["representative_block_errors"]
        and not checks["stability_errors"]
    )
    return {
        "schema": "routeE_r42_boundary_summary_verification_v1",
        "source": str(cert),
        "ok": ok,
        "checks": checks,
        "summary": {
            "sample_q_values": [sample.get("q") for sample in data.get("samples", [])],
            "q_ge_1_transition_fits_verified": not checks["transition_fit_errors"],
            "q_ge_1_transition_symbolics_verified": not checks["transition_symbolic_errors"],
            "q_ge_1_block_formula_symbolics_verified": not checks["block_formula_symbolic_errors"],
            "q1_representative_block_formulas_verified": not checks["representative_block_errors"],
            "q1_representative_null_formula_field_count": len(representative_null_fields),
            "q1_null_fields_have_q_ge_2_tail_formulas": all(
                item.get("tail_formula") is not None
                for item in representative_null_fields
                if item.get("field", "").startswith("terminal_affine_")
            ),
            "stability_verified": not checks["stability_errors"],
        },
        "warning": (
            "This verifies the compact R42 boundary summary artifact.  It does "
            "not prove pointwise no-early returns or the full R42 branch theorem."
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
    for key, value in payload["summary"].items():
        print(key, value)
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")
    if not payload["ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
