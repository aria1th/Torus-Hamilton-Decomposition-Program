#!/usr/bin/env python3
"""Regenerate R42 boundary block tables and verify stored formulas.

This verifier deliberately uses temporary CSV files only.  It compiles/runs the
all-pair C++ checker, reconstructs the R42 boundary block table, and checks it
against the compact formulas stored in
`certs/routeE_r42_boundary_quotient_summary.json`.

It is stronger than the compact-summary verifier: the compact verifier checks
internal consistency, while this script checks that the formulas still match
freshly regenerated finite witnesses for selected q-values.
"""

from __future__ import annotations

import argparse
import json
import tempfile
from pathlib import Path
from typing import Any

import summarize_routeE_r42_boundary_quotient as r42
from verify_routeE_r42_boundary_summary import eval_formula, path_run_counts


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CERT = ROOT / "certs" / "routeE_r42_boundary_quotient_summary.json"
DEFAULT_BIN = Path(tempfile.gettempdir()) / "routeE_allpair_cpp_v1_2"


def parse_q_values(text: str) -> list[int]:
    if ":" not in text:
        return [int(part) for part in text.split(",") if part.strip()]
    parts = [int(part) for part in text.split(":")]
    if len(parts) == 2:
        start, stop = parts
        step = 1
    elif len(parts) == 3:
        start, stop, step = parts
    else:
        raise ValueError("q range syntax is start:stop[:step]")
    return list(range(start, stop + 1, step))


def formula_value(block_formula: dict[str, Any], field: str, q: int) -> tuple[int | None, str | None]:
    value = block_formula.get(field)
    if value is not None:
        return eval_formula(value, q), field
    tail_field = f"{field}_q_ge_2"
    if q >= 2 and block_formula.get(tail_field) is not None:
        return eval_formula(block_formula.get(tail_field), q), tail_field
    return None, None


def compare_block(q: int, index: int, actual: dict[str, Any], formula: dict[str, Any]) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    bad = []
    open_nulls = []
    key = r42.structural_block_key(actual)
    if key != formula.get("key"):
        bad.append({"index": index, "q": q, "check": "structural_key", "expected": formula.get("key"), "actual": key})
    condition = actual.get("condition") or {}
    terminal = actual.get("terminal") or {}
    comparisons = [
        ("condition_count", condition.get("count")),
        ("condition_min", condition.get("min")),
        ("condition_max", condition.get("max")),
        ("condition_interval_count", condition.get("interval_count")),
        ("terminal_affine_alpha", (terminal.get("affine_mod") or [None, None])[0]),
        ("terminal_affine_beta", (terminal.get("affine_mod") or [None, None])[1]),
    ]
    for field, actual_value in comparisons:
        expected, source_field = formula_value(formula, field, q)
        if expected is None and actual_value is None:
            continue
        if expected is None and actual_value is not None and (
            field == "condition_interval_count" or q == 1
        ):
            # condition_interval_count is optional compression metadata rather
            # than transition-mass data. q=1 also has finite boundary
            # exceptions for block 24 terminal fields.
            open_nulls.append(
                {
                    "index": index,
                    "q": q,
                    "field": field,
                    "actual": actual_value,
                }
            )
            continue
        if expected != actual_value:
            bad.append(
                {
                    "index": index,
                    "q": q,
                    "check": field,
                    "source_field": source_field,
                    "expected": expected,
                    "actual": actual_value,
                }
            )
    actual_runs = path_run_counts(actual.get("path"))
    expected_runs = [
        {"label": run["label"], "count": eval_formula(run["count"], q)}
        for run in formula.get("path_run_counts", [])
    ]
    if actual_runs != expected_runs:
        bad.append(
            {
                "index": index,
                "q": q,
                "check": "path_run_counts",
                "expected": expected_runs,
                "actual": actual_runs,
            }
        )
    return bad, open_nulls


def verify_q(binary: Path, q: int, formulas: list[dict[str, Any]], workdir: Path) -> dict[str, Any]:
    sample = r42.summarize_sample(binary, q, workdir)
    blocks = sample.pop("_block_table_for_fit")
    bad = []
    open_nulls = []
    if sample.get("boundary_nodes") != 3 * sample.get("m") - 2:
        bad.append({"q": q, "check": "boundary_size", "sample": sample})
    if sample.get("boundary_cycle_lengths") != [sample.get("boundary_nodes")]:
        bad.append({"q": q, "check": "boundary_cycle", "sample": sample})
    if len(blocks) != len(formulas):
        bad.append({"q": q, "check": "block_count", "expected": len(formulas), "actual": len(blocks)})
    for index, (actual, formula) in enumerate(zip(blocks, formulas, strict=False)):
        block_bad, block_open_nulls = compare_block(q, index, actual, formula)
        bad.extend(block_bad)
        open_nulls.extend(block_open_nulls)
    return {
        "q": q,
        "m": sample.get("m"),
        "x": sample.get("x"),
        "z": sample.get("z"),
        "boundary_nodes": sample.get("boundary_nodes"),
        "boundary_cycle_lengths": sample.get("boundary_cycle_lengths"),
        "block_count": len(blocks),
        "ok": not bad,
        "bad_examples": bad[:10],
        "open_null_formula_fields": open_nulls[:20],
        "open_null_formula_field_count": len(open_nulls),
    }


def build_verification(cert: Path, q_values: list[int], binary: Path, compile_binary: bool) -> dict[str, Any]:
    data = json.loads(cert.read_text())
    formulas = data.get("q_ge_1_block_formula_fits", {}).get("blocks", [])
    if compile_binary:
        r42.compile_checker(binary)
    with tempfile.TemporaryDirectory(prefix="routeE-r42-block-regeneration-") as tmp:
        rows = [verify_q(binary, q, formulas, Path(tmp)) for q in q_values]
    return {
        "schema": "routeE_r42_block_formula_regeneration_verification_v1",
        "source": str(cert),
        "q_values": q_values,
        "raw_csv_preserved": False,
        "rows": rows,
        "ok": all(row.get("ok") for row in rows),
        "summary": {
            "verified_q_values": [row.get("q") for row in rows if row.get("ok")],
            "block_count": len(formulas),
            "all_boundary_single_cycle": all(
                row.get("boundary_cycle_lengths") == [row.get("boundary_nodes")]
                for row in rows
            ),
            "all_block_formulas_match_regeneration": all(row.get("ok") for row in rows),
            "open_null_formula_field_count": sum(
                row.get("open_null_formula_field_count", 0) for row in rows
            ),
        },
        "warning": (
            "This verifies regenerated finite R42 block tables against stored "
            "formulas.  It still does not prove no-early returns for all q."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cert", type=Path, default=DEFAULT_CERT)
    parser.add_argument("--q-values", default="1:5")
    parser.add_argument("--binary", type=Path, default=DEFAULT_BIN)
    parser.add_argument("--no-compile", action="store_true")
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    payload = build_verification(
        args.cert, parse_q_values(args.q_values), args.binary, not args.no_compile
    )
    print("schema", payload["schema"])
    print("ok", payload["ok"])
    print("verified_q_values", payload["summary"]["verified_q_values"])
    print("block_count", payload["summary"]["block_count"])
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")
    if not payload["ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
