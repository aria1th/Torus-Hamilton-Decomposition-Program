#!/usr/bin/env python3
"""Verify compact generated all-zero-set 4+2 formula witnesses.

The full kappa table has size m * m^4.  For generated witnesses whose kappa is
given by a rotation formula, this wrapper keeps the committed certificate small:
it validates the row/base-word shape, optionally reruns the Target-A section
audit, and delegates section/product cycle checks to the C++ formula checker.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import tempfile
from pathlib import Path

from analyze_4plus2_base_rows import (
    base_word_count_summary,
    diagnose_column_exact_cover,
    parse_word,
)
from analyze_targetA_section import analyze_word


DEFAULT_CERT = (
    Path(__file__).resolve().parents[1]
    / "certs"
    / "d7_4plus2_compact_formula_witnesses.json"
)
DEFAULT_CHECKER_SRC = (
    Path(__file__).resolve().parent / "fast_4plus2_section_formula_search.cpp"
)


def row_base_projection(row: str) -> str:
    return "".join(ch for ch in row if ch in "01234")


def formula_arg(formula: dict) -> str:
    if formula.get("family") != "rotation":
        raise ValueError("only rotation formulas are supported by the compact checker")
    reflected = 1 if formula.get("reflected") else 0
    return ",".join(
        str(int(formula[key])) for key in ("a", "b", "c", "d")
    ) + f",{reflected}"


def validate_witness_shape(witness: dict) -> dict:
    name = witness.get("name", "<unnamed>")
    m = witness.get("m")
    rows = witness.get("rows")
    base_words = witness.get("base_words")
    if not isinstance(m, int) or m <= 0:
        raise ValueError(f"{name}: m must be a positive integer")
    if not isinstance(rows, list) or len(rows) != 7:
        raise ValueError(f"{name}: expected seven full rows")
    if not isinstance(base_words, list) or len(base_words) != 7:
        raise ValueError(f"{name}: expected seven base words")
    for row_index, row in enumerate(rows):
        if not isinstance(row, str) or len(row) != m:
            raise ValueError(f"{name}: row {row_index} must be a string of length m")
        if any(ch not in "0123456" for ch in row):
            raise ValueError(f"{name}: row {row_index} has an entry outside 0..6")
    for word_index, word in enumerate(base_words):
        if not isinstance(word, str):
            raise ValueError(f"{name}: base word {word_index} must be a string")
        parse_word(word)
        projection = row_base_projection(rows[word_index])
        if projection != word:
            raise ValueError(
                f"{name}: row {word_index} projects to {projection}, expected {word}"
            )
    for layer in range(m):
        column = sorted(int(row[layer]) for row in rows)
        if column != list(range(7)):
            raise ValueError(f"{name}: column {layer} is not a permutation of 0..6")
    words = [parse_word(word) for word in base_words]
    count_summary = base_word_count_summary(m, words)
    if not count_summary["total_length_ok"] or not count_summary["slot_counts_ok"]:
        raise ValueError(f"{name}: base-word counts are not balanced")
    return {
        "name": name,
        "m": m,
        "rows_arg": ",".join(rows),
        "formula_arg": formula_arg(witness["formula"]),
        "count_summary": count_summary,
    }


def compile_checker(source: Path, output: Path) -> None:
    subprocess.run(
        ["g++", "-std=c++17", "-O3", str(source), "-o", str(output)],
        check=True,
    )


def run_cpp_checker(
    checker: Path,
    m: int,
    rows_arg: str,
    formula: str,
    *,
    product: bool,
) -> str:
    cmd = [
        str(checker),
        "--m",
        str(m),
        "--rows",
        rows_arg,
        "--formula",
        formula,
    ]
    if product:
        cmd.append("--verify-product")
    result = subprocess.run(cmd, check=True, text=True, capture_output=True)
    return result.stdout.strip()


def target_a_summary(witness: dict) -> dict:
    m = witness["m"]
    words = [parse_word(word) for word in witness["base_words"]]
    analyses = [analyze_word(m, word, include_records=False) for word in words]
    column = diagnose_column_exact_cover(m, words)
    return {
        "all_base_single": all(item["base_single_cycle"] for item in analyses),
        "all_section_single": all(item["section_single_cycle"] for item in analyses),
        "return_time_sums": sorted({item["return_time_sum"] for item in analyses}),
        "all_segment_cover": all(
            item["segment_coverage"]["covers_all_states_once"] for item in analyses
        ),
        "column_target_reached": column["target_reached"],
        "column_max_depth": column["max_depth"],
        "column_reachable_states": column["reachable_states"],
        "column_truncated": column["truncated"],
    }


def select_witnesses(payload: dict, only: set[int] | None) -> list[dict]:
    witnesses = payload.get("witnesses")
    if not isinstance(witnesses, list):
        raise ValueError("certificate JSON must contain a witnesses list")
    if only is None:
        return witnesses
    return [witness for witness in witnesses if witness.get("m") in only]


def parse_only(value: str | None) -> set[int] | None:
    if value is None:
        return None
    return {int(part) for part in value.split(",") if part}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cert-json", type=Path, default=DEFAULT_CERT)
    parser.add_argument("--only", help="comma-separated moduli to verify")
    parser.add_argument(
        "--checker-src",
        type=Path,
        default=DEFAULT_CHECKER_SRC,
        help="C++ checker source to compile",
    )
    parser.add_argument(
        "--checker-bin",
        type=Path,
        help="precompiled checker binary; if omitted, compile to a temporary path",
    )
    parser.add_argument(
        "--target-a",
        action="store_true",
        help="rerun the Target-A section and column exact-cover audits",
    )
    parser.add_argument(
        "--product",
        action="store_true",
        help="also run direct product-return single-cycle checks",
    )
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    payload = json.loads(args.cert_json.read_text())
    selected = select_witnesses(payload, parse_only(args.only))
    if not selected:
        raise ValueError("no witnesses selected")

    with tempfile.TemporaryDirectory() as tmp_dir:
        checker = args.checker_bin or Path(tmp_dir) / "fast_4plus2_section_formula_search"
        if args.checker_bin is None:
            compile_checker(args.checker_src, checker)
        results = []
        for witness in selected:
            shape = validate_witness_shape(witness)
            cpp_output = run_cpp_checker(
                checker,
                shape["m"],
                shape["rows_arg"],
                shape["formula_arg"],
                product=args.product,
            )
            result = {
                "name": shape["name"],
                "m": shape["m"],
                "count_summary": shape["count_summary"],
                "formula": witness["formula"],
                "cpp_checker_output": cpp_output.splitlines(),
            }
            if args.target_a:
                result["target_a"] = target_a_summary(witness)
            results.append(result)

    out = {
        "description": "Compact all-zero-set 4+2 formula witness verification.",
        "cert_json": str(args.cert_json),
        "target_a_checked": args.target_a,
        "product_checked": args.product,
        "results": results,
    }
    text = json.dumps(out, indent=2, sort_keys=True)
    if args.json_out is None:
        print(text)
    else:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(text + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
