#!/usr/bin/env python3
"""Verify that R42 boundary block formulas expand to all-pair label counts.

The R42 boundary quotient summary records a stable 29-block first-return table
for q >= 1.  Each boundary block has:

* a condition-count formula, giving how many boundary nodes use the block;
* run-count formulas for the all-pair labels encountered before the next
  boundary hit.

This verifier checks that the committed boundary block formulas expand to the
same all-pair source-label counts recorded by the all-pair time-fit artifact.
It is a bridge artifact for the boundary/transducer proof route; it is not a
pointwise first-return/no-early proof.
"""

from __future__ import annotations

import argparse
import ast
import json
from fractions import Fraction
from pathlib import Path
from typing import Any

from summarize_routeE_r42_allpair_time_fits import LABELS


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_BOUNDARY = ROOT / "certs" / "routeE_r42_boundary_quotient_summary.json"
DEFAULT_ALLPAIR_TIME = ROOT / "certs" / "routeE_r42_allpair_time_fit_summary.json"


class FormulaError(ValueError):
    pass


def eval_ast(node: ast.AST, q: Fraction) -> Fraction:
    if isinstance(node, ast.Expression):
        return eval_ast(node.body, q)
    if isinstance(node, ast.Constant) and isinstance(node.value, int):
        return Fraction(node.value)
    if isinstance(node, ast.Name) and node.id == "q":
        return q
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        return -eval_ast(node.operand, q)
    if isinstance(node, ast.BinOp):
        left = eval_ast(node.left, q)
        right = eval_ast(node.right, q)
        if isinstance(node.op, ast.Add):
            return left + right
        if isinstance(node.op, ast.Sub):
            return left - right
        if isinstance(node.op, ast.Mult):
            return left * right
        if isinstance(node.op, ast.Div):
            return left / right
        if isinstance(node.op, ast.Pow):
            if right.denominator != 1 or right < 0:
                raise FormulaError("non-natural power")
            return left ** right.numerator
    raise FormulaError(f"unsupported formula node: {ast.dump(node)}")


def eval_formula(text: str | None, q_value: int) -> int:
    if text is None:
        raise FormulaError("missing formula")
    parsed = ast.parse(text.replace("^", "**"), mode="eval")
    value = eval_ast(parsed, Fraction(q_value))
    if value.denominator != 1:
        raise FormulaError(f"formula {text!r} is non-integral at q={q_value}")
    return value.numerator


def expand_boundary_blocks(blocks: list[dict[str, Any]], q_value: int) -> dict[str, int]:
    counts = {label: 0 for label in LABELS}
    for block in blocks:
        condition_count = eval_formula(block.get("condition_count"), q_value)
        for run in block.get("path_run_counts", []):
            label = run["label"]
            run_count = eval_formula(run.get("count"), q_value)
            counts[label] += condition_count * run_count
    return counts


def expected_label_counts(fits: dict[str, Any], q_value: int) -> dict[str, int]:
    label_fits = fits.get("fits", {}).get("label_count", {})
    return {
        label: eval_formula(label_fits[label]["formula"], q_value)
        for label in LABELS
    }


def build_verification(
    boundary_path: Path,
    allpair_time_path: Path,
    q_values: list[int],
) -> dict[str, Any]:
    boundary = json.loads(boundary_path.read_text())
    allpair_time = json.loads(allpair_time_path.read_text())
    blocks = boundary.get("q_ge_1_block_formula_fits", {}).get("blocks", [])
    rows = []
    for q_value in q_values:
        expanded = expand_boundary_blocks(blocks, q_value)
        expected = expected_label_counts(allpair_time, q_value)
        rows.append(
            {
                "q": q_value,
                "m": 48 * q_value + 42,
                "expanded_label_counts": expanded,
                "expected_label_counts": expected,
                "label_counts_match": expanded == expected,
                "difference_expected_minus_expanded": {
                    label: expected[label] - expanded.get(label, 0)
                    for label in LABELS
                    if expected[label] != expanded.get(label, 0)
                },
                "expanded_total": sum(expanded.values()),
                "expected_total": 10 * ((48 * q_value + 42) - 1) + 1,
                "total_matches": sum(expanded.values())
                == 10 * ((48 * q_value + 42) - 1) + 1,
            }
        )
    return {
        "schema": "routeE_r42_boundary_expansion_verification_v1",
        "boundary_summary": str(boundary_path),
        "allpair_time_summary": str(allpair_time_path),
        "q_values": q_values,
        "block_count": len(blocks),
        "rows": rows,
        "ok": (
            boundary.get("q_ge_1_block_formula_fits", {}).get(
                "stable_structural_keys"
            )
            is True
            and len(blocks) == 29
            and all(row["label_counts_match"] and row["total_matches"] for row in rows)
        ),
        "note": (
            "The boundary summary preserves boundary segment path-run counts, "
            "including the unique Z>13 path, so expansion to all-pair "
            "source-label counts is direct."
        ),
        "promotion_impact": {
            "supports_boundary_transducer_route": True,
            "pointwise_equations_closed": False,
            "no_early_closed": False,
        },
    }


def parse_q_values(text: str) -> list[int]:
    if ":" in text:
        start, stop = [int(part) for part in text.split(":", 1)]
        return list(range(start, stop + 1))
    return [int(part) for part in text.split(",") if part.strip()]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--boundary", type=Path, default=DEFAULT_BOUNDARY)
    parser.add_argument("--allpair-time", type=Path, default=DEFAULT_ALLPAIR_TIME)
    parser.add_argument("--q-values", default="1:6")
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    payload = build_verification(
        args.boundary,
        args.allpair_time,
        parse_q_values(args.q_values),
    )
    print("schema", payload["schema"])
    print("ok", payload["ok"])
    print("block_count", payload["block_count"])
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")
    if not payload["ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
