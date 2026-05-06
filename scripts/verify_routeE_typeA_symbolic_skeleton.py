#!/usr/bin/env python3
"""Verify Route-E Type-A symbolic skeleton polynomial identities.

The B16/R14e closure packages use `sympy` in their original verifier scripts,
but this repository environment does not assume that dependency.  This script
implements a tiny one-variable integer-polynomial checker using only the Python
standard library and verifies the mass/count identities preserved in
`certs/routeE_typeA_symbolic_skeleton.json`.
"""

from __future__ import annotations

import argparse
import ast
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SKELETON = ROOT / "certs" / "routeE_typeA_symbolic_skeleton.json"

Poly = dict[int, int]


def trim(poly: Poly) -> Poly:
    return {degree: coeff for degree, coeff in poly.items() if coeff}


def const(value: int) -> Poly:
    return {} if value == 0 else {0: value}


def var() -> Poly:
    return {1: 1}


def add(a: Poly, b: Poly) -> Poly:
    out = dict(a)
    for degree, coeff in b.items():
        out[degree] = out.get(degree, 0) + coeff
    return trim(out)


def neg(a: Poly) -> Poly:
    return {degree: -coeff for degree, coeff in a.items()}


def sub(a: Poly, b: Poly) -> Poly:
    return add(a, neg(b))


def mul(a: Poly, b: Poly) -> Poly:
    out: Poly = {}
    for da, ca in a.items():
        for db, cb in b.items():
            out[da + db] = out.get(da + db, 0) + ca * cb
    return trim(out)


def pow_poly(a: Poly, exponent: int) -> Poly:
    if exponent < 0:
        raise ValueError("negative exponents are not supported")
    out = const(1)
    base = a
    exp = exponent
    while exp:
        if exp & 1:
            out = mul(out, base)
        base = mul(base, base)
        exp >>= 1
    return out


def parse_poly(text: str, variable: str) -> Poly:
    tree = ast.parse(text, mode="eval")

    def go(node: ast.AST) -> Poly:
        if isinstance(node, ast.Expression):
            return go(node.body)
        if isinstance(node, ast.Constant) and isinstance(node.value, int):
            return const(node.value)
        if isinstance(node, ast.Name) and node.id == variable:
            return var()
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return neg(go(node.operand))
        if isinstance(node, ast.BinOp):
            if isinstance(node.op, ast.Add):
                return add(go(node.left), go(node.right))
            if isinstance(node.op, ast.Sub):
                return sub(go(node.left), go(node.right))
            if isinstance(node.op, ast.Mult):
                return mul(go(node.left), go(node.right))
            if isinstance(node.op, ast.Pow):
                right = go(node.right)
                if set(right) - {0}:
                    raise ValueError(f"nonconstant exponent in {text!r}")
                return pow_poly(go(node.left), right.get(0, 0))
        raise ValueError(f"unsupported polynomial expression {text!r}: {ast.dump(node)}")

    return go(tree)


def sum_polys(values: list[str], variable: str) -> Poly:
    total: Poly = {}
    for value in values:
        total = add(total, parse_poly(value, variable))
    return total


def equal_poly(left: str | Poly, right: str | Poly, variable: str) -> bool:
    a = parse_poly(left, variable) if isinstance(left, str) else left
    b = parse_poly(right, variable) if isinstance(right, str) else right
    return trim(a) == trim(b)


def verify_b16(data: dict[str, Any]) -> dict[str, Any]:
    label_sum = data["label_sum_polynomials"]
    label_dst = data["label_dst_sum_polynomials"]
    label_total = sum_polys(list(label_sum.values()), "q")
    dst_total = sum_polys(list(label_dst.values()), "q")
    m4 = parse_poly(data["m4_poly"], "q")
    return {
        "label_entry_count": len(label_sum),
        "label_dst_entry_count": len(label_dst),
        "label_total_matches_recorded": equal_poly(
            label_total, data["total_poly_from_labels"], "q"
        ),
        "label_dst_total_matches_recorded": equal_poly(
            dst_total, data["total_poly_from_label_dst"], "q"
        ),
        "label_total_equals_m4": trim(label_total) == trim(m4),
        "label_dst_total_equals_m4": trim(dst_total) == trim(m4),
        "recorded_flags_true": data["label_total_equals_m4"]
        and data["label_dst_total_equals_m4"],
    }


def verify_r14e(data: dict[str, Any]) -> dict[str, Any]:
    label_time_values = [item["time_poly"] for item in data["label_sum_polynomials"]]
    dst_time_values = [item["time_poly"] for item in data["label_dst_sum_polynomials"]]
    dst_count_values = [item["count_poly"] for item in data["label_dst_sum_polynomials"]]
    insertion_weighted_values = []
    insertion_count_values = []
    for key, count_poly in data["expected_insertion_bylabel"].items():
        _label, length = key.split(":", 1)
        insertion_count_values.append(count_poly)
        insertion_weighted_values.append(f"({length})*({count_poly})")

    label_total = sum_polys(label_time_values, "k")
    dst_total = sum_polys(dst_time_values, "k")
    dst_count_total = sum_polys(dst_count_values, "k")
    insertion_count_total = sum_polys(insertion_count_values, "k")
    insertion_weighted_total = sum_polys(insertion_weighted_values, "k")
    m4 = parse_poly(data["m4_poly"], "k")
    allpair_size = parse_poly(data["expected_allpair_size"], "k")
    boundary_size = parse_poly(data["expected_boundary_size"], "k")
    return {
        "label_entry_count": len(data["label_sum_polynomials"]),
        "label_dst_entry_count": len(data["label_dst_sum_polynomials"]),
        "insertion_entry_count": len(data["expected_insertion_bylabel"]),
        "label_total_matches_recorded": equal_poly(
            label_total, data["total_poly_from_labels"], "k"
        ),
        "label_dst_total_matches_recorded": equal_poly(
            dst_total, data["total_poly_from_label_dst"], "k"
        ),
        "label_total_equals_m4": trim(label_total) == trim(m4),
        "label_dst_total_equals_m4": trim(dst_total) == trim(m4),
        "label_dst_count_matches_recorded": equal_poly(
            dst_count_total, data["label_dst_count_total"], "k"
        ),
        "label_dst_count_equals_allpair_size": trim(dst_count_total)
        == trim(allpair_size),
        "insertion_count_equals_boundary_size": trim(insertion_count_total)
        == trim(boundary_size),
        "insertion_weighted_matches_recorded": equal_poly(
            insertion_weighted_total, data["expected_insertion_weighted_sum"], "k"
        ),
        "insertion_weighted_equals_allpair_size": trim(insertion_weighted_total)
        == trim(allpair_size),
        "macro_symbolics_match": (
            data["insertion_macro_symbolic"]["boundary_count"]
            == data["expected_insertion_boundary_count"]
            and data["insertion_macro_symbolic"]["boundary_size"]
            == data["expected_boundary_size"]
            and data["insertion_macro_symbolic"]["weighted_steps"]
            == data["expected_insertion_weighted_sum"]
            and data["insertion_macro_symbolic"]["allpair_size"]
            == data["expected_allpair_size"]
        ),
        "recorded_flags_true": (
            data["label_total_equals_m4"]
            and data["label_dst_total_equals_m4"]
            and data["label_dst_count_equals_allpair_size"]
            and data["expected_insertion_weighted_equals_allpair_size"]
        ),
    }


def all_true(payload: dict[str, Any]) -> bool:
    return all(value is True or not key.endswith(("equals_m4", "matches_recorded", "flags_true", "equals_allpair_size", "equals_boundary_size", "symbolics_match")) for key, value in payload.items())


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--skeleton", type=Path, default=DEFAULT_SKELETON)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    skeleton = json.loads(args.skeleton.read_text())
    b16 = verify_b16(skeleton["b16"])
    r14e = verify_r14e(skeleton["r14e"])
    checks = [
        b16["label_total_matches_recorded"],
        b16["label_dst_total_matches_recorded"],
        b16["label_total_equals_m4"],
        b16["label_dst_total_equals_m4"],
        b16["recorded_flags_true"],
        r14e["label_total_matches_recorded"],
        r14e["label_dst_total_matches_recorded"],
        r14e["label_total_equals_m4"],
        r14e["label_dst_total_equals_m4"],
        r14e["label_dst_count_matches_recorded"],
        r14e["label_dst_count_equals_allpair_size"],
        r14e["insertion_count_equals_boundary_size"],
        r14e["insertion_weighted_matches_recorded"],
        r14e["insertion_weighted_equals_allpair_size"],
        r14e["macro_symbolics_match"],
        r14e["recorded_flags_true"],
    ]
    payload = {
        "schema": "routeE_typeA_symbolic_skeleton_verification_v1",
        "skeleton": str(args.skeleton),
        "b16": b16,
        "r14e": r14e,
        "all_ok": all(checks),
    }
    print("all_ok", payload["all_ok"])
    print("b16", b16)
    print("r14e", r14e)
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")
    if not payload["all_ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
