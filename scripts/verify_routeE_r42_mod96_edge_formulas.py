#!/usr/bin/env python3
"""Verify the R42 mod-96 block-edge formula table."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_FORMULAS = ROOT / "certs" / "routeE_r42_mod96_edge_formulas.json"
FORMULA_RE = re.compile(r"^\s*([+-]?\d+)?\*?s(?:\s*([+-])\s*(\d+))?\s*$")


def eval_formula(expr: str | None, s: int) -> int | None:
    if expr is None:
        return None
    expr = str(expr).strip()
    if "s" not in expr:
        return int(expr)
    if expr == "s":
        return s
    match = FORMULA_RE.match(expr)
    if match is None:
        raise ValueError(f"unsupported formula: {expr!r}")
    coeff = match.group(1)
    slope = int(coeff) if coeff not in {None, "", "+"} else 1
    value = slope * s
    if match.group(2):
        term = int(match.group(3))
        value += term if match.group(2) == "+" else -term
    return value


def build_verification(formulas_path: Path) -> dict[str, Any]:
    data = json.loads(formulas_path.read_text())
    errors = []
    for row in data.get("edge_formulas", []):
        for branch_key in ["even_q_branch", "odd_q_branch"]:
            branch = row[branch_key]
            for s, actual in branch.get("sample_points_s", []):
                expected = eval_formula(branch.get("formula"), int(s))
                if expected != actual:
                    errors.append(
                        {
                            "src": row.get("src"),
                            "dst": row.get("dst"),
                            "branch": branch_key,
                            "s": s,
                            "formula": branch.get("formula"),
                            "expected": expected,
                            "actual": actual,
                        }
                    )
    ok = (
        data.get("schema") == "routeE_r42_mod96_edge_formulas_v1"
        and data.get("edge_count") == 69
        and data.get("summary", {}).get("all_even_branch_formulas_affine_in_s")
        is True
        and data.get("summary", {}).get("all_odd_branch_formulas_affine_in_s")
        is True
        and data.get("summary", {}).get("even_sample_s_values") == [1, 2, 3]
        and data.get("summary", {}).get("odd_sample_s_values") == [1, 2]
        and not errors
        and data.get("promotion_impact", {}).get("closes_residue") is False
    )
    return {
        "schema": "routeE_r42_mod96_edge_formulas_verification_v1",
        "formulas": str(formulas_path),
        "ok": ok,
        "edge_count": data.get("edge_count"),
        "error_count": len(errors),
        "errors": errors[:20],
        "promotion_impact": data.get("promotion_impact"),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--formulas", type=Path, default=DEFAULT_FORMULAS)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    payload = build_verification(args.formulas)
    print("schema", payload["schema"])
    print("ok", payload["ok"])
    print("edge_count", payload["edge_count"])
    print("error_count", payload["error_count"])
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")
    if not payload["ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
