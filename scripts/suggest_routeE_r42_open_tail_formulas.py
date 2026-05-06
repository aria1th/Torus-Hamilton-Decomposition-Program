#!/usr/bin/env python3
"""Suggest tail formulas for open R42 block-regeneration fields.

The R42 block-formula verifier treats missing `condition_interval_count`
formulas as optional compression debt.  This helper mines the regenerated
q-samples and records the linear tails that are visible from those open fields.
The output is not a proof; it is a proof-planning artifact for completing the
compact 29-block table.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_REGENERATION = (
    ROOT / "certs" / "routeE_r42_block_formula_regeneration_verification.json"
)


def formula_text(a: Fraction, b: Fraction) -> str:
    def term(coeff: Fraction, name: str) -> str | None:
        if coeff == 0:
            return None
        if coeff == 1:
            return name
        if coeff == -1:
            return f"-{name}"
        if coeff.denominator == 1:
            return f"{coeff.numerator}*{name}"
        return f"({coeff.numerator}/{coeff.denominator})*{name}"

    parts: list[str] = []
    qterm = term(a, "q")
    if qterm is not None:
        parts.append(qterm)
    if b:
        value = str(b.numerator) if b.denominator == 1 else f"{b.numerator}/{b.denominator}"
        if parts and b > 0:
            parts.append(f"+ {value}")
        elif parts:
            parts.append(f"- {abs(b.numerator) if b.denominator == 1 else abs(b)}")
        else:
            parts.append(value)
    return " ".join(parts) if parts else "0"


def fit_linear(points: list[tuple[int, int]]) -> dict[str, Any]:
    if len(points) < 2:
        return {"status": "single_sample_only"}
    (x0, y0), (x1, y1) = points[0], points[1]
    if x1 == x0:
        return {"status": "duplicate_q"}
    a = Fraction(y1 - y0, x1 - x0)
    b = Fraction(y0) - a * x0
    ok = all(a * x + b == y for x, y in points)
    return {
        "status": "linear_fit" if ok else "nonlinear_or_unstable",
        "formula": formula_text(a, b) if ok else None,
        "slope": str(a),
        "intercept": str(b),
    }


def collect_open_fields(data: dict[str, Any]) -> dict[tuple[int, str], list[tuple[int, int]]]:
    out: dict[tuple[int, str], list[tuple[int, int]]] = {}
    for row in data.get("rows", []):
        q = int(row["q"])
        for field in row.get("open_null_formula_fields", []):
            key = (int(field["index"]), str(field["field"]))
            out.setdefault(key, []).append((q, int(field["actual"])))
    return out


def build_suggestions(regeneration_path: Path) -> dict[str, Any]:
    data = json.loads(regeneration_path.read_text())
    suggestions = []
    for (index, field), points in sorted(collect_open_fields(data).items()):
        points = sorted(points)
        fit = fit_linear(points)
        suggestions.append(
            {
                "index": index,
                "field": field,
                "first_q": points[0][0],
                "sample_points": points,
                **fit,
            }
        )
    linear = [row for row in suggestions if row.get("status") == "linear_fit"]
    single = [row for row in suggestions if row.get("status") == "single_sample_only"]
    return {
        "schema": "routeE_r42_open_tail_formula_suggestions_v1",
        "source": str(regeneration_path),
        "source_q_values": data.get("summary", {}).get("verified_q_values"),
        "suggestions": suggestions,
        "summary": {
            "suggestion_count": len(suggestions),
            "linear_tail_count": len(linear),
            "single_sample_boundary_exception_count": len(single),
            "all_multi_sample_fields_linear": all(
                row.get("status") == "linear_fit"
                for row in suggestions
                if len(row.get("sample_points", [])) >= 2
            ),
        },
        "warning": (
            "These formulas are inferred from regenerated q-samples.  They are "
            "not a substitute for the pointwise first-return/no-early proof."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--regeneration", type=Path, default=DEFAULT_REGENERATION)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    payload = build_suggestions(args.regeneration)
    print("schema", payload["schema"])
    print("suggestion_count", payload["summary"]["suggestion_count"])
    print("linear_tail_count", payload["summary"]["linear_tail_count"])
    print(
        "single_sample_boundary_exception_count",
        payload["summary"]["single_sample_boundary_exception_count"],
    )
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
