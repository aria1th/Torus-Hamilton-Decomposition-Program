#!/usr/bin/env python3
"""Verify the R42 qtime interval-profile diagnostic."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PROFILES = ROOT / "certs" / "routeE_r42_qtime_interval_profiles.json"
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


def build_verification(profiles_path: Path) -> dict[str, Any]:
    data = json.loads(profiles_path.read_text())
    errors = []
    expected_counts = {"6": 22, "7": 22, "8": 22, "9": 22}
    for sample in data.get("samples", []):
        q = str(sample.get("q"))
        if sample.get("nonaffine_edge_count") != expected_counts.get(q):
            errors.append(
                {
                    "q": sample.get("q"),
                    "expected_nonaffine_edge_count": expected_counts.get(q),
                    "actual": sample.get("nonaffine_edge_count"),
                }
            )
        if sample.get("bad_interval_count") != 0:
            errors.append(
                {
                    "q": sample.get("q"),
                    "bad_interval_count": sample.get("bad_interval_count"),
                }
            )
    branches = {branch.get("name"): branch for branch in data.get("generic_subbranches", [])}
    for name, branch in branches.items():
        if branch.get("edge_count") != 22:
            errors.append({"branch": name, "edge_count": branch.get("edge_count")})
        for row in branch.get("edge_interval_formulas", []):
            for sample in row.get("sample_points", []):
                interval_expected = eval_formula(
                    row.get("interval_count_formula"), int(sample["s"])
                )
                member_expected = eval_formula(
                    row.get("member_count_formula"), int(sample["s"])
                )
                if interval_expected != sample.get("interval_count"):
                    errors.append(
                        {
                            "branch": name,
                            "src": row.get("src"),
                            "dst": row.get("dst"),
                            "kind": "interval_count",
                            "s": sample.get("s"),
                            "expected": interval_expected,
                            "actual": sample.get("interval_count"),
                        }
                    )
                if member_expected != sample.get("member_count"):
                    errors.append(
                        {
                            "branch": name,
                            "src": row.get("src"),
                            "dst": row.get("dst"),
                            "kind": "member_count",
                            "s": sample.get("s"),
                            "expected": member_expected,
                            "actual": sample.get("member_count"),
                        }
                    )
    ok = (
        data.get("schema") == "routeE_r42_qtime_interval_profiles_v1"
        and data.get("q_values") == [6, 7, 8, 9]
        and data.get("summary", {}).get("all_samples_ok") is True
        and data.get("summary", {}).get("all_nonaffine_edges_interval_affine") is True
        and data.get("summary", {}).get("all_interval_counts_affine_in_s") is True
        and data.get("summary", {}).get("all_member_counts_affine_in_s") is True
        and data.get("summary", {}).get("branch_multi_point_interval_edge_counts")
        == {"R42-even-q": 1, "R42-odd-q": 1}
        and data.get("summary", {}).get("nonaffine_edge_counts") == expected_counts
        and data.get("summary", {}).get("bad_interval_counts")
        == {"6": 0, "7": 0, "8": 0, "9": 0}
        and data.get("promotion_impact", {}).get("closes_residue") is False
        and data.get("promotion_impact", {}).get("pointwise_equations_closed") is False
        and data.get("promotion_impact", {}).get("no_early_closed") is False
        and not errors
    )
    return {
        "schema": "routeE_r42_qtime_interval_profiles_verification_v1",
        "profiles": str(profiles_path),
        "ok": ok,
        "q_values": data.get("q_values"),
        "error_count": len(errors),
        "errors": errors[:20],
        "promotion_impact": data.get("promotion_impact"),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--profiles", type=Path, default=DEFAULT_PROFILES)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    payload = build_verification(args.profiles)
    print("schema", payload["schema"])
    print("ok", payload["ok"])
    print("q_values", payload["q_values"])
    print("error_count", payload["error_count"])
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")
    if not payload["ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
