#!/usr/bin/env python3
"""Verify the R42 mod-96 tail-refinement diagnostic."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_REFINEMENT = ROOT / "certs" / "routeE_r42_mod96_tail_refinement.json"


EXPECTED = {
    "R42-even-q": {
        0: (7, 57, 22, 35, 0),
        1: (0, 57, 22, 35, 0),
        2: (0, 22, 22, 0, 0),
    },
    "R42-odd-q": {
        0: (1, 57, 22, 35, 0),
        1: (0, 57, 22, 35, 0),
        2: (0, 22, 22, 0, 0),
    },
}


def build_verification(refinement_path: Path) -> dict[str, Any]:
    data = json.loads(refinement_path.read_text())
    errors: list[dict[str, Any]] = []
    for branch in data.get("branches", []):
        name = branch.get("name")
        expected_branch = EXPECTED.get(name)
        if expected_branch is None:
            errors.append({"unknown_branch": name})
            continue
        for tail in branch.get("tail_refinements", []):
            drop = tail.get("drop_first_sample_count")
            expected = expected_branch.get(drop)
            actual = (
                tail.get("target_bad_edge_count"),
                tail.get("qtime_bad_edge_count"),
                tail.get("qtime_missing_edge_count"),
                tail.get("qtime_nonaffine_edge_count"),
                tail.get("qsteps_bad_edge_count"),
            )
            if expected != actual:
                errors.append(
                    {
                        "branch": name,
                        "drop": drop,
                        "expected": expected,
                        "actual": actual,
                    }
                )
    ok = (
        data.get("schema") == "routeE_r42_mod96_tail_refinement_v1"
        and data.get("q_values") == [2, 3, 4, 5, 6, 7, 8, 9]
        and data.get("conclusion", {}).get(
            "target_coefficients_affine_after_dropping_first_generic_sample"
        )
        is True
        and data.get("conclusion", {}).get(
            "qtime_nonaffine_edges_removed_after_dropping_first_two_generic_samples"
        )
        is True
        and data.get("conclusion", {}).get(
            "remaining_qtime_missing_edges_after_two_drops"
        )
        == {"R42-even-q": 22, "R42-odd-q": 22}
        and data.get("promotion_impact", {}).get("closes_residue") is False
        and data.get("promotion_impact", {}).get("pointwise_equations_closed") is False
        and data.get("promotion_impact", {}).get("no_early_closed") is False
        and not errors
    )
    return {
        "schema": "routeE_r42_mod96_tail_refinement_verification_v1",
        "refinement": str(refinement_path),
        "ok": ok,
        "q_values": data.get("q_values"),
        "error_count": len(errors),
        "errors": errors[:20],
        "promotion_impact": data.get("promotion_impact"),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--refinement", type=Path, default=DEFAULT_REFINEMENT)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    payload = build_verification(args.refinement)
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
