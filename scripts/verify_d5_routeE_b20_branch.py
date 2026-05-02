#!/usr/bin/env python3
"""Verify the D5 even Route-E B20 branch candidate.

B20 is the branch ``m = 24*q + 20`` with slot zero and counts

    nu = (r, 0, 0, h+r, r),  h = m/2, r = (h-1)/3.

The expected first return on the Theta seam is the two-block map

    1 <= a <= h-2:   a |-> a + h + 1
    h-1 <= a <= m-1: a |-> a + h + 2

modulo ``m``.  This script checks that finite claim using the repo Route-E
small-seam verifier.  It is a regression artifact, not the symbolic proof.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import verify_d5_even_routeE as route_e


def b20_counts(m: int) -> tuple[int, int, int, int, int]:
    if m % 24 != 20:
        raise ValueError(f"B20 expects m == 20 mod 24, got {m}")
    h = m // 2
    r = (h - 1) // 3
    if 3 * r != h - 1:
        raise ValueError(f"B20 r is not integral for m={m}")
    return (r, 0, 0, h + r, r)


def expected_blocks(m: int) -> list[dict]:
    h = m // 2
    return [
        {"start": 1, "end": h - 2, "delta": h + 1, "length": h - 2},
        {"start": h - 1, "end": m - 1, "delta": h + 2, "length": h + 1},
    ]


def analyze_modulus(m: int) -> dict:
    counts = b20_counts(m)
    result = route_e.verify_small_seam_case(m, 0, counts)
    expected = expected_blocks(m)
    return {
        "m": m,
        "h": m // 2,
        "r": counts[0],
        "slot": 0,
        "counts": counts,
        "small_seam_ok": result["ok"],
        "cycle_lengths": result["cycle_lengths"],
        "return_time_sum": result["return_time_sum"],
        "expected_return_time_sum": result["expected_return_time_sum"],
        "return_time_sum_ok": result["return_time_sum"] == m**4,
        "translation_blocks": result["translation_blocks"],
        "expected_translation_blocks": expected,
        "translation_blocks_ok": result["translation_blocks"] == expected,
        "orbit_prefix_from_1": result["orbit_prefix_from_1"],
        "time_distribution": result["time_distribution"],
        "ok": result["ok"] and result["translation_blocks"] == expected,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--moduli",
        default="20,44",
        help="comma-separated B20 moduli; larger cases such as 68,92 are slower",
    )
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    moduli = route_e.parse_moduli(args.moduli)
    results = [analyze_modulus(m) for m in moduli]
    payload = {
        "schema": "d5_routeE_b20_branch_v1",
        "moduli": moduli,
        "all_ok": all(result["ok"] for result in results),
        "results": results,
    }

    for result in results:
        print(
            "m={m} counts={counts} small_ok={small_seam_ok} "
            "blocks_ok={translation_blocks_ok} sum_ok={return_time_sum_ok} "
            "blocks={translation_blocks}".format(**result)
        )
    print(f"all_ok={payload['all_ok']}")

    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")
    if not payload["all_ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
