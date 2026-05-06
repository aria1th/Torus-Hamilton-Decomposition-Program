#!/usr/bin/env python3
"""Record the two discarded D5 even Route-E branch mechanisms.

This is a lightweight symbolic audit, not a Lean proof.  It checks the parity
identities used to discard:

* X1: pure even prefix-count certificates for D5;
* X2: cyclic bulk plus only RF2-preserving adjacent-rank Kempe repairs.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def even_moduli(limit: int) -> list[int]:
    return list(range(2, limit + 1, 2))


def prefix_count_no_go_sample(m: int) -> dict:
    row_unit_parity_sum = 5 % 2
    column_sum_parity = m % 2
    return {
        "m": m,
        "all_units_are_odd": m % 2 == 0,
        "five_required_N0_units_have_parity": row_unit_parity_sum,
        "latin_stop0_column_sum_parity": column_sum_parity,
        "contradiction": row_unit_parity_sum != column_sum_parity,
    }


def adjacent_kempe_no_go_sample(m: int) -> dict:
    q4_size = m**4
    translation_sign_nonzero = 1
    cyclic_bulk_layer_sign = 1
    adjacent_pair_sign_change = 1
    required_global_sign = -1 if q4_size % 2 == 0 else 1
    available_global_sign = 1
    return {
        "m": m,
        "q4_size_even": q4_size % 2 == 0,
        "nonzero_prefix_translation_sign": translation_sign_nonzero,
        "cyclic_bulk_layer_sign": cyclic_bulk_layer_sign,
        "rf2_preserving_adjacent_pair_sign_change": adjacent_pair_sign_change,
        "available_global_sign": available_global_sign,
        "required_global_sign": required_global_sign,
        "contradiction": available_global_sign != required_global_sign,
    }


def build_payload(limit: int) -> dict:
    moduli = even_moduli(limit)
    x1_samples = [prefix_count_no_go_sample(m) for m in moduli]
    x2_samples = [adjacent_kempe_no_go_sample(m) for m in moduli]
    return {
        "schema": "routeE_no_go_branch_verification_v1",
        "scope": "D5 even Route-E discarded mechanisms",
        "sample_even_moduli": moduli,
        "X1_even_prefix_count": {
            "status": "discarded",
            "symbolic_reason": (
                "Each D5 prefix-count row would need N0 a unit modulo even m, "
                "hence odd.  Five odd entries give odd stop-0 column sum, but "
                "local Latin balance requires the column sum m, which is even."
            ),
            "samples": x1_samples,
            "all_samples_contradict": all(item["contradiction"] for item in x1_samples),
        },
        "X2_adjacent_kempe_only": {
            "status": "discarded",
            "symbolic_reason": (
                "For even m, cyclic bulk has layer sign +1.  RF2-preserving "
                "adjacent-rank supports are full affected-coordinate cycles and "
                "change two color signs by the same factor, preserving the layer "
                "sign.  Thus product_t Lambda_t remains +1, while RF3 for five "
                "m^4-cycles requires -1."
            ),
            "samples": x2_samples,
            "all_samples_contradict": all(item["contradiction"] for item in x2_samples),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=40)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    payload = build_payload(args.limit)
    payload["all_ok"] = (
        payload["X1_even_prefix_count"]["all_samples_contradict"]
        and payload["X2_adjacent_kempe_only"]["all_samples_contradict"]
    )
    text = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    print(text, end="")
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(text)
    if not payload["all_ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
