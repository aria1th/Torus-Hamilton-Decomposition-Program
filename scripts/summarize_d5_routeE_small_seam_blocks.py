#!/usr/bin/env python3
"""Summarize D5 Route-E small-seam translation-block traces.

The full verifier records, for each even m in the absorbed small-seam table,
the first-return map on the seam parameter a=1..m-1.  This script compresses
those traces into proof-facing block statistics: maximal intervals on which
V(a)-a is constant, low-complexity cases, and block-length fingerprints.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path

import verify_d5_even_routeE as route_e


def load_or_compute(path: Path | None) -> list[dict]:
    if path is not None:
        payload = json.loads(path.read_text())
        if isinstance(payload, dict) and "small_seam" in payload:
            return payload["small_seam"]
        if isinstance(payload, list):
            return payload
        raise ValueError("expected a verifier JSON object with small_seam or a result list")
    return route_e.verify_small_seam_cases(sorted(route_e.SMALL_SEAM_CASES))


def case_summary(case: dict) -> dict:
    m = case["m"]
    blocks = case.get("translation_blocks", [])
    lengths = [block["length"] for block in blocks]
    deltas = [block["delta"] for block in blocks]
    length_hist = Counter(lengths)
    delta_hist = Counter(deltas)
    long_blocks = [
        block for block in blocks if block["length"] >= max(2, (m - 1 + 3) // 4)
    ]
    return {
        "m": m,
        "ok": case.get("ok", False),
        "slot": case.get("slot"),
        "counts": case.get("counts"),
        "normalized_counts_slot0": route_e.normalize_counts_to_slot0(
            case["slot"], tuple(case["counts"])
        ),
        "seam_size": case.get("seam_size"),
        "return_time_sum": case.get("return_time_sum"),
        "expected_return_time_sum": case.get("expected_return_time_sum"),
        "block_count": len(blocks),
        "max_block_length": max(lengths) if lengths else 0,
        "singleton_blocks": length_hist.get(1, 0),
        "non_singleton_blocks": len(blocks) - length_hist.get(1, 0),
        "length_histogram": dict(sorted(length_hist.items())),
        "delta_histogram_top": [
            {"delta": delta, "count": count}
            for delta, count in delta_hist.most_common(8)
        ],
        "long_blocks": long_blocks,
        "orbit_prefix_from_1": case.get("orbit_prefix_from_1", []),
    }


def summarize(cases: list[dict]) -> dict:
    summaries = [case_summary(case) for case in sorted(cases, key=lambda c: c["m"])]
    low_block_cases = [
        item for item in summaries if item["ok"] and item["block_count"] <= 10
    ]
    long_block_cases = [
        item for item in summaries if item["ok"] and item["max_block_length"] >= item["m"] // 4
    ]
    mostly_singleton_cases = [
        item
        for item in summaries
        if item["ok"] and item["singleton_blocks"] * 2 >= item["block_count"]
    ]
    return {
        "source": "verify_d5_even_routeE.SMALL_SEAM_CASES",
        "case_count": len(summaries),
        "all_ok": all(item["ok"] for item in summaries),
        "return_sums_ok": all(
            item["return_time_sum"] == item["expected_return_time_sum"]
            for item in summaries
        ),
        "moduli": [item["m"] for item in summaries],
        "block_count_by_m": {
            str(item["m"]): item["block_count"] for item in summaries
        },
        "low_block_cases": [
            {
                "m": item["m"],
                "block_count": item["block_count"],
                "max_block_length": item["max_block_length"],
                "normalized_counts_slot0": item["normalized_counts_slot0"],
                "long_blocks": item["long_blocks"],
            }
            for item in low_block_cases
        ],
        "long_block_cases": [
            {
                "m": item["m"],
                "block_count": item["block_count"],
                "max_block_length": item["max_block_length"],
                "long_blocks": item["long_blocks"],
            }
            for item in long_block_cases
        ],
        "mostly_singleton_moduli": [item["m"] for item in mostly_singleton_cases],
        "cases": summaries,
    }


def print_text(summary: dict) -> None:
    print(
        "cases",
        summary["case_count"],
        "all_ok",
        summary["all_ok"],
        "return_sums_ok",
        summary["return_sums_ok"],
    )
    print("m block_count max_block singleton non_singleton")
    for item in summary["cases"]:
        print(
            item["m"],
            item["block_count"],
            item["max_block_length"],
            item["singleton_blocks"],
            item["non_singleton_blocks"],
        )
    print("low_block_moduli", [item["m"] for item in summary["low_block_cases"]])
    print("long_block_moduli", [item["m"] for item in summary["long_block_cases"]])


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--verify-json",
        type=Path,
        help="reuse JSON emitted by verify_d5_even_routeE.py --small-seam-moduli",
    )
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    summary = summarize(load_or_compute(args.verify_json))
    print_text(summary)
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
