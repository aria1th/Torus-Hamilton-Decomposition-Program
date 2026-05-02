#!/usr/bin/env python3
"""Search constrained D5 even Route-E small-seam candidates.

This is a research tool.  It avoids the expensive full `m^4` one-Lambda_E
cycle scan when possible by searching constrained count families and checking
the proof-facing small-seam criterion directly.
"""
from __future__ import annotations

import argparse
import json
from itertools import combinations
from math import gcd
from pathlib import Path
from typing import Iterable, List, Tuple

import verify_d5_even_routeE as route_e

CountVec = Tuple[int, int, int, int, int]


def parse_moduli(text: str) -> List[int]:
    return [int(part) for part in text.split(",") if part.strip()]


def parse_support_pattern(text: str | None) -> Tuple[int, ...] | None:
    if text is None or text.strip() == "":
        return None
    pattern = tuple(int(part) for part in text.split(",") if part.strip())
    if len(set(pattern)) != len(pattern) or any(index < 0 or index >= 5 for index in pattern):
        raise ValueError("support pattern must be distinct indices in 0..4")
    return pattern


def normalized_summary(counts: CountVec) -> dict:
    return {
        "counts": counts,
        "support": [i for i, count in enumerate(counts) if count != 0],
        "zero_positions": [i for i, count in enumerate(counts) if count == 0],
        "support_count": sum(1 for count in counts if count != 0),
        "open_port_normal_form": counts[0] == 0 and counts[4] == 0,
    }


def open_port_section_candidates(m: int) -> Iterable[dict]:
    """Yield normalized slot-zero open-port candidates passing section checks."""
    for c_count in range(1, m):
        if gcd(c_count, m) != 1:
            continue
        for a_count in range(m - c_count):
            b_count = m - 1 - a_count - c_count
            section = route_e.check_section_case(m, a_count, b_count, c_count)
            if not (
                section["C_unit"]
                and section["section_formula_ok"]
                and section["H_single"]
            ):
                continue
            counts = (0, a_count, b_count, c_count, 0)
            yield {
                "m": m,
                "slot": 0,
                "A": a_count,
                "B": b_count,
                "C": c_count,
                **normalized_summary(counts),
                "section": section,
            }


def weak_compositions_positive(total: int, parts: int):
    if parts == 1:
        if total >= 1:
            yield (total,)
        return
    for value in range(1, total - parts + 2):
        for tail in weak_compositions_positive(total - value, parts - 1):
            yield (value,) + tail


def support_at_most_candidates(
    m: int, max_support: int, support_pattern: Tuple[int, ...] | None
) -> Iterable[dict]:
    """Yield slot-zero count vectors with support size at most max_support."""
    indices = range(5)
    total = m - 1
    if support_pattern is not None:
        support_size = len(support_pattern)
        if support_size > max_support:
            return
        for values in weak_compositions_positive(total, support_size):
            counts = [0, 0, 0, 0, 0]
            for index, value in zip(support_pattern, values):
                counts[index] = value
            vec = tuple(counts)  # type: ignore[assignment]
            yield {
                "m": m,
                "slot": 0,
                **normalized_summary(vec),
            }
        return
    for support_size in range(1, max_support + 1):
        for support in combinations(indices, support_size):
            for values in weak_compositions_positive(total, support_size):
                counts = [0, 0, 0, 0, 0]
                for index, value in zip(support, values):
                    counts[index] = value
                vec = tuple(counts)  # type: ignore[assignment]
                yield {
                    "m": m,
                    "slot": 0,
                    **normalized_summary(vec),
                }


def effective_max_steps(m: int, max_return_steps: int | None, m3_factor: float | None):
    if max_return_steps is not None:
        return max_return_steps
    if m3_factor is not None:
        return max(1, int(m3_factor * (m**3)))
    return None


def verify_small_seam_case_with_cap(
    m: int,
    slot: int,
    counts: CountVec,
    max_steps: int | None,
) -> dict:
    seam_port = (slot + 2) % 5
    first_return = {}
    return_times = {}
    start_ok = True
    no_return = []
    repeat_exhausted = []
    limit = max_steps if max_steps is not None else m**4 + 5
    for a in range(1, m):
        w = route_e.theta_state(m, slot, a)
        if route_e.lam(route_e.PERT, route_e.shifted_zero_mask(w), slot) != seam_port:
            start_ok = False
        seen = {w}
        for time in range(1, limit + 1):
            w = route_e.one_e_return_step_with_slot(m, slot, counts, w)
            b = route_e.theta_param(m, slot, w)
            if b is not None:
                first_return[a] = b
                return_times[a] = time
                break
            if w in seen:
                no_return.append(a)
                repeat_exhausted.append(a)
                break
            seen.add(w)
        else:
            no_return.append(a)
            break
        if no_return:
            break

    cycle_lengths = (
        route_e.cycle_lengths_from_param_map(first_return, range(1, m))
        if not no_return
        else []
    )
    blocks = route_e.translation_blocks(m, first_return) if not no_return else []
    return_time_sum = sum(return_times.values())
    ok = (
        start_ok
        and not no_return
        and cycle_lengths == [m - 1]
        and return_time_sum == m**4
    )
    return {
        "m": m,
        "slot": slot,
        "counts": counts,
        "seam_port": seam_port,
        "seam_size": m - 1,
        "start_ok": start_ok,
        "cycle_lengths": cycle_lengths,
        "return_time_sum": return_time_sum,
        "expected_return_time_sum": m**4,
        "translation_block_count": len(blocks),
        "translation_blocks": blocks,
        "no_return_examples": no_return,
        "cap_exhausted": bool(no_return) and not repeat_exhausted,
        "repeat_exhausted": bool(repeat_exhausted),
        "max_return_steps": max_steps,
        "ok": ok,
    }


def score_candidate(
    candidate: dict, max_return_steps: int | None, m3_factor: float | None
) -> dict:
    max_steps = effective_max_steps(candidate["m"], max_return_steps, m3_factor)
    result = verify_small_seam_case_with_cap(
        candidate["m"], candidate["slot"], candidate["counts"], max_steps
    )
    blocks = result.get("translation_blocks", [])
    return {
        **{k: v for k, v in candidate.items() if k != "section"},
        "small_seam_ok": result["ok"],
        "start_ok": result["start_ok"],
        "cycle_lengths": result["cycle_lengths"],
        "return_time_sum": result["return_time_sum"],
        "expected_return_time_sum": result["expected_return_time_sum"],
        "block_count": result["translation_block_count"],
        "max_block_length": max((block["length"] for block in blocks), default=0),
        "translation_blocks_prefix": blocks[:8],
        "cap_exhausted": result["cap_exhausted"],
        "repeat_exhausted": result["repeat_exhausted"],
        "max_return_steps": result["max_return_steps"],
        "section_ok": candidate.get("section", {}).get("section_formula_ok"),
        "section_H_single": candidate.get("section", {}).get("H_single"),
    }


def candidate_stream(
    m: int, mode: str, max_support: int, support_pattern: Tuple[int, ...] | None
) -> Iterable[dict]:
    if mode == "open-port":
        return open_port_section_candidates(m)
    if mode == "support":
        return support_at_most_candidates(m, max_support, support_pattern)
    raise ValueError(f"unknown mode {mode!r}")


def best_hits(hits: List[dict], top: int) -> dict:
    good = [hit for hit in hits if hit["small_seam_ok"]]
    return {
        "min_block": sorted(
            good,
            key=lambda hit: (
                hit["block_count"],
                -hit["max_block_length"],
                hit["support_count"],
                hit["counts"],
            ),
        )[:top],
        "low_support": sorted(
            good,
            key=lambda hit: (
                hit["support_count"],
                hit["block_count"],
                -hit["max_block_length"],
                hit["counts"],
            ),
        )[:top],
    }


def search_modulus(
    m: int,
    mode: str,
    max_support: int,
    support_pattern: Tuple[int, ...] | None,
    hit_limit: int,
    candidate_limit: int | None,
    max_return_steps: int | None,
    m3_factor: float | None,
    top: int,
) -> dict:
    hits = []
    checked = 0
    capped = 0
    repeated = 0
    for candidate in candidate_stream(m, mode, max_support, support_pattern):
        checked += 1
        scored = score_candidate(candidate, max_return_steps, m3_factor)
        if scored["cap_exhausted"]:
            capped += 1
        if scored["repeat_exhausted"]:
            repeated += 1
        if scored["small_seam_ok"]:
            hits.append(scored)
            if hit_limit and len(hits) >= hit_limit:
                break
        if candidate_limit is not None and checked >= candidate_limit:
            break
    return {
        "m": m,
        "mode": mode,
        "support_pattern": support_pattern,
        "checked": checked,
        "cap_exhausted_count": capped,
        "repeat_exhausted_count": repeated,
        "hit_count": len(hits),
        "ok": bool(hits),
        "hits": hits,
        "best": best_hits(hits, top),
    }


def print_summary(results: List[dict]) -> None:
    print("m mode checked capped repeated hits best_min_block best_low_support")
    for result in results:
        min_block = result["best"]["min_block"]
        low_support = result["best"]["low_support"]
        print(
            result["m"],
            result["mode"],
            result["checked"],
            result["cap_exhausted_count"],
            result["repeat_exhausted_count"],
            result["hit_count"],
            compact_best(min_block[0]) if min_block else None,
            compact_best(low_support[0]) if low_support else None,
        )


def compact_best(hit: dict) -> dict:
    return {
        "counts": hit["counts"],
        "blocks": hit["block_count"],
        "max": hit["max_block_length"],
        "support": hit["support_count"],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--moduli", required=True, help="comma-separated even moduli")
    parser.add_argument(
        "--mode",
        choices=["open-port", "support"],
        default="open-port",
        help="candidate family to search",
    )
    parser.add_argument(
        "--max-support",
        type=int,
        default=3,
        help="maximum support size for --mode support",
    )
    parser.add_argument(
        "--support-pattern",
        help="comma-separated support indices to scan exactly, e.g. 0,1,3",
    )
    parser.add_argument(
        "--hit-limit",
        type=int,
        default=5,
        help="stop each modulus after this many hits; 0 means no hit limit",
    )
    parser.add_argument(
        "--candidate-limit",
        type=int,
        help="stop each modulus after checking this many candidates",
    )
    parser.add_argument(
        "--max-return-steps",
        type=int,
        help="exploratory cap for each seam point's first-return search",
    )
    parser.add_argument(
        "--max-return-m3-factor",
        type=float,
        help="exploratory cap set to factor*m^3 steps for each seam point",
    )
    parser.add_argument("--top", type=int, default=5)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    support_pattern = parse_support_pattern(args.support_pattern)

    results = [
        search_modulus(
            m,
            args.mode,
            args.max_support,
            support_pattern,
            args.hit_limit,
            args.candidate_limit,
            args.max_return_steps,
            args.max_return_m3_factor,
            args.top,
        )
        for m in parse_moduli(args.moduli)
    ]
    output = {
        "schema": "d5_routeE_small_seam_candidate_search_v1",
        "mode": args.mode,
        "moduli": parse_moduli(args.moduli),
        "support_pattern": support_pattern,
        "max_return_steps": args.max_return_steps,
        "max_return_m3_factor": args.max_return_m3_factor,
        "results": results,
    }
    print_summary(results)
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
