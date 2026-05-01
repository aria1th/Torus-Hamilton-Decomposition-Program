#!/usr/bin/env python3
"""Analyze base-row candidates for the all-zero-set 4+2 bridge.

This is a search aid for the uniform ``BridgeConcreteFullRankPackage`` target.
It deliberately ignores the D3 fiber compiler and tests only the A5 base
return induced by words over the five all-zero-set base slots.
"""

from __future__ import annotations

import argparse
import copy
import itertools
import json
from pathlib import Path

from verify_4plus2_allN_bridge_cert import (
    BridgeModel,
    base_tuple,
    default_bundle_path,
    load_bundle,
    parse_only,
    verify_certificate,
)


def base_step_for_word(model: BridgeModel, word: tuple[int, ...], base: int) -> int:
    for slot in word:
        base = model.base_next[slot][base]
    return base


def is_single_cycle(size: int, step) -> bool:
    seen = bytearray(size)
    state = 0
    for _ in range(size):
        if seen[state]:
            return False
        seen[state] = 1
        state = step(state)
    return state == 0


def first_orbit_prefix(
    model: BridgeModel, word: tuple[int, ...], limit: int
) -> list[list[int]]:
    out = []
    state = 0
    for _ in range(limit):
        out.append(list(base_tuple(state, model.m)))
        state = base_step_for_word(model, word, state)
    return out


def word_string(word: tuple[int, ...]) -> str:
    return "".join(str(slot) for slot in word)


def parse_word(value: str) -> tuple[int, ...]:
    if any(ch not in "01234" for ch in value):
        raise ValueError(f"base word must use only slots 0..4: {value}")
    return tuple(int(ch) for ch in value)


def base_word_count_summary(m: int, words: list[tuple[int, ...]]) -> dict:
    slot_counts = {
        str(slot): sum(1 for word in words for value in word if value == slot)
        for slot in range(5)
    }
    total_base_slots = sum(slot_counts.values())
    return {
        "word_lengths": [len(word) for word in words],
        "total_base_slots": total_base_slots,
        "target_total_base_slots": 5 * m,
        "total_length_ok": total_base_slots == 5 * m,
        "slot_counts": slot_counts,
        "target_count_per_base_slot": m,
        "slot_counts_ok": all(count == m for count in slot_counts.values()),
    }


def row_candidates_for_base_word(word: tuple[int, ...], m: int) -> list[list[int]]:
    if len(word) > m:
        return []
    candidates = []
    for base_positions in itertools.combinations(range(m), len(word)):
        row = [None] * m
        for position, slot in zip(base_positions, word):
            row[position] = slot
        extra_positions = [position for position, slot in enumerate(row) if slot is None]
        for extra_slots in itertools.product((5, 6), repeat=len(extra_positions)):
            candidate = list(row)
            for position, slot in zip(extra_positions, extra_slots):
                candidate[position] = slot
            candidates.append(candidate)
    return candidates


def search_column_exact_cover(
    m: int, words: list[tuple[int, ...]], limit: int
) -> list[dict]:
    if len(words) != 7:
        raise ValueError("exact-cover search expects exactly seven base words")
    if sum(len(word) for word in words) != 5 * m:
        return []
    if any(len(word) > m for word in words):
        return []

    lengths = tuple(len(word) for word in words)
    target = lengths
    column_choices = list(itertools.combinations(range(7), 5))
    solutions = []
    dead_states: set[tuple[int, ...]] = set()
    path: list[tuple[int, ...]] = []

    def emit_solution() -> None:
        progress = [0] * 7
        rows: list[list[int]] = [[] for _ in range(7)]
        for chosen_rows in path:
            extra_rows = [row for row in range(7) if row not in chosen_rows]
            if len(extra_rows) != 2:
                raise AssertionError("each exact-cover column has two extra rows")
            for row in range(7):
                if row in chosen_rows:
                    rows[row].append(words[row][progress[row]])
                    progress[row] += 1
                else:
                    rows[row].append(5 if row == extra_rows[0] else 6)
        if tuple(progress) != target:
            raise AssertionError("exact-cover path did not consume all base words")
        solutions.append(
            {
                "base_words": [word_string(word) for word in words],
                "count_summary": base_word_count_summary(m, words),
                "rows": rows,
            }
        )

    def search(state: tuple[int, ...]) -> bool:
        if len(solutions) >= limit:
            return True
        if state == target:
            emit_solution()
            return True
        if state in dead_states:
            return False

        found_from_state = False
        for chosen_rows in column_choices:
            next_symbols = []
            for row in chosen_rows:
                if state[row] >= lengths[row]:
                    break
                next_symbols.append(words[row][state[row]])
            else:
                if sorted(next_symbols) != [0, 1, 2, 3, 4]:
                    continue
                next_state = list(state)
                for row in chosen_rows:
                    next_state[row] += 1
                path.append(chosen_rows)
                found = search(tuple(next_state))
                path.pop()
                found_from_state = found_from_state or found
                if len(solutions) >= limit:
                    return True
                continue

        if not found_from_state:
            dead_states.add(state)
        return found_from_state

    search((0, 0, 0, 0, 0, 0, 0))
    return solutions


def analyze_bundled_rows(bundle: Path, only: set[int] | None) -> list[dict]:
    out = []
    for cert in load_bundle(bundle, only):
        m = cert["m"]
        model = BridgeModel(m)
        rows = []
        for color, row in enumerate(cert["rows"]):
            base_word = tuple(slot for slot in row if slot < 5)
            primitive = is_single_cycle(
                m**4, lambda base, word=base_word: base_step_for_word(model, word, base)
            )
            rows.append(
                {
                    "color": color,
                    "row": row,
                    "base_word": word_string(base_word),
                    "base_word_length": len(base_word),
                    "extra_positions": [
                        {"layer": layer, "slot": slot}
                        for layer, slot in enumerate(row)
                        if slot >= 5
                    ],
                    "base_primitive": primitive,
                }
            )
        out.append({"m": m, "rows": rows})
    return out


def scan_primitive_words(m: int, max_len: int, limit: int) -> list[dict]:
    model = BridgeModel(m)
    found = []
    for word in primitive_word_tuples(model, max_len, limit):
        found.append(
            {
                "word": word_string(word),
                "length": len(word),
                "orbit_prefix": first_orbit_prefix(model, word, min(8, m**4)),
            }
        )
    return found


def primitive_word_tuples(
    model: BridgeModel, max_len: int, limit: int
) -> list[tuple[int, ...]]:
    found = []
    for length in range(1, max_len + 1):
        for word in itertools.product(range(5), repeat=length):
            if is_single_cycle(
                model.m**4,
                lambda base, word=word: base_step_for_word(model, word, base),
            ):
                found.append(word)
                if len(found) >= limit:
                    return found
    return found


def search_cover_from_primitive_pool(
    m: int,
    max_len: int,
    pool_limit: int,
    combo_limit: int,
    solution_limit: int,
    length_pattern: list[int] | None = None,
) -> dict:
    model = BridgeModel(m)
    pool = primitive_word_tuples(model, max_len, pool_limit)
    pool_counts = [
        [sum(1 for value in word if value == slot) for slot in range(5)]
        for word in pool
    ]
    target_len = 5 * m
    target_counts = [m] * 5
    solutions = []
    combos_checked = 0
    count_pruned_combos = 0
    count_feasible_combos = 0
    pattern = sorted(length_pattern) if length_pattern is not None else None
    if pattern is not None and (len(pattern) != 7 or sum(pattern) != target_len):
        return {
            "m": m,
            "max_len": max_len,
            "pool_limit": pool_limit,
            "pool_size": len(pool),
            "primitive_pool": [word_string(word) for word in pool],
            "combo_limit": combo_limit,
            "combos_checked": 0,
            "count_pruned_combos": 0,
            "count_feasible_combos": 0,
            "length_pattern": pattern,
            "solutions": [],
        }

    def search_words(
        start: int,
        depth: int,
        total_len: int,
        counts: list[int],
        words: list[tuple[int, ...]],
    ) -> None:
        nonlocal combos_checked, count_pruned_combos, count_feasible_combos
        if len(solutions) >= solution_limit or combos_checked >= combo_limit:
            return
        if any(count > m for count in counts):
            return
        remaining = 7 - depth
        remaining_length_budget = (
            sum(pattern[depth:]) if pattern is not None else remaining * max_len
        )
        if any(counts[slot] + remaining_length_budget < m for slot in range(5)):
            return
        if remaining == 0:
            if total_len != target_len:
                return
            combos_checked += 1
            if counts != target_counts:
                count_pruned_combos += 1
                return
            count_feasible_combos += 1
            cover_solutions = search_column_exact_cover(m, words, 1)
            if cover_solutions:
                solutions.append(cover_solutions[0])
            return
        if total_len + remaining > target_len:
            return
        if total_len + remaining * max_len < target_len:
            return

        for idx in range(start, len(pool)):
            word = pool[idx]
            if pattern is not None and len(word) != pattern[depth]:
                continue
            next_len = total_len + len(word)
            if next_len > target_len:
                continue
            word_counts = pool_counts[idx]
            next_counts = [counts[slot] + word_counts[slot] for slot in range(5)]
            words.append(word)
            search_words(idx, depth + 1, next_len, next_counts, words)
            words.pop()
            if len(solutions) >= solution_limit or combos_checked >= combo_limit:
                return

    search_words(0, 0, 0, [0] * 5, [])
    return {
        "m": m,
        "max_len": max_len,
        "pool_limit": pool_limit,
        "pool_size": len(pool),
        "primitive_pool": [word_string(word) for word in pool],
        "combo_limit": combo_limit,
        "combos_checked": combos_checked,
        "count_pruned_combos": count_pruned_combos,
        "count_feasible_combos": count_feasible_combos,
        "length_pattern": pattern,
        "solutions": solutions,
    }


def cover_from_bundled(bundle: Path, only: set[int] | None, limit: int) -> list[dict]:
    out = []
    for cert in load_bundle(bundle, only):
        m = cert["m"]
        words = [tuple(slot for slot in row if slot < 5) for row in cert["rows"]]
        out.append(
            {
                "m": m,
                "base_words": [word_string(word) for word in words],
                "count_summary": base_word_count_summary(m, words),
                "solutions": search_column_exact_cover(m, words, limit),
            }
        )
    return out


def test_rows_with_bundled_kappa(cert: dict, rows: list[list[int]]) -> dict:
    candidate = copy.deepcopy(cert)
    candidate["rows"] = rows
    try:
        message, _summary = verify_certificate(candidate)
    except Exception as exc:
        return {"ok": False, "error": f"{type(exc).__name__}: {exc}"}
    return {"ok": True, "message": message}


def annotate_with_bundled_kappa_tests(cover_searches: list[dict], bundle: Path) -> None:
    cert_by_m = {cert["m"]: cert for cert in load_bundle(bundle, None)}
    for search in cover_searches:
        cert = cert_by_m.get(search["m"])
        if cert is None:
            continue
        for solution in search["solutions"]:
            solution["bundled_kappa_test"] = test_rows_with_bundled_kappa(
                cert, solution["rows"]
            )


def parse_moduli(value: str | None) -> list[int]:
    if value is None:
        return []
    return [int(part) for part in value.split(",") if part]


def parse_lengths(value: str | None) -> list[int] | None:
    if value is None:
        return None
    return [int(part) for part in value.split(",") if part]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bundle", type=Path, default=default_bundle_path())
    parser.add_argument("--only", help="comma-separated bundled moduli to analyze")
    parser.add_argument(
        "--scan-moduli",
        help="comma-separated moduli for primitive base-word scans, e.g. 5,7,9,11",
    )
    parser.add_argument("--max-len", type=int, default=3)
    parser.add_argument("--limit", type=int, default=20)
    parser.add_argument(
        "--cover-from-bundled",
        action="store_true",
        help="search column exact-covers using the bundled rows' base words",
    )
    parser.add_argument("--cover-m", type=int, help="modulus for --cover-words")
    parser.add_argument(
        "--cover-words",
        help="comma-separated seven base words over 0..4 for column exact-cover search",
    )
    parser.add_argument(
        "--cover-primitive-m",
        type=int,
        help="search exact-covers by choosing seven words from the primitive-word pool",
    )
    parser.add_argument("--cover-primitive-max-len", type=int, default=5)
    parser.add_argument("--cover-pool-limit", type=int, default=60)
    parser.add_argument(
        "--cover-lengths",
        help="comma-separated seven base-word lengths for primitive-pool cover search",
    )
    parser.add_argument("--combo-limit", type=int, default=1000)
    parser.add_argument("--cover-limit", type=int, default=3)
    parser.add_argument(
        "--test-with-bundled-kappa",
        action="store_true",
        help="test cover solutions against the bundled kappa table for the same modulus",
    )
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    payload = {
        "bundled_rows": analyze_bundled_rows(args.bundle, parse_only(args.only)),
        "cover_searches": [],
        "primitive_scans": [],
    }
    for m in parse_moduli(args.scan_moduli):
        payload["primitive_scans"].append(
            {
                "m": m,
                "max_len": args.max_len,
                "primitive_words": scan_primitive_words(m, args.max_len, args.limit),
            }
        )
    if args.cover_from_bundled:
        payload["cover_searches"].extend(
            cover_from_bundled(args.bundle, parse_only(args.only), args.cover_limit)
        )
    if args.cover_words is not None:
        if args.cover_m is None:
            raise ValueError("--cover-words requires --cover-m")
        words = [parse_word(word) for word in args.cover_words.split(",") if word]
        payload["cover_searches"].append(
            {
                "m": args.cover_m,
                "base_words": [word_string(word) for word in words],
                "count_summary": base_word_count_summary(args.cover_m, words),
                "solutions": search_column_exact_cover(
                    args.cover_m, words, args.cover_limit
                ),
            }
        )
    if args.cover_primitive_m is not None:
        payload["cover_searches"].append(
            search_cover_from_primitive_pool(
                args.cover_primitive_m,
                args.cover_primitive_max_len,
                args.cover_pool_limit,
                args.combo_limit,
                args.cover_limit,
                parse_lengths(args.cover_lengths),
            )
        )
    if args.test_with_bundled_kappa:
        annotate_with_bundled_kappa_tests(payload["cover_searches"], args.bundle)

    text = json.dumps(payload, indent=2, sort_keys=True)
    if args.json_out is None:
        print(text)
    else:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(text + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
