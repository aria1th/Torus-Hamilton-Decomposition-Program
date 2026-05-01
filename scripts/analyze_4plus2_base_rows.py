#!/usr/bin/env python3
"""Analyze base-row candidates for the all-zero-set 4+2 bridge.

This is a search aid for the uniform ``BridgeConcreteFullRankPackage`` target.
It deliberately ignores the D3 fiber compiler and tests only the A5 base
return induced by words over the five all-zero-set base slots.
"""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

from verify_4plus2_allN_bridge_cert import (
    BridgeModel,
    base_tuple,
    default_bundle_path,
    load_bundle,
    parse_only,
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

    candidates_by_word = [row_candidates_for_base_word(word, m) for word in words]
    if any(not candidates for candidates in candidates_by_word):
        return []

    order = sorted(range(7), key=lambda idx: len(candidates_by_word[idx]))
    used = [set() for _ in range(m)]
    chosen: dict[int, list[int]] = {}
    solutions = []

    def compatible(row: list[int]) -> bool:
        return all(slot not in used[layer] for layer, slot in enumerate(row))

    def push(row: list[int]) -> None:
        for layer, slot in enumerate(row):
            used[layer].add(slot)

    def pop(row: list[int]) -> None:
        for layer, slot in enumerate(row):
            used[layer].remove(slot)

    def search(depth: int) -> None:
        if len(solutions) >= limit:
            return
        if depth == 7:
            if all(len(column) == 7 for column in used):
                solutions.append(
                    {
                        "base_words": [word_string(word) for word in words],
                        "rows": [chosen[idx] for idx in range(7)],
                    }
                )
            return

        idx = order[depth]
        for row in candidates_by_word[idx]:
            if not compatible(row):
                continue
            chosen[idx] = row
            push(row)
            search(depth + 1)
            pop(row)
            del chosen[idx]
            if len(solutions) >= limit:
                return

    search(0)
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
    for length in range(1, max_len + 1):
        for word in itertools.product(range(5), repeat=length):
            if is_single_cycle(
                m**4, lambda base, word=word: base_step_for_word(model, word, base)
            ):
                found.append(
                    {
                        "word": word_string(word),
                        "length": length,
                        "orbit_prefix": first_orbit_prefix(model, word, min(8, m**4)),
                    }
                )
                if len(found) >= limit:
                    return found
    return found


def cover_from_bundled(bundle: Path, only: set[int] | None, limit: int) -> list[dict]:
    out = []
    for cert in load_bundle(bundle, only):
        m = cert["m"]
        words = [tuple(slot for slot in row if slot < 5) for row in cert["rows"]]
        out.append(
            {
                "m": m,
                "base_words": [word_string(word) for word in words],
                "solutions": search_column_exact_cover(m, words, limit),
            }
        )
    return out


def parse_moduli(value: str | None) -> list[int]:
    if value is None:
        return []
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
    parser.add_argument("--cover-limit", type=int, default=3)
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
                "solutions": search_column_exact_cover(
                    args.cover_m, words, args.cover_limit
                ),
            }
        )

    text = json.dumps(payload, indent=2, sort_keys=True)
    if args.json_out is None:
        print(text)
    else:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(text + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
