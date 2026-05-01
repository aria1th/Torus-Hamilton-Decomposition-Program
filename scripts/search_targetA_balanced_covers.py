#!/usr/bin/env python3
"""Search balanced Target-A base-word multisets and column exact covers.

The Target-A base problem has two independent finite gates:

1. each selected A5 base word must be primitive;
2. the seven selected words must be placeable into seven length-m rows whose
   columns are exact covers of slots 0..6.

Before column placement is possible, the base words must satisfy the aggregate
count condition

    count(slot 0) = ... = count(slot 4) = m.

This script takes a primitive-word pool, searches seven-word multisets passing
the length/count gate, and then calls the existing column exact-cover placer.
It is designed to consume the ``HIT ... word=...`` output from the C++ primitive
word search helper.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

from analyze_4plus2_base_rows import (
    base_word_count_summary,
    parse_lengths,
    parse_word,
    search_column_exact_cover,
    word_string,
)


WORD_RE = re.compile(r"(?:word=)?([0-4]+)")


def word_counts(word: tuple[int, ...]) -> tuple[int, int, int, int, int]:
    return tuple(sum(1 for value in word if value == slot) for slot in range(5))


def add_counts(
    left: tuple[int, int, int, int, int], right: tuple[int, int, int, int, int]
) -> tuple[int, int, int, int, int]:
    return tuple(a + b for a, b in zip(left, right))


def leq_counts(
    left: tuple[int, int, int, int, int],
    right: tuple[int, int, int, int, int],
) -> bool:
    return all(a <= b for a, b in zip(left, right))


def parse_word_line(line: str) -> tuple[int, ...] | None:
    if "word=" in line:
        text = line.rsplit("word=", 1)[1].strip().split()[0]
        return parse_word(text)
    stripped = line.strip()
    if not stripped or stripped.startswith("#"):
        return None
    match = WORD_RE.fullmatch(stripped)
    if match is None:
        return None
    return parse_word(match.group(1))


def load_words(
    files: list[Path], inline_words: str | None, pool_limit: int | None
) -> list[tuple[int, ...]]:
    words: list[tuple[int, ...]] = []
    seen: set[tuple[int, ...]] = set()

    def add(word: tuple[int, ...]) -> None:
        if word in seen:
            return
        seen.add(word)
        words.append(word)

    if inline_words:
        for text in inline_words.split(","):
            text = text.strip()
            if text:
                add(parse_word(text))

    for path in files:
        with path.open() as handle:
            for line in handle:
                word = parse_word_line(line)
                if word is not None:
                    add(word)
                if pool_limit is not None and len(words) >= pool_limit:
                    return words

    if pool_limit is not None:
        return words[:pool_limit]
    return words


def filter_words(
    words: list[tuple[int, ...]],
    min_len: int | None,
    max_len: int | None,
    max_per_length: int | None,
) -> list[tuple[int, ...]]:
    out = []
    by_length: dict[int, int] = {}
    for word in sorted(words, key=lambda item: (len(item), word_string(item))):
        if min_len is not None and len(word) < min_len:
            continue
        if max_len is not None and len(word) > max_len:
            continue
        count = by_length.get(len(word), 0)
        if max_per_length is not None and count >= max_per_length:
            continue
        by_length[len(word)] = count + 1
        out.append(word)
    return out


def suffix_max_counts(
    counts: list[tuple[int, int, int, int, int]]
) -> list[tuple[int, int, int, int, int]]:
    suffix = [(0, 0, 0, 0, 0)] * (len(counts) + 1)
    current = [0, 0, 0, 0, 0]
    for idx in range(len(counts) - 1, -1, -1):
        for slot in range(5):
            current[slot] = max(current[slot], counts[idx][slot])
        suffix[idx] = tuple(current)
    return suffix


def search_count_vector_combos(
    m: int,
    words: list[tuple[int, ...]],
    length_pattern: list[int] | None,
    limit: int,
) -> dict | None:
    if limit <= 0 or length_pattern is None:
        return None

    target_len = 5 * m
    target_counts = (m, m, m, m, m)
    pattern = sorted(length_pattern)
    if len(pattern) != 7 or sum(pattern) != target_len:
        return {
            "enabled": True,
            "error": "length pattern must have seven entries summing to 5*m",
            "combos": [],
        }

    groups: dict[int, dict[tuple[int, int, int, int, int], list[tuple[int, ...]]]] = {}
    for word in words:
        groups.setdefault(len(word), {}).setdefault(word_counts(word), []).append(word)

    vectors_by_length = {
        length: sorted(counts_by_vector)
        for length, counts_by_vector in groups.items()
    }
    combos: list[list[tuple[int, tuple[int, int, int, int, int]]]] = []
    chosen: list[tuple[int, tuple[int, int, int, int, int]]] = []
    states_visited = 0
    truncated = False

    def search(
        depth: int,
        total_counts: tuple[int, int, int, int, int],
        min_index_by_length: dict[int, int],
    ) -> None:
        nonlocal states_visited, truncated
        if len(combos) >= limit:
            truncated = True
            return
        states_visited += 1
        if any(value > m for value in total_counts):
            return
        if depth == 7:
            if total_counts == target_counts:
                combos.append(list(chosen))
            return

        length = pattern[depth]
        vectors = vectors_by_length.get(length, [])
        start = min_index_by_length.get(length, 0)
        for idx in range(start, len(vectors)):
            vector = vectors[idx]
            next_counts = add_counts(total_counts, vector)
            if not leq_counts(next_counts, target_counts):
                continue
            next_min_index_by_length = dict(min_index_by_length)
            next_min_index_by_length[length] = idx
            chosen.append((length, vector))
            search(depth + 1, next_counts, next_min_index_by_length)
            chosen.pop()
            if len(combos) >= limit:
                truncated = True
                return

    search(0, (0, 0, 0, 0, 0), {})
    return {
        "enabled": True,
        "length_pattern": pattern,
        "states_visited": states_visited,
        "combo_count_reported": len(combos),
        "truncated": truncated,
        "vector_counts_by_length": {
            str(length): len(vectors) for length, vectors in vectors_by_length.items()
        },
        "combos": [
            [
                {
                    "length": length,
                    "count_vector": list(vector),
                    "word_count": len(groups[length][vector]),
                    "representatives": [
                        word_string(word) for word in groups[length][vector][:5]
                    ],
                }
                for length, vector in combo
            ]
            for combo in combos
        ],
    }


def search_balanced_covers(
    m: int,
    words: list[tuple[int, ...]],
    length_pattern: list[int] | None,
    combo_limit: int,
    solution_limit: int,
    cover_limit: int,
    count_vector_limit: int = 0,
) -> dict:
    target_len = 5 * m
    target_counts = (m, m, m, m, m)
    pattern = sorted(length_pattern) if length_pattern is not None else None
    if pattern is not None and (len(pattern) != 7 or sum(pattern) != target_len):
        return {
            "m": m,
            "pool_size": len(words),
            "length_pattern": pattern,
            "combo_limit": combo_limit,
            "combos_checked": 0,
            "balanced_combos": 0,
            "solutions": [],
            "error": "length pattern must have seven entries summing to 5*m",
        }

    counts = [word_counts(word) for word in words]
    suffix_counts = suffix_max_counts(counts)
    combos_checked = 0
    balanced_combos = 0
    placement_failures = 0
    solutions = []

    def can_still_reach(
        start: int,
        depth: int,
        total_len: int,
        total_counts: tuple[int, int, int, int, int],
    ) -> bool:
        if any(value > m for value in total_counts):
            return False
        remaining = 7 - depth
        if remaining == 0:
            return total_len == target_len and total_counts == target_counts
        if pattern is not None:
            remaining_lengths = pattern[depth:]
            min_length = sum(remaining_lengths)
            max_length = min_length
        else:
            if not words:
                return False
            min_word_len = len(words[start]) if start < len(words) else 0
            max_word_len = max((len(word) for word in words[start:]), default=0)
            min_length = remaining * min_word_len
            max_length = remaining * max_word_len
        if total_len + min_length > target_len:
            return False
        if total_len + max_length < target_len:
            return False
        max_counts = (
            suffix_counts[start] if start < len(suffix_counts) else (0, 0, 0, 0, 0)
        )
        return all(
            total_counts[slot] + remaining * max_counts[slot] >= m
            for slot in range(5)
        )

    chosen: list[tuple[int, ...]] = []

    def search(
        start: int,
        depth: int,
        total_len: int,
        total_counts: tuple[int, int, int, int, int],
    ) -> None:
        nonlocal combos_checked, balanced_combos, placement_failures
        if len(solutions) >= solution_limit or combos_checked >= combo_limit:
            return
        if not can_still_reach(start, depth, total_len, total_counts):
            return
        if depth == 7:
            combos_checked += 1
            if total_counts != target_counts or total_len != target_len:
                return
            balanced_combos += 1
            cover_solutions = search_column_exact_cover(m, chosen, cover_limit)
            if cover_solutions:
                for solution in cover_solutions:
                    solutions.append(solution)
                    if len(solutions) >= solution_limit:
                        return
            else:
                placement_failures += 1
            return

        required_len = pattern[depth] if pattern is not None else None
        for idx in range(start, len(words)):
            word = words[idx]
            if required_len is not None and len(word) != required_len:
                continue
            next_len = total_len + len(word)
            if next_len > target_len:
                continue
            next_counts = add_counts(total_counts, counts[idx])
            if not leq_counts(next_counts, target_counts):
                continue
            chosen.append(word)
            search(idx, depth + 1, next_len, next_counts)
            chosen.pop()
            if len(solutions) >= solution_limit or combos_checked >= combo_limit:
                return

    search(0, 0, 0, (0, 0, 0, 0, 0))
    count_vector_search = search_count_vector_combos(
        m, words, length_pattern, count_vector_limit
    )
    return {
        "m": m,
        "pool_size": len(words),
        "pool_words": [word_string(word) for word in words],
        "length_pattern": pattern,
        "count_vector_search": count_vector_search,
        "combo_limit": combo_limit,
        "combos_checked": combos_checked,
        "balanced_combos": balanced_combos,
        "placement_failures": placement_failures,
        "solutions": solutions,
        "solution_count_summaries": [
            base_word_count_summary(
                m, [parse_word(word) for word in solution["base_words"]]
            )
            for solution in solutions
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--m", type=int, required=True)
    parser.add_argument("--word-file", type=Path, action="append", default=[])
    parser.add_argument("--words", help="comma-separated inline candidate words")
    parser.add_argument("--lengths", help="comma-separated seven-word length pattern")
    parser.add_argument("--min-len", type=int)
    parser.add_argument("--max-len", type=int)
    parser.add_argument("--pool-limit", type=int)
    parser.add_argument("--max-per-length", type=int)
    parser.add_argument("--combo-limit", type=int, default=100000)
    parser.add_argument("--solution-limit", type=int, default=3)
    parser.add_argument("--cover-limit", type=int, default=1)
    parser.add_argument(
        "--count-vector-limit",
        type=int,
        default=0,
        help="also report this many balanced count-vector combos for the length pattern",
    )
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    words = load_words(args.word_file, args.words, args.pool_limit)
    words = filter_words(words, args.min_len, args.max_len, args.max_per_length)
    result = search_balanced_covers(
        args.m,
        words,
        parse_lengths(args.lengths),
        args.combo_limit,
        args.solution_limit,
        args.cover_limit,
        args.count_vector_limit,
    )
    payload = {"search": result}

    print(
        "m={m} pool={pool_size} checked={combos_checked} balanced={balanced_combos} "
        "placement_failures={placement_failures} solution_count={solution_count}".format(
            solution_count=len(result["solutions"]), **result
        )
    )
    for idx, solution in enumerate(result["solutions"][: args.solution_limit]):
        print(f"solution[{idx}] words={solution['base_words']}")

    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
