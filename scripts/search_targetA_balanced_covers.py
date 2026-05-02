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
import itertools
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


def first_symbol(word: tuple[int, ...]) -> int:
    if not word:
        raise ValueError("empty base words are not supported")
    return word[0]


def first_symbol_histogram(words: list[tuple[int, ...]]) -> list[int]:
    out = [0, 0, 0, 0, 0]
    for word in words:
        out[first_symbol(word)] += 1
    return out


def select_count_vector_representatives(
    words: list[tuple[int, ...]],
    representatives_per_vector: int,
    representatives_per_symbol: int,
) -> list[tuple[int, ...]]:
    if representatives_per_symbol > 0:
        selected: list[tuple[int, ...]] = []
        counts = [0, 0, 0, 0, 0]
        for word in words:
            symbol = first_symbol(word)
            if counts[symbol] >= representatives_per_symbol:
                continue
            counts[symbol] += 1
            selected.append(word)
            if all(count >= representatives_per_symbol for count in counts):
                break
        return selected
    if representatives_per_vector > 0:
        return words[:representatives_per_vector]
    return words


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


def cyclic_rotations(word: tuple[int, ...]) -> list[tuple[int, ...]]:
    return [word[idx:] + word[:idx] for idx in range(len(word))]


def close_under_cyclic_rotations(words: list[tuple[int, ...]]) -> list[tuple[int, ...]]:
    out = []
    seen: set[tuple[int, ...]] = set()
    for word in words:
        for rotated in cyclic_rotations(word):
            if rotated in seen:
                continue
            seen.add(rotated)
            out.append(rotated)
    return out


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


def first_frontier_has_exact_cover(words: tuple[tuple[int, ...], ...]) -> bool:
    frontier = [word[0] for word in words]
    return all(slot in frontier for slot in range(5))


def combo_first_frontier_possible(
    combo: list[tuple[int, tuple[int, int, int, int, int]]],
    groups: dict[int, dict[tuple[int, int, int, int, int], list[tuple[int, ...]]]],
) -> bool:
    masks = {0}
    for length, vector in combo:
        first_symbols = {first_symbol(word) for word in groups[length][vector]}
        next_masks = set()
        for mask in masks:
            for symbol in first_symbols:
                next_masks.add(mask | (1 << symbol))
        masks = next_masks
    return (0b11111 in masks)


def word_groups_first_frontier_possible(
    word_groups: list[list[tuple[int, ...]]],
) -> bool:
    masks = {0}
    for group_words in word_groups:
        first_symbols = {first_symbol(word) for word in group_words}
        next_masks = set()
        for mask in masks:
            for symbol in first_symbols:
                next_masks.add(mask | (1 << symbol))
        masks = next_masks
    return (0b11111 in masks)


def search_count_vector_placements(
    m: int,
    words: list[tuple[int, ...]],
    length_pattern: list[int] | None,
    vector_combo_start: int,
    vector_combo_limit: int,
    product_limit: int,
    representatives_per_vector: int,
    representatives_per_symbol: int,
    solution_limit: int,
    cover_limit: int,
) -> dict | None:
    if vector_combo_limit <= 0 or length_pattern is None:
        return None

    target_len = 5 * m
    target_counts = (m, m, m, m, m)
    pattern = sorted(length_pattern)
    if len(pattern) != 7 or sum(pattern) != target_len:
        return {
            "enabled": True,
            "error": "length pattern must have seven entries summing to 5*m",
            "solutions": [],
        }

    groups: dict[int, dict[tuple[int, int, int, int, int], list[tuple[int, ...]]]] = {}
    for word in words:
        groups.setdefault(len(word), {}).setdefault(word_counts(word), []).append(word)
    for counts_by_vector in groups.values():
        for vector, group_words in counts_by_vector.items():
            counts_by_vector[vector] = sorted(
                group_words, key=lambda item: word_string(item)
            )

    vectors_by_length = {
        length: sorted(counts_by_vector)
        for length, counts_by_vector in groups.items()
    }
    vector_combos_seen = 0
    vector_combos_tested = 0
    vector_combos_frontier_impossible = 0
    word_products_checked = 0
    frontier_failures = 0
    dp_products_checked = 0
    sampled_frontier_impossible = 0
    skipped_product_limit = 0
    states_visited = 0
    truncated = False
    solutions = []
    attempts = []
    chosen: list[tuple[int, tuple[int, int, int, int, int]]] = []

    def emit_vector_combo(
        combo: list[tuple[int, tuple[int, int, int, int, int]]]
    ) -> None:
        nonlocal vector_combos_seen, vector_combos_tested
        nonlocal vector_combos_frontier_impossible, word_products_checked
        nonlocal frontier_failures, dp_products_checked
        nonlocal skipped_product_limit, truncated
        if len(solutions) >= solution_limit:
            return
        vector_combos_seen += 1
        if vector_combos_seen <= vector_combo_start:
            return
        if vector_combos_seen > vector_combo_start + vector_combo_limit:
            truncated = True
            return
        combo_frontier_possible = combo_first_frontier_possible(combo, groups)

        word_groups = []
        combo_summary = []
        product_size = 1
        for length, vector in combo:
            group_words = groups[length][vector]
            selected_words = select_count_vector_representatives(
                group_words, representatives_per_vector, representatives_per_symbol
            )
            word_groups.append(group_words)
            product_size *= len(selected_words)
            combo_summary.append(
                {
                    "length": length,
                    "count_vector": list(vector),
                    "word_count": len(groups[length][vector]),
                    "tested_word_count": len(selected_words),
                    "first_symbol_histogram": first_symbol_histogram(group_words),
                    "tested_first_symbol_histogram": first_symbol_histogram(
                        selected_words
                    ),
                    "representatives": [
                        word_string(word) for word in selected_words[:10]
                    ],
                }
            )
            word_groups[-1] = selected_words
        sampled_frontier_possible = word_groups_first_frontier_possible(word_groups)
        attempt = {
            "vector_combo_index": vector_combos_seen - 1,
            "product_size": product_size,
            "tested": False,
            "combo_frontier_possible": combo_frontier_possible,
            "sampled_frontier_possible": sampled_frontier_possible,
            "solution_count": 0,
            "frontier_failures": 0,
            "dp_products_checked": 0,
            "combo": combo_summary,
        }
        attempts.append(attempt)
        if not combo_frontier_possible:
            vector_combos_frontier_impossible += 1
            attempt["skipped"] = "frontier_impossible"
            return
        if not sampled_frontier_possible:
            sampled_frontier_impossible += 1
            attempt["skipped"] = "sampled_frontier_impossible"
            return
        if product_size > product_limit:
            skipped_product_limit += 1
            attempt["skipped"] = "product_limit"
            return

        vector_combos_tested += 1
        attempt["tested"] = True
        for word_choice in itertools.product(*word_groups):
            word_products_checked += 1
            if not first_frontier_has_exact_cover(word_choice):
                frontier_failures += 1
                attempt["frontier_failures"] += 1
                continue
            dp_products_checked += 1
            attempt["dp_products_checked"] += 1
            cover_solutions = search_column_exact_cover(m, list(word_choice), cover_limit)
            if cover_solutions:
                attempt["solution_count"] += len(cover_solutions)
                for solution in cover_solutions:
                    solutions.append(solution)
                    if len(solutions) >= solution_limit:
                        return

    def search(
        depth: int,
        total_counts: tuple[int, int, int, int, int],
        min_index_by_length: dict[int, int],
    ) -> None:
        nonlocal states_visited, truncated
        if len(solutions) >= solution_limit or truncated:
            return
        states_visited += 1
        if any(value > m for value in total_counts):
            return
        if depth == 7:
            if total_counts == target_counts:
                emit_vector_combo(list(chosen))
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
            if len(solutions) >= solution_limit or truncated:
                return

    search(0, (0, 0, 0, 0, 0), {})
    return {
        "enabled": True,
        "length_pattern": pattern,
        "states_visited": states_visited,
        "vector_combo_start": vector_combo_start,
        "vector_combo_limit": vector_combo_limit,
        "product_limit": product_limit,
        "representatives_per_vector": representatives_per_vector,
        "representatives_per_symbol": representatives_per_symbol,
        "vector_combos_seen": vector_combos_seen,
        "vector_combos_tested": vector_combos_tested,
        "vector_combos_frontier_impossible": vector_combos_frontier_impossible,
        "word_products_checked": word_products_checked,
        "frontier_failures": frontier_failures,
        "dp_products_checked": dp_products_checked,
        "sampled_frontier_impossible": sampled_frontier_impossible,
        "skipped_product_limit": skipped_product_limit,
        "truncated": truncated,
        "attempts": attempts,
        "solutions": solutions,
    }


def search_balanced_covers(
    m: int,
    words: list[tuple[int, ...]],
    length_pattern: list[int] | None,
    combo_limit: int,
    solution_limit: int,
    cover_limit: int,
    count_vector_limit: int = 0,
    count_vector_placement_start: int = 0,
    count_vector_placement_limit: int = 0,
    count_vector_product_limit: int = 10000,
    count_vector_representatives_per_vector: int = 0,
    count_vector_representatives_per_symbol: int = 0,
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
    count_vector_placement_search = search_count_vector_placements(
        m,
        words,
        length_pattern,
        count_vector_placement_start,
        count_vector_placement_limit,
        count_vector_product_limit,
        count_vector_representatives_per_vector,
        count_vector_representatives_per_symbol,
        solution_limit,
        cover_limit,
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
        "count_vector_placement_search": count_vector_placement_search,
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
    parser.add_argument(
        "--cyclic-rotations",
        action="store_true",
        help="close the primitive-word pool under cyclic rotations",
    )
    parser.add_argument("--combo-limit", type=int, default=100000)
    parser.add_argument("--solution-limit", type=int, default=3)
    parser.add_argument("--cover-limit", type=int, default=1)
    parser.add_argument(
        "--count-vector-limit",
        type=int,
        default=0,
        help="also report this many balanced count-vector combos for the length pattern",
    )
    parser.add_argument(
        "--count-vector-placement-start",
        type=int,
        default=0,
        help="skip this many balanced count-vector combos before placement tests",
    )
    parser.add_argument(
        "--count-vector-placement-limit",
        type=int,
        default=0,
        help="try column placements for this many balanced count-vector combos",
    )
    parser.add_argument(
        "--count-vector-product-limit",
        type=int,
        default=10000,
        help="skip a count-vector placement combo if its word product is larger",
    )
    parser.add_argument(
        "--count-vector-representatives-per-vector",
        type=int,
        default=0,
        help="limit tested words per count vector; 0 means all words in the pool",
    )
    parser.add_argument(
        "--count-vector-representatives-per-symbol",
        type=int,
        default=0,
        help=(
            "limit tested words to this many representatives for each first "
            "symbol within a count vector; takes precedence over "
            "--count-vector-representatives-per-vector"
        ),
    )
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    words = load_words(args.word_file, args.words, args.pool_limit)
    if args.cyclic_rotations:
        words = close_under_cyclic_rotations(words)
    words = filter_words(words, args.min_len, args.max_len, args.max_per_length)
    result = search_balanced_covers(
        args.m,
        words,
        parse_lengths(args.lengths),
        args.combo_limit,
        args.solution_limit,
        args.cover_limit,
        args.count_vector_limit,
        args.count_vector_placement_start,
        args.count_vector_placement_limit,
        args.count_vector_product_limit,
        args.count_vector_representatives_per_vector,
        args.count_vector_representatives_per_symbol,
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
    placement_diag = result.get("count_vector_placement_search")
    if placement_diag is not None:
        print(
            "count_vector_placement "
            "start={vector_combo_start} seen={vector_combos_seen} "
            "tested={vector_combos_tested} "
            "frontier_impossible={vector_combos_frontier_impossible} "
            "word_products={word_products_checked} "
            "frontier_failures={frontier_failures} "
            "dp_products={dp_products_checked} "
            "sampled_frontier_impossible={sampled_frontier_impossible} "
            "skipped={skipped_product_limit} "
            "diag_solutions={solution_count} truncated={truncated}".format(
                solution_count=len(placement_diag["solutions"]),
                **placement_diag,
            )
        )

    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
