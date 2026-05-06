#!/usr/bin/env python3
"""Summarize local adjacent-switch structure in a D5 Route-E layer table.

Input is the same JSON format as `d5_routeE_nested_diagnostics.py`.
For each layer, the script chooses the modal local stop row as that layer's
bulk row and writes every distinct local row as a shortest word in adjacent
stop-rank swaps relative to that modal row.

This is an extraction aid for the full-layered Route-E proof target.  It helps
separate constant bulk layers from finite/state-dependent defect layers and
shows which adjacent swap ranks are actually used.
"""

from __future__ import annotations

import argparse
from collections import Counter, deque
from pathlib import Path

import d5_routeE_nested_diagnostics as nested


Row = tuple[int, int, int, int, int]


def apply_adjacent_value_swap(row: Row, rank: int) -> Row:
    out = list(row)
    i = out.index(rank)
    j = out.index(rank + 1)
    out[i], out[j] = out[j], out[i]
    return tuple(out)  # type: ignore[return-value]


def shortest_words_from(base: Row) -> dict[Row, list[tuple[int, int]]]:
    prev: dict[Row, tuple[Row | None, int | None]] = {base: (None, None)}
    queue: deque[Row] = deque([base])
    while queue:
        row = queue.popleft()
        for rank in range(4):
            nxt = apply_adjacent_value_swap(row, rank)
            if nxt not in prev:
                prev[nxt] = (row, rank)
                queue.append(nxt)

    words: dict[Row, list[tuple[int, int]]] = {}
    for row in prev:
        word: list[tuple[int, int]] = []
        x = row
        while prev[x][0] is not None:
            px, rank = prev[x]
            assert px is not None and rank is not None
            word.append((rank, rank + 1))
            x = px
        words[row] = list(reversed(word))
    return words


def word_text(word: list[tuple[int, int]]) -> str:
    return " ".join(f"{a}/{b}" for a, b in word) or "identity"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("json_table", type=Path)
    parser.add_argument("--max-rows", type=int, default=12)
    parser.add_argument(
        "--all-layers",
        action="store_true",
        help="print constant layers too; by default only defect layers are expanded",
    )
    args = parser.parse_args()

    m, layers = nested.load_layers(args.json_table)
    print(f"m={m} vertices={m**4} layers={m}")
    total_defect_layers = 0
    for t, layer in enumerate(layers):
        counts: Counter[Row] = Counter(tuple(row) for row in layer)  # type: ignore[arg-type]
        modal, modal_count = counts.most_common(1)[0]
        words = shortest_words_from(modal)
        max_len = max(len(words[row]) for row in counts)
        rank_totals: Counter[int] = Counter()
        nonmodal = len(layer) - modal_count
        color_signs = [
            nested.permutation_sign(nested.layer_map(m, layers, t, color))
            for color in range(5)
        ]
        layer_sign = 1
        for sign in color_signs:
            layer_sign *= sign
        for row, count in counts.items():
            for rank, _ in words[row]:
                rank_totals[rank] += count

        is_defect = len(counts) != 1
        if is_defect:
            total_defect_layers += 1
        if not args.all_layers and not is_defect:
            continue

        print(
            f"layer={t} distinct_rows={len(counts)} modal={modal} "
            f"modal_count={modal_count} nonmodal={nonmodal} max_word_len={max_len} "
            f"rank_totals={dict(sorted(rank_totals.items()))} "
            f"layer_sign={layer_sign} color_signs={color_signs}"
        )
        shown = 0
        for row, count in sorted(
            counts.items(),
            key=lambda kv: (-kv[1], len(words[kv[0]]), kv[0]),
        ):
            if shown >= args.max_rows:
                remaining = len(counts) - shown
                if remaining > 0:
                    print(f"  ... {remaining} more rows")
                break
            print(
                f"  count={count:6d} row={row} "
                f"len={len(words[row]):2d} word={word_text(words[row])}"
            )
            shown += 1

    print(f"defect_layers={total_defect_layers}")


if __name__ == "__main__":
    main()
