#!/usr/bin/env python3
"""Analyze the local Lambda_E defect layer in D5 Route E.

The one-Lambda_E witnesses are constant on all but one layer.  The exceptional
layer is controlled by a shifted zero mask.  This script prints the reachable
zero masks, the induced local stop-rank permutations, and a shortest
decomposition into adjacent stop-rank switches relative to the bulk row
`(4,3,2,1,0)`.
"""

from __future__ import annotations

import argparse
import collections
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import verify_d5_even_routeE as routee  # noqa: E402


BULK_ROW = (4, 3, 2, 1, 0)
PRED_NAMES = ["z4=z3", "z3=z2", "z2=z1", "z1=0", "z4=0"]


def row_for_mask(mask: int) -> tuple[int, ...]:
    return tuple(4 - routee.lam(routee.PERT, mask, color) for color in range(5))


def apply_adjacent_value_swap(row: tuple[int, ...], rank: int) -> tuple[int, ...]:
    out = list(row)
    i = out.index(rank)
    j = out.index(rank + 1)
    out[i], out[j] = out[j], out[i]
    return tuple(out)


def shortest_words_from_bulk() -> dict[tuple[int, ...], list[tuple[int, int]]]:
    prev: dict[tuple[int, ...], tuple[tuple[int, ...] | None, int | None]] = {
        BULK_ROW: (None, None)
    }
    queue = collections.deque([BULK_ROW])
    while queue:
        row = queue.popleft()
        for rank in range(4):
            nxt = apply_adjacent_value_swap(row, rank)
            if nxt not in prev:
                prev[nxt] = (row, rank)
                queue.append(nxt)

    words: dict[tuple[int, ...], list[tuple[int, int]]] = {}
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


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--csv", action="store_true")
    args = parser.parse_args()

    reachable = [mask for mask in range(32) if mask in routee.CANON]
    rows: dict[tuple[int, ...], list[int]] = {}
    for mask in reachable:
        rows.setdefault(row_for_mask(mask), []).append(mask)
    words = shortest_words_from_bulk()

    if args.csv:
        print("row,masks,predicates,adjacent_length,adjacent_word")
    else:
        print(f"reachable_masks={len(reachable)} distinct_rows={len(rows)}")
    for row, masks in sorted(rows.items(), key=lambda kv: (len(words[kv[0]]), kv[0])):
        mask_text = " ".join(f"{mask:05b}" for mask in masks)
        pred_text = " | ".join(
            "&".join(PRED_NAMES[i] for i in range(5) if mask & (1 << i)) or "none"
            for mask in masks
        )
        word = words[row]
        word_text = " ".join(f"{a}/{b}" for a, b in word) or "identity"
        if args.csv:
            print(f'"{row}","{mask_text}","{pred_text}",{len(word)},"{word_text}"')
        else:
            print(
                f"row={row} masks={mask_text} predicates={pred_text} "
                f"adjacent_length={len(word)} word={word_text}"
            )


if __name__ == "__main__":
    main()
