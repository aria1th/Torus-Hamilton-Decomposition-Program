#!/usr/bin/env python3
"""Small finite sanity checks for the q>=2 signed-column field.

This script is audit-only.  It verifies two facts over small finite domains:

1. The broad arbitrary-row packing goal is false; the Lean counterexample
   `PrefixCount.not_qge2SignedColumnPackingGoal` has cut bounds but no packing.
2. The active ordinary-row/proper-cut target has no counterexample for small
   even `n` tested here.  The default checks only `n=4`; use `--max-n 6` for a
   slower exhaustive `n=4,6` pass.
"""

from __future__ import annotations

import argparse
from functools import lru_cache
from itertools import combinations, product

SIGNED_VALS = (-2, -1, 1, 2)


def qge2_column_capacity(n: int, j: int, c: int) -> int:
    return min(2 * j, 2 * (n - j) - c)


@lru_cache(maxsize=None)
def signed_column_vectors(n: int, c: int) -> tuple[tuple[int, ...], ...]:
    return tuple(v for v in product(SIGNED_VALS, repeat=n) if sum(v) == -c)


@lru_cache(maxsize=None)
def possible_row_sums(entries_left: int) -> frozenset[int]:
    sums = {0}
    for _ in range(entries_left):
        sums = {s + v for s in sums for v in SIGNED_VALS}
    return frozenset(sums)


def proper_cut_bounds_hold(row_target: tuple[int, ...], columns: tuple[int, ...]) -> bool:
    n = len(row_target)
    for mask in range(1, (1 << n) - 1):
        j = mask.bit_count()
        lhs = sum(row_target[i] for i in range(n) if (mask >> i) & 1)
        rhs = sum(qge2_column_capacity(n, j, c) for c in columns)
        if lhs > rhs:
            return False
    return True


def all_cut_bounds_hold(row_target: tuple[int, ...], columns: tuple[int, ...]) -> bool:
    n = len(row_target)
    for mask in range(1 << n):
        j = mask.bit_count()
        lhs = sum(row_target[i] for i in range(n) if (mask >> i) & 1)
        rhs = sum(qge2_column_capacity(n, j, c) for c in columns)
        if lhs > rhs:
            return False
    return True


def has_signed_packing(row_target: tuple[int, ...], columns: tuple[int, ...]) -> bool:
    n = len(row_target)
    columns = tuple(sorted(columns, reverse=True))

    @lru_cache(maxsize=None)
    def dfs(k: int, residual: tuple[int, ...]) -> bool:
        entries_left = len(columns) - k
        possible = possible_row_sums(entries_left)
        if any(x not in possible for x in residual):
            return False
        if k == len(columns):
            return all(x == 0 for x in residual)

        possible_after = possible_row_sums(entries_left - 1)
        candidates: list[tuple[int, tuple[int, ...]]] = []
        for vector in signed_column_vectors(n, columns[k]):
            next_residual = tuple(residual[i] - vector[i] for i in range(n))
            if all(x in possible_after for x in next_residual):
                candidates.append((sum(abs(x) for x in next_residual), next_residual))
        candidates.sort()
        return any(dfs(k + 1, next_residual) for _, next_residual in candidates)

    return dfs(0, row_target)


def verify_arbitrary_row_counterexample() -> None:
    row_target = (-6, -5, 2, 6)
    columns = (1, 1, 1)
    assert sum(row_target) == -sum(columns)
    assert all_cut_bounds_hold(row_target, columns)
    assert not has_signed_packing(row_target, columns)
    print("arbitrary-row counterexample verified: n=4, c=(1,1,1), R=(-6,-5,2,6)")


def ordinary_row_targets(n: int):
    for r in range(1, n):
        if r % 2 == 0:
            continue
        for a in product((1, 2), repeat=n):
            capital_c = sum(a)
            column_choices = [
                c for c in product((1, 2), repeat=n - 1) if sum(c) == capital_c
            ]
            if not column_choices:
                continue
            for eps_ones in combinations(range(n), r):
                eps = [0] * n
                for i in eps_ones:
                    eps[i] = 1
                row_target = tuple(r - a[i] - n * eps[i] for i in range(n))
                for columns in column_choices:
                    yield r, a, tuple(eps), row_target, columns


def verify_ordinary_proper_cut_small(max_n: int) -> None:
    for n in range(4, max_n + 1, 2):
        checked = 0
        skipped = 0
        for r, a, eps, row_target, columns in ordinary_row_targets(n):
            if not proper_cut_bounds_hold(row_target, columns):
                skipped += 1
                continue
            checked += 1
            if not has_signed_packing(row_target, columns):
                raise AssertionError(
                    "ordinary proper-cut counterexample "
                    f"n={n} r={r} a={a} eps={eps} c={columns} R={row_target}"
                )
        print(f"ordinary proper-cut exhaustive check passed: n={n}, checked={checked}, skipped={skipped}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--max-n",
        type=int,
        default=4,
        help="largest even n to exhaustively check for ordinary-row data; default 4",
    )
    args = parser.parse_args()
    if args.max_n < 4 or args.max_n % 2:
        raise SystemExit("--max-n must be an even integer >= 4")

    verify_arbitrary_row_counterexample()
    verify_ordinary_proper_cut_small(args.max_n)


if __name__ == "__main__":
    main()
