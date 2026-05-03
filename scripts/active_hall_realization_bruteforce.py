#!/usr/bin/env python3
"""Small brute-force sanity checks for ActiveHall.HallRealizationGoal.

The script enumerates small active-incidence instances, all count matrices with
the forced row/column sums, filters by the Lean `HallCuts` inequality, and
checks that every surviving matrix is realized by an explicit symboling.

This is not a proof of the theorem.  It is a regression/sanity check for the
finite theorem isolated in docs/ACTIVE_HALL_REALIZATION_REQUEST_20260503.md.
"""

from __future__ import annotations

from itertools import combinations, permutations, product
from typing import Iterable


DEFAULT_CASES = (
    (2, 2, 2),
    (2, 3, 2),
    (2, 3, 3),
    (2, 4, 3),
    (3, 3, 3),
    (3, 4, 3),
)


def subsets(n: int) -> Iterable[set[int]]:
    for mask in range(1 << n):
        yield {i for i in range(n) if (mask >> i) & 1}


def weak_compositions(n: int, k: int) -> Iterable[tuple[int, ...]]:
    if k == 1:
        yield (n,)
        return
    for a in range(n + 1):
        for rest in weak_compositions(n - a, k - 1):
            yield (a,) + rest


def incidences(x_count: int, color_count: int, symbol_count: int):
    active_sets = [set(a) for a in combinations(range(color_count), symbol_count)]
    for indexes in product(range(len(active_sets)), repeat=x_count):
        active = [active_sets[i] for i in indexes]
        if all(any(c in a for a in active) for c in range(color_count)):
            yield active


def symboling_count_set(
    x_count: int,
    color_count: int,
    symbol_count: int,
    active: list[set[int]],
) -> set[tuple[int, ...]]:
    per_x = [list(permutations(tuple(active[x]), symbol_count)) for x in range(x_count)]
    out: set[tuple[int, ...]] = set()
    for choices in product(*per_x):
        counts = [0] * (color_count * symbol_count)
        for perm in choices:
            for sigma, color in enumerate(perm):
                counts[color * symbol_count + sigma] += 1
        out.add(tuple(counts))
    return out


def count_matrices(
    x_count: int,
    color_count: int,
    symbol_count: int,
    active: list[set[int]],
):
    degrees = [
        sum(1 for x in range(x_count) if c in active[x])
        for c in range(color_count)
    ]
    row_options = [
        list(weak_compositions(degrees[c], symbol_count))
        for c in range(color_count)
    ]
    for rows in product(*row_options):
        if all(
            sum(rows[c][sigma] for c in range(color_count)) == x_count
            for sigma in range(symbol_count)
        ):
            yield tuple(
                rows[c][sigma]
                for c in range(color_count)
                for sigma in range(symbol_count)
            )


def hall_cuts_hold(
    matrix: tuple[int, ...],
    x_count: int,
    color_count: int,
    symbol_count: int,
    active: list[set[int]],
) -> bool:
    for colors in subsets(color_count):
        for symbols in subsets(symbol_count):
            mass = sum(
                matrix[c * symbol_count + sigma]
                for c in colors
                for sigma in symbols
            )
            cap = sum(
                min(len(active[x] & colors), len(symbols))
                for x in range(x_count)
            )
            if mass > cap:
                return False
    return True


def run_case(symbol_count: int, color_count: int, x_count: int) -> tuple[int, int]:
    incidence_count = 0
    hall_matrix_count = 0
    for active in incidences(x_count, color_count, symbol_count):
        incidence_count += 1
        realized = symboling_count_set(x_count, color_count, symbol_count, active)
        for matrix in count_matrices(x_count, color_count, symbol_count, active):
            if not hall_cuts_hold(matrix, x_count, color_count, symbol_count, active):
                continue
            hall_matrix_count += 1
            if matrix not in realized:
                rows = [
                    matrix[c * symbol_count : (c + 1) * symbol_count]
                    for c in range(color_count)
                ]
                raise AssertionError(
                    "counterexample found: "
                    f"T={symbol_count}, C={color_count}, X={x_count}, "
                    f"active={[sorted(a) for a in active]}, rows={rows}"
                )
    return incidence_count, hall_matrix_count


def main() -> None:
    for case in DEFAULT_CASES:
        incidence_count, hall_matrix_count = run_case(*case)
        print(
            "ok "
            f"T={case[0]} C={case[1]} X={case[2]} "
            f"incidences={incidence_count} hall_matrices={hall_matrix_count}"
        )
    print("no counterexample in default range")


if __name__ == "__main__":
    main()
