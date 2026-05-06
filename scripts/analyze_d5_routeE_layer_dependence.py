#!/usr/bin/env python3
"""Diagnose whether a D5 Route-E layer table is stationary.

The stationary seam ansatz ignores the layer coordinate.  For D5 even Route E
this is too narrow: the stationary SAT class is already UNSAT at m=2, while the
full layered class has a SAT witness.  This script gives a small reproducible
diagnostic for any exported/full-layer JSON table:

* compare layer rows across layers;
* count layer/color maps and return cycles;
* report whether each color is stationary and, if so, whether its return is a
  power of one repeated layer map.

It is intentionally a checker/summary tool, not a searcher.
"""

from __future__ import annotations

import argparse
from collections import Counter
from pathlib import Path

import d5_routeE_nested_diagnostics as nested


def compose(a: list[int], b: list[int]) -> list[int]:
    """Return b after a: x |-> b[a[x]]."""
    return [b[x] for x in a]


def pow_perm(perm: list[int], exponent: int) -> list[int]:
    out = list(range(len(perm)))
    for _ in range(exponent):
        out = [perm[x] for x in out]
    return out


def row_signature(layer: list[list[int]]) -> tuple[tuple[int, ...], ...]:
    return tuple(tuple(row) for row in layer)


def layer_map_signature(m: int, layers: list[list[list[int]]], t: int, color: int) -> tuple[int, ...]:
    return tuple(nested.layer_map(m, layers, t, color))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("json_table", type=Path)
    args = parser.parse_args()

    m, layers = nested.load_layers(args.json_table)
    layer_sigs = [row_signature(layer) for layer in layers]
    distinct_layer_rows = len(set(layer_sigs))
    row_counts = Counter(layer_sigs)
    print(f"m={m} vertices={m**4}")
    print(f"distinct_full_layers={distinct_layer_rows}")
    print(f"full_layer_multiplicities={sorted(row_counts.values(), reverse=True)[:10]}")
    print(f"stationary_full_table={distinct_layer_rows == 1}")

    for color in range(5):
        map_sigs = [layer_map_signature(m, layers, t, color) for t in range(m)]
        distinct_maps = len(set(map_sigs))
        stationary = distinct_maps == 1
        ret = nested.return_map(m, layers, color)
        ret_cycles = nested.permutation_cycles(ret)
        repeated_cycles: list[int] | None = None
        repeated_matches = False
        if stationary:
            repeated = pow_perm(list(map_sigs[0]), m)
            repeated_matches = repeated == ret
            repeated_cycles = nested.permutation_cycles(repeated)
        print(
            f"color={color} distinct_layer_maps={distinct_maps} "
            f"stationary={stationary} return_cycles={ret_cycles}"
        )
        if stationary:
            print(
                f"  repeated_layer_power_matches={repeated_matches} "
                f"repeated_cycles={repeated_cycles}"
            )


if __name__ == "__main__":
    main()
