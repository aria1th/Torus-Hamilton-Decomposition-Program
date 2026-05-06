#!/usr/bin/env python3
"""Export existing D5 even Route-E witnesses as nested-diagnostic JSON tables.

The verifier `verify_d5_even_routeE.py` stores schedules in the original
root-flat coordinates.  The nested diagnostics use prefix stop ranks on
`Q4 = (Z/m)^4`.  This script converts the known finite/small-seam witnesses to
the JSON format consumed by `d5_routeE_nested_diagnostics.py`.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import verify_d5_even_routeE as routee


def unidx(i: int, m: int, n: int = 4) -> tuple[int, ...]:
    z = [0] * n
    for k in range(n - 1, -1, -1):
        z[k] = i % m
        i //= m
    return tuple(z)


def prefix_to_root_state(z: tuple[int, int, int, int], m: int) -> routee.State:
    z0, z1, z2, z3 = z
    return (
        (-z3) % m,
        (z3 - z2) % m,
        (z2 - z1) % m,
        (z1 - z0) % m,
        z0 % m,
    )


def symbol_direction(maps: dict[routee.Symbol, list[int]], idx: dict[routee.State, int],
                     m: int, symbol: routee.Symbol, w: routee.State) -> int:
    start = idx[w]
    target = maps[symbol][start]
    for direction in range(5):
        if routee.q_step(m, idx, w, direction) == target:
            return direction
    raise ValueError(f"symbol {symbol} at {w} does not match any basis direction")


def rows_for_m(m: int) -> list[list[routee.Symbol]]:
    if m == 4:
        return routee.M4_ROWS
    if m in routee.SMALL_SEAM_CASES:
        data = routee.SMALL_SEAM_CASES[m]
        return routee.one_e_rows(m, data["slot"], data["counts"])
    raise ValueError(f"no embedded D5 even Route-E witness for m={m}")


def export_layers(m: int) -> dict:
    states, idx, maps = routee.build_symbol_maps(m)
    del states
    rows = rows_for_m(m)
    if any(len(row) != m for row in rows):
        raise ValueError(f"expected every color row to have length {m}")
    n = m**4
    layers: list[list[list[int]]] = []
    for t in range(m):
        layer: list[list[int]] = []
        for zidx in range(n):
            z = unidx(zidx, m)
            w = prefix_to_root_state(z, m)
            stops: list[int] = []
            for color in range(5):
                direction = symbol_direction(maps, idx, m, rows[color][t], w)
                stops.append(4 - direction)
            layer.append(stops)
        layers.append(layer)
    return {"m": m, "layers": layers}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--m", type=int, required=True)
    parser.add_argument("--json-out", type=Path, required=True)
    args = parser.parse_args()

    payload = export_layers(args.m)
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(payload) + "\n")
    print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
