#!/usr/bin/env python3
"""Search helpers for the H2 terminal transported seed-row slot.

The Lean target `TerminalA2M4TransportedSeedRowRealization` asks for

* an equivalence `eT : Q4 ~= (Z/4)^2`,
* four terminal Latin/RF2 root-flat layers, and
* first returns conjugate through `eT` to the paper terminal maps `F_i`.

This script handles the inner finite problem: for a fixed `eT`, decide whether
the conjugated terminal return triple factors into four RF1/RF2 terminal layers.
It uses a meet-in-the-middle table of all two-layer products, so it is intended
as a witness/obstruction audit before any Lean table is generated.
"""

from __future__ import annotations

import argparse
import json
import random
from dataclasses import dataclass
from pathlib import Path

from verify_d5m4_h2_realization import Q_STATES, terminal_return, root_step_d3

N = 16
COLORS = range(3)
DIRECTIONS = range(3)
ORIGIN = Q_STATES.index((0, 0))


Perm = tuple[int, ...]
Layer = tuple[Perm, Perm, Perm]


def compose(p: Perm, q: Perm) -> Perm:
    """Permutation composition `p o q`, represented by image tuples."""
    return tuple(p[q[i]] for i in range(N))


def invert(p: Perm) -> Perm:
    out = [0] * N
    for i, j in enumerate(p):
        out[j] = i
    return tuple(out)


def pack_layer(layer: Layer) -> bytes:
    return bytes([x for perm in layer for x in perm])


def unpack_layer(blob: bytes) -> Layer:
    assert len(blob) == 3 * N
    return (
        tuple(blob[0:N]),
        tuple(blob[N : 2 * N]),
        tuple(blob[2 * N : 3 * N]),
    )


def row_layers() -> list[tuple[Layer, tuple[tuple[int, ...], ...]]]:
    """All single terminal layers satisfying RF1 and RF2.

    The second component records the direction row table as
    `directions[source][color]`.
    """

    q_index = {q: i for i, q in enumerate(Q_STATES)}
    step_target = [
        [q_index[root_step_d3(d, q)] for d in DIRECTIONS] for q in Q_STATES
    ]
    single_color: list[tuple[Perm, tuple[int, ...]]] = []

    dirs: list[int | None] = [None] * N

    def go(used_targets: int) -> None:
        if all(d is not None for d in dirs):
            dir_tuple = tuple(d for d in dirs if d is not None)
            perm = tuple(step_target[q][dir_tuple[q]] for q in range(N))
            single_color.append((perm, dir_tuple))
            return

        best = -1
        best_choices: list[int] | None = None
        for q, direction in enumerate(dirs):
            if direction is not None:
                continue
            choices = [
                d for d in DIRECTIONS
                if not ((used_targets >> step_target[q][d]) & 1)
            ]
            if best_choices is None or len(choices) < len(best_choices):
                best = q
                best_choices = choices
                if len(choices) <= 1:
                    break
        assert best_choices is not None
        for d in best_choices:
            target = step_target[best][d]
            dirs[best] = d
            go(used_targets | (1 << target))
            dirs[best] = None

    go(0)
    layers: list[tuple[Layer, tuple[tuple[int, ...], ...]]] = []

    for perm0, dirs0 in single_color:
        for perm1, dirs1 in single_color:
            if any(dirs0[q] == dirs1[q] for q in range(N)):
                continue
            dirs2 = tuple(({0, 1, 2} - {dirs0[q], dirs1[q]}).pop() for q in range(N))
            perm2 = tuple(step_target[q][dirs2[q]] for q in range(N))
            if len(set(perm2)) != N:
                continue
            rows = tuple((dirs0[q], dirs1[q], dirs2[q]) for q in range(N))
            layers.append(((perm0, perm1, perm2), rows))
    return layers


@dataclass(frozen=True)
class PairTable:
    layers: list[tuple[Layer, tuple[tuple[int, ...], ...]]]
    pair_index: dict[bytes, tuple[int, int]]


def build_pair_table(verbose: bool = False) -> PairTable:
    layers = row_layers()
    if verbose:
        print(f"terminal_rf_layers={len(layers)}", flush=True)
    pair_index: dict[bytes, tuple[int, int]] = {}
    for i, (left, _left_rows) in enumerate(layers):
        if verbose and i != 0 and i % 240 == 0:
            print(f"pair_table_progress={i}/{len(layers)}", flush=True)
        for j, (right, _right_rows) in enumerate(layers):
            product_layer: Layer = (
                compose(right[0], left[0]),
                compose(right[1], left[1]),
                compose(right[2], left[2]),
            )
            pair_index.setdefault(pack_layer(product_layer), (i, j))
    return PairTable(layers=layers, pair_index=pair_index)


def target_triple_for_emap(emap: list[int]) -> Layer:
    """Return `eT o F_i o eT^-1` on standard root indices."""
    if sorted(emap) != list(range(N)):
        raise ValueError("emap must be a permutation of 0..15")
    inv = [0] * N
    for q, r in enumerate(emap):
        inv[r] = q
    q_index = {q: i for i, q in enumerate(Q_STATES)}
    out: list[Perm] = []
    for c in COLORS:
        image = []
        for r in range(N):
            q = inv[r]
            fq = q_index[terminal_return(c, Q_STATES[q])]
            image.append(emap[fq])
        out.append(tuple(image))
    return (out[0], out[1], out[2])


def factor_fixed_emap(table: PairTable, emap: list[int]) -> tuple[int, int, int, int] | None:
    target = target_triple_for_emap(emap)
    for first_blob, first_pair in table.pair_index.items():
        first = unpack_layer(first_blob)
        needed: Layer = (
            compose(target[0], invert(first[0])),
            compose(target[1], invert(first[1])),
            compose(target[2], invert(first[2])),
        )
        second_pair = table.pair_index.get(pack_layer(needed))
        if second_pair is not None:
            return (first_pair[0], first_pair[1], second_pair[0], second_pair[1])
    return None


def identity_emap() -> list[int]:
    return list(range(N))


def random_emap(rng: random.Random) -> list[int]:
    tail = [i for i in range(N) if i != ORIGIN]
    rng.shuffle(tail)
    emap = [0] * N
    emap[ORIGIN] = ORIGIN
    for q, r in zip([i for i in range(N) if i != ORIGIN], tail):
        emap[q] = r
    return emap


def write_witness(
    path: Path,
    table: PairTable,
    emap: list[int],
    factor: tuple[int, int, int, int],
) -> None:
    payload = {
        "emap": emap,
        "layers": [
            [list(row) for row in table.layers[idx][1]] for idx in factor
        ],
        "layer_indices": list(factor),
    }
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--identity", action="store_true")
    parser.add_argument("--random", type=int, default=0)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--emap-json", type=Path)
    parser.add_argument("--witness-out", type=Path)
    args = parser.parse_args()

    table = build_pair_table(verbose=True)
    print(f"two_layer_products={len(table.pair_index)}", flush=True)

    candidates: list[tuple[str, list[int]]] = []
    if args.identity:
        candidates.append(("identity", identity_emap()))
    if args.emap_json is not None:
        candidates.append(("emap-json", json.loads(args.emap_json.read_text())))
    rng = random.Random(args.seed)
    for i in range(args.random):
        candidates.append((f"random-{i}", random_emap(rng)))

    if not candidates:
        candidates.append(("identity", identity_emap()))

    for label, emap in candidates:
        print(f"checking={label}", flush=True)
        factor = factor_fixed_emap(table, emap)
        if factor is None:
            print(f"[no] {label}: no four-layer RF1/RF2 factorization", flush=True)
        else:
            print(f"[yes] {label}: layer_indices={factor}", flush=True)
            if args.witness_out is not None:
                write_witness(args.witness_out, table, emap, factor)
                print(f"witness_out={args.witness_out}", flush=True)
            return


if __name__ == "__main__":
    main()
