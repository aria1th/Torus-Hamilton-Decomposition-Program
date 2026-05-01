#!/usr/bin/env python3
"""Verify bundled all-zero-set 4+2 additive bridge certificates.

The certificates live in ``D7_current_research_note_bundle_v1_1.zip`` and
contain the row words plus the state-dependent S3 kappa table for m = 5, 7, 9.
This script independently checks the finite product return maps on
A5(m) x A3(m), using the D5 zero-set layer and the odd D3 affine packet.
"""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path
from zipfile import ZipFile


CERT_NAMES = {
    5: "bridge_4plus2_allN_m5_permindex_cert.json",
    7: "bridge_4plus2_allN_m7_rows_kappa_cert.json",
    9: "bridge_4plus2_allN_m9_rows_kappa_cert.json",
}

PERMS3 = list(itertools.permutations(range(3)))

LAMBDA1 = {
    (False, False, False, False, False): (0, 1, 2, 3, 4),
    (True, False, False, False, False): (0, 1, 3, 2, 4),
    (False, True, False, False, False): (0, 1, 2, 4, 3),
    (True, True, False, False, False): (4, 1, 3, 2, 0),
    (False, False, True, False, False): (4, 1, 2, 3, 0),
    (True, False, True, False, False): (4, 1, 3, 0, 2),
    (False, True, True, False, False): (1, 0, 2, 4, 3),
    (True, True, True, False, False): (1, 0, 3, 4, 2),
    (False, False, False, True, False): (1, 0, 2, 3, 4),
    (True, False, False, True, False): (1, 3, 0, 2, 4),
    (False, True, False, True, False): (3, 0, 2, 4, 1),
    (True, True, False, True, False): (4, 3, 0, 2, 1),
    (False, False, True, True, False): (4, 2, 1, 3, 0),
    (True, False, True, True, False): (4, 3, 1, 0, 2),
    (False, True, True, True, False): (3, 2, 1, 4, 0),
    (True, True, True, True, False): (0, 1, 2, 3, 4),
    (False, False, False, False, True): (0, 2, 1, 3, 4),
    (True, False, False, False, True): (0, 2, 1, 4, 3),
    (False, True, False, False, True): (0, 2, 4, 1, 3),
    (True, True, False, False, True): (4, 2, 3, 1, 0),
    (False, False, True, False, True): (2, 4, 1, 3, 0),
    (True, False, True, False, True): (2, 4, 1, 0, 3),
    (False, True, True, False, True): (2, 0, 4, 1, 3),
    (True, True, True, False, True): (0, 1, 2, 3, 4),
    (False, False, False, True, True): (1, 0, 3, 2, 4),
    (True, False, False, True, True): (1, 2, 0, 4, 3),
    (False, True, False, True, True): (3, 0, 4, 2, 1),
    (True, True, False, True, True): (0, 1, 2, 3, 4),
    (False, False, True, True, True): (1, 4, 3, 2, 0),
    (True, False, True, True, True): (0, 1, 2, 3, 4),
    (False, True, True, True, True): (0, 1, 2, 3, 4),
    (True, True, True, True, True): (0, 1, 2, 3, 4),
}


def default_bundle_path() -> Path:
    return Path(__file__).resolve().parents[2] / "D7_current_research_note_bundle_v1_1.zip"


def base_tuple(index: int, m: int) -> tuple[int, int, int, int]:
    xs = [0, 0, 0, 0]
    for i in range(3, -1, -1):
        xs[i] = index % m
        index //= m
    return (xs[0], xs[1], xs[2], xs[3])


def base_index(xs: tuple[int, int, int, int], m: int) -> int:
    index = 0
    for x in xs:
        index = index * m + x
    return index


def fiber_tuple(index: int, m: int) -> tuple[int, int]:
    return (index // m, index % m)


def fiber_index(ys: tuple[int, int], m: int) -> int:
    return ys[0] * m + ys[1]


def add_base_q(xs: tuple[int, int, int, int], direction: int, m: int) -> tuple[int, int, int, int]:
    if direction == 4:
        return xs
    out = list(xs)
    out[direction] = (out[direction] + 1) % m
    return (out[0], out[1], out[2], out[3])


def add_fiber_q(ys: tuple[int, int], direction: int, m: int) -> tuple[int, int]:
    if direction == 2:
        return ys
    out = list(ys)
    out[direction] = (out[direction] + 1) % m
    return (out[0], out[1])


def lambda1_direction(xs: tuple[int, int, int, int], slot: int, m: int) -> int:
    full = (xs[0], xs[1], xs[2], xs[3], (-sum(xs)) % m)
    mask_minus_one = tuple(full[(i + 1) % 5] == 0 for i in range(5))
    return LAMBDA1[mask_minus_one][slot]


def d3_odd_direction(layer: int, ys: tuple[int, int], slot: int, m: int) -> int:
    k_coord = (-ys[0] - ys[1] + layer) % m
    if slot == 0:
        if layer == 0 and k_coord != 0:
            return 1
        if layer == 1 % m:
            return 2
        return 0
    if slot == 1:
        if layer == 0:
            return 2
        if layer == 1 % m and k_coord == 0:
            return 0
        return 1
    if layer in {0, 1 % m}:
        return 1 if k_coord == 0 else 0
    return 2


def validate_certificate(cert: dict) -> None:
    m = cert.get("m")
    rows = cert.get("rows")
    kappa = cert.get("kappa_perm_indices")
    if not isinstance(m, int) or m <= 0:
        raise ValueError("certificate field 'm' must be a positive integer")
    if not isinstance(rows, list) or len(rows) != 7:
        raise ValueError(f"m={m}: expected seven row words")
    for c, row in enumerate(rows):
        if not isinstance(row, list) or len(row) != m:
            raise ValueError(f"m={m}: row {c} must have length m")
        if any(not isinstance(x, int) or x < 0 or x > 6 for x in row):
            raise ValueError(f"m={m}: row {c} contains a non-slot entry")
    for t in range(m):
        column = sorted(rows[c][t] for c in range(7))
        if column != list(range(7)):
            raise ValueError(f"m={m}: column {t} is not a permutation of 0..6")
    if not isinstance(kappa, list) or len(kappa) != m:
        raise ValueError(f"m={m}: expected one kappa table per layer")
    for t, layer_table in enumerate(kappa):
        if not isinstance(layer_table, list) or len(layer_table) != m**4:
            raise ValueError(f"m={m}: kappa layer {t} must have length m^4")
        if any(not isinstance(x, int) or x < 0 or x >= len(PERMS3) for x in layer_table):
            raise ValueError(f"m={m}: kappa layer {t} contains a non-permutation index")


def assert_single_cycle(size: int, start: int, step, label: str) -> None:
    seen = bytearray(size)
    state = start
    for step_count in range(size):
        if not 0 <= state < size:
            raise ValueError(f"{label}: state {state} is outside 0..{size - 1}")
        if seen[state]:
            raise ValueError(f"{label}: repeated state {state} after {step_count} steps")
        seen[state] = 1
        state = step(state)
    if state != start:
        raise ValueError(f"{label}: did not return to start {start}; ended at {state}")


class BridgeModel:
    def __init__(self, m: int):
        self.m = m
        self.fiber_size = m * m
        self.base_direction = [[0] * (m**4) for _ in range(5)]
        self.base_next = [[0] * (m**4) for _ in range(5)]
        for slot in range(5):
            for b in range(m**4):
                xs = base_tuple(b, m)
                direction = lambda1_direction(xs, slot, m)
                self.base_direction[slot][b] = direction
                self.base_next[slot][b] = base_index(add_base_q(xs, direction, m), m)
        self.fiber_forced_q0 = [0] * self.fiber_size
        self.fiber_next = [
            [[0] * self.fiber_size for _slot in range(3)] for _layer in range(m)
        ]
        for f in range(self.fiber_size):
            ys = fiber_tuple(f, m)
            self.fiber_forced_q0[f] = fiber_index(add_fiber_q(ys, 0, m), m)
            for layer in range(m):
                for slot in range(3):
                    direction = d3_odd_direction(layer, ys, slot, m)
                    self.fiber_next[layer][slot][f] = fiber_index(
                        add_fiber_q(ys, direction, m), m
                    )

    def layer_step(self, state: int, layer: int, output_slot: int, kappa: list[list[int]]) -> int:
        base = state // self.fiber_size
        fiber = state % self.fiber_size
        if output_slot < 5:
            direction = self.base_direction[output_slot][base]
            next_base = self.base_next[output_slot][base]
            if direction != 4:
                next_fiber = self.fiber_forced_q0[fiber]
            else:
                perm = PERMS3[kappa[layer][base]]
                next_fiber = self.fiber_next[layer][perm[0]][fiber]
        else:
            perm = PERMS3[kappa[layer][base]]
            next_base = base
            next_fiber = self.fiber_next[layer][perm[output_slot - 4]][fiber]
        return next_base * self.fiber_size + next_fiber

    def return_step(self, state: int, row: list[int], kappa: list[list[int]]) -> int:
        for layer, output_slot in enumerate(row):
            state = self.layer_step(state, layer, output_slot, kappa)
        return state

    def base_return_step(self, base: int, row: list[int]) -> int:
        for output_slot in row:
            if output_slot < 5:
                base = self.base_next[output_slot][base]
        return base

    def section_return_step(
        self,
        fiber: int,
        row: list[int],
        kappa: list[list[int]],
        base_point: int,
        base_period: int,
    ) -> int:
        state = base_point * self.fiber_size + fiber
        for _ in range(base_period):
            state = self.return_step(state, row, kappa)
        base = state // self.fiber_size
        if base != base_point:
            raise ValueError(
                f"section return left base point {base_point}; ended at base {base}"
            )
        return state % self.fiber_size


def verify_certificate(cert: dict) -> str:
    validate_certificate(cert)
    m = cert["m"]
    rows = cert["rows"]
    kappa = cert["kappa_perm_indices"]
    total_states = m**6
    base_period = m**4
    model = BridgeModel(m)
    for color, row in enumerate(rows):
        assert_single_cycle(
            base_period,
            0,
            lambda base, row=row: model.base_return_step(base, row),
            f"m={m}: color {color} base return",
        )
        assert_single_cycle(
            model.fiber_size,
            0,
            lambda fiber, row=row: model.section_return_step(
                fiber, row, kappa, 0, base_period
            ),
            f"m={m}: color {color} fiber section return",
        )
        assert_single_cycle(
            total_states,
            0,
            lambda state, row=row: model.return_step(state, row, kappa),
            f"m={m}: color {color} product return",
        )
    return (
        f"verified m={m} product_states={total_states} rows=7 "
        "base_cycles=single section_cycles=single return_cycles=single"
    )


def load_bundle(path: Path, only: set[int] | None) -> list[dict]:
    certs = []
    with ZipFile(path) as bundle:
        for m, name in CERT_NAMES.items():
            if only is not None and m not in only:
                continue
            certs.append(json.loads(bundle.read(name)))
    return certs


def load_json_files(paths: list[Path]) -> list[dict]:
    return [json.loads(path.read_text()) for path in paths]


def parse_only(value: str | None) -> set[int] | None:
    if value is None:
        return None
    out = {int(part) for part in value.split(",") if part}
    unknown = out - set(CERT_NAMES)
    if unknown:
        raise ValueError(f"unsupported modulus in --only: {sorted(unknown)}")
    return out


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--bundle",
        type=Path,
        default=default_bundle_path(),
        help="path to D7_current_research_note_bundle_v1_1.zip",
    )
    parser.add_argument(
        "--cert-json",
        type=Path,
        action="append",
        default=[],
        help="verify an extracted certificate JSON instead of reading the bundle",
    )
    parser.add_argument(
        "--only",
        help="comma-separated subset of bundled moduli to verify, e.g. 5,7",
    )
    args = parser.parse_args()
    only = parse_only(args.only)
    if args.cert_json:
        certs = load_json_files(args.cert_json)
    else:
        certs = load_bundle(args.bundle, only)
    for cert in certs:
        print(verify_certificate(cert))


if __name__ == "__main__":
    main()
