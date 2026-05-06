#!/usr/bin/env python3
"""Diagnostics for D5 Route-E nested root-flat repair candidates.

Input JSON format:

    {
      "m": 6,
      "layers": [
        [[s_0_0, ..., s_0_4], ..., [s_N_0, ..., s_N_4]],
        ...
      ]
    }

There must be exactly `m` layers.  Each layer has `m^4` rows, indexed in
lexicographic base-`m` order by `(z1,z2,z3,z4)`, and each row lists the five
stop ranks assigned to colors `0..4`.

This script is not a searcher.  It is an early-fail gate for candidate
direction fields:

* RF1 local Latin at every `(t,z)`;
* RF2 layer bijectivity for every `(t,color)`;
* even-modulus sign product diagnostic;
* nested first-return diagnostics along
  `z1=0`, then `z2=0`, then `z3=0`, then `z4=0`.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path


def unidx(i: int, m: int, n: int = 4) -> tuple[int, ...]:
    out = [0] * n
    for k in range(n - 1, -1, -1):
        out[k] = i % m
        i //= m
    return tuple(out)


def idx(z: tuple[int, ...], m: int) -> int:
    out = 0
    for a in z:
        out = out * m + a
    return out


def sub_stop(zidx: int, m: int, stop: int) -> int:
    z = list(unidx(zidx, m))
    for i in range(stop):
        z[i] = (z[i] - 1) % m
    return idx(tuple(z), m)


def permutation_cycles(perm: list[int]) -> list[int]:
    seen = [False] * len(perm)
    cycles: list[int] = []
    for start in range(len(perm)):
        if seen[start]:
            continue
        x = start
        length = 0
        while not seen[x]:
            seen[x] = True
            length += 1
            x = perm[x]
        cycles.append(length)
    cycles.sort()
    return cycles


def permutation_sign(perm: list[int]) -> int:
    # sign = (-1)^(N - number_of_cycles)
    return -1 if (len(perm) - len(permutation_cycles(perm))) % 2 else 1


@dataclass
class FirstReturn:
    section_size: int
    ambient_size: int
    time_sum: int
    cycles: list[int]
    ok_permutation: bool
    ok_time_sum: bool
    map_on_section: dict[int, int]
    section: list[int]


def first_return(perm: dict[int, int], domain: list[int], section: list[int]) -> FirstReturn:
    section_pos = {x: i for i, x in enumerate(section)}
    domain_set = set(domain)
    section_set = set(section)
    image: list[int] = []
    times: list[int] = []
    for start in section:
        x = perm[start]
        t = 1
        while x not in section_set:
            if x not in domain_set:
                raise ValueError(f"map leaves current domain at {x}")
            x = perm[x]
            t += 1
            if t > len(domain):
                raise ValueError(f"no first return from {start}")
        image.append(section_pos[x])
        times.append(t)
    ok_perm = sorted(image) == list(range(len(section)))
    cycles = permutation_cycles(image) if ok_perm else []
    return FirstReturn(
        section_size=len(section),
        ambient_size=len(domain),
        time_sum=sum(times),
        cycles=cycles,
        ok_permutation=ok_perm,
        ok_time_sum=sum(times) == len(domain),
        map_on_section={section[i]: section[image[i]] for i in range(len(section))},
        section=section,
    )


def load_layers(path: Path) -> tuple[int, list[list[list[int]]]]:
    data = json.loads(path.read_text())
    m = int(data["m"])
    layers = data["layers"]
    n = m**4
    if len(layers) != m:
        raise ValueError(f"expected {m} layers, got {len(layers)}")
    for t, layer in enumerate(layers):
        if len(layer) != n:
            raise ValueError(f"layer {t}: expected {n} rows, got {len(layer)}")
        for z, row in enumerate(layer):
            if len(row) != 5:
                raise ValueError(f"layer {t}, row {z}: expected 5 stops")
            if any((not isinstance(stop, int)) or stop < 0 or stop > 4 for stop in row):
                raise ValueError(f"layer {t}, row {z}: invalid stop row {row}")
    return m, layers


def check_rf1(m: int, layers: list[list[list[int]]]) -> list[str]:
    errors: list[str] = []
    want = [0, 1, 2, 3, 4]
    for t, layer in enumerate(layers):
        for z, row in enumerate(layer):
            if sorted(row) != want:
                errors.append(f"RF1 fail t={t} z={z} row={row}")
                if len(errors) >= 10:
                    return errors
    return errors


def layer_map(m: int, layers: list[list[list[int]]], t: int, color: int) -> list[int]:
    return [sub_stop(z, m, layers[t][z][color]) for z in range(m**4)]


def check_rf2(m: int, layers: list[list[list[int]]]) -> tuple[list[str], int]:
    errors: list[str] = []
    sign_product = 1
    n = m**4
    for t in range(m):
        for color in range(5):
            perm = layer_map(m, layers, t, color)
            if sorted(perm) != list(range(n)):
                errors.append(f"RF2 fail t={t} color={color}")
                if len(errors) >= 10:
                    return errors, sign_product
            else:
                sign_product *= permutation_sign(perm)
    return errors, sign_product


def return_map(m: int, layers: list[list[list[int]]], color: int) -> list[int]:
    n = m**4
    out = list(range(n))
    for t in range(m):
        layer = layers[t]
        out = [sub_stop(z, m, layer[z][color]) for z in out]
    return out


def nested_diagnostics(m: int, perm: list[int]) -> list[FirstReturn]:
    domain = list(range(m**4))
    current_perm = {z: perm[z] for z in domain}
    results: list[FirstReturn] = []
    for level in range(4):
        section = [z for z in domain if unidx(z, m)[level] == 0]
        fr = first_return(current_perm, domain, section)
        results.append(fr)
        domain = section
        current_perm = fr.map_on_section
    return results


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("json_table", type=Path)
    parser.add_argument("--color", type=int, action="append", help="restrict nested diagnostics to colors")
    args = parser.parse_args()

    m, layers = load_layers(args.json_table)
    rf1_errors = check_rf1(m, layers)
    rf2_errors, sign_product = check_rf2(m, layers)
    sign_target = -1 if (5 * (m**4 - 1)) % 2 else 1

    print(f"m={m} vertices={m**4}")
    print(f"rf1_ok={not rf1_errors}")
    for err in rf1_errors:
        print(err)
    print(f"rf2_ok={not rf2_errors}")
    for err in rf2_errors:
        print(err)
    print(f"sign_product={sign_product} sign_target={sign_target} sign_ok={sign_product == sign_target}")

    colors = args.color if args.color is not None else list(range(5))
    for color in colors:
        perm = return_map(m, layers, color)
        is_perm = sorted(perm) == list(range(m**4))
        cycles = permutation_cycles(perm) if is_perm else []
        print(f"color={color} return_perm={is_perm} return_cycles={cycles[:20]}")
        if not is_perm:
            continue
        for level, fr in enumerate(nested_diagnostics(m, perm), start=1):
            print(
                f"  level={level} section={fr.section_size} ambient={fr.ambient_size} "
                f"time_sum={fr.time_sum} time_ok={fr.ok_time_sum} "
                f"perm_ok={fr.ok_permutation} cycles={fr.cycles[:20]}"
            )


if __name__ == "__main__":
    main()
