#!/usr/bin/env python3
"""Verify the D7(m), m=3,5, zero-set certificates.

The certificate format is d7_m3_m5_zero_set_certificates.json.  The construction is:

  A_m = {w in (Z/mZ)^7 : sum_i w_i = 0}
  q_i = e_i - e_6 for i=0,...,5, and q_6=0.

For the unique non-constant layer t=1:
  d_1(w,c) = p(Z(w)-c)+c mod 7.

For all other layers:
  d_t(w,c) = c+s_t mod 7,

where the offsets s_t are stored in the certificate.

The script checks:
  1. the non-constant row Latin condition;
  2. the incoming exact-cover condition MC7;
  3. bijectivity of every layer map P_{t,c};
  4. each color return R_c is a single m^6-cycle.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Dict, FrozenSet, Iterable, List, Tuple

D = 7
NONCONST_LAYER = 1

State = Tuple[int, ...]


def root_states(m: int) -> List[State]:
    out: List[State] = []

    def rec(prefix: List[int], k: int) -> None:
        if k == D - 1:
            out.append(tuple(prefix + [(-sum(prefix)) % m]))
        else:
            for x in range(m):
                rec(prefix + [x], k + 1)

    rec([], 0)
    return out


def add_q(w: State, i: int, m: int, sign: int = 1) -> State:
    if i == D - 1:
        return w
    ww = list(w)
    ww[i] = (ww[i] + sign) % m
    ww[D - 1] = (ww[D - 1] - sign) % m
    return tuple(ww)


def zero_set(w: State, m: int) -> FrozenSet[int]:
    return frozenset(i for i, x in enumerate(w) if x % m == 0)


def shift_set(Z: FrozenSet[int], c: int) -> FrozenSet[int]:
    return frozenset((i - c) % D for i in Z)


def load_selector(case: dict) -> Dict[FrozenSet[int], int]:
    return {frozenset(row["Z"]): int(row["p"]) for row in case["selector"]}


def direction(t: int, c: int, w: State, m: int, selector: Dict[FrozenSet[int], int], offsets: Dict[int, int]) -> int:
    if t == NONCONST_LAYER:
        Zc = shift_set(zero_set(w, m), c)
        return (selector[Zc] + c) % D
    return (c + offsets[t]) % D


def is_perm(arr: List[int]) -> bool:
    return sorted(arr) == list(range(len(arr)))


def is_single_cycle(p: List[int]) -> bool:
    n = len(p)
    seen = [False] * n
    x = 0
    for _ in range(n):
        if seen[x]:
            return False
        seen[x] = True
        x = p[x]
    return x == 0 and all(seen)


def verify_case(case: dict, verbose: bool = True) -> bool:
    m = int(case["m"])
    offsets = {int(k): int(v) for k, v in case["constant_offsets"].items()}
    assert NONCONST_LAYER not in offsets
    assert set(offsets) == set(range(m)) - {NONCONST_LAYER}, (m, offsets)
    selector = load_selector(case)

    states = root_states(m)
    idx = {w: i for i, w in enumerate(states)}
    n = len(states)
    ok = True

    # Selector should be defined on every zero-set encountered in A_m.
    encountered = {zero_set(w, m) for w in states}
    missing = encountered - set(selector)
    if missing:
        print(f"m={m}: selector missing zero-sets: {sorted(map(sorted, missing))}")
        ok = False

    # Row Latin condition for the non-constant layer.
    for w in states:
        row = [direction(NONCONST_LAYER, c, w, m, selector, offsets) for c in range(D)]
        if sorted(row) != list(range(D)):
            print(f"m={m}: non-Latin row at w={w}: {row}")
            ok = False
            break

    # Incoming exact-cover MC7 for color 0 non-constant layer:
    # #{i : p(Z(y-q_i)) = i} = 1.
    for y in states:
        count = 0
        hits = []
        for i in range(D):
            pred = add_q(y, i, m, sign=-1)
            if selector[zero_set(pred, m)] == i:
                count += 1
                hits.append(i)
        if count != 1:
            print(f"m={m}: MC7 fails at y={y}, hits={hits}")
            ok = False
            break

    # Build and check every layer map.
    layer_maps: List[List[List[int]]] = []
    for t in range(m):
        layer = []
        for c in range(D):
            arr = [idx[add_q(w, direction(t, c, w, m, selector, offsets), m)] for w in states]
            if not is_perm(arr):
                print(f"m={m}: layer map not bijective at t={t}, color={c}")
                ok = False
            layer.append(arr)
        layer_maps.append(layer)

    # Return maps.
    for c in range(D):
        p = list(range(n))
        for t in range(m):
            f = layer_maps[t][c]
            p = [f[x] for x in p]
        cyc = is_single_cycle(p)
        if verbose:
            print(f"m={m}, color={c}: return single cycle = {cyc}, length target={n}")
        if not cyc:
            ok = False

    if verbose:
        print(f"m={m}: verified={ok}, root states={n}, torus Hamilton length={m*n}")
    return ok


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate", nargs="?", default="d7_m3_m5_zero_set_certificates.json")
    parser.add_argument("--m", choices=["3", "5"], help="verify only one modulus")
    args = parser.parse_args()

    data = json.loads(Path(args.certificate).read_text(encoding="utf-8"))
    cases = data["certificates"]
    keys = [args.m] if args.m else sorted(cases, key=int)
    ok = True
    for key in keys:
        ok = verify_case(cases[key]) and ok
    raise SystemExit(0 if ok else 1)


if __name__ == "__main__":
    main()
