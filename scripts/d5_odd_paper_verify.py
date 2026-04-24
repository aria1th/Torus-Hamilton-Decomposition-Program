#!/usr/bin/env python3
"""Verifier for the D_5(m) odd-case zero-set table construction.

It checks, for a supplied odd m >= 3:
  1. the cyclic Lambda_1 table has no conflicts;
  2. the layer-1 map P is a bijection on A_m;
  3. the normalized return map G is a single m^4-cycle;
  4. the p=2 first-return formulas hold.

Usage:
  python d5_odd_verify.py 5
  python d5_odd_verify.py 3 5 7 9 11
"""
from __future__ import annotations
from itertools import combinations
import sys

REPS = {
    frozenset(): (0, 1, 2, 3, 4),
    frozenset({0}): (0, 1, 3, 2, 4),
    frozenset({0, 1}): (4, 1, 3, 2, 0),
    frozenset({0, 2}): (4, 1, 3, 0, 2),
    frozenset({0, 1, 2}): (1, 0, 3, 4, 2),
    frozenset({0, 1, 3}): (4, 3, 0, 2, 1),
    frozenset({0, 1, 2, 3, 4}): (0, 1, 2, 3, 4),
}

def rot_set(S: frozenset[int], k: int) -> frozenset[int]:
    return frozenset((x + k) % 5 for x in S)

def rot_perm(row: tuple[int, ...], k: int) -> tuple[int, ...]:
    out = [None] * 5
    for a in range(5):
        out[(a + k) % 5] = (row[a] + k) % 5
    return tuple(out)  # type: ignore[arg-type]

def build_lambda() -> dict[frozenset[int], tuple[int, ...]]:
    lam: dict[frozenset[int], tuple[int, ...]] = {}
    for S, row in REPS.items():
        for k in range(5):
            Sr = rot_set(S, k)
            rr = rot_perm(row, k)
            if Sr in lam and lam[Sr] != rr:
                raise AssertionError(f"cyclic conflict for {Sr}: {lam[Sr]} vs {rr}")
            lam[Sr] = rr
    return lam

LAMBDA = build_lambda()

def p_from_Z(Z: frozenset[int]) -> int:
    return LAMBDA[rot_set(Z, -1)][0]

def Zset(w: tuple[int, ...]) -> frozenset[int]:
    return frozenset(i for i, x in enumerate(w) if x == 0)

def A(m: int):
    for a in range(m):
        for b in range(m):
            for c in range(m):
                for d in range(m):
                    yield (a, b, c, d, (-a - b - c - d) % m)

def q(i: int, m: int) -> tuple[int, ...]:
    if i == 4:
        return (0, 0, 0, 0, 0)
    v = [0] * 5
    v[i] += 1
    v[4] -= 1
    return tuple(x % m for x in v)

def add(u: tuple[int, ...], v: tuple[int, ...], m: int) -> tuple[int, ...]:
    return tuple((u[i] + v[i]) % m for i in range(5))

def P(w: tuple[int, ...], m: int) -> tuple[int, ...]:
    return add(w, q(p_from_Z(Zset(w)), m), m)

def G(w: tuple[int, ...], m: int) -> tuple[int, ...]:
    p = p_from_Z(Zset(w))
    B = (-3, 0, 0, 1, 1)
    return tuple((w[i] + B[i] + (1 if i == p else 0)) % m for i in range(5))

def sigma(a: int, b: int, m: int) -> tuple[int, ...]:
    return (0, a % m, b % m, 0, (-a - b) % m)

def in_sigma(w: tuple[int, ...], m: int) -> bool:
    return w[0] == 0 and w[3] == 0 and w[4] != 0

def check_first_return(m: int) -> None:
    h = (m - 1) // 2
    for a in range(m):
        for b in range(m):
            if (a + b) % m == 0:
                continue
            w = sigma(a, b, m)
            z = G(w, m)
            steps = 1
            while not in_sigma(z, m):
                z = G(z, m)
                steps += 1
                if steps > m ** 4:
                    raise AssertionError(f"no first return from {(a,b)}")
            got = (z[1], z[2])
            if b <= m - 2:
                s = (a + b) % m
                expected = ((a if s == h else a + h) % m, (b + 1) % m)
                if 1 <= s <= h - 1:
                    expected_steps = (h + 1) * m
                elif s == h:
                    expected_steps = 2 * (h + 1) * m
                elif h + 1 <= s <= 2 * h:
                    expected_steps = (3 * h + 2) * m
                else:
                    raise AssertionError(f"bad residue s={s}")
            else:
                if a == 1:
                    continue
                if a == 0:
                    expected = (1, 0)
                    expected_steps = m ** 3 - (m - 1) * (m - 2)
                else:
                    expected = (a, 0)
                    expected_steps = m - 1
            if got != expected or steps != expected_steps:
                raise AssertionError(
                    f"first return mismatch m={m}, (a,b)={(a,b)}, "
                    f"got {got} in {steps}, expected {expected} in {expected_steps}"
                )

def check(m: int) -> tuple[int, int]:
    if m < 3 or m % 2 == 0:
        raise ValueError("m must be odd and >= 3")
    pts = list(A(m))
    if len({P(w, m) for w in pts}) != m ** 4:
        raise AssertionError("P is not bijective")
    # p=2 section condition
    for w in pts:
        if (p_from_Z(Zset(w)) == 2) != in_sigma(w, m):
            raise AssertionError(f"p=2 section mismatch at {w}, Z={Zset(w)}")
    check_first_return(m)
    start = pts[0]
    w = start
    seen = set()
    while w not in seen:
        seen.add(w)
        w = G(w, m)
        if len(seen) > m ** 4:
            raise AssertionError("cycle too long")
    if w != start or len(seen) != m ** 4:
        raise AssertionError(f"G cycle length {len(seen)} instead of {m**4}")
    return len({P(w, m) for w in pts}), len(seen)

def main(argv: list[str]) -> int:
    ms = [int(x) for x in argv[1:]] if len(argv) > 1 else [3, 5, 7, 9, 11, 13, 15, 17]
    for m in ms:
        matching_size, cycle_len = check(m)
        print(f"m={m}: matching={matching_size}, G-cycle={cycle_len}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
