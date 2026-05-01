#!/usr/bin/env python3
"""SAT search for D5 even seam certificates.

The encoded object is the finite table

    sigma : Color -> Vec4 m -> Direction

from `D5Odd/Even.lean`.  The constraints match the Lean seam target:

* for each root coordinate z, c |-> sigma(c, z) is Latin;
* for each color c, z |-> z + b4(sigma(c, z)) is bijective;
* for each color c, z |-> seamStepMap(c, z - b4(c)) is one Hamiltonian cycle.

This is intended as a witness-finding tool, not as a proof artifact.
"""

from __future__ import annotations

import argparse
from collections.abc import Iterable

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver


def unidx(i: int, m: int, n: int = 4) -> tuple[int, ...]:
    z = [0] * n
    for k in range(n - 1, -1, -1):
        z[k] = i % m
        i //= m
    return tuple(z)


def idx(z: Iterable[int], m: int) -> int:
    r = 0
    for a in z:
        r = r * m + a
    return r


def add_dir_index(m: int, zidx: int, d: int) -> int:
    z = list(unidx(zidx, m))
    if d > 0:
        z[d - 1] = (z[d - 1] + 1) % m
    return idx(z, m)


def sub_color_index(m: int, zidx: int, c: int) -> int:
    z = list(unidx(zidx, m))
    if c > 0:
        z[c - 1] = (z[c - 1] - 1) % m
    return idx(z, m)


def exactly_one(cnf: list[list[int]], lits: list[int], vpool: IDPool) -> None:
    cnf.extend(
        CardEnc.equals(
            lits=lits,
            bound=1,
            vpool=vpool,
            encoding=EncType.seqcounter,
        ).clauses
    )


class Encoding:
    def __init__(self, m: int) -> None:
        self.m = m
        self.n = m**4
        self.vpool = IDPool()
        self.cnf: list[list[int]] = []

    def x(self, c: int, z: int, d: int) -> int:
        return self.vpool.id(("x", c, z, d))

    def p(self, c: int, k: int, z: int) -> int:
        return self.vpool.id(("p", c, k, z))

    def build(self) -> None:
        m = self.m
        n = self.n

        for z in range(n):
            for c in range(5):
                exactly_one(self.cnf, [self.x(c, z, d) for d in range(5)], self.vpool)
            for d in range(5):
                exactly_one(self.cnf, [self.x(c, z, d) for c in range(5)], self.vpool)

        for c in range(5):
            for y in range(n):
                preimages = [
                    self.x(c, z, d)
                    for z in range(n)
                    for d in range(5)
                    if add_dir_index(m, z, d) == y
                ]
                exactly_one(self.cnf, preimages, self.vpool)

        for c in range(5):
            for k in range(n):
                exactly_one(self.cnf, [self.p(c, k, z) for z in range(n)], self.vpool)
            for z in range(n):
                exactly_one(self.cnf, [self.p(c, k, z) for k in range(n)], self.vpool)

            self.cnf.append([self.p(c, 0, 0)])
            for k in range(n):
                kn = (k + 1) % n
                for z in range(n):
                    u = sub_color_index(m, z, c)
                    for d in range(5):
                        y = add_dir_index(m, u, d)
                        self.cnf.append([-self.p(c, k, z), -self.x(c, u, d), self.p(c, kn, y)])


def table_from_model(enc: Encoding, model: list[int]) -> list[list[int]]:
    positive = {lit for lit in model if lit > 0}
    return [
        [
            next(d for d in range(5) if enc.x(c, z, d) in positive)
            for z in range(enc.n)
        ]
        for c in range(5)
    ]


def verify(m: int, sigma: list[list[int]]) -> None:
    n = m**4

    for z in range(n):
        row = [sigma[c][z] for c in range(5)]
        assert sorted(row) == list(range(5)), (z, row)

    for c in range(5):
        step = [add_dir_index(m, z, sigma[c][z]) for z in range(n)]
        assert len(set(step)) == n, ("step", c)

        seen: set[int] = set()
        z = 0
        for _ in range(n):
            assert z not in seen, ("early return", c, z)
            seen.add(z)
            u = sub_color_index(m, z, c)
            z = add_dir_index(m, u, sigma[c][u])
        assert z == 0 and len(seen) == n, ("not cycle", c, z, len(seen))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--m", type=int, required=True)
    parser.add_argument("--solver", default="cadical153")
    parser.add_argument("--print-table", action="store_true")
    args = parser.parse_args()

    enc = Encoding(args.m)
    enc.build()
    print(f"m={args.m} vertices={enc.n} vars={enc.vpool.top} clauses={len(enc.cnf)}", flush=True)

    with Solver(name=args.solver, bootstrap_with=enc.cnf) as solver:
        is_sat = solver.solve()
        print(f"result={'sat' if is_sat else 'unsat'}", flush=True)
        if not is_sat:
            return
        sigma = table_from_model(enc, solver.get_model())
        verify(args.m, sigma)
        print("verified=true", flush=True)
        if args.print_table:
            for z in range(enc.n):
                print(z, unidx(z, args.m), [sigma[c][z] for c in range(5)])


if __name__ == "__main__":
    main()
