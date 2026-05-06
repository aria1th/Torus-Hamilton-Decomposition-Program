#!/usr/bin/env python3
"""SAT search for full layered D5 root-flat certificates at small modulus.

This is broader than the stationary seam-table search.  Variables are

    x(t, c, z, s)

where layer `t`, color `c`, and root-flat state `z in (Z/m)^4` choose stop
rank `s in {0,1,2,3,4}`.  The constraints are exactly the finite root-flat
certificate conditions:

* RF1 local Latin at every `(t,z)`;
* RF2 each layer/color map `z -> z - p_s` is bijective;
* RF3 the m-layer return map of every color is one cycle on `(Z/m)^4`.

The encoding is intended for very small moduli, especially `m=2`.  It is a
search/audit tool, not a Lean proof artifact.
"""

from __future__ import annotations

import argparse
import json
from collections.abc import Iterable
from pathlib import Path

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


def sub_stop_index(m: int, zidx: int, stop: int) -> int:
    z = list(unidx(zidx, m))
    for i in range(stop):
        z[i] = (z[i] - 1) % m
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

    def x(self, t: int, c: int, z: int, stop: int) -> int:
        return self.vpool.id(("x", t, c, z, stop))

    def p(self, c: int, k: int, z: int) -> int:
        return self.vpool.id(("p", c, k, z))

    def build(self) -> None:
        m = self.m
        n = self.n

        # RF1: each vertex/layer uses each stop exactly once across colors.
        for t in range(m):
            for z in range(n):
                for c in range(5):
                    exactly_one(self.cnf, [self.x(t, c, z, s) for s in range(5)], self.vpool)
                for s in range(5):
                    exactly_one(self.cnf, [self.x(t, c, z, s) for c in range(5)], self.vpool)

        # RF2: each layer/color map is a permutation of Q4.
        for t in range(m):
            for c in range(5):
                for y in range(n):
                    preimages = [
                        self.x(t, c, z, s)
                        for z in range(n)
                        for s in range(5)
                        if sub_stop_index(m, z, s) == y
                    ]
                    exactly_one(self.cnf, preimages, self.vpool)

        # RF3: position variables witness a single return cycle for each color.
        for c in range(5):
            for k in range(n):
                exactly_one(self.cnf, [self.p(c, k, z) for z in range(n)], self.vpool)
            for z in range(n):
                exactly_one(self.cnf, [self.p(c, k, z) for k in range(n)], self.vpool)
            self.cnf.append([self.p(c, 0, 0)])

            for k in range(n):
                kn = (k + 1) % n
                for z0 in range(n):
                    # Enumerate stop choices through the m layers.  This is
                    # exponential in m and therefore only meant for tiny m.
                    stack = [(0, z0, [])]
                    while stack:
                        t, z, stops = stack.pop()
                        if t == m:
                            y = z
                            lits = [-self.p(c, k, z0)]
                            zz = z0
                            for tt, stop in enumerate(stops):
                                lits.append(-self.x(tt, c, zz, stop))
                                zz = sub_stop_index(m, zz, stop)
                            lits.append(self.p(c, kn, y))
                            self.cnf.append(lits)
                        else:
                            for stop in range(5):
                                stack.append((t + 1, sub_stop_index(m, z, stop), stops + [stop]))


def table_from_model(enc: Encoding, model: list[int]) -> list[list[list[int]]]:
    positive = {lit for lit in model if lit > 0}
    layers: list[list[list[int]]] = []
    for t in range(enc.m):
        layer: list[list[int]] = []
        for z in range(enc.n):
            layer.append([
                next(stop for stop in range(5) if enc.x(t, c, z, stop) in positive)
                for c in range(5)
            ])
        layers.append(layer)
    return layers


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--m", type=int, required=True)
    parser.add_argument("--solver", default="cadical153")
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    enc = Encoding(args.m)
    enc.build()
    print(f"m={args.m} vertices={enc.n} vars={enc.vpool.top} clauses={len(enc.cnf)}", flush=True)
    with Solver(name=args.solver, bootstrap_with=enc.cnf) as solver:
        is_sat = solver.solve()
        print(f"result={'sat' if is_sat else 'unsat'}", flush=True)
        if not is_sat:
            return
        table = table_from_model(enc, solver.get_model())
        if args.json_out is not None:
            args.json_out.parent.mkdir(parents=True, exist_ok=True)
            args.json_out.write_text(json.dumps({"m": args.m, "layers": table}) + "\n")
            print(f"json_out={args.json_out}", flush=True)


if __name__ == "__main__":
    main()
