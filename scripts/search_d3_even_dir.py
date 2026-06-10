#!/usr/bin/env python3
"""Computational search for the D3-even root-flat schedule (hole H1b, per-color form).

Problem.  For even m >= 4 construct
    dir : (layer t in Z/m) x (state w in (Z/m)^2) x (color c in {0,1,2}) -> {0,1,2}
with
  RF1 (Latin)  : c |-> dir(t,w,c) is a bijection onto {0,1,2} for every (t,w);
  RF2 (layers) : L_{t,c} : w |-> w + e_{dir(t,w,c)} is a bijection of (Z/m)^2,
                 where e_0=(1,0), e_1=(0,1), e_2=(0,0);
  RF3 (returns): R_c = L_{m-1,c} o ... o L_{0,c} is a single m^2-cycle for each c.

This file is self-contained (stdlib only).  Subcommands:

  verify    --cert FILE            RF1/RF2/RF3 check + cycle structure + parity report
  export-m4 [--out FILE]           extract EvenV11/D3EvenM4.lean into a cert (anchor)
  negative  --m M                  numeric verification of the no-go results
                                   (single-functional stripe families, pair-swap parity)
  search    --m M [--mode wild1|general] [--seed S] [--iters N] [--restarts R]
            [--out FILE]           simulated annealing search (JM-chase + line swaps)
  analyze   --cert FILE            structure mining: per-layer base, deviation
                                   rho-cycles, layer signs, triple product N

Key structural facts used (derived 2026-06-10, see docs/WILDE_SEARCH_20260610.md):
  * each R_c must be an ODD permutation (single m^2-cycle, m^2 even), so
    prod_c sign(R_c) = -1; translations are even; pair-swap layers always have
    layer triple product N = +1; hence every solution needs an odd number of
    genuinely 3-color-entangled layers ("wild seams", N = -1).
  * relative to any constant Latin base, the deviation rho_c of a layer's color
    map decomposes into cycles of length == 0 (mod m); N = (-1)^(total #cycles).
"""

import argparse
import itertools
import json
import math
import os
import random
import re
import sys

EV = ((1, 0), (0, 1), (0, 0))            # e_0, e_1, e_2
PERMS = tuple(itertools.permutations((0, 1, 2)))
ID = (0, 1, 2)

# ---------------------------------------------------------------------------
# table representation: layers[t][x][y] = (d0, d1, d2) = directions per color
# ---------------------------------------------------------------------------


def states(m):
    return [(x, y) for x in range(m) for y in range(m)]


def add(w, e, m):
    return ((w[0] + e[0]) % m, (w[1] + e[1]) % m)


def layer_map(layer, c, m):
    """color-c map of one layer, as dict."""
    return {(x, y): add((x, y), EV[layer[x][y][c]], m)
            for x in range(m) for y in range(m)}


def compose_return(layers, c, m):
    R = {}
    for s in states(m):
        cur = s
        for t in range(len(layers)):
            cur = add(cur, EV[layers[t][cur[0]][cur[1]][c]], m)
        R[s] = cur
    return R


def cycle_lengths(f):
    seen = set()
    out = []
    for s in f:
        if s in seen:
            continue
        n = 0
        cur = s
        while cur not in seen:
            seen.add(cur)
            cur = f[cur]
            n += 1
        out.append(n)
    return sorted(out, reverse=True)


def sign_of(f):
    sg = 1
    for n in cycle_lengths(f):
        if n % 2 == 0:
            sg = -sg
    return sg


def rf1_ok(layers, m):
    for t, layer in enumerate(layers):
        for x in range(m):
            for y in range(m):
                if tuple(sorted(layer[x][y])) != (0, 1, 2):
                    return False, (t, x, y)
    return True, None


def rf2_ok(layers, m):
    for t, layer in enumerate(layers):
        for c in range(3):
            img = {add((x, y), EV[layer[x][y][c]], m)
                   for x in range(m) for y in range(m)}
            if len(img) != m * m:
                return False, (t, c)
    return True, None


def verify_table(layers, m, verbose=True):
    ok1, w1 = rf1_ok(layers, m)
    ok2, w2 = rf2_ok(layers, m)
    rets = [compose_return(layers, c, m) for c in range(3)]
    cycs = [cycle_lengths(R) for R in rets]
    ok3 = all(cy == [m * m] for cy in cycs)
    if verbose:
        print(f"m={m}  RF1={'ok' if ok1 else f'FAIL at {w1}'}  "
              f"RF2={'ok' if ok2 else f'FAIL at {w2}'}  RF3={'ok' if ok3 else 'FAIL'}")
        for c in range(3):
            print(f"  color {c}: return cycle type {cycs[c]}  sign {sign_of(rets[c])}")
        for t, layer in enumerate(layers):
            sgs = [sign_of(layer_map(layer, c, m)) for c in range(3)]
            print(f"  layer {t}: color signs {sgs}  N={sgs[0]*sgs[1]*sgs[2]}")
    return ok1 and ok2 and ok3


# ---------------------------------------------------------------------------
# JSON certificates
# ---------------------------------------------------------------------------


def save_cert(layers, m, path, meta=None):
    data = {"m": m,
            "format": "layers[t][x][y] = [dir(color0), dir(color1), dir(color2)]; "
                      "e0=(1,0) e1=(0,1) e2=(0,0); R_c = L_{m-1,c} o ... o L_{0,c}",
            "layers": [[[list(layer[x][y]) for y in range(m)] for x in range(m)]
                       for layer in layers]}
    if meta:
        data["meta"] = meta
    with open(path, "w") as fh:
        json.dump(data, fh)
    print(f"wrote {path}")


def load_cert(path):
    with open(path) as fh:
        data = json.load(fh)
    m = data["m"]
    layers = [[[tuple(data["layers"][t][x][y]) for y in range(m)]
               for x in range(m)] for t in range(m)]
    return layers, m


# ---------------------------------------------------------------------------
# export the known m=4 witness (EvenV11/D3EvenM4.lean) through the root-flat chart
#   t = x0+x1+x2,  w = (x0, x2);  3-torus dir 0 -> e_(1,0), 2 -> e_(0,1), 1 -> zero
# ---------------------------------------------------------------------------


def export_m4(out):
    here = os.path.dirname(os.path.abspath(__file__))
    path = os.path.join(here, "..", "EvenV11", "D3EvenM4.lean")
    src = open(path).read()
    block = src.split("def dirWordNat")[1].split("def colorDir")[0]
    word = {}
    for mm in re.finditer(
            r"\|\s*(\d+),\s*(\d+),\s*(\d+)\s*=>\s*\((\d+),\s*(\d+),\s*(\d+)\)", block):
        x0, x1, x2, a, b, c = map(int, mm.groups())
        word[(x0, x1, x2)] = (a, b, c)
    assert len(word) == 64
    m = 4
    rfd = {0: 0, 2: 1, 1: 2}
    layers = []
    for t in range(m):
        layer = [[None] * m for _ in range(m)]
        for x in range(m):
            for y in range(m):
                x1 = (t - x - y) % m
                layer[x][y] = tuple(rfd[word[(x, x1, y)][c]] for c in range(3))
        layers.append(layer)
    save_cert(layers, m, out, meta={"source": "EvenV11/D3EvenM4.lean dirWordNat",
                                    "chart": "t=x0+x1+x2, w=(x0,x2)"})
    assert verify_table(layers, m)


# ---------------------------------------------------------------------------
# negative results (numeric verification of the proofs in the design note)
# ---------------------------------------------------------------------------


def negative(m):
    assert m % 2 == 0
    print(f"== negative checks at m={m} ==")

    # (N1) y-stripe (and by symmetry x-stripe) family: per layer the stripe map
    # j -> j + [dir=e1] must be a bijection of Z/m, hence all-or-nothing; so per
    # layer exactly one color is the y-mover; r_c = #mover layers must satisfy
    # gcd(r_c, m) = 1 for transitivity of the y-factor, i.e. r_c odd; but
    # r_0+r_1+r_2 = m is even.  Verified here: no triple of odd r's sums to m.
    bad = [r for r in itertools.product(range(1, m, 2), repeat=3) if sum(r) == m]
    print(f"(N1) y/x-stripe family: odd (r0,r1,r2) with sum m: {len(bad)} -> "
          f"{'IMPOSSIBLE (as proven)' if not bad else 'check failed!'}")

    # (N2) x+y-stripe family: per layer exactly one color reads e2 everywhere,
    # the others advance s=x+y by 1; n_c moving layers needs gcd(n_c,m)=1 and
    # n_0+n_1+n_2 = 2m: same parity contradiction.
    bad = [r for r in itertools.product(range(1, m, 2), repeat=3) if sum(r) == 2 * m]
    print(f"(N2) x+y-stripe family: odd (n0,n1,n2) with sum 2m: {len(bad)} -> "
          f"{'IMPOSSIBLE (as proven)' if not bad else 'check failed!'}")

    # (N3) x-y stripe family: enumerate ALL valid layers (function
    # d -> S3 with the three +/-1/0 stripe maps bijective) and verify every
    # layer has triple sign product N = +1; since three single m^2-cycles need
    # prod_c sign(R_c) = -1, the family is empty for even m.
    stripe_perms = tuple(itertools.permutations((1, -1, 0)))

    def stripe_ok(eps):
        return len({(d + eps[d]) % m for d in range(m)}) == m

    n_layers = 0
    trip = set()
    ev = {1: (1, 0), -1: (0, 1), 0: (0, 0)}
    for g in itertools.product(range(6), repeat=m):
        gg = [stripe_perms[i] for i in g]
        if not all(stripe_ok([gg[d][c] for d in range(m)]) for c in range(3)):
            continue
        n_layers += 1
        sgs = []
        for c in range(3):
            f = {}
            for x in range(m):
                for y in range(m):
                    f[(x, y)] = add((x, y), ev[gg[(x - y) % m][c]], m)
            sgs.append(sign_of(f))
        trip.add(sgs[0] * sgs[1] * sgs[2])
    print(f"(N3) x-y stripe family: {n_layers} valid layers, "
          f"triple products {trip} -> "
          f"{'IMPOSSIBLE (N always +1)' if trip == {1} else 'check failed!'}")

    # (N4) pair-swap parity invariant: a legal swap of colors (a,b) on a
    # delta-invariant U has L_a(U) = U+e_b and L_b(U) = U+e_a with
    # |(U+e_b) cap (U+e_a)| = |U|, so the layer triple product never changes.
    # Spot-verified on random legal line swaps from random constant bases.
    rng = random.Random(0)
    ok = True
    for _ in range(200):
        sigma = rng.choice(PERMS)
        layer = [[sigma for _ in range(m)] for _ in range(m)]
        a, b = rng.sample(range(3), 2)
        da, db = sigma[a], sigma[b]
        delta = ((EV[db][0] - EV[da][0]) % m, (EV[db][1] - EV[da][1]) % m)
        w0 = (rng.randrange(m), rng.randrange(m))
        line = set()
        cur = w0
        while cur not in line:
            line.add(cur)
            cur = add(cur, delta, m)
        tau = list(sigma)
        tau[a], tau[b] = tau[b], tau[a]
        layer2 = [[tuple(tau) if (x, y) in line else sigma for y in range(m)]
                  for x in range(m)]
        sgs = [sign_of(layer_map(layer2, c, m)) for c in range(3)]
        if sgs[0] * sgs[1] * sgs[2] != 1:
            ok = False
    print(f"(N4) pair-swap layers keep N=+1: {'verified (200 random)' if ok else 'FAILED'}")
    print("=> every even-m solution needs an odd number of 3-color-entangled "
          "layers (N=-1), i.e. layers whose constant-base deviations have an odd "
          "total number of rho-cycles.")


# ---------------------------------------------------------------------------
# search: Jacobson-Matthews-style chase trades + line swaps, simulated annealing
# ---------------------------------------------------------------------------


def constant_layer(sigma, m):
    return [[tuple(sigma) for _ in range(m)] for _ in range(m)]


def copy_layer(layer):
    return [row[:] for row in layer]


def jm_chase(layer, m, rng, max_steps=400):
    """Random RF1/RF2-preserving trade on one layer via defect chasing.

    Start by swapping two colors at one cell; repeatedly repair the resulting
    image defects by further single-cell color swaps; abort (returning None)
    if the chase does not close within max_steps.  Returns a new layer."""
    L = copy_layer(layer)

    # per-color image counters
    cnt = [dict() for _ in range(3)]
    for c in range(3):
        for x in range(m):
            for y in range(m):
                v = add((x, y), EV[L[x][y][c]], m)
                cnt[c][v] = cnt[c].get(v, 0) + 1

    def apply_swap(w, a, b):
        x, y = w
        p = list(L[x][y])
        for c in (a, b):
            v = add(w, EV[p[c]], m)
            cnt[c][v] -= 1
        p[a], p[b] = p[b], p[a]
        L[x][y] = tuple(p)
        for c in (a, b):
            v = add(w, EV[p[c]], m)
            cnt[c][v] = cnt[c].get(v, 0) + 1

    w0 = (rng.randrange(m), rng.randrange(m))
    a, b = rng.sample(range(3), 2)
    apply_swap(w0, a, b)

    for _ in range(max_steps):
        # find a defective color
        defect = None
        for c in range(3):
            for v, k in cnt[c].items():
                if k >= 2:
                    defect = (c, v)
                    break
            if defect:
                break
        if defect is None:
            return L
        c, v = defect
        # preimages of v under color c
        pre = []
        for d in range(3):
            u = add(v, ((-EV[d][0]) % m, (-EV[d][1]) % m), m)
            if L[u[0]][u[1]][c] == d:
                pre.append(u)
        u = rng.choice(pre)
        # swap color c at u with one of the other two colors (prefer a swap
        # whose new image for c is currently uncovered)
        others = [d for d in range(3) if d != c]
        rng.shuffle(others)
        choice = None
        for oc in others:
            nd = L[u[0]][u[1]][oc]
            nv = add(u, EV[nd], m)
            if cnt[c].get(nv, 0) == 0:
                choice = oc
                break
        if choice is None:
            choice = others[0]
        apply_swap(u, c, choice)
    return None


def line_swap(layer, m, rng):
    """Pair swap on a coset line; returns new layer or None if RF2 breaks."""
    a, b = rng.sample(range(3), 2)
    kind = rng.randrange(3)
    if kind == 0:    # rows  (cosets of (1,0))
        j = rng.randrange(m)
        cells = [(x, j) for x in range(m)]
    elif kind == 1:  # columns
        i = rng.randrange(m)
        cells = [(i, y) for y in range(m)]
    else:            # anti-diagonals (cosets of (-1,1))
        s = rng.randrange(m)
        cells = [(x, (s - x) % m) for x in range(m)]
    L = copy_layer(layer)
    for (x, y) in cells:
        p = list(L[x][y])
        p[a], p[b] = p[b], p[a]
        L[x][y] = tuple(p)
    for c in (a, b):
        img = {add((x, y), EV[L[x][y][c]], m) for x in range(m) for y in range(m)}
        if len(img) != m * m:
            return None
    return L


def total_score(layers, m):
    """Sum of (cycle count - 1) over colors, plus a penalty when the global
    parity prod_c sign(R_c) is +1 (in that sector the minimum is 1, so any
    odd-sector table with the same cycle counts is strictly preferred)."""
    sc = 0
    par = 1
    for c in range(3):
        cl = cycle_lengths(compose_return(layers, c, m))
        sc += len(cl) - 1
        for n in cl:
            if n % 2 == 0:
                par = -par
    if par == 1:
        sc += 2
    return sc


def search(m, mode, seed, iters, restarts, out):
    rng = random.Random(seed)
    best_overall = None
    for r in range(restarts):
        layers = init_tables(m, mode, rng)
        sc = total_score(layers, m)
        T0 = 3.0
        for it in range(iters):
            t = rng.randrange(m)
            if mode == "wild1":
                # only the last layer is wild; cheap layers stay constant
                t = m - 1 if rng.random() < 0.85 else rng.randrange(m)
            move = rng.random()
            if move < 0.55:
                newlayer = jm_chase(layers[t], m, rng)
            else:
                newlayer = line_swap(layers[t], m, rng)
            if newlayer is None:
                continue
            cand = layers[:t] + [newlayer] + layers[t + 1:]
            s2 = total_score(cand, m)
            T = max(T0 * (1 - it / iters), 0.05)
            if s2 <= sc or rng.random() < math.exp((sc - s2) / T):
                layers, sc = cand, s2
            if sc == 0:
                print(f"restart {r}: SOLVED at iteration {it}")
                if verify_table(layers, m):
                    if out:
                        save_cert(layers, m, out,
                                  meta={"mode": mode, "seed": seed,
                                        "restart": r, "iteration": it})
                    return layers
        print(f"restart {r}: best score {sc}")
        if best_overall is None or sc < best_overall[0]:
            best_overall = (sc, layers)
    print(f"no solution; best score {best_overall[0]}")
    return None


def init_tables(m, mode, rng):
    """Initial table: constant Latin layers with balanced drifts; in wild1 mode
    the cheap layers give color roles a rotating pattern."""
    layers = []
    for t in range(m):
        sigma = PERMS[t % len(PERMS)] if mode == "general" else \
            ((0, 1, 2) if t % 2 == 0 else (1, 0, 2))
        layers.append(constant_layer(sigma, m))
    if mode == "wild1":
        # seed the last layer with a few random chases to give it 3-color content
        for _ in range(6):
            L = jm_chase(layers[m - 1], m, rng)
            if L is not None:
                layers[m - 1] = L
    return layers


# ---------------------------------------------------------------------------
# closed-form parametric construction ("rail-seam" schedule)
#
# Layers 0..m-2 are the constant Latin rows
#     id    : color c reads direction c
#     rho+  : color c reads direction c+1 (mod 3)
#     rho++ : color c reads direction c+2 (mod 3)
# with multiplicities (#id, #rho+, #rho++) =
#     (0, 1, m-2)           if 3 does not divide m   [drifts u=((1,1),(m-2,1),(1,m-2))]
#     (m-5, 1, 3)           if 3 divides m           [drifts u=((m-4,1),(3,m-4),(1,3))]
# Layer m-1 is the wild "rail seam" layer: base id (color c reads c) except on
# the 3m-cell support  P (01-swap), Q (02-swap), S (12-swap):
#     P = antidiagonal {x+y=0} with cells x=1,2 replaced by (1,m-2),(2,m-1)
#     Q = row {y=m-1}    with cells x=1,2 replaced by (1,0),  (2,m-2)
#     S = column {x=2},y<m-2,   plus      (1,m-1),(3,m-2)
# (the pairwise crossing cells of the three lines are cyclically reassigned to
# the third set; this makes each color's deviation rho_c a single 2m-cycle, so
# the layer has triple sign product N = -1, as parity requires).
#
# Discovered by structured search 2026-06-10; verified for even m in [4, 24+].
# ---------------------------------------------------------------------------


def canonical_seam(m):
    P = [(0, 0)] + [(x, (m - x) % m) for x in range(3, m)] + [(1, m - 2), (2, m - 1)]
    Q = [(x, m - 1) for x in [0] + list(range(3, m))] + [(1, 0), (2, m - 2)]
    S = [(2, y) for y in range(m - 2)] + [(1, m - 1), (3, m - 2)]
    return P, Q, S


def construct(m, out=None, quiet=False):
    assert m >= 4 and m % 2 == 0
    P, Q, S = canonical_seam(m)
    wild = [[ID for _ in range(m)] for _ in range(m)]
    for (x, y) in P:
        wild[x][y] = (1, 0, 2)            # swap colors 0,1
    for (x, y) in Q:
        wild[x][y] = (2, 1, 0)            # swap colors 0,2
    for (x, y) in S:
        wild[x][y] = (0, 2, 1)            # swap colors 1,2
    rho_plus = (1, 2, 0)                  # color c -> direction c+1
    rho_pp = (2, 0, 1)                    # color c -> direction c+2
    if m % 3 != 0:
        counts = [(rho_plus, 1), (rho_pp, m - 2)]
        u = ((1, 1), (m - 2, 1), (1, m - 2))
    else:
        counts = [(ID, m - 5), (rho_plus, 1), (rho_pp, 3)]
        u = ((m - 4, 1), (3, m - 4), (1, 3))
    layers = []
    for sigma, k in counts:
        layers += [constant_layer(sigma, m)] * k
    layers.append(wild)
    assert len(layers) == m
    if not quiet:
        print(f"construct m={m}: drifts u={u}")
    ok = verify_table(layers, m, verbose=not quiet)
    if out and ok:
        save_cert(layers, m, out, meta={
            "construction": "rail-seam: m-1 constant 3-cycle layers + 1 wild layer",
            "seam": {"P": P, "Q": Q, "S": S},
            "drifts": u})
    return ok


# ---------------------------------------------------------------------------
# analyze: structure mining
# ---------------------------------------------------------------------------


def analyze(layers, m):
    print(f"analysis of m={m} table")
    for t, layer in enumerate(layers):
        # best constant base
        best = None
        for sg in PERMS:
            supp = sum(1 for x in range(m) for y in range(m)
                       for c in range(3) if layer[x][y][c] != sg[c])
            if best is None or supp < best[1]:
                best = (sg, supp)
        sigma = best[0]
        sgs = [sign_of(layer_map(layer, c, m)) for c in range(3)]
        N = sgs[0] * sgs[1] * sgs[2]
        # pattern histogram
        hist = {}
        for x in range(m):
            for y in range(m):
                hist[layer[x][y]] = hist.get(layer[x][y], 0) + 1
        print(f"layer {t}: base {sigma} (dev {best[1]} color-cells), "
              f"signs {sgs}, N={N}")
        print(f"   patterns: {sorted(hist.items(), key=lambda kv: -kv[1])}")
        ncyc_total = 0
        for c in range(3):
            rho = {}
            for x in range(m):
                for y in range(m):
                    e = EV[layer[x][y][c]]
                    eb = EV[sigma[c]]
                    rho[(x, y)] = add((x, y), ((e[0] - eb[0]) % m,
                                               (e[1] - eb[1]) % m), m)
            cl = [n for n in cycle_lengths(rho) if n > 1]
            ncyc_total += len(cl)
            if cl:
                print(f"   color {c}: rho-cycles {cl}")
        print(f"   total rho-cycles {ncyc_total} ({'odd: wild seam' if ncyc_total % 2 else 'even'})")


# ---------------------------------------------------------------------------


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("verify")
    p.add_argument("--cert", required=True)

    p = sub.add_parser("export-m4")
    p.add_argument("--out", default=None)

    p = sub.add_parser("negative")
    p.add_argument("--m", type=int, required=True)

    p = sub.add_parser("search")
    p.add_argument("--m", type=int, required=True)
    p.add_argument("--mode", choices=["wild1", "general"], default="general")
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--iters", type=int, default=40000)
    p.add_argument("--restarts", type=int, default=4)
    p.add_argument("--out", default=None)

    p = sub.add_parser("analyze")
    p.add_argument("--cert", required=True)

    p = sub.add_parser("construct")
    p.add_argument("--m", type=int, required=True)
    p.add_argument("--out", default=None)
    p.add_argument("--quiet", action="store_true")

    p = sub.add_parser("construct-scan")
    p.add_argument("--mmax", type=int, default=24)

    args = ap.parse_args()
    if args.cmd == "verify":
        layers, m = load_cert(args.cert)
        ok = verify_table(layers, m)
        sys.exit(0 if ok else 1)
    elif args.cmd == "export-m4":
        out = args.out or os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                       "d3_even_dir_m4_from_lean.json")
        export_m4(out)
    elif args.cmd == "negative":
        negative(args.m)
    elif args.cmd == "search":
        out = args.out or os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                       f"d3_even_dir_m{args.m}.json")
        search(args.m, args.mode, args.seed, args.iters, args.restarts, out)
    elif args.cmd == "analyze":
        layers, m = load_cert(args.cert)
        analyze(layers, m)
    elif args.cmd == "construct":
        ok = construct(args.m, out=args.out, quiet=args.quiet)
        sys.exit(0 if ok else 1)
    elif args.cmd == "construct-scan":
        allok = True
        for m in range(4, args.mmax + 1, 2):
            ok = construct(m, quiet=True)
            print(f"m={m}: {'OK (RF1/RF2/RF3)' if ok else 'FAIL'}")
            allok = allok and ok
        sys.exit(0 if allok else 1)


if __name__ == "__main__":
    main()
