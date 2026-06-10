#!/usr/bin/env python3
"""Part (c) of the oldGensSpec numeric gate (see check_oldgens_span.py):
the DECISIVE new-color replay of the paper's chained 7->9 projection-discharge
argument over the two shipped dimension-7 bases.

Three machine checks, each replaying one reading of the paper's construction
(`prop:chained-two-hole` + `ex:D9-chained-growth` of subtex/high_even_growth.tex)
and measuring whether the two leaf returns (new chart labels 0 and 1) can be
single K-cycles:

  (C1) ALPHABET SCAN over the embedded base (the GrowthStepCore/growthDir
       picture: old colors keep their old reads; the two displayed four-point
       words (0 2)(7 5) and (1 2)(0 8) are inserted as head substitutions on
       ARBITRARY supports).  The reachable read alphabet of each new color is
       computed exactly; an invariant-coordinate argument then bounds the
       cycle structure of the leaf returns for EVERY placement.

  (C2) CANONICAL SHIFT TRANSPORT (the re-realized skeleton picture of design
       doc 1.3: the dimension-7 rows are reread over Z_9 so the two new
       labels join the cyclic order).  At each point the base row is written
       as per-color shifts c -> c + s_c and reread as c+2 -> c+2+s_c over
       Z_9; new labels read the two leftover labels (skeleton-consistent
       assignment).  Check: well-definedness (the shift rereading must stay
       Latin over Z_9), RF2, and the (z0,z1)-monodromy order obstruction.

  (C3) the recorded GrowthStepCore findings (growth_step_replay.py
       --growth-step / --core-findings) quoted as machine context.

Stdlib only.  Driven from check_oldgens_span.py --new-color-replay [--m 4|6].
"""
from __future__ import annotations
from array import array
import json, sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from growth_step_replay import load_seed, cycle_lengths

ROW_WORDS = [{0: 2, 2: 0, 7: 5, 5: 7}, {1: 2, 2: 1, 0: 8, 8: 0}]

def gcd(a, b):
    while b:
        a, b = b, a % b
    return a

# ---------------------------------------------------------------- C1

def alphabet_scan(res, m):
    """embedded base + the two displayed row words on arbitrary supports:
    exact reachable alphabets of the two new colors."""
    # default reads: new color 0 -> label 0 (leaf0), new color 1 -> label 1.
    # a point inside support of row word w replaces a color's head h by w[h];
    # supports are arbitrary, so the reachable alphabet is the closure of the
    # defaults under both words (any nesting of the two substitutions at
    # different layers).
    def closure(start):
        alph = {start}
        changed = True
        while changed:
            changed = False
            for w in ROW_WORDS:
                for h in list(alph):
                    h2 = w.get(h, h)
                    if h2 not in alph:
                        alph.add(h2)
                        changed = True
        return alph
    a0, a1 = closure(0), closure(1)
    res.info(f'C1: reachable head alphabet of new color 0: {sorted(a0)}; '
             f'of new color 1: {sorted(a1)}')
    # direction semantics: x-coordinates touched and z-coordinates touched
    def touched(alph):
        xs = sorted(l - 2 for l in alph if 2 <= l <= 7)
        zs = sorted(l for l in alph if l in (0, 1))
        return xs, zs
    x0, z0 = touched(a0)
    x1, z1 = touched(a1)
    res.info(f'C1: new color 0 can move x-coordinates {x0} and leaves {z0}; '
             f'new color 1 can move x-coordinates {x1} and leaves {z1}')
    # invariant-coordinate verdict: a single K*m^2-cycle return needs all six
    # old coordinates AND both leaves movable.
    ok0 = set(x0) == set(range(6)) and set(z0) == {0, 1}
    ok1 = set(x1) == set(range(6)) and set(z1) == {0, 1}
    res.clause(f'm={m} C1: new color 0 can reach a single-cycle alphabet '
               'under the two displayed row words (any supports)', ok0,
               detail=f'invariant coordinates: x {sorted(set(range(6)) - set(x0))}, '
                      f'leaves {sorted({0, 1} - set(z0))} -> return is never a '
                      'single cycle for ANY placement')
    res.clause(f'm={m} C1: new color 1 likewise', ok1,
               detail=f'invariant coordinates: x {sorted(set(range(6)) - set(x1))}, '
                      f'leaves {sorted({0, 1} - set(z1))}')
    return ok0 and ok1

# ---------------------------------------------------------------- C2

def shift_transport(res, m):
    """canonical re-realized skeleton transport; returns clause verdicts."""
    d, dirs = load_seed(m)
    K = m ** (d - 1)
    powm = [m ** i for i in range(6)]
    n_fallback = 0
    # per color: per layer x-map + leaf carries (reads are z-independent here)
    xmaps = [[array('I', range(K)) for _ in range(m)] for _ in range(9)]
    dz = [[[bytearray(K), bytearray(K)] for _ in range(m)] for _ in range(9)]
    rf2_bad = []
    for t in range(m):
        heads_all = [None] * 9
        for x in range(K):
            pi = [dirs[t][c][x] for c in range(d)]
            hs = [(c + 2 + ((pi[c] - c) % 7)) % 9 for c in range(d)]
            if len(set(hs)) != 7:
                n_fallback += 1
                hs = [pi[c] + 2 for c in range(d)]
            left = sorted(set(range(9)) - set(hs))
            a, b = left
            if (b - a) % 9 == 1:
                new_heads = (a, b)
            elif (a - b) % 9 == 1:
                new_heads = (b, a)
            else:
                new_heads = (a, b)
            heads = list(new_heads) + hs
            for cc in range(9):
                lab = heads[cc]
                if 2 <= lab <= 7:
                    i = lab - 2
                    dig = (x // powm[i]) % m
                    xmaps[cc][t][x] = x + powm[i] if dig < m - 1 \
                        else x - (m - 1) * powm[i]
                elif lab == 0:
                    dz[cc][t][0][x] = 1
                elif lab == 1:
                    dz[cc][t][1][x] = 1
        for cc in range(9):
            seen = bytearray(K)
            for v in xmaps[cc][t]:
                seen[v] += 1
            if any(s != 1 for s in seen):
                rf2_bad.append((t, cc))
    res.info(f'C2 m={m}: shift-rereading fallback points (Latin failure of the '
             f'canonical transport): {n_fallback} of {m * K}')
    res.clause(f'm={m} C2: canonical shift transport is well defined '
               '(0 fallback points)', n_fallback == 0,
               detail='the wild base rows do not extend along the chart '
                      'Z_7 -> Z_9 \\ {0,1}: no canonical re-realized skeleton '
                      'exists over this base', severity='gate')
    res.clause(f'm={m} C2: RF2 of the transported child', not rf2_bad,
               detail=f'non-bijective (layer, child color) pairs: {rf2_bad[:8]}'
                      f'{"..." if len(rf2_bad) > 8 else ""}')
    # returns at x-level + leaf carries; (z0,z1)-monodromy order obstruction
    types = {}
    max_ord = m  # order of any element of (Z_m)^2 divides m
    for cc in range(9):
        F = array('I', range(K))
        c0 = array('I', [0]) * K
        c1 = array('I', [0]) * K
        for t in range(m):
            X, D0, D1 = xmaps[cc][t], dz[cc][t][0], dz[cc][t][1]
            for x in range(K):
                y = F[x]
                c0[x] += D0[y]
                c1[x] += D1[y]
                F[x] = X[y]
        # cycles of the K*m^2 return via the skew formula
        seen = bytearray(K)
        ctype = {}
        ncyc = 0
        for x0 in range(K):
            if seen[x0]:
                continue
            L = 0
            a = b = 0
            x = x0
            while not seen[x]:
                seen[x] = 1
                a += c0[x]
                b += c1[x]
                L += 1
                x = F[x]
            a %= m
            b %= m
            orda = m // gcd(a, m)
            ordb = m // gcd(b, m)
            o = orda * ordb // gcd(orda, ordb)
            ncyc += m * m // o
            ctype[L * o] = ctype.get(L * o, 0) + m * m // o
        types[cc] = (ncyc, sorted(ctype.items(), reverse=True)[:3])
    res.info(f'C2 m={m}: child return cycle counts per color '
             f'{ {cc: types[cc][0] for cc in range(9)} }')
    leaf_single = types[0][0] == 1 and types[1][0] == 1
    res.clause(f'm={m} C2: the two leaf returns are single K-cycles under the '
               'canonical transport', leaf_single,
               detail=f'new color 0: {types[0][0]} cycles {types[0][1]}; '
                      f'new color 1: {types[1][0]} cycles {types[1][1]}.  '
                      'Structural cause: the transported reads are '
                      '(z0,z1)-independent, so every return is a double '
                      'translation skew over its x-part and its '
                      f'(z0,z1)-monodromy order divides m = {m}; at least '
                      f'm = {m} cycles per color, for EVERY such transport')
    return leaf_single

# ---------------------------------------------------------------- driver

class Res:
    def __init__(self):
        self.fails = []
        self.records = []
    def clause(self, name, ok, detail='', severity='gate'):
        tag = 'PASS' if ok else 'FAIL'
        print(f'  [{tag}] {name}' + ('' if ok or not detail else f'\n          {detail}'))
        self.records.append(dict(name=name, ok=bool(ok),
                                 detail='' if ok else detail))
        if not ok:
            self.fails.append(name)
    def info(self, msg):
        print(f'  [info] {msg}')
        self.records.append(dict(info=msg))

def new_color_replay(m):
    res = Res()
    print(f'=== part (c): decisive new-color replay, chained 7->9 at the '
          f'(7,{m}) base ===')
    print('--- C1: displayed row words over the embedded base '
          '(the GrowthStepCore picture) ---')
    ok1 = alphabet_scan(res, m)
    print('--- C2: canonical re-realized skeleton transport '
          '(design doc 1.3 picture) ---')
    ok2 = shift_transport(res, m)
    print('--- C3: recorded GrowthStepCore findings (context) ---')
    res.info('C3: growth_step_replay --growth-step: under growthDir the two '
             'new-color returns have cycle type m x (K*m); --core-findings: '
             '0/9576 same-layer m-letter role products, 0/28 dropped-letter '
             'words, 0/252 donated two-layer words single; donated-cycles '
             'parity identity refutes single-partner handovers.')
    verdict = 'PASS' if not res.fails else 'FAIL'
    print(f'=== new-color replay verdict at (7,{m}): {verdict} ===')
    for f in res.fails:
        print(f'  failed: {f}')
    out = Path(__file__).resolve().parent / f'oldgens_newcolor_replay_m{m}.json'
    out.write_text(json.dumps(dict(m=m, verdict=verdict, fails=res.fails,
                                   records=res.records), indent=1))
    print(f'[json] {out}')
    return not res.fails

if __name__ == '__main__':
    m = 4
    if '--m' in sys.argv:
        m = int(sys.argv[sys.argv.index('--m') + 1])
    sys.exit(0 if new_color_replay(m) else 1)
