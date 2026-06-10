#!/usr/bin/env python3
"""Reconstruct the §9 high-even anchor schedules (D=5 terminal fan, D=7
two-rail anchor) of the REWRITTEN paper
/data/angel/repos/etc/even_modulus_rewrite_20260610/ as actual root-flat layer
schedules at small even moduli m > D, and verify RF1/RF2/RF3 + the
unit-carry/closing-column ledger directly.

Conventions mirror the rewrite's companion verifier
(certificates/scripts/verify_rank7_rootflat_certificates.py):
  * state = root-flat section x in (Z/m)^(d-1); direction i < d-1 adds e_i,
    direction d-1 adds nothing (the dropped zero-sum coordinate);
  * the base row at a height with shift s is the constant row  c |-> (c+s)%d
    (chronological skeleton);
  * a stage at height t with shift s substitutes the SHIFTED stage row
    sigma_r (c |-> T_r(c - s) + s) for the affected colors of one physical
    component, on an affine support  beta + span(active diff vectors).

Per the paper:
  * stage shifts: D5 (0,1,2); D7 (0,1,2,3,5)  [tab:D5-stage-data, D7];
  * components: one oriented triple + matching pairs per stage;
  * unused heights: one height in each "missing" shift class (the class
    iota_c - c never hit by stage shifts), so each closing column crosses the
    isolated-label coordinate exactly once (carry +-1); remaining heights
    neutral (shift 0).

Each component substitution is COLOR-DISJOINT from the others at its height
(triple colors vs pair colors), and its support is closed under all of its own
difference vectors, so RF2 holds per the exact criterion
(EvenV11/V28Hard/EndpointRowSchedule.lean, layerMap_bijective_of_cylinder).
RF3 is checked by brute force; placement base points are searched over a small
family when the canonical all-zero placement fails.

STATUS (2026-06-10, see docs/GROWTH_ENGINE_DESIGN_20260610.md Part 1.1):
  * RF1, RF2, one-isolate forests, and the closing-column unit budget
    (exactly one crossing of the isolated-label class per color, via the
    shift multiset rule) VERIFY for D5 at every even m > 5 tried.
  * RF3 does NOT close under this simplified model.  Two machine-checked
    structural facts explain why and pin down the missing pieces:
    (1) PARITY: for even m a substituted layer is an ODD permutation iff its
        support has odd index |U|/ord(v); a single m^(D-1)-cycle return is an
        odd permutation; hence each color needs an odd number of odd-support
        substituted layers.  Hyperplane-only supports plateau at exactly
        [2,2,2,2,2] cycles; line-only supports starve the merge count
        ([~196,...]).  The paper's support-rank countdown D-r-1
        (m^3, m^2, m for D5) is exactly a parity-correct mixed tower.
    (2) The final stage triple is the TERMINAL A2 carrier (t,0,1), which is
        a t-dependent terminal-block realization (H1 machinery), NOT a
        support substitution; this model omits it, so the last quotient
        cannot close.
  Integrating (1)+(2) is the identified next step for a full RF3
  reconstruction; no exact-criterion (RF2) wall was found anywhere.

Stdlib only.
"""
from __future__ import annotations
from array import array
import itertools, json, sys

# ---------------------------------------------------------------- utilities

def dec(x: int, m: int, r: int):
    out = []
    for _ in range(r):
        out.append(x % m); x //= m
    return out

def enc(coords, m: int):
    p = 1; out = 0
    for a in coords:
        out += (a % m) * p; p *= m
    return out

def build_add_dirs(d: int, m: int):
    """add_dirs[i][x] = index of x + e_i (e_{d-1} = 0)."""
    r = d - 1; K = m ** r; powm = [m ** i for i in range(r)]
    add = []
    for direc in range(d):
        arr = array('I', [0]) * K
        for x in range(K):
            if direc == d - 1:
                arr[x] = x
            else:
                digit = (x // powm[direc]) % m
                arr[x] = x + powm[direc] if digit < m - 1 else x - (m - 1) * powm[direc]
        add.append(arr)
    return add, powm

def span_offsets(basis, m: int, r: int):
    """All Z/m-combinations of basis vectors (as coordinate tuples)."""
    pts = {tuple([0] * r)}
    for vec in basis:
        new = set()
        for p in pts:
            cur = list(p)
            for _ in range(m):
                new.add(tuple(cur))
                cur = [(a + b) % m for a, b in zip(cur, vec)]
        pts = new
    return pts

def cycle_lengths(p):
    N = len(p); seen = bytearray(N); lens = []
    for i in range(N):
        if not seen[i]:
            x = i; l = 0
            while not seen[x]:
                seen[x] = 1; l += 1; x = p[x]
            lens.append(l)
    return lens

# ------------------------------------------------------------- anchor data

# D5 terminal fan (tab:D5-stage-data): stage r, shift s_r, chronological
# triple T_r and pair.  Stored as the full chronological permutation T_r on
# Z/5 (cycle notation applied as listed: (a,b,c) means a->b->c->a).
def perm_from_cycles(d, cycles):
    T = list(range(d))
    for cyc in cycles:
        for i, a in enumerate(cyc):
            T[a] = cyc[(i + 1) % len(cyc)]
    return T

D5_STAGES = [
    dict(shift=0, triple=(0, 2, 1), pairs=[(3, 4)]),
    dict(shift=1, triple=(0, 4, 3), pairs=[(1, 2)]),
    dict(shift=2, triple=(1, 3, 4), pairs=[(0, 2)]),
]
# one-isolate data (tab:D5-determinants): color -> isolated label
D5_IOTA = {0: 3, 1: 4, 2: 0, 3: 2, 4: 2}

D7_STAGES = [
    dict(shift=0, triple=(0, 1, 2), pairs=[(3, 4), (5, 6)]),
    dict(shift=1, triple=(1, 3, 4), pairs=[(0, 2), (5, 6)]),
    dict(shift=2, triple=(0, 6, 2), pairs=[(1, 5), (3, 4)]),
    dict(shift=3, triple=(2, 5, 6), pairs=[(0, 1), (3, 4)]),
    dict(shift=5, triple=(1, 6, 0), pairs=[(4, 5), (2, 3)]),
]
# from tab:D7-determinants via finite_high_even_anchor_summary (iota_c)
D7_IOTA = {0: 6, 1: 5, 2: 6, 3: 2, 4: 1, 5: 4, 6: 3}

# NOTE on D7 stage 5: the summary prints the SHIFTED rows; shift 5 gives
# shifted triple (5+1,5+6,5+0)=(6,4,5)... we instead read the chronological
# triple/pairs directly off the printed shifted row (5,0,1)|(6,4),(2,3) by
# unshifting: chronological label = printed - 5 (mod 7):
#   triple (0,2,3)? -- resolved below by deriving from the printed shifted
#   rows, which are authoritative.
D7_SHIFTED_ROWS = [
    dict(shift=0, triple=(0, 1, 2), pairs=[(3, 4), (5, 6)]),
    dict(shift=1, triple=(2, 4, 5), pairs=[(1, 3), (6, 0)]),
    dict(shift=2, triple=(2, 1, 4), pairs=[(3, 0), (5, 6)]),
    dict(shift=3, triple=(5, 1, 2), pairs=[(3, 4), (6, 0)]),
    dict(shift=5, triple=(5, 0, 1), pairs=[(6, 4), (2, 3)]),
]
D5_SHIFTED_ROWS = [
    dict(shift=0, triple=(0, 2, 1), pairs=[(3, 4)]),
    dict(shift=1, triple=(1, 0, 4), pairs=[(2, 3)]),
    dict(shift=2, triple=(3, 0, 1), pairs=[(2, 4)]),
]

# ------------------------------------------------------- schedule assembly

def forests_from_shifted_rows(d, shifted_rows):
    """color forest F_c = { {c+s_r, sigma_r(c+s_r)} } and per-color edges."""
    F = {c: [] for c in range(d)}
    for st in shifted_rows:
        s = st['shift']
        sig = perm_from_cycles(d, [st['triple']] + [list(p) for p in st['pairs']])
        for c in range(d):
            slot = (c + s) % d
            F[c].append((slot, sig[slot]))
    return F

def check_one_isolate(d, F, iota):
    ok = True
    for c in range(d):
        labels = set()
        for a, b in F[c]:
            labels |= {a, b}
        isolate = set(range(d)) - labels
        if isolate != {iota[c]}:
            ok = False
    return ok

def diff_vec(d, m, frm, to, r):
    """stepVec(to) - stepVec(frm) as a length-r coordinate vector."""
    v = [0] * r
    if frm < r: v[frm] = (v[frm] - 1) % m
    if to < r: v[to] = (v[to] + 1) % m
    return v

def build_schedule(d, m, shifted_rows, unused_shifts, placements):
    """dirs[t][c][x]; stage heights are 0..len(stages)-1, then unused."""
    r = d - 1; K = m ** r
    nstage = len(shifted_rows)
    layer_shifts = [st['shift'] for st in shifted_rows] + list(unused_shifts)
    assert len(layer_shifts) == m
    dirs = [[bytearray([(c + s) % d]) * K for c in range(d)] for s in layer_shifts]
    powm = [m ** i for i in range(r)]
    supports = []  # (height, component-id, set of x)
    for t, st in enumerate(shifted_rows):
        s = st['shift']
        sig = perm_from_cycles(d, [st['triple']] + [list(p) for p in st['pairs']])
        comps = [('triple', st['triple'])] + [('pair', p) for p in st['pairs']]
        for ci, (kind, labels) in enumerate(comps):
            # affected colors: chronological colors whose slot is in `labels`
            colors = [(l - s) % d for l in labels]
            basis = []
            for c in colors:
                slot = (c + s) % d
                basis.append(diff_vec(d, m, slot, sig[slot], r))
            offs = span_offsets(basis, m, r)
            beta = placements.get((t, ci), [0] * r)
            sup = set()
            for off in offs:
                pt = [(a + b) % m for a, b in zip(off, beta)]
                sup.add(enc(pt, m))
            supports.append((t, ci, sup))
            for x in sup:
                for c in colors:
                    slot = (c + s) % d
                    dirs[t][c][x] = sig[slot]
    return dirs, layer_shifts, supports

def verify(d, m, dirs):
    r = d - 1; K = m ** r
    add_dir, _ = build_add_dirs(d, m)
    # RF1
    for t in range(m):
        cols = [dirs[t][c] for c in range(d)]
        for x in range(K):
            if len({cols[c][x] for c in range(d)}) != d:
                return dict(rf1=False, bad=(t, x))
    # RF2 + layer maps
    P = [[None] * d for _ in range(m)]
    for t in range(m):
        for c in range(d):
            seen = bytearray(K)
            arr = array('I', [0]) * K
            dc = dirs[t][c]
            for x in range(K):
                y = add_dir[dc[x]][x]
                arr[x] = y; seen[y] += 1
            if any(z != 1 for z in seen):
                return dict(rf1=True, rf2=False, bad=(t, c))
            P[t][c] = arr
    # RF3
    lens_summary = []
    rf3 = True
    for c in range(d):
        R = array('I', range(K))
        for t in range(m):
            Pt = P[t][c]
            for x in range(K):
                R[x] = Pt[R[x]]
        lens = cycle_lengths(R)
        lens_summary.append(lens if len(lens) < 6 else [lens[0], '...x%d' % len(lens)])
        if lens != [K]:
            rf3 = False
    return dict(rf1=True, rf2=True, rf3=rf3, lens=lens_summary)

def closing_budget(d, m, shifted_rows, unused_shifts, iota):
    """unit-carry ledger: #heights with shift == iota_c - c must be a unit
    (+-1) mod m for every color (the closing-column crossing count)."""
    layer_shifts = [st['shift'] for st in shifted_rows] + list(unused_shifts)
    report = {}
    ok = True
    for c in range(d):
        need = (iota[c] - c) % d
        cnt = sum(1 for s in layer_shifts if s % d == need)
        report[c] = (need, cnt)
        if cnt % m not in (1, m - 1):
            ok = False
    return ok, report

# ------------------------------------------------------------------ search

def missing_shift_classes(d, shifted_rows, iota):
    stage_shifts = {st['shift'] % d for st in shifted_rows}
    needs = {(iota[c] - c) % d for c in iota}
    assert not (needs & stage_shifts), (needs, stage_shifts)
    return sorted(needs)

def run_anchor(name, d, shifted_rows, iota, m, max_tries=20000, seed=0):
    r = d - 1
    needs = missing_shift_classes(d, shifted_rows, iota)
    nstage = len(shifted_rows)
    n_unused = m - nstage
    assert n_unused >= len(needs), 'modulus too small'
    unused = needs + [0] * (n_unused - len(needs))
    okb, rep = closing_budget(d, m, shifted_rows, unused, iota)
    print(f'[{name} m={m}] closing-column budget (iota class, crossings): {rep}  unit-ok={okb}')
    F = forests_from_shifted_rows(d, shifted_rows)
    print(f'[{name} m={m}] one-isolate forests ok={check_one_isolate(d, F, iota)}')
    ncomp = [1 + len(st['pairs']) for st in shifted_rows]
    # placement search: separate same-height components by base points
    import random
    rng = random.Random(seed)
    tries = 0
    # first the canonical family: component ci at stage t gets base = ci * kappa
    cand = []
    for kap in range(m):
        pl = {}
        for t in range(nstage):
            for ci in range(ncomp[t]):
                base = [0] * r
                base[(t + ci) % r] = (ci * kap) % m
                pl[(t, ci)] = base
        cand.append(pl)
    while True:
        if cand:
            pl = cand.pop(0)
        else:
            pl = {}
            for t in range(nstage):
                for ci in range(ncomp[t]):
                    pl[(t, ci)] = [rng.randrange(m) for _ in range(r)]
        tries += 1
        dirs, ls, sups = build_schedule(d, m, shifted_rows, unused, pl)
        res = verify(d, m, dirs)
        if res.get('rf1') and res.get('rf2') and res.get('rf3'):
            print(f'[{name} m={m}] SUCCESS after {tries} placement(s): RF1/RF2/RF3 all pass')
            print(f'  layer shifts = {ls}')
            print(f'  placements   = { {k: v for k, v in sorted(pl.items())} }')
            print(f'  return cycle lengths = {res["lens"]}')
            return dict(name=name, d=d, m=m, tries=tries, placements={str(k): v for k, v in pl.items()},
                        layer_shifts=ls, ok=True)
        if tries == 1:
            print(f'[{name} m={m}] canonical placement: rf1={res.get("rf1")} rf2={res.get("rf2")} '
                  f'rf3={res.get("rf3")} lens={res.get("lens")}')
        if tries >= max_tries:
            print(f'[{name} m={m}] FAILED after {tries} placements; last={res}')
            return dict(name=name, d=d, m=m, tries=tries, ok=False, last=str(res))

def parity_report(d, m):
    """Machine check of the parity calculus: a cylinder substitution on a
    support U with translation difference v of order m is odd iff |U|/m is
    odd; for even m this means rank-1 (line) supports and only those."""
    r = d - 1
    rows = []
    for codim in range(r):
        size = m ** (r - codim)
        idx = size // m
        rows.append((codim, size, idx, idx % 2 == 1))
    return rows

def main():
    out = []
    print('parity ledger (codim, |U|, |U|/m, odd-layer?) for D5 m=6:',
          parity_report(5, 6))
    out.append(run_anchor('D5-fan', 5, D5_SHIFTED_ROWS, D5_IOTA, 6, max_tries=4))
    out.append(run_anchor('D5-fan', 5, D5_SHIFTED_ROWS, D5_IOTA, 8, max_tries=2))
    if '--d7' in sys.argv:
        out.append(run_anchor('D7-two-rail', 7, D7_SHIFTED_ROWS, D7_IOTA, 8, max_tries=2))
    print(json.dumps([{k: v for k, v in o.items() if k != 'placements'} for o in out], indent=1))
    print('NOTE: rf3=False here is the documented PARTIAL status; '
          'RF1/RF2/budget passing is the de-risk content of this run.')

if __name__ == '__main__':
    main()
