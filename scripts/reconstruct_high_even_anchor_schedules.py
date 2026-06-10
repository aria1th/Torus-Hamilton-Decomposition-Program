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

RESOLVED (2026-06-10, v2 -- see the `--tower`/`--certs` subcommands):
  Integrating (1)+(2) closes RF3.  Verdicts (deterministic, canonical
  placement, no search needed):
    * D5 terminal fan, m=6:  RF1+RF2+RF3 PASS, all five returns single
      1296-cycles; realized unit carry +1 on K/<F_c> for every color.
    * D5 terminal fan, m=8:  PASS (single 4096-cycles); also replayed at
      m=10, 12 (uniform in m, as the paper claims).
    * D7 two-rail anchor, m=8:  RF1+RF2+RF3 PASS, all seven returns
      single 262144-cycles, realized unit carries +1; also replayed at
      m=10 per color.
  The working placement reading (the G6 spec):
    (a) Rank-countdown supports.  The splice row of component P at stage
        r is substituted (full shifted stage row on the affected colors)
        on the affine coset  base_{r,P} + <alpha_e : e in M_{r,P}>  of
        rank D-r-1, where M_{r,P} is the printed support forest read in
        SLOT labels at that stage's height, and the exterior fibers of
        the base point realize the kappa dictionary of
        tab:anchor-affine-lift-dictionary (the omitted contracted
        component of each affected color sits at level kappa_{r,P}; the
        remaining row-band levels are free).  Substituting only the
        active basis (no countdown) starves at ~150-176 cycles per
        color even with the terminal block; the countdown is
        load-bearing exactly as the parity calculus predicts.
    (b) Terminal A2 block.  The final triple (t,0,1) is realized as the
        pointwise word omega_m (subtex/terminal_A2_block.tex,
        eq:terminal-word; encoding cross-checked against the printed
        m=4 orbits) on the rank-2 affine block
        Pi = x0 + <step(L0)-step(L2), step(L1)-step(L2)>, where
        (L0,L1,L2) assigns block colors to the carrier slots; exterior
        fibers of x0 pinned.  At a block point with word w, the carrier
        color of block index i reads direction L_{w_i}.  All three
        carrier colors must read omega at the SAME root-flat point
        (their common triangle base); the per-color eta-offset
        convention of the F_i analysis (word at x - a_i) reproduces the
        same single-cycle returns but is NOT pointwise row-Latin (12
        non-Latin points at m=6), so the layer table must use the
        shared-point convention.  Without the block the carrier colors
        plateau at exactly m cycles of length m^{D-2} (the H_{c,2}
        levels), machine-confirming mechanism (2).
  Robustness (recorded for paper section 8 precision): at D5 m=6 the
  RF3 verdict is insensitive to all six carrier-slot assignments, all
  m^2 word offsets phi, and the scanned band/pin placements -- the
  kappa/row-band values are load-bearing for the separation and reserve
  clauses, not for RF3 itself at these moduli.  The only genuine
  prose ambiguity found (slot-vs-chronological labels for the support
  forests) resolves to SLOT labels: chronological-label spans break the
  active-basis containment, hence RF2.
  Certificates: scripts/anchor_certs/*.json (rank7 root-flat seed
  conventions + affine 'base' extension on supports; terminal block as
  a point-major layer_override on the carrier colors), with
  verification_output.json carrying cycle types and sha256; rebuild via
  `--certs`, re-verify from JSON alone via `--verify-certs`.

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

def legacy_main():
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

# ======================================================================
# v2 (2026-06-10): full RF3 reconstruction.
#
# Two mechanisms added on top of the v1 harness (see STATUS in docstring):
#   (i)  the rank-countdown support tower: each splice row at stage r is
#        substituted on an affine coset  base + <alpha_e : e in M_{r,P}>
#        of rank D-r-1 (the printed support forests, slot labels), with
#        the exterior fibers pinned by the kappa values of
#        tab:anchor-affine-lift-dictionary (omitted contracted component
#        per affected color) plus free "row-band" values;
#   (ii) the terminal A2 block: the final triple (t,0,1) is NOT a
#        constant-row substitution; the three carrier colors are given
#        the pointwise terminal row word omega_m on a rank-2 affine
#        block Pi = x0 + <v1,v2> (v_i = differences of the carrier slot
#        step vectors), exterior fibers pinned; color of block index i
#        reads the word at the triangle base q = x - a_i (the eta
#        convention of subtex/terminal_A2_block.tex).
# ======================================================================

TERM_WORDS = dict(default=(0, 1, 2), t02=(2, 1, 0), t12=(0, 2, 1),
                  t01=(1, 0, 2), chip=(1, 2, 0), chim=(2, 0, 1))

def terminal_word_table(m):
    """omega_m of subtex/terminal_A2_block.tex eq:terminal-word, as a dict
    (z1,z2) -> word tuple (head index per block color); default rows omitted.
    Verified against the printed m=4 orbits of lem:terminal-m4-finite-check."""
    p = (1, 2)
    tab = {}
    lines = [((1, 0), 't02', 'chim', 'chip'),       # H: p-eH chi-, p+eH chi+
             ((0, 1), 't12', 'chip', 'chim'),       # V: p-eV chi+, p+eV chi-
             ((m - 1, 1), 't01', 'chim', 'chip')]   # D: p-eD chi-, p+eD chi+
    for vec, gen, minus, plus in lines:
        for t in range(1, m):
            z = ((p[0] + t * vec[0]) % m, (p[1] + t * vec[1]) % m)
            tab[z] = TERM_WORDS[plus if t == 1 else (minus if t == m - 1 else gen)]
    return tab

TERM_A = [(1, 0), (0, 1), (0, 0)]   # a_0, a_1, a_2 block steps

def alpha_vec(d, i, j):
    """u_j - u_i in the (d-1)-coordinate chart (label d-1 steps 0)."""
    r = d - 1
    v = [0] * r
    if i < r: v[i] -= 1
    if j < r: v[j] += 1
    return v

def step_vec(d, label):
    r = d - 1
    v = [0] * r
    if label < r: v[label] = 1
    return v

# --- anchor tower configurations -------------------------------------
# comps: (stage, affected chronological colors, support forest M (slot
# labels), base-point function(params, m) -> coords).  Base points encode
# the kappa pins of tab:anchor-affine-lift-dictionary; b* are the free
# row-band values, default 0.

def _g(prm, k):
    return prm.get(k, 0)

D5_TOWER = dict(
    d=5,
    shifted_rows=D5_SHIFTED_ROWS,
    stage_shifts=[0, 1, 2],
    missing=[3, 4],
    comps=[
        # stage 1 (h=0): triple (0,2,1) kappa 0; pair (3,4) kappa 1
        dict(stage=0, colors=[0, 2, 1], M=[(0, 1), (0, 2), (0, 3)],
             base=lambda prm, m: (0, 0, 0, 0)),                       # Sum x = 0
        dict(stage=0, colors=[3, 4], M=[(0, 1), (0, 3), (3, 4)],
             base=lambda prm, m: (0, 0, 1, 0)),                       # x2 = 1
        # stage 2 (h=1): triple (0,4,3) kappa 0; pair (1,2) kappa 1
        dict(stage=1, colors=[0, 4, 3], M=[(0, 1), (0, 4)],
             base=lambda prm, m: (0, 0, 0, 0)),                       # x2 = x3 = 0
        dict(stage=1, colors=[1, 2], M=[(0, 2), (2, 3)],
             base=lambda prm, m: (0, _g(prm, 'b1'), 0,
                                  (-1 - _g(prm, 'b1')) % m)),         # Sum x = -1, x1 = b1
        # stage 3 (h=2): final pair (0,2) kappa 0
        dict(stage=2, colors=[0, 2], M=[(2, 4)],
             base=lambda prm, m: (0, _g(prm, 'b2'), 0, 0)),           # x0 = x3 = 0, x1 = b2
    ],
    terminal=dict(stage=2, slots=(3, 0, 1),
                  base=lambda prm, m: ((-_g(prm, 'pb') - _g(prm, 'pa')) % m, 0,
                                       _g(prm, 'pa'), 0)),            # x2 = pa, x4 = pb
)

D7_TOWER = dict(
    d=7,
    shifted_rows=D7_SHIFTED_ROWS,
    stage_shifts=[0, 1, 2, 3, 5],
    missing=[4, 6],
    comps=[
        # stage 1 (h=0): kappa 0;1;2
        dict(stage=0, colors=[0, 1, 2], M=[(0, 1), (0, 2), (0, 3), (0, 4), (0, 5)],
             base=lambda prm, m: (0, 0, 0, 0, 0, 0)),                 # Sum x = 0
        dict(stage=0, colors=[3, 4], M=[(0, 1), (0, 2), (0, 3), (0, 5), (3, 4)],
             base=lambda prm, m: ((-1) % m, 0, 0, 0, 0, 0)),          # Sum x = -1
        dict(stage=0, colors=[5, 6], M=[(0, 1), (0, 2), (0, 3), (0, 5), (5, 6)],
             base=lambda prm, m: (0, 0, 0, 0, 2, 0)),                 # x4 = 2
        # stage 2 (h=1): kappa 0;1;2
        dict(stage=1, colors=[1, 3, 4], M=[(0, 1), (0, 3), (2, 4), (2, 5)],
             base=lambda prm, m: ((-_g(prm, 's2t')) % m, 0, _g(prm, 's2t'), 0, 0, 0)),
        dict(stage=1, colors=[0, 2], M=[(0, 4), (0, 5), (1, 2), (1, 3)],
             base=lambda prm, m: (_g(prm, 's2p1'), (-1 - _g(prm, 's2p1')) % m, 0, 0, 0, 0)),
        dict(stage=1, colors=[5, 6], M=[(0, 1), (0, 2), (0, 3), (0, 6)],
             base=lambda prm, m: (0, 0, 0, 0, 2, _g(prm, 's2p2'))),
        # stage 3 (h=2): kappa 0;1;2
        dict(stage=2, colors=[0, 6, 2], M=[(1, 2), (1, 4), (1, 5)],
             base=lambda prm, m: (_g(prm, 's3t'), (-_g(prm, 's3t')) % m, 0, 0, 0, 0)),
        dict(stage=2, colors=[1, 5], M=[(0, 1), (0, 3), (2, 5)],
             base=lambda prm, m: ((-2 - _g(prm, 's3p1')) % m, 0, _g(prm, 's3p1'), 0, 1, 0)),
        dict(stage=2, colors=[3, 4], M=[(0, 2), (0, 3), (5, 6)],
             base=lambda prm, m: ((-2 - _g(prm, 's3p2a') - _g(prm, 's3p2b')) % m, 2, 0, 0,
                                  _g(prm, 's3p2a'), _g(prm, 's3p2b'))),
        # stage 4 (h=3): kappa 0;1;2
        dict(stage=3, colors=[2, 5, 6], M=[(1, 2), (1, 5)],
             base=lambda prm, m: (_g(prm, 's4t'), (-_g(prm, 's4t')) % m, 0, 0, 0, 0)),
        dict(stage=3, colors=[0, 1], M=[(0, 5), (3, 4)],
             base=lambda prm, m: ((-1 - _g(prm, 's4p1a') - _g(prm, 's4p1b') - _g(prm, 's4p1c')) % m,
                                  _g(prm, 's4p1b'), _g(prm, 's4p1c'), _g(prm, 's4p1a'), 0, 0)),
        dict(stage=3, colors=[3, 4], M=[(0, 6), (2, 3)],
             base=lambda prm, m: (0, 2, _g(prm, 's4p2a'), 0, _g(prm, 's4p2b'), _g(prm, 's4p2c'))),
        # stage 5 (h=4): final pairs, kappa 0;1
        dict(stage=4, colors=[1, 6], M=[(4, 6)],
             base=lambda prm, m: (_g(prm, 's5p1a'), _g(prm, 's5p1b'), _g(prm, 's5p1c'), 0, 0, 0)),
        dict(stage=4, colors=[4, 5], M=[(2, 3)],
             base=lambda prm, m: (_g(prm, 's5p2a'), 1, _g(prm, 's5p2c'), 0, 1, _g(prm, 's5p2b'))),
    ],
    terminal=dict(stage=4, slots=(5, 0, 1),
                  base=lambda prm, m: ((-_g(prm, 'p4') - _g(prm, 'p1') - _g(prm, 'p2') - _g(prm, 'p3')) % m,
                                       0, _g(prm, 'p1'), _g(prm, 'p2'), _g(prm, 'p3'), 0)),
)

class TowerAnchor:
    """Builds and checks one anchor schedule under the tower+terminal reading.

    params (all default 0 unless noted):
      b*/s*  row-band values of splice supports;
      pa,pb / p1..p4  exterior pins of the terminal block plane;
      phi    (f1,f2) word-table offset inside the block;
      assign permutation of the carrier slots: block color i <-> slot L[i];
      eta    1 = word read at triangle base q = x - a_i (paper eta
             convention), 0 = word read at the point itself.
    """

    def __init__(self, cfg, m):
        self.cfg = cfg
        self.d = cfg['d']
        self.m = m
        self.r = self.d - 1
        self.K = m ** self.r
        add, powm = build_add_dirs(self.d, m)
        self.ADD = [list(a) for a in add]
        self.powm = powm
        nstage = len(cfg['stage_shifts'])
        assert m >= nstage + len(cfg['missing'])
        self.layer_shifts = list(cfg['stage_shifts']) + list(cfg['missing']) + \
            [0] * (m - nstage - len(cfg['missing']))
        self.sigmas = [perm_from_cycles(self.d, [st['triple']] + [list(p) for p in st['pairs']])
                       for st in cfg['shifted_rows']]
        self.word_tab = terminal_word_table(m)
        ts = cfg['terminal']
        self.tslots = ts['slots']
        self.theight = ts['stage']
        s_term = cfg['stage_shifts'][ts['stage']]
        self.carrier = [(L - s_term) % self.d for L in self.tslots]  # chrono colors by slot order
        self._patch_cache = {}

    def enc_pt(self, coords):
        return enc(coords, self.m)

    def support_points(self, comp, prm):
        base = tuple(a % self.m for a in comp['base'](prm, self.m))
        key = (id(comp), base)
        cached = self._patch_cache.get(key)
        if cached is not None:
            return cached
        basis = [alpha_vec(self.d, i, j) for (i, j) in comp['M']]
        offs = span_offsets(basis, self.m, self.r)
        pts = [self.enc_pt([(a + b) % self.m for a, b in zip(off, base)]) for off in offs]
        self._patch_cache[key] = pts
        return pts

    def stage_patch(self, comp, c, prm):
        """dict x -> direction for color c on comp's support."""
        st = comp['stage']
        s = self.cfg['stage_shifts'][st]
        slot = (c + s) % self.d
        newdir = self.sigmas[st][slot]
        return {x: newdir for x in self.support_points(comp, prm)}

    def terminal_patch(self, prm):
        """per chrono carrier color: dict x -> direction (non-default only)."""
        m, d = self.m, self.d
        L = prm.get('assign', tuple(self.tslots))
        x0 = [a % m for a in self.cfg['terminal']['base'](prm, m)]
        v1 = alpha_vec(d, L[2], L[0])
        v2 = alpha_vec(d, L[2], L[1])
        steps = [step_vec(d, l) for l in L]
        f1, f2 = prm.get('phi', (0, 0))
        eta = prm.get('eta', 1)
        out = {}
        for i in range(3):
            c = (L[i] - self.cfg['stage_shifts'][self.theight]) % d
            patch = {}
            for z1 in range(m):
                for z2 in range(m):
                    w = self.word_tab.get(((z1 + f1) % m, (z2 + f2) % m))
                    if w is None or w[i] == i:
                        continue
                    q = [(x0[k] + z1 * v1[k] + z2 * v2[k]) % m for k in range(self.r)]
                    if eta:
                        q = [(q[k] + steps[i][k]) % m for k in range(self.r)]
                    patch[self.enc_pt(q)] = L[w[i]]
            out[c] = patch
        return out

    def color_layers(self, c, prm, term_patch=None):
        """list of layer maps for color c: ('perm', list) or ('patch', basearr, dict)."""
        m, d = self.m, self.d
        if term_patch is None:
            term_patch = self.terminal_patch(prm)
        layers = []
        for t in range(m):
            s = self.layer_shifts[t]
            slot = (c + s) % d
            base = self.ADD[slot]
            patch = {}
            for comp in self.cfg['comps']:
                if comp['stage'] == t and t < len(self.cfg['stage_shifts']) and c in comp['colors']:
                    patch.update(self.stage_patch(comp, c, prm))
            if t == self.theight and c in self.carrier:
                patch.update(term_patch[c])
            if patch:
                arr = list(base)
                for x, dr in patch.items():
                    arr[x] = self.ADD[dr][x]
                layers.append(arr)
            else:
                layers.append(base)
        return layers

    def color_return(self, c, prm, term_patch=None):
        R = list(range(self.K))
        for P in self.color_layers(c, prm, term_patch):
            R = [P[v] for v in R]
        return R

    def is_perm(self, arr):
        seen = bytearray(self.K)
        for y in arr:
            if seen[y]:
                return False
            seen[y] = 1
        return True

    def cycle_type(self, R):
        return sorted(cycle_lengths(R), reverse=True)

    def single_cycle(self, R):
        x = R[0]
        n = 1
        while x != 0:
            x = R[x]
            n += 1
            if n > self.K:
                return False
        return n == self.K

    def build_dirs(self, prm):
        """full dirs[t][c][x] for the existing verify()."""
        m, d, K = self.m, self.d, self.K
        dirs = [[bytearray([(c + s) % d]) * K for c in range(d)] for s in self.layer_shifts]
        for comp in self.cfg['comps']:
            t = comp['stage']
            s = self.cfg['stage_shifts'][t]
            pts = self.support_points(comp, prm)
            for c in comp['colors']:
                slot = (c + s) % d
                nd = self.sigmas[t][slot]
                for x in pts:
                    dirs[t][c][x] = nd
        tp = self.terminal_patch(prm)
        for c, patch in tp.items():
            for x, dr in patch.items():
                dirs[self.theight][c][x] = dr
        return dirs

# ---------------------------------------------------------------- search

def d5_screen(m, verbose=True):
    """Deterministic staged search for the D5 fan at modulus m.
    Returns (params, verify-result) on success, else None."""
    anchor = TowerAnchor(D5_TOWER, m)
    K = anchor.K
    # carrier colors by slot order (3,0,1) -> chrono (1,3,4); colors 3,4 are
    # band-free, color 1 sees band b1; pair colors 0,2 see b1/b2.
    slots = list(anchor.tslots)
    assigns = []
    for pm in itertools.permutations(slots):
        assigns.append(pm)
    base_prm = dict()
    # precompute PRE/POST compositions for the band-free carrier colors
    def pre_post(c, prm):
        layers = anchor.color_layers(c, prm, term_patch={cc: {} for cc in anchor.carrier})
        PRE = list(range(K))
        for P in layers[:anchor.theight]:
            PRE = [P[v] for v in PRE]
        POST = list(range(K))
        for P in layers[anchor.theight + 1:]:
            POST = [P[v] for v in POST]
        base_term = layers[anchor.theight]
        return PRE, POST, base_term
    found = []
    tried = 0
    for eta in (0, 1):   # eta=0 (shared-point word) is the row-Latin reading
        for assign in assigns:
            prm0 = dict(base_prm, assign=assign, eta=eta)
            screen_colors = [c for c in anchor.carrier if c in (3, 4)]
            pp = {c: pre_post(c, prm0) for c in screen_colors}
            for pa in range(m):
                for pb in range(m):
                    for f1 in range(m):
                        for f2 in range(m):
                            prm = dict(prm0, pa=pa, pb=pb, phi=(f1, f2))
                            tried += 1
                            tp = anchor.terminal_patch(prm)
                            ok = True
                            ADD = anchor.ADD
                            for c in screen_colors:
                                PRE, POST, bt = pp[c]
                                patch = tp[c]
                                R = [POST[bt[v] if v not in patch else ADD[patch[v]][v]]
                                     for v in PRE]
                                if not anchor.single_cycle(R):
                                    ok = False
                                    break
                            if not ok:
                                continue
                            # color 1 (carrier, sees band b1)
                            for b1 in range(m):
                                prm2 = dict(prm, b1=b1)
                                R1 = anchor.color_return(1, prm2, tp)
                                if not anchor.single_cycle(R1):
                                    continue
                                for b2 in range(m):
                                    prm3 = dict(prm2, b2=b2)
                                    R0 = anchor.color_return(0, prm3, tp)
                                    if not anchor.single_cycle(R0):
                                        continue
                                    R2 = anchor.color_return(2, prm3, tp)
                                    if not anchor.single_cycle(R2):
                                        continue
                                    found.append(prm3)
                                    if verbose:
                                        print(f'[D5 m={m}] candidate after {tried} screens: {fmt_prm(prm3)}')
                                    dirs = anchor.build_dirs(prm3)
                                    res = verify(5, m, dirs)
                                    if res.get('rf1') and res.get('rf2') and res.get('rf3'):
                                        return prm3, res
                                    if verbose:
                                        print(f'  full verify failed: {res}')
    if verbose:
        print(f'[D5 m={m}] screen exhausted ({tried} terminal placements), no RF3 candidate')
    return None

def fmt_prm(prm):
    return {k: v for k, v in sorted(prm.items()) if not callable(v)}

# ------------------------------------------------------------ certificates

def realized_unit_carries(cfg, m, dirs, iota):
    """Marked-ledger check: the final one-isolate quotient K/<F_c> ~ Z/m is
    coordinatized by lambda_c(x) = x_{iota_c} (the isolated label is avoided
    by every forest edge).  The realized return must translate this quotient
    coordinate by a constant unit +-1 -- the closing-column unit carry as
    actual return cyclicity.  Returns {c: carry} or {c: None} on failure."""
    d = cfg['d']; r = d - 1; K = m ** r
    add_dir, _ = build_add_dirs(d, m)
    out = {}
    for c in range(d):
        R = array('I', range(K))
        for t in range(m):
            dc = dirs[t][c]
            for x in range(K):
                R[x] = add_dir[dc[R[x]]][R[x]]
        i = iota[c]
        def lam(x):
            co = dec(x, m, r)
            return co[i] % m if i < r else (-sum(co)) % m
        carries = {(lam(R[x]) - lam(x)) % m for x in range(K)}
        if len(carries) == 1:
            v = carries.pop()
            out[c] = v if v in (1, m - 1) else None
        else:
            out[c] = None
    return out

CANONICAL_PRM = dict(eta=0, phi=(0, 0))   # all bands/pins 0; assign = (t,0,1)

def canonical_params(cfg):
    return dict(CANONICAL_PRM, assign=tuple(cfg['terminal']['slots']))

def make_seed(cfg, m, prm):
    """JSON seed in the conventions of even_modulus_rewrite_20260610/
    certificates (verify_rank7_rootflat_certificates.py), with one format
    extension: each support carries an affine 'base' point.  The terminal
    A2 block ships both structurally ('terminal_block') and as a standard
    point-major zlib+base64 layer override on the carrier colors."""
    import base64, zlib
    d = cfg['d']
    anchor = TowerAnchor(cfg, m)
    dirs = anchor.build_dirs(prm)
    stages = []
    for st_idx, st in enumerate(cfg['shifted_rows']):
        s = cfg['stage_shifts'][st_idx]
        # chronological row permutation T_r (verifier reads dirs as (T[c]+shift)%d)
        T = [(anchor.sigmas[st_idx][(c + s) % d] - s) % d for c in range(d)]
        sups = []
        for comp in cfg['comps']:
            if comp['stage'] != st_idx:
                continue
            base = [a % m for a in comp['base'](prm, m)]
            sups.append(dict(colors=list(comp['colors']),
                             basis=[alpha_vec(d, i, j) for (i, j) in comp['M']],
                             base=base,
                             support_forest=[list(e) for e in comp['M']]))
        stages.append(dict(layer=st_idx, shift=s, sigma=T, supports=sups))
    K = anchor.K
    carrier = sorted(anchor.carrier)
    raw = bytearray()
    for x in range(K):
        for c in carrier:
            raw.append(dirs[anchor.theight][c][x])
    ts = cfg['terminal']
    L = prm.get('assign', tuple(ts['slots']))
    seed = dict(
        d=d, m=m,
        status='reconstructed high-even anchor schedule (RF1+RF2+RF3 verified)',
        certificate_type='high_even_anchor_tower_terminalA2',
        format_note=('rank7 root-flat seed conventions; extension: supports are affine '
                     '(field "base"); the terminal triple is realized by the omega_m '
                     'terminal A2 block (subtex/terminal_A2_block.tex) on the carrier '
                     'colors, shipped as the layer_overrides entry below'),
        layer_shifts=anchor.layer_shifts,
        stages=stages,
        layer_overrides=[dict(layer=anchor.theight, colors=carrier,
                              encoding='zlib+base64', order='point-major',
                              data=base64.b64encode(zlib.compress(bytes(raw), 9)).decode())],
        terminal_block=dict(slots=list(ts['slots']),
                            assign=list(L),
                            plane_base=[a % m for a in ts['base'](prm, m)],
                            v1=alpha_vec(d, L[2], L[0]),
                            v2=alpha_vec(d, L[2], L[1]),
                            phi=list(prm.get('phi', (0, 0))),
                            eta_convention=prm.get('eta', 0),
                            word='omega_m of terminal_A2_block.tex eq:terminal-word'),
        params={k: list(v) if isinstance(v, tuple) else v for k, v in fmt_prm(prm).items()},
    )
    return seed, dirs

def reconstruct_seed(seed):
    """Reconstruct dirs from a seed JSON alone (affine-support extension of
    the rank7 verifier's reconstruct_rootflat)."""
    import base64, zlib
    d = int(seed['d']); m = int(seed['m']); r = d - 1; K = m ** r
    layer_shifts = seed['layer_shifts']
    dirs = [[bytearray([(c + s) % d]) * K for c in range(d)] for s in layer_shifts]
    for st in seed['stages']:
        layer = int(st['layer']); shift = int(st['shift']); sig = st['sigma']
        for sup in st.get('supports', []):
            offs = span_offsets(sup['basis'], m, r)
            base = sup.get('base', [0] * r)
            for off in offs:
                x = enc([(a + b) % m for a, b in zip(off, base)], m)
                for c in sup['colors']:
                    dirs[layer][c][x] = (sig[c] + shift) % d
    for ov in seed.get('layer_overrides', []):
        layer = int(ov['layer']); colors = [int(c) for c in ov['colors']]
        raw = zlib.decompress(base64.b64decode(ov['data']))
        assert len(raw) == K * len(colors)
        pos = 0
        for x in range(K):
            for c in colors:
                dirs[layer][c][x] = raw[pos]; pos += 1
    return dirs

def run_tower_case(name, cfg, m, prm=None):
    import hashlib
    prm = prm or canonical_params(cfg)
    print(f'[{name} m={m}] tower+terminal reconstruction, params={fmt_prm(prm)}')
    seed, dirs = make_seed(cfg, m, prm)
    # round-trip: dirs reconstructed from the JSON alone must agree
    dirs2 = reconstruct_seed(seed)
    rt = all(dirs[t][c] == dirs2[t][c] for t in range(m) for c in range(cfg['d']))
    res = verify(cfg['d'], m, dirs2)
    iota = D5_IOTA if cfg['d'] == 5 else D7_IOTA
    okb, rep = closing_budget(cfg['d'], m, cfg['shifted_rows'],
                              cfg['missing'] + [0] * (m - len(cfg['stage_shifts']) - len(cfg['missing'])),
                              iota)
    res['closing_budget_unit'] = okb
    res['closing_budget'] = rep
    carries = realized_unit_carries(cfg, m, dirs2, iota)
    res['realized_unit_carries'] = carries
    print(f'  closing-column ledger (iota class, crossings): {rep}  unit-ok={okb}')
    print(f'  realized unit carries on K/<F_c> (must be +-1 units): {carries}')
    print(f'  seed round-trip={rt}  RF1={res.get("rf1")} RF2={res.get("rf2")} RF3={res.get("rf3")}')
    print(f'  return cycle lengths: {res.get("lens")}')
    ok = rt and res.get('rf1') and res.get('rf2') and res.get('rf3')
    return ok, seed, res

def write_certs(with_d7=True):
    import hashlib, os
    here = __file__.rsplit('/', 1)[0]
    outdir = here + '/anchor_certs'
    os.makedirs(outdir, exist_ok=True)
    cases = [('D5_fan', D5_TOWER, 6), ('D5_fan', D5_TOWER, 8)]
    if with_d7:
        cases.append(('D7_two_rail', D7_TOWER, 8))
    report = {}
    allok = True
    for name, cfg, m in cases:
        ok, seed, res = run_tower_case(name, cfg, m)
        allok = allok and ok
        fname = f'{name}_m{m}_seed.json'
        path = f'{outdir}/{fname}'
        with open(path, 'w') as f:
            json.dump(seed, f, separators=(',', ':'))
        sha = hashlib.sha256(open(path, 'rb').read()).hexdigest()
        report[f'{name}_m{m}'] = dict(
            ok=bool(ok), d=cfg['d'], m=m, root_flat_size=m ** (cfg['d'] - 1),
            rf1=bool(res.get('rf1')), rf2=bool(res.get('rf2')), rf3=bool(res.get('rf3')),
            return_cycle_lengths=res.get('lens'),
            params=seed['params'], seed_file=fname, sha256=sha)
        print(f'  wrote {path}  sha256={sha}')
    with open(f'{outdir}/verification_output.json', 'w') as f:
        json.dump(report, f, indent=2)
    print(f'[certs] all ok = {allok}; report at {outdir}/verification_output.json')
    return allok

def verify_certs():
    import hashlib, os
    here = __file__.rsplit('/', 1)[0]
    outdir = here + '/anchor_certs'
    report = json.load(open(f'{outdir}/verification_output.json'))
    allok = True
    for key, rec in report.items():
        path = f'{outdir}/{rec["seed_file"]}'
        sha = hashlib.sha256(open(path, 'rb').read()).hexdigest()
        seed = json.load(open(path))
        dirs = reconstruct_seed(seed)
        res = verify(seed['d'], seed['m'], dirs)
        ok = (sha == rec['sha256'] and res.get('rf1') and res.get('rf2')
              and res.get('rf3'))
        allok = allok and ok
        print(f'[{key}] sha-match={sha == rec["sha256"]} rf1={res.get("rf1")} '
              f'rf2={res.get("rf2")} rf3={res.get("rf3")} lens={res.get("lens")}')
    print(f'[verify-certs] all ok = {allok}')
    return allok

def tower_main(argv):
    cases = [(D5_TOWER, 6), (D5_TOWER, 8)]
    if '--d7' in argv:
        cases.append((D7_TOWER, 8))
    for cfg, m in cases:
        name = 'D5-fan' if cfg['d'] == 5 else 'D7-two-rail'
        run_tower_case(name, cfg, m)

def main():
    argv = sys.argv[1:]
    if not argv or '--legacy' in argv:
        legacy_main()
        return
    if '--tower' in argv:
        tower_main(argv)
        return
    if '--certs' in argv:
        ok = write_certs(with_d7='--no-d7' not in argv)
        sys.exit(0 if ok else 1)
    if '--verify-certs' in argv:
        ok = verify_certs()
        sys.exit(0 if ok else 1)
    if '--screen-d5' in argv:
        m = int(argv[argv.index('--screen-d5') + 1])
        out = d5_screen(m)
        if out:
            prm, res = out
            print(f'[D5 m={m}] RF1/RF2/RF3 PASS  params={fmt_prm(prm)}')
            print(f'  cycle lengths: {res["lens"]}')
        return
    legacy_main()

if __name__ == '__main__':
    main()
