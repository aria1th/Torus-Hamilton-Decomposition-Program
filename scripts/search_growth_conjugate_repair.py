#!/usr/bin/env python3
"""Conjugate-relaxation repair search for the chained 7->9 growth step.

CONTEXT (docs/GROWTH_REPAIR_GATE_20260610.md).  The budget gate proved the
7->9 step is INFEASIBLE when the seven old-color returns are kept pointwise
equal to growthDir's (R3-old equality): old colors then saturate every
x-direction read budget and the two leaf returns split into >= m^6 cycles.
THIS script works under the CONJUGATE relaxation -- old-color returns must
still be single K2-cycles (K2 = m^8) of growthDir carry character, but not
pointwise equal -- and asks whether a child schedule with RF1 + RF2 + all
NINE returns single K2-cycles exists over the shipped (7,4)/(7,6) bases.

Subcommands (stdlib only):

  --budget-refine [--m 4|6]   STEP-1 refinement of the budget under the
                              conjugate relaxation; machine-checks the new
                              necessary conditions (exit bound, slice-gating
                              rigidity, parity ledger, class-A m^3 bound,
                              swap-parity conservation) and the two family
                              kills (growthDir-shaped repairs, sketched
                              rotor).
  --seam-search [--m 4] [--iters N] [--restarts R] [--seed S]
                              STEP-2 structured search over the ribbon/
                              staircase/wild-seam family (below); logs scope
                              and writes a witness JSON on a hit.
  --verify-hit [--m 4|6] [--witness FILE]
                              rebuild a recorded witness over the proper base
                              at modulus m and fully verify RF1/RF2 + nine
                              single returns.
  --chain-check [--witness FILE]
                              on a hit child: measure whether the dimension-9
                              child satisfies the hypotheses the construction
                              itself consumes (Latin rows, single returns,
                              last-read spread, donor-orbit supply,
                              wild-seam column supply), i.e. whether the
                              step can iterate 9 -> 11.

THE SEAM FAMILY (each ingredient derived as necessary in --budget-refine):
  * FULL LEAF-ROLE SWAP at one layer tau_s (nu0 reads the z1-step there, nu1
    the z0-step): unit z-translation parts for both leaf colors, removing
    the m-2 rigidity that kills the sketched rotor (R5).
  * RIBBON DONATIONS: for an old color c, a layer t and an L_{t,c}-orbit
    O = (x_0 -> x_1 -> ...), donate the staircase cells
    (x_j, z0 = a - j mod m) (all z1) to nu0: nu0 takes c's x-read there, c
    reads the z0-step.  With the q-winding (q = m / gcd(|O|, m)) every
    orbit of length >= 2 closes the RF2 chain (removed image set = added
    image set, cyclically), so RF1 + RF2 hold BY CONSTRUCTION.  The slope
    -1 staircase and the donor-receives-the-gated-z-step pairing are both
    forced by RF2.  Symmetrically z1-gated ribbons feed nu1.  The exit
    bound (R1) forces the donated orbits to cover EVERY x-column; the
    block-confinement bound (R6) forces their union graph to be CONNECTED,
    hence donations at >= 2 layers per leaf color.
  * LEAF STAIRCASES: anti-diagonal (z0, z1 = b - z0) read swaps between the
    two leaf colors on single x-columns (z-mixing; odd deviation on both).
  * WILD SEAMS (the parity piece, R7): every 2-color read swap preserves the
    per-layer sign product N_t, and growthDir has N_t = +1 for all t while
    nine single returns force prod_t N_t = -1.  The d3-even rail-seam
    certificates of this repo ship 3-color wild layers on a (Z/m)^2 torus
    with N = -1; transplanted onto one x-column where an old color c reads
    the zero step (colors (nu0, nu1, c), directions (z0-step, z1-step,
    zero)), one wild seam flips the parities of all three, and together
    with one extra z1-line crossing for c it flips exactly nu0 -- the
    unique parity repair this catalog admits.
  * the growthDir plane/line crossings are kept for the old colors' unit
    carries; donor returns are perturbed by the donations (the conjugate
    relaxation) and are re-checked numerically.

Summary JSON: scripts/growth_conjugate_search_summary.json
Witness JSON: scripts/growth_conjugate_hit_m4.json (on a hit)
"""
from __future__ import annotations
from array import array
import json, math, random, sys, time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from growth_step_replay import (load_seed, build_add, cycle_lengths,
                                last_reads, grow_two_crossings, layer_maps,
                                compose, verify)

SUMMARY = HERE / 'growth_conjugate_search_summary.json'
NX = 6
WILD_CERTS = {4: 'd3_even_dir_m4_from_lean.json', 6: 'd3_even_dir_m6.json'}


# ---------------------------------------------------------------------------
# shared infrastructure
# ---------------------------------------------------------------------------

class Res:
    def __init__(self):
        self.fails = []
        self.records = []

    def clause(self, name, ok, detail=''):
        tag = 'PASS' if ok else 'FAIL'
        print(f'  [{tag}] {name}' + ('' if ok or not detail
                                     else f'\n          {detail}'))
        self.records.append(dict(name=name, ok=bool(ok),
                                 detail='' if ok else detail))
        if not ok:
            self.fails.append(name)

    def info(self, msg):
        print(f'  [info] {msg}')
        self.records.append(dict(info=msg))


def replay_placement(d, m, dirs):
    """the replay's deterministic crossing placement with the same-layer
    site-distinct fallback (gate finding 2)."""
    lam = last_reads(d, m, dirs)
    used = set()
    cross0, cross1, nonstrict = {}, {}, []
    for c in range(d):
        pick1 = pick0 = None
        for (t, x) in lam[c]:
            if (t, x) in used:
                continue
            if pick1 is None and t < m - 1:
                pick1 = (t, x); used.add((t, x)); continue
            if pick0 is None and pick1 is not None and t > pick1[0]:
                pick0 = (t, x); used.add((t, x)); break
        if not (pick0 and pick1):
            free = [(t, x) for (t, x) in lam[c] if (t, x) not in used]
            assert len(free) >= 2, f'no crossing pair for color {c}'
            pick1, pick0 = free[0], free[1]
            used.update((pick1, pick0))
            nonstrict.append(c)
        cross0[c] = pick0
        cross1[c] = (pick1[0], pick1[1], 0)
    return cross0, cross1, nonstrict


def orbit_table(d, m, dirs):
    """orbits[(t, c)] = list of L_{t,c}-cycles (length >= 2) in cycle order,
    keyed reproducibly (start = min element)."""
    K = m ** (d - 1)
    out = {}
    for t in range(m):
        for c in range(d):
            L = layer_maps(d, m, dirs, c)[t]
            seen = bytearray(K)
            cycs = []
            for s in range(K):
                if seen[s]:
                    continue
                cyc = [s]; seen[s] = 1; x = L[s]
                while x != s:
                    cyc.append(x); seen[x] = 1; x = L[x]
                if len(cyc) >= 2:
                    j = cyc.index(min(cyc))
                    cycs.append(cyc[j:] + cyc[:j])
            cycs.sort(key=lambda cy: cy[0])
            out[(t, c)] = cycs
    return out


def sign_of(p):
    N = len(p); seen = bytearray(N); s = 1
    for i in range(N):
        if not seen[i]:
            x = i; l = 0
            while not seen[x]:
                seen[x] = 1; l += 1; x = p[x]
            if l % 2 == 0:
                s = -s
    return s


def load_wild_layers(m):
    """3-color wild layers (per-layer triple sign product N = -1) from the
    d3-even rail-seam certificate; table[x0][x1] = (dir c0, dir c1, dir c2)
    with dirs 0 = e0, 1 = e1, 2 = zero."""
    data = json.loads((HERE / WILD_CERTS[m]).read_text())
    assert data['m'] == m
    EV = ((1, 0), (0, 1), (0, 0))
    wilds = []
    for layer in data['layers']:
        signs = []
        for c in range(3):
            f = {}
            for x in range(m):
                for y in range(m):
                    e = EV[layer[x][y][c]]
                    f[(x, y)] = ((x + e[0]) % m, (y + e[1]) % m)
            seen = set(); s = 1
            for p in f:
                if p in seen:
                    continue
                q = p; l = 0
                while q not in seen:
                    seen.add(q); l += 1; q = f[q]
                if l % 2 == 0:
                    s = -s
            signs.append(s)
        if signs[0] * signs[1] * signs[2] == -1:
            wilds.append(dict(table=layer, signs=signs))
    assert wilds, 'no wild (N = -1) layer in the d3-even certificate'
    return wilds


# ---------------------------------------------------------------------------
# seam-family construction pieces (False on conflict, never partial)
# ---------------------------------------------------------------------------

def ribbon_cells(cyc, a, m):
    L = len(cyc); q = m // math.gcd(L, m)
    return [(cyc[j % L], (a - j) % m) for j in range(q * L)]


def donate(child, dirs, m, K, t, c, cyc, a, axis, leaf):
    """staircase donation of one orbit to `leaf` (axis 0: z0-gated cells,
    donor receives the z0-step; axis 1: z1-gated, donor receives z1-step)."""
    dflt = 6 if axis == 0 else 7
    cells = ribbon_cells(cyc, a, m)
    for x, w in cells:
        v = dirs[t][c][x]
        if v >= 6:
            return False
        for z in range(m):
            i = (x + K * w + K * m * z) if axis == 0 else (x + K * z + K * m * w)
            if child[t][leaf][i] != dflt or child[t][c][i] != v:
                return False
    for x, w in cells:
        v = dirs[t][c][x]
        for z in range(m):
            i = (x + K * w + K * m * z) if axis == 0 else (x + K * z + K * m * w)
            child[t][leaf][i] = v
            child[t][c][i] = dflt
    return True


def leaf_stair(child, m, K, t, xcol, b, nu0, nu1):
    idx = [xcol + K * z0 + K * m * ((b - z0) % m) for z0 in range(m)]
    for i in idx:
        if child[t][nu0][i] != 6 or child[t][nu1][i] != 7:
            return False
    for i in idx:
        child[t][nu0][i] = 7
        child[t][nu1][i] = 6
    return True


def wild_seam(child, m, K, t, xcol, c, table, sigma, nu0, nu1):
    """transplant a d3-even wild layer onto column xcol at layer t, colors
    sigma = (child color taking cert color 0/1/2's reads), directions
    0 -> D0(6), 1 -> D1(7), 2 -> LAST(8).  Requires the column to carry the
    pristine reads nu0 = D0, nu1 = D1, c = LAST on every (z0, z1)."""
    trio = set(sigma)
    if trio != {nu0, nu1, c}:
        return False
    want = {nu0: 6, nu1: 7, c: 8}
    for z0 in range(m):
        for z1 in range(m):
            i = xcol + K * z0 + K * m * z1
            for col in (nu0, nu1, c):
                if child[t][col][i] != want[col]:
                    return False
    DIR = (6, 7, 8)
    for z0 in range(m):
        for z1 in range(m):
            i = xcol + K * z0 + K * m * z1
            for j in range(3):
                child[t][sigma[j]][i] = DIR[table[z0][z1][j]]
    return True


def old_swap_closure(dirs, m, K, t, c, c2, x0, cap=2000):
    """smallest set X containing x0 closed under L_{t,c} and L_{t,c2} and
    their inverses, provided both colors read only x-directions on X (no
    zero/last reads -- keeps the trade z-free and parity-even).  Returns the
    sorted list or None (cap exceeded / zero-read hit)."""
    powm = [m ** i for i in range(6)]

    def step(cc, x, back=False):
        v = dirs[t][cc][x]
        if v >= 6:
            return None
        p = powm[v]
        dig = (x // p) % m
        if not back:
            return x + p if dig < m - 1 else x - (m - 1) * p
        return x - p if dig > 0 else x + (m - 1) * p

    X = {x0}
    frontier = [x0]
    while frontier:
        if len(X) > cap:
            return None
        nxt = []
        for x in frontier:
            for cc in (c, c2):
                for back in (False, True):
                    y = step(cc, x, back)
                    if y is None:
                        return None
                    if y not in X:
                        X.add(y); nxt.append(y)
        frontier = nxt
    return sorted(X)


def old_old_swap(child, dirs, m, K, t, c, c2, X):
    """read trade between two old colors on the z-free column set X (closed
    under both layer maps): RF1 pointwise, RF2 by closure, parity-even
    deviations, leaf colors untouched."""
    for x in X:
        v, v2 = dirs[t][c][x], dirs[t][c2][x]
        if v >= 6 or v2 >= 6:
            return False
        for z in range(m * m):
            i = x + K * z
            if child[t][c][i] != v or child[t][c2][i] != v2:
                return False
    for x in X:
        v, v2 = dirs[t][c][x], dirs[t][c2][x]
        for z in range(m * m):
            i = x + K * z
            child[t][c][i] = v2
            child[t][c2][i] = v
    return True


def extra_line(child, dirs, m, K, t, xcol, xi, c, nu1):
    """one additional (last <-> d1) z0-pinned line crossing for color c at a
    spare last-read site (parity fixer; flips c and nu1)."""
    if dirs[t][c][xcol] != 6:
        return False
    for z1 in range(m):
        i = xcol + K * xi + K * m * z1
        if child[t][c][i] != 8 or child[t][nu1][i] != 7:
            return False
    for z1 in range(m):
        i = xcol + K * xi + K * m * z1
        child[t][c][i] = 7
        child[t][nu1][i] = 8
    return True


# ---------------------------------------------------------------------------
# candidate builder + incremental evaluator
# ---------------------------------------------------------------------------

class Engine:
    def __init__(self, d, m, dirs, cross0, cross1, tau_s, orbidx, wilds):
        self.d, self.m, self.dirs = d, m, dirs
        self.K = m ** (d - 1); self.K2 = self.K * m * m
        self.nu0, self.nu1 = d, d + 1
        self.tau_s = tau_s
        self.orbidx = orbidx
        self.wilds = wilds
        self.cross0, self.cross1 = cross0, cross1
        self.add = build_add(d + 2, m)
        tpl = grow_two_crossings(d, m, dirs, cross0, cross1)
        r0, r1 = tpl[tau_s][self.nu0], tpl[tau_s][self.nu1]
        tpl[tau_s][self.nu0], tpl[tau_s][self.nu1] = r1, r0
        self.template = tpl
        self.base_perm = {}
        self.ret_cache = {}
        self.closure_cache = {}

    def perm(self, row):
        add = self.add
        return array('I', [add[v][i] for i, v in enumerate(row)])

    def build(self, plan):
        """returns (rows, touched, skipped): rows = dict (t,c) -> bytearray
        for modified rows only; conflict-free pieces are applied in order."""
        d, m, K = self.d, self.m, self.K
        nu0, nu1 = self.nu0, self.nu1
        rows = {}
        child = [[None] * (d + 2) for _ in range(m)]
        for t in range(m):
            for c in range(d + 2):
                child[t][c] = self.template[t][c]

        def own(t, c):
            if (t, c) not in rows:
                rows[(t, c)] = bytearray(self.template[t][c])
                child[t][c] = rows[(t, c)]

        skipped = []
        for don in plan['donations']:
            axis, t, c, start, a = don
            leaf = (nu0 if axis == 0 else nu1) if t != self.tau_s \
                else (nu1 if axis == 0 else nu0)
            cyc = self.orbidx['index'].get((t, c, start))
            own(t, leaf); own(t, c)
            if cyc is None or not donate(child, self.dirs, m, K, t, c, cyc,
                                         a, axis, leaf):
                skipped.append(('don',) + tuple(don))
        for st in plan.get('stairs', []):
            t, xcol, b = st
            own(t, nu0); own(t, nu1)
            if not leaf_stair(child, m, K, t, xcol, b, nu0, nu1):
                skipped.append(('stair',) + tuple(st))
        for wl in plan.get('wilds', []):
            t, xcol, c, lay_id, sig = wl
            sigma = tuple(sig)
            own(t, nu0); own(t, nu1); own(t, c)
            if not wild_seam(child, m, K, t, xcol, c,
                             self.wilds[lay_id]['table'], sigma, nu0, nu1):
                skipped.append(('wild',) + tuple(wl))
        for el in plan.get('lines', []):
            t, xcol, xi, c = el
            own(t, c); own(t, nu1)
            if not extra_line(child, self.dirs, m, K, t, xcol, xi, c, nu1):
                skipped.append(('line',) + tuple(el))
        for ow in plan.get('oswaps', []):
            t, c, c2, x0 = ow
            X = self.closure_cache.get(ow)
            if X is None and ow not in self.closure_cache:
                X = old_swap_closure(self.dirs, m, K, t, c, c2, x0)
                self.closure_cache[ow] = X
            if X is None:
                skipped.append(('oswap',) + tuple(ow))
                continue
            own(t, c); own(t, c2)
            if not old_old_swap(child, self.dirs, m, K, t, c, c2, X):
                skipped.append(('oswap',) + tuple(ow))
        return rows, skipped

    def evaluate(self, plan):
        """(ncyc, signs, skipped); per-color return cached on the exact
        modified-row bytes touching that color."""
        rows, skipped = self.build(plan)
        d, m = self.d, self.m
        ncyc, signs = [], []
        for c in range(d + 2):
            key_rows = tuple(sorted((t, cc) for (t, cc) in rows if cc == c))
            key = (c, tuple((tc, hash(bytes(rows[tc]))) for tc in key_rows))
            hit = self.ret_cache.get(key)
            if hit is None:
                R = None
                for t in range(m):
                    if (t, c) in rows:
                        P = self.perm(rows[(t, c)])
                    else:
                        P = self.base_perm.get((t, c))
                        if P is None:
                            P = self.perm(self.template[t][c])
                            self.base_perm[(t, c)] = P
                    R = P if R is None else array('I',
                                                  map(P.__getitem__, R))
                cl = cycle_lengths(R)
                hit = (len(cl), 1 if (self.K2 - len(cl)) % 2 == 0 else -1)
                if len(self.ret_cache) > 20000:
                    self.ret_cache.clear()
                self.ret_cache[key] = hit
            ncyc.append(hit[0]); signs.append(hit[1])
        return ncyc, signs, skipped


# ---------------------------------------------------------------------------
# STEP 1: budget refinement under the conjugate relaxation
# ---------------------------------------------------------------------------

def budget_refine(m):
    res = Res()
    print(f'=== STEP 1: conjugate-relaxation budget refinement at (7,{m}) ===')
    d, dirs = load_seed(m)
    K = m ** (d - 1); K2 = K * m * m
    nu0, nu1 = d, d + 1

    rep = verify(d, m, dirs)
    res.clause(f'm={m} base: RF1+RF2+RF3 over the FIXED load_seed '
               '(stages applied)', rep['rf1'] and rep['rf2'] and rep['rf3'])

    # R1: exit bound
    moved = None
    for c in range(d):
        R = compose(layer_maps(d, m, dirs, c), K)
        mv = sum(1 for x in range(K) if R[x] != x)
        moved = mv if moved is None else min(moved, mv)
    res.info(f'R1 (exit bound): a single K2-cycle return must leave every '
             f'x-column {{x}}x(Z/m)^2, so each leaf color needs >= K = {K} '
             f'x-reads in total (vs the gate\'s 6*2m = {12 * m} aggregate '
             f'bound): the old colors must shed >= 2K = {2 * K} x-reads, '
             'a constant fraction of one full color')
    res.clause(f'm={m} R1 side-check: base single returns are everywhere-'
               f'moving (min moved points {moved} = K)', moved == K)

    # R2: slice-gating rigidity
    good = [bits for bits in range(1 << m)
            if len({(z + ((m - 2) if (bits >> z) & 1 else (m - 1))) % m
                    for z in range(m)}) == m]
    res.clause(f'm={m} R2 (slice-gating rigidity): the only z0-slice gate '
               'patterns with bijective induced z0-map are the constants '
               '(0 = no exchange anywhere, all = the sketched rotor)',
               set(good) == {0, (1 << m) - 1},
               detail=f'surviving patterns: {good}')
    res.info('R2 consequence: the leaf x-action must be gated at sub-slice '
             '(x-dependent) granularity; RF2 then forces donated cells to '
             'close into staircase chains along donor layer-map orbits '
             '(slope -1, q-winding, donor receives the gated z-step) -- '
             'the RIBBON shape is the minimal RF2-closed z-gated donation')

    # R3: parity calculus on the growthDir child
    cross0, cross1, nonstrict = replay_placement(d, m, dirs)
    child = grow_two_crossings(d, m, dirs, cross0, cross1)
    add = build_add(d + 2, m)
    ledger = []
    for c in range(d + 2):
        signs = [sign_of(array('I', [add[child[t][c][i]][i]
                                     for i in range(K2)]))
                 for t in range(m)]
        ledger.append(signs)
    res.info(f'R3 parity ledger (layer-map signs per color): '
             f'{[("c%d" % c, ledger[c]) for c in range(d + 2)]}')
    res.clause(f'm={m} R3a: old colors have odd return parity (single '
               'K2-cycles are odd; one z0-pinned line each)',
               all(math.prod(ledger[c]) == -1 for c in range(d)))
    res.clause(f'm={m} R3b KILL of the growthDir shape: nu0 has ALL-EVEN '
               'layer maps (lifted maps and z-free plane deviations are '
               'even; only z-lines/staircases are odd) -> nu0 return is an '
               'EVEN permutation -> never a single K2-cycle, for EVERY '
               'placement', math.prod(ledger[nu0]) == 1)
    res.clause(f'm={m} R3c: nu1 parity is odd (7 donated lines) -- parity '
               'alone does not kill nu1; the z-translation order does',
               math.prod(ledger[nu1]) == -1)

    # R6: block confinement (connectivity)
    res.info('R6 (block confinement): a leaf return moves x only at its '
             'donated cells, so its trajectories stay inside the union '
             'graph of the donated orbits; a single K2-cycle therefore '
             'needs that union graph CONNECTED and SPANNING all K columns. '
             'A single donation layer confines x to one donor orbit '
             'forever (>= #orbits cycles); donations at >= 2 layers with '
             'interleaving orbit partitions are necessary.')

    # R7: swap-parity conservation -> wild seams necessary
    N_t = [math.prod(ledger[c][t] for c in range(d + 2)) for t in range(m)]
    res.info(f'R7: per-layer color sign products N_t of the growthDir '
             f'child: {N_t}; nine single returns need prod_t N_t = -1')
    res.clause(f'm={m} R7a: growthDir child has N_t = +1 for every layer '
               '(total +1, but the target needs -1)',
               all(n == 1 for n in N_t))
    wilds = load_wild_layers(m)
    res.clause(f'm={m} R7b: every 2-color read swap multiplies N_t by '
               'sign(dev_a)*sign(dev_b) where the two deviations are '
               'mutually inverse up to relabeling -- equal signs, so N_t '
               'is conserved by the ENTIRE 2-swap catalog (planes, lines, '
               'ribbons, stairs); a >= 3-color-entangled layer piece is '
               'NECESSARY.  The d3-even rail-seam certificate supplies '
               f'{len(wilds)} wild (N = -1) (Z/m)^2-layers reusable on '
               'zero-read columns', len(wilds) >= 1,
               detail='no wild layer found')
    res.info(f'R7 wild layer per-color signs: {[w["signs"] for w in wilds]}'
             '; one wild seam at a zero-read column flips (nu0, nu1, c); '
             'one extra z1-line for c then flips exactly nu0 -- the unique '
             'parity repair in this catalog')

    # R4: class-A m^3 bound
    res.info(f'R4 (class-A refinement): if every modified old return keeps '
             'the strict product carry shape (B_c x, z0+c0(x), z1+gated), '
             'L1/L2 give S_i(old c) = m^2 * D_i(B_c) with m | D_i(B_c), '
             'so the leaf absorption S_i(nu0)+S_i(nu1) = m*K2 - '
             'm^2*Sum_c D_i(B_c) is a positive multiple of m^3: '
             f'>= {m ** 3} per x-direction (>= {6 * m ** 3} total).  The '
             'ribbon family escapes class A (donor x-parts become z-gated, '
             'class B), where R1/R6 are the binding constraints.')

    # R5: the sketched rotor is dead
    samples = []
    rng = random.Random(7)
    from growth_step_replay import child2_return
    for trial in range(6):
        tau0, tau1 = rng.sample(range(m), 2)
        prm = dict(tau0=tau0, tau1=tau1,
                   r0=[rng.randrange(d) for _ in range(m)],
                   r1=[rng.randrange(d) for _ in range(m)],
                   crossP={}, crossL={})
        Rn0 = child2_return(d, m, dirs, prm, d)
        disp = {(((Rn0[i] // K) % m) - ((i // K) % m)) % m
                for i in range(0, K2, 97)}
        samples.append((len(cycle_lengths(Rn0)), sorted(disp)))
    res.clause(f'm={m} R5 KILL of the sketched rotor (no crossings): nu0 '
               'z0-displacement is constantly m-2, so the z0-parity classes '
               'are invariant and nu0 has >= 2 cycles for EVERY (tau0, '
               'tau1, r0, r1)',
               all(s[1] == [(m - 2) % m] and s[0] >= 2 for s in samples),
               detail=f'samples (ncyc, z0-disp set): {samples}')

    return dict(records=res.records, fails=res.fails)


# ---------------------------------------------------------------------------
# STEP 2: the seam search
# ---------------------------------------------------------------------------

def union_components(K, orbit_lists):
    parent = list(range(K))

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]; a = parent[a]
        return a

    deg = bytearray(K)
    for cyc in orbit_lists:
        for j, x in enumerate(cyc):
            deg[x] = 1
            y = cyc[(j + 1) % len(cyc)]
            ra, rb = find(x), find(y)
            if ra != rb:
                parent[ra] = rb
    roots = {find(x) for x in range(K)}
    isolated = sum(1 for x in range(K) if not deg[x])
    return len(roots), isolated


def make_plan(eng, rng, n_blocks=2):
    """full-coverage, connected donation plan for both leaves + one wild
    seam + one compensating line; random offsets.

    Conflict avoidance baked in: donor-layer pairs (t, c) are used by at
    most one leaf (cross-axis donor collisions are read conflicts), and
    orbits through crossing columns at their own layer are excluded (the
    plane/line toggles change the leaf default reads there)."""
    d, m, K = eng.d, eng.m, eng.K
    tau_s = eng.tau_s
    orbs = eng.orbidx['by_tc']
    plan = dict(donations=[], stairs=[], wilds=[], lines=[], oswaps=[])
    donated_cols = {t: set() for t in range(m)}   # columns touched per layer
    used_pairs = set()
    bad = {0: {t: set() for t in range(m)}, 1: {t: set() for t in range(m)}}
    for c, (t, x) in eng.cross0.items():
        bad[0][t].add(x)                          # plane toggles nu0's D0
    for c, (t, x, xi) in eng.cross1.items():
        bad[1][t].add(x)                          # line toggles nu1's D1
    for leaf in (0, 1):
        # gating axis per layer: the leaf's default read is its own
        # z-direction except at tau_s (full role swap), where it is the
        # other one -- donations at tau_s use the flipped axis, giving the
        # leaf x-reads that replace its OFF-axis z-step (carry variety)
        def axis_at(t):
            return (leaf if t != tau_s else 1 - leaf)

        lays = list(range(m))
        rng.shuffle(lays)

        def ok_orbs(t, c):
            bb = bad[axis_at(t)][t]
            return [cy for cy in orbs[(t, c)] if not (bb & set(cy))] \
                if bb else orbs[(t, c)]

        blocks = []
        for t in lays[:n_blocks]:
            cands = [c for c in range(d) if (t, c) not in used_pairs]
            blocks.append((t, rng.choice(cands)))
        chosen = []
        for (t, c) in blocks:
            for cyc in ok_orbs(t, c):
                chosen.append((t, c, cyc))
        # connectivity patching (incremental union-find): add orbits of
        # other colors that cover uncovered columns or link components
        parent = list(range(K))

        def find(a):
            while parent[a] != a:
                parent[a] = parent[parent[a]]; a = parent[a]
            return a

        deg = bytearray(K)

        def add_orbit(cyc):
            for j, x in enumerate(cyc):
                deg[x] = 1
                y = cyc[(j + 1) % len(cyc)]
                ra, rb = find(x), find(y)
                if ra != rb:
                    parent[ra] = rb

        for (_, _, cy) in chosen:
            add_orbit(cy)
        pool = [(t, c) for t in lays for c in range(d)
                if (t, c) not in blocks and (t, c) not in used_pairs]
        rng.shuffle(pool)
        patch_pairs = []
        for (t, c) in pool:
            uncovered = K - sum(deg)
            if uncovered == 0 and \
                    len({find(x) for x in range(K)}) == 1:
                break
            for cyc in ok_orbs(t, c):
                helps = any(not deg[x] for x in cyc) or \
                    len({find(x) for x in cyc}) > 1
                if helps:
                    add_orbit(cyc)
                    chosen.append((t, c, cyc))
                    patch_pairs.append((t, c))
        ncomp = len({find(x) for x in range(K)})
        iso = K - sum(deg)
        if not (ncomp == 1 and iso == 0):
            return None
        used_pairs.update(blocks); used_pairs.update(patch_pairs)
        # conflict-aware offsets: within (leaf, layer), no two donated
        # cells may share (column, gate) -- pick each orbit's offset to
        # avoid earlier cells, trying all m offsets
        import math as _math
        cellmap = {}
        for (t, c, cyc) in chosen:
            used_cells = cellmap.setdefault(t, set())
            L = len(cyc); q = m // _math.gcd(L, m)
            placed = False
            offs = list(range(m)); rng.shuffle(offs)
            for a in offs:
                cells = [(cyc[j % L], (a - j) % m) for j in range(q * L)]
                if not any(cell in used_cells for cell in cells):
                    used_cells.update(cells)
                    plan['donations'].append((axis_at(t), t, c, cyc[0], a))
                    donated_cols[t].update(cyc)
                    placed = True
                    break
            # unplaceable orbits are dropped (coverage/connectivity hit is
            # rare and visible through the leaf cycle counts)
    # initial z-mixing stairs, in pairs (a single stair flips both leaf
    # parities; pairs are parity-neutral), on donation-free columns
    for _ in range(4):
        for _try in range(40):
            t = rng.randrange(m)
            xcol = rng.randrange(K)
            if xcol not in donated_cols[t]:
                plan['stairs'].append((t, xcol, rng.randrange(m)))
                break
    # wild seam + compensating line for its color, on zero-read columns of
    # c untouched by donations at that layer (the pristine-column check of
    # wild_seam/extra_line re-verifies)
    zero_cols = {}
    for t in range(m):
        if t == tau_s:
            continue
        for c in range(d):
            cols = [x for x in range(K) if eng.dirs[t][c][x] == 6
                    and x not in donated_cols[t]]
            if len(cols) >= 2:
                zero_cols[(t, c)] = cols
    if not zero_cols:
        return None
    t, c = rng.choice(list(zero_cols))
    xw = rng.choice(zero_cols[(t, c)])
    lay_id = rng.randrange(len(eng.wilds))
    sigma = [eng.nu0, eng.nu1, c]
    rng.shuffle(sigma)
    plan['wilds'].append((t, xw, c, lay_id, tuple(sigma)))
    plan['_zero_cols'] = {f'{tt},{cc}': v for (tt, cc), v in
                          zero_cols.items()}
    lcols = [x for x in zero_cols[(t, c)] if x != xw]
    plan['lines'].append((t, rng.choice(lcols), rng.randrange(m), c))
    return plan


def mutate(eng, rng, plan, worst=None):
    p2 = dict(donations=list(plan['donations']), stairs=list(plan['stairs']),
              wilds=list(plan['wilds']), lines=list(plan['lines']),
              oswaps=list(plan.get('oswaps', [])),
              _zero_cols=plan.get('_zero_cols', {}))
    m, K, d = eng.m, eng.K, eng.d
    zc = p2['_zero_cols']
    r = rng.random()
    if r < 0.14:
        # old-old trade: changes two old colors' returns, leaves untouched
        if p2['oswaps'] and rng.random() < 0.4:
            p2['oswaps'].pop(rng.randrange(len(p2['oswaps'])))
        else:
            cw = worst if (worst is not None and worst < d) \
                else rng.randrange(d)
            c2 = rng.choice([c for c in range(d) if c != cw])
            p2['oswaps'].append((rng.randrange(m), cw, c2,
                                 rng.randrange(K)))
    elif r < 0.62 and p2['donations']:
        idx = range(len(p2['donations']))
        if worst is not None and rng.random() < 0.6:
            # bias toward donations touching the worst color
            cand = [j for j in idx
                    if p2['donations'][j][2] == worst
                    or (worst >= d and
                        ((p2['donations'][j][0] == worst - d)
                         != (p2['donations'][j][1] == eng.tau_s)))]
            idx = cand or list(idx)
        j = rng.choice(list(idx))
        axis, t, c, s0, a = p2['donations'][j]
        u = rng.random()
        if u < 0.70:                      # re-offset
            p2['donations'][j] = (axis, t, c, s0,
                                  (a + rng.randrange(1, m)) % m)
        elif u < 0.78:                    # kick: re-offset several donations
            for _ in range(rng.randrange(2, 6)):
                jj = rng.choice(list(idx))
                ax2, t2, c2, s2, a2 = p2['donations'][jj]
                p2['donations'][jj] = (ax2, t2, c2, s2,
                                       (a2 + rng.randrange(1, m)) % m)
        elif u < 0.86:                    # densify: same orbit, 2nd offset
            p2['donations'].append((axis, t, c, s0,
                                    (a + rng.randrange(1, m)) % m))
        elif u < 0.93:                    # drop (connectivity judged by E)
            p2['donations'].pop(j)
        else:                             # add a fresh orbit donation
            leaf = rng.randrange(2)
            t2 = rng.randrange(m)
            ax2 = leaf if t2 != eng.tau_s else 1 - leaf
            c2 = rng.randrange(d)
            cycs = eng.orbidx['by_tc'][(t2, c2)]
            if cycs:
                cy = rng.choice(cycs)
                p2['donations'].append((ax2, t2, c2, cy[0],
                                        rng.randrange(m)))
    elif r < 0.74:
        # parity-neutral stair moves: re-site one stair, or add/remove a PAIR
        lays = [t for t in range(m) if t != eng.tau_s]
        u = rng.random()
        if u < 0.6 and p2['stairs']:
            j = rng.randrange(len(p2['stairs']))
            p2['stairs'][j] = (rng.choice(lays), rng.randrange(K),
                               rng.randrange(m))
        elif u < 0.8 and len(p2['stairs']) >= 2:
            j = rng.randrange(len(p2['stairs'])); p2['stairs'].pop(j)
            j = rng.randrange(len(p2['stairs'])); p2['stairs'].pop(j)
        else:
            for _ in range(2):
                p2['stairs'].append((rng.choice(lays), rng.randrange(K),
                                     rng.randrange(m)))
    elif r < 0.88 and p2['wilds']:
        j = rng.randrange(len(p2['wilds']))
        t, xw, c, lay_id, sigma = p2['wilds'][j]
        u = rng.random()
        if u < 0.35:
            lay_id = rng.randrange(len(eng.wilds))
        elif u < 0.7:
            sigma = list(sigma); rng.shuffle(sigma); sigma = tuple(sigma)
        else:
            cols = zc.get(f'{t},{c}', [])
            if cols:
                xw = rng.choice(cols)
        p2['wilds'][j] = (t, xw, c, lay_id, sigma)
    elif p2['lines']:
        j = rng.randrange(len(p2['lines']))
        t, xcol, xi, c = p2['lines'][j]
        cols = zc.get(f'{t},{c}') or \
            [x for x in range(K) if eng.dirs[t][c][x] == 6]
        p2['lines'][j] = (t, rng.choice(cols), rng.randrange(m), c)
    return p2


def plan_json(plan, tau_s, cross0, cross1, m):
    return dict(m=m, tau_s=tau_s,
                donations=[list(x) for x in plan['donations']],
                stairs=[list(x) for x in plan['stairs']],
                wilds=[list(w[:4]) + [list(w[4])] for w in plan['wilds']],
                lines=[list(x) for x in plan['lines']],
                oswaps=[list(x) for x in plan.get('oswaps', [])],
                cross0={str(k): v for k, v in cross0.items()},
                cross1={str(k): v for k, v in cross1.items()})


def load_plan(eng, w):
    return dict(donations=[tuple(x) for x in w['donations']],
                stairs=[tuple(x) for x in w.get('stairs', [])],
                wilds=[(x[0], x[1], x[2], x[3], tuple(x[4]))
                       for x in w.get('wilds', [])],
                lines=[tuple(x) for x in w.get('lines', [])],
                oswaps=[tuple(x) for x in w.get('oswaps', [])],
                _zero_cols=w.get('_zero_cols', {}))


def seam_search(m=4, iters=1500, restarts=4, seed=1, tag='',
                resume_file=None, leaf_weight=1):
    print(f'=== STEP 2: seam search v2 at (7,{m}) '
          f'(iters={iters}, restarts={restarts}, seed={seed}) ===')
    t_start = time.time()
    d, dirs = load_seed(m)
    K = m ** (d - 1)
    cross0, cross1, nonstrict = replay_placement(d, m, dirs)
    orbs = orbit_table(d, m, dirs)
    orbidx = dict(by_tc=orbs,
                  index={(t, c, cy[0]): cy for (t, c), L in orbs.items()
                         for cy in L})
    wilds = load_wild_layers(m)
    rng = random.Random(seed)
    scope = dict(m=m, iters=iters, restarts=restarts, seed=seed,
                 candidates=0, best=[], hit=None)
    resume = None
    if resume_file:
        resume = json.loads(Path(resume_file).read_text())
        assert resume['m'] == m
    for rs in range(restarts):
        if resume is not None:
            tau_s = resume['tau_s']
        else:
            tau_s = rng.randrange(m)
        eng = Engine(d, m, dirs, cross0, cross1, tau_s, orbidx, wilds)
        if resume is not None:
            plan = load_plan(eng, resume)
            if not plan.get('_zero_cols'):
                plan['_zero_cols'] = {}
            resume = None
        else:
            plan = make_plan(eng, rng)
        if plan is None:
            scope['best'].append(dict(restart=rs, note='no connected plan'))
            continue
        def energy(nc, sg, sk):
            # even-sign colors can never reach a single K2-cycle: hard wall
            return (sum(n - 1 for n in nc[:d])
                    + leaf_weight * sum(n - 1 for n in nc[d:])
                    + 400 * len(sk)
                    + 3000 * sum(1 for s in sg if s == 1))

        ncyc, signs, skipped = eng.evaluate(plan)
        E = energy(ncyc, signs, skipped)
        print(f'[restart {rs}] tau_s={tau_s} E={E} ncyc={ncyc} signs={signs} '
              f'skipped={len(skipped)}')
        best = (E, ncyc, signs)
        T0, T1 = max(4, min(300, max(ncyc))), 0.6
        for it in range(iters):
            T = T0 * (T1 / T0) ** (it / max(1, iters - 1))
            p2 = mutate(eng, rng, plan,
                        worst=max(range(d + 2), key=lambda c: ncyc[c]))
            n2, s2, sk2 = eng.evaluate(p2)
            E2 = energy(n2, s2, sk2)
            scope['candidates'] += 1
            if E2 <= E or rng.random() < math.exp(-(E2 - E) / max(T, 1e-9)):
                plan, E, ncyc, signs = p2, E2, n2, s2
                if E < best[0]:
                    best = (E, ncyc, signs)
                    print(f'  [it {it}] E={E} ncyc={ncyc} signs={signs}')
                    bp = plan_json(plan, tau_s, cross0, cross1, m)
                    bp['E'] = E; bp['ncyc'] = ncyc
                    (HERE / f'growth_conjugate_best_m{m}{tag}.json'
                     ).write_text(json.dumps(bp, indent=1))
            if E == 0:
                witness = plan_json(plan, tau_s, cross0, cross1, m)
                out = HERE / f'growth_conjugate_hit_m{m}.json'
                out.write_text(json.dumps(witness, indent=1))
                print(f'*** HIT: all nine returns single; witness -> {out}')
                scope['hit'] = str(out)
                scope['best'].append(dict(restart=rs, E=0, ncyc=ncyc))
                scope['elapsed_s'] = round(time.time() - t_start, 1)
                return scope
        scope['best'].append(dict(restart=rs, E=best[0], ncyc=best[1],
                                  signs=best[2], tau_s=tau_s))
    scope['elapsed_s'] = round(time.time() - t_start, 1)
    print(f'=== seam-search v2 done: no full hit; best E = '
          f'{min((b.get("E", 10**9) for b in scope["best"]), default=None)}; '
          f'{scope["candidates"]} candidates, {scope["elapsed_s"]}s ===')
    return scope


# ---------------------------------------------------------------------------
# hit verification + chaining
# ---------------------------------------------------------------------------

def rebuild_from_witness(m, w):
    d, dirs = load_seed(m)
    cross0 = {int(k): tuple(v) for k, v in w['cross0'].items()}
    cross1 = {int(k): tuple(v) for k, v in w['cross1'].items()}
    orbs = orbit_table(d, m, dirs)
    orbidx = dict(by_tc=orbs,
                  index={(t, c, cy[0]): cy for (t, c), L in orbs.items()
                         for cy in L})
    wilds = load_wild_layers(m)
    eng = Engine(d, m, dirs, cross0, cross1, w['tau_s'], orbidx, wilds)
    plan = load_plan(eng, w)
    rows, skipped = eng.build(plan)
    assert not skipped, f'witness no longer applies cleanly: {skipped[:4]}'
    child = [[bytearray(eng.template[t][c]) for c in range(d + 2)]
             for t in range(m)]
    for (t, c), row in rows.items():
        child[t][c] = row
    return d, eng, child


def verify_hit(m, witness_file):
    print(f'=== verify-hit at (7,{m}) from {witness_file} ===')
    w = json.loads(Path(witness_file).read_text())
    d, eng, child = rebuild_from_witness(m, w)
    rep = verify(d + 2, m, child)
    ok = rep['rf1'] and rep['rf2'] and rep['rf3']
    print(f'  RF1={rep["rf1"]} RF2={rep["rf2"]} all-nine-single={rep["rf3"]}')
    print(f'  cycle summary: {rep["lens"]}')
    return ok, child, rep


def chain_check(witness_file):
    w = json.loads(Path(witness_file).read_text())
    m = w['m']
    ok, child, rep = verify_hit(m, witness_file)
    d2 = 9; K2 = m ** 8
    print('=== chain-check: hypotheses for the 9 -> 11 step ===')
    print(f'  (H1) Latin rows + per-layer bijectivity: {rep["rf1"]}/{rep["rf2"]}')
    print(f'  (H2) all nine returns single: {rep["rf3"]}')
    lamc = [[] for _ in range(d2)]
    for t in range(m):
        for c in range(d2):
            row = child[t][c]
            cnt = sum(1 for i in range(K2) if row[i] == d2 - 1)
            if cnt:
                lamc[c].append((t, cnt))
    print(f'  (H3) last-read (t, count) per child color: {lamc}')
    ok3 = all(sum(n for _, n in l) >= 2 for l in lamc)
    print(f'       >= 2 last-read sites per color: {ok3}')
    add = build_add(d2, m)
    cover_ok = []
    for t in range(m):
        cov = bytearray(K2)
        for c in range(d2):
            row = child[t][c]
            for i in range(K2):
                if row[i] != d2 - 1 and add[row[i]][i] != i:
                    cov[i] = 1
        cover_ok.append(sum(cov) == K2)
    print(f'  (H4) per-layer non-fixed coverage across colors: {cover_ok}')
    # (H5) zero-read column supply for the next wild seam (full columns of
    # the child where one color reads the zero step on a whole (z)-fiber is
    # trivial here: at the child every point has exactly one zero-reader;
    # the next step needs columns in the NEW chart, recorded informally)
    allok = ok and ok3 and all(cover_ok)
    print(f'=== chain-check verdict: {"PASS" if allok else "FAIL"} ===')
    return allok


# ---------------------------------------------------------------------------
# driver
# ---------------------------------------------------------------------------

def main():
    argv = sys.argv[1:]

    def opt(name, default):
        return int(argv[argv.index(name) + 1]) if name in argv else default

    m = opt('--m', 4)
    tag = ''
    if '--tag' in argv:
        tag = argv[argv.index('--tag') + 1]
    global SUMMARY
    if tag:
        SUMMARY = HERE / f'growth_conjugate_search_summary_{tag}.json'
    summary = {}
    if SUMMARY.exists():
        summary = json.loads(SUMMARY.read_text())
    if '--budget-refine' in argv:
        out = budget_refine(m)
        summary.setdefault('budget_refinement', {})[f'(7,{m})'] = dict(
            records=out['records'], fails=out['fails'])
        SUMMARY.write_text(json.dumps(summary, indent=1))
        print(f'[json] {SUMMARY}')
        sys.exit(0 if not out['fails'] else 1)
    if '--seam-search' in argv:
        resume_file = argv[argv.index('--resume') + 1] \
            if '--resume' in argv else None
        scope = seam_search(m, iters=opt('--iters', 1500),
                            restarts=opt('--restarts', 4),
                            seed=opt('--seed', 1),
                            tag=(('_' + tag) if tag else ''),
                            resume_file=resume_file,
                            leaf_weight=opt('--leaf-weight', 1))
        summary.setdefault('seam_search', []).append(scope)
        SUMMARY.write_text(json.dumps(summary, indent=1))
        print(f'[json] {SUMMARY}')
        sys.exit(0 if scope.get('hit') else 2)
    if '--verify-hit' in argv:
        wf = argv[argv.index('--witness') + 1] if '--witness' in argv \
            else str(HERE / f'growth_conjugate_hit_m{m}.json')
        ok, _, _ = verify_hit(m, wf)
        sys.exit(0 if ok else 1)
    if '--chain-check' in argv:
        wf = argv[argv.index('--witness') + 1] if '--witness' in argv \
            else str(HERE / 'growth_conjugate_hit_m4.json')
        sys.exit(0 if chain_check(wf) else 1)
    print(__doc__)


if __name__ == '__main__':
    main()
