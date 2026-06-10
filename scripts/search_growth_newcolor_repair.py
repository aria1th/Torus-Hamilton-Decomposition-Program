#!/usr/bin/env python3
"""Feasibility gate for the chained 7->9 growth-step REPAIR (the two new-color
returns), in the house tradition of the displacement-budget check.

THE QUESTION (orchestrator, 2026-06-10).  Does a child schedule exist for the
7->9 step at m in {4, 6} (child = 9 colors on (Z/m)^8, m layers, directions
0..5 = x-steps e0..e5, 6 = leaf z0-step, 7 = leaf z1-step, 8 = zero step) with
  (R1)      rows Latin (9 distinct reads at every (t, point)),
  (R2)      every (layer, color) map bijective,
  (R3-old)  the seven old-color returns EQUAL the growthDir returns of
            scripts/growth_step_replay.py (so EvenV11's closed `oldReturns_eq`
            machinery applies verbatim),
  (R3-new)  BOTH leaf-color returns single m^8-cycles?

VERDICT: INFEASIBLE, at both bases, by an exact counting (displacement-budget)
argument -- plan step 1 is decisive; no search is needed and none can help.

THE BUDGET ARGUMENT (machine-checked ingredients marked [num]):

  L1 (count-vector uniqueness; exhaustively verified [num]).  A color's
     return trajectory from a point p consists of m unit steps from
     {e0..e5, e_z0, e_z1, 0}.  Writing n_i for the number of steps in moving
     direction i and r_i(p) = ((R(p) - p)_i mod m) for the displacement
     residues, we have n_i >= 0, n_i == r_i (mod m), sum_i n_i <= m.  Hence
     n_i = r_i for every i -- UNLESS r = 0, which forces R(p) = p.  So for a
     FIXED-POINT-FREE return the per-trajectory step counts are uniquely
     determined by the return alone.

  L2 (read totals are return-invariants).  R2 makes each (t, q) lie on exactly
     one trajectory of each color, so color c's total number of direction-i
     reads equals sum_p n_i(p) = sum_p r_i(p) by L1 -- a function of the
     RETURN only.  R3-old therefore pins every old color's per-direction read
     totals to growthDir's.

  L3 (saturation [num]).  The growthDir old returns act on x by the base
     returns R_c (z-coordinates get unit carries only), so per x-direction i
     the old colors' total i-reads are
        m^2 * D_i,   D_i := sum_{c<7} sum_x ((R_c x - x)_i mod m).
     Numerically D_i = m*K (K = m^6) for EVERY i in 0..5 at BOTH bases
     [num: 16384 = 4*4096 at m=4; 279936 = 6*46656 at m=6].  (This is forced:
     base rows are Latin over 7 directions, so each x-direction is read
     exactly K times per layer, and base returns are single K-cycles, hence
     fixed-point-free, so L1/L2 apply to the base.)

  KILL.  In the child, R1 gives exactly m*K2 read slots per direction
     (K2 = m^8).  Old colors need m^2 * D_i = m^3 * K = m*K2 of the
     direction-i slots -- ALL of them, for every x-direction i.  So under
     R1 + R2 + R3-old the two leaf colors NEVER read an x-direction; their
     layer maps fix all six x-coordinates; both leaf returns preserve every
     fiber {x} x (Z/m)^2 and split into >= K2/m^2 = K cycles (4096 at m=4,
     46656 at m=6).  R3-new demands 1.  INFEASIBLE.

  Scope.  The argument uses only R1 + R2 + fixed-point-freeness of the old
  returns + their displacement field; it covers EVERY placement of growthDir's
  crossings, every z-gated row family, every rerouting of old trajectories
  (reorderings change WHERE old colors read, never HOW OFTEN).  It is uniform
  in d and m: at any chained step d -> d+2 over a base with single-cycle
  (hence fixed-point-free) returns and Latin rows, R3-old-equality saturates
  every x-budget, so the same kill applies to 9->11, 11->13, ... -- the
  repair cannot keep `oldReturns_eq` verbatim at ANY step of the chain.

CHEAPEST RELAXATION (R3-old "conjugate" = old returns single K2-cycles with
the growthDir carry shape, not pointwise equal).  Necessary budget conditions,
derived here and recorded in the JSON:
  * a single K2-cycle visiting all m values of coordinate i needs >= m
    i-transitions, so each leaf color needs >= m direction-i reads: the old
    colors must SHED >= 2m direction-i reads per x-direction i (>= 12m total);
    with R3-old equal the shed is 0.
  * old returns must stay single (odd) K2-cycles: if R''_c differs from the
    growthDir R'_c on exactly k points then (R'_c)^{-1} R''_c is an even
    permutation moving k points, so k >= 3 per modified old color.
  * O3 (recorded) still applies: the leaf-color reads must be z-gated.
The rotor constellation of growth_step_replay.py (z0-gated old-role borrowing
at one layer) is exactly this relaxation shape; its Lean cost is rebuilding
the old-color return proofs (oldReturns_eq no longer verbatim).

FINDING 1 (base-loading discrepancy): growth_step_replay.load_seed ignores
the `stages` field of the seed JSONs.  D7_m4_seed.json has no stages (only
layer overrides), so every recorded m=4 result is unaffected; D7_m6_seed.json
carries 5 stage substitutions, and load_seed's m=6 reconstruction FAILS RF3
(per-color cycle counts 7776/7669/7655/7671 instead of single 46656-cycles).
The m=6 base facts below use the proper reconstruction (mirroring
certificates/scripts/verify_rank7_rootflat_certificates.py, RF1/RF2/RF3 all
PASS).  Recorded m=6 numbers that went through load_seed (the C2 transport
ledger of check_oldgens_span*.py) were computed over the broken base; their
structural conclusions (alphabet confinement, monodromy order bound) are
base-independent, but the m=6 incidence counts should be re-derived.

FINDING 2 (placement unsatisfiable at (7,6)): GrowthPlacement
(EvenV11/V28Hard/GrowthStepCore.lean:388) requires the z1-crossing strictly
before the z0-crossing (`order : (t1 c) < (t0 c)`), both at last-read points
of color c.  Over the PROPER (7,6) base the last-reads of colors 0, 1, 4 are
confined to a SINGLE layer each (color 0: 36 sites all in layer 3; color 1:
46440 sites all in layer 2; color 4: 7776 sites all in layer 0), so no strict
placement exists: the growthDir construction itself cannot be instantiated at
(7,6) over the shipped base.  (Masked until now by Finding 1: the broken
load_seed base has well-spread last-reads.)  The (7,6) budget verdict below
is independent of this -- it kills ANY old-return family whose x-displacement
field is the lifted base (placement-independent) -- but the R3-old-equality
question is additionally VACUOUS at (7,6) as stated.  Numerically the
RELAXED placement (t1 = t0 allowed at two distinct last-read sites of the
same layer) still yields RF1 + RF2 + all seven old returns single
K2-cycles at (7,6) [--child-evidence --m 6], so weakening
GrowthPlacement.order to site-distinctness looks repairable on the old-color
side; the budget kill of course still bars R3-new on top of it.

Stdlib only.  Run:
  python3 scripts/search_growth_newcolor_repair.py --budget-gate
  python3 scripts/search_growth_newcolor_repair.py --child-evidence [--m 4|6]
JSON summary: scripts/growth_repair_gate_summary.json (written by --budget-gate).
"""
from __future__ import annotations
from array import array
from itertools import combinations_with_replacement
import base64, json, sys, zlib
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from growth_step_replay import (build_add, cycle_lengths, last_reads,
                                grow_two_crossings, layer_maps, compose,
                                verify, load_seed)

CERTS = Path('/data/angel/repos/etc/even_modulus_rewrite_20260610'
             '/certificates/certs')
NX = 6                      # x-directions e0..e5 in the child chart


# ---------------------------------------------------------------------------
# proper base reconstruction (mirrors verify_rank7_rootflat_certificates.py:
# constant shifted rows -> stage substitutions on lattice spans -> overrides)
# ---------------------------------------------------------------------------

def dec(x, m, r):
    out = []
    for _ in range(r):
        out.append(x % m); x //= m
    return out


def enc(coords, m):
    p = 1; out = 0
    for a in coords:
        out += (a % m) * p; p *= m
    return out


def span_points(basis, m, r):
    pts = {0}
    for raw in basis:
        vec = [v % m for v in raw]
        new = set()
        for p in pts:
            cur = list(dec(p, m, r))
            for _ in range(m):
                new.add(enc(cur, m))
                cur = [(a + v) % m for a, v in zip(cur, vec)]
        pts = new
    return pts


def proper_base(m):
    """the ACTUAL D7(m) base: d, dirs (load_seed + the seed's `stages`,
    which load_seed ignores -- required for m=6, a no-op for m=4)."""
    data = json.loads((CERTS / f'D7_m{m}_seed.json').read_text())
    d = data['d']; r = d - 1; K = m ** r
    dirs = [[bytearray([(c + s) % d]) * K for c in range(d)]
            for s in data['layer_shifts']]
    for st in data.get('stages', []):
        layer, shift, sig = st['layer'], st['shift'], st['sigma']
        for sup in st.get('supports', []):
            Q = span_points(sup['basis'], m, r)
            for x in Q:
                for c in sup['colors']:
                    dirs[layer][c][x] = (sig[c] + shift) % d
    for ov in data.get('layer_overrides', []):
        t = ov['layer']; colors = ov['colors']
        raw = zlib.decompress(base64.b64decode(ov['data']))
        assert len(raw) == K * len(colors)
        pos = 0
        for x in range(K):
            for c in colors:
                dirs[t][c][x] = raw[pos]; pos += 1
    return d, dirs


# ---------------------------------------------------------------------------
# result collector (house shape)
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


# ---------------------------------------------------------------------------
# L1: exhaustive count-vector uniqueness over all step multisets
# ---------------------------------------------------------------------------

def lemma_unique_counts(res, m):
    """enumerate ALL multisets of m steps over the 9 child letters
    (8 moving directions + zero step); check that the displacement-residue
    vector determines the moving-direction count vector, except residue 0,
    whose preimages are exactly {m zero-steps} + {m steps of one direction}."""
    seen = {}
    for comb in combinations_with_replacement(range(9), m):  # letter 8 = zero
        n = [0] * 9
        for s in comb:
            n[s] += 1
        rvec = tuple(v % m for v in n[:8])
        seen.setdefault(rvec, set()).add(tuple(n[:8]))
    ambig = {r: v for r, v in seen.items() if len(v) > 1}
    zero = (0,) * 8
    want_zero = {tuple(0 for _ in range(8))} | \
        {tuple(m if i == j else 0 for i in range(8)) for j in range(8)}
    ok = set(ambig) == {zero} and seen[zero] == want_zero
    res.info(f'L1 m={m}: {len(seen)} residue classes over '
             f'{sum(len(v) for v in seen.values())} count vectors '
             f'({len(ambig)} ambiguous class(es))')
    res.clause(f'm={m} L1: displacement residues determine trajectory step '
               'counts except at fixed points (residue 0: m zero-steps or '
               'm equal steps -- both mean R(p) = p)', ok,
               detail=f'ambiguous classes: {sorted(ambig)[:4]}')
    return ok


# ---------------------------------------------------------------------------
# base facts + the saturation identity
# ---------------------------------------------------------------------------

def base_gate(res, m):
    d, dirs = proper_base(m)
    K = m ** (d - 1)
    powm = [m ** i for i in range(NX)]
    # RF1 of the base (full)
    rf1 = all(len({dirs[t][c][x] for c in range(d)}) == d
              for t in range(m) for x in range(K))
    res.clause(f'm={m} base: RF1 (rows Latin over the 7 directions)', rf1)
    # base returns: single K-cycles (hence fixed-point-free), saturation
    sat = [0] * NX
    singles, fpf = [], True
    for c in range(d):
        R = compose(layer_maps(d, m, dirs, c), K)
        singles.append(cycle_lengths(R) == [K])
        for x in range(K):
            y = R[x]
            if y == x:
                fpf = False
            for i in range(NX):
                sat[i] += ((y // powm[i]) % m - (x // powm[i]) % m) % m
    res.clause(f'm={m} base: RF3 (all 7 returns single {K}-cycles; proper '
               'reconstruction incl. seed `stages`)', all(singles),
               detail=f'singles={singles}')
    res.clause(f'm={m} base: returns fixed-point-free (L1 applies)', fpf)
    res.info(f'm={m} base: displacement totals D_i = '
             f'sum_c sum_x ((R_c x - x)_i mod m) = {sat}; m*K = {m * K}')
    res.clause(f'm={m} base: SATURATION D_i = m*K for every x-direction i '
               '(forced by L1 + Latin rows + fixed-point-freeness)',
               all(D == m * K for D in sat),
               detail=f'D={sat} vs m*K={m * K}')
    # load_seed cross-check (the recorded-results finding)
    d2, dirs2 = load_seed(m)
    same = all(bytes(dirs[t][c]) == bytes(dirs2[t][c])
               for t in range(m) for c in range(d))
    res.info(f'm={m} base: load_seed reconstruction '
             f'{"matches" if same else "DIFFERS from"} the proper one '
             f'{"(no stages in this seed)" if same else "(seed stages ignored by load_seed: recorded m=6 ledgers used a broken base)"}')
    # GrowthPlacement satisfiability (strict order t1 < t0 at last-reads)
    lam = last_reads(d, m, dirs)
    lam_layers = [sorted({t for (t, _x) in lam[c]}) for c in range(d)]
    stuck = [c for c in range(d) if len(lam_layers[c]) < 2]
    res.info(f'm={m} base: last-read layers per color: '
             f'{ {c: lam_layers[c] for c in range(d)} }')
    res.info(f'm={m} base: GrowthPlacement strict order (t1 < t0) '
             + ('satisfiable for every color'
                if not stuck else
                f'UNSATISFIABLE for colors {stuck} (single-layer last-reads):'
                ' growthDir cannot be instantiated over this base; the '
                'R3-old-equality question is vacuous here, the budget kill '
                'below is placement-independent'))
    return sat, K, d, stuck


def child_budget(res, m, sat, K):
    K2 = K * m * m
    slots = m * K2                      # direction-i read slots in the child
    old_x = [m * m * D for D in sat]    # old colors' pinned i-read totals
    budget = [slots - o for o in old_x]
    res.info(f'm={m} child: K2 = {K2}; per-direction read slots m*K2 = {slots}')
    res.info(f'm={m} child: old-color x-read totals (pinned by R3-old via '
             f'L1/L2) = {old_x}')
    res.clause(f'm={m} child: new-color x-read budget B_i = m*K2 - m^2*D_i '
               'is ZERO for every x-direction -> leaf colors never move x',
               all(b == 0 for b in budget), detail=f'B={budget}')
    # z/zero budgets, for the record (not needed for the kill)
    z0_old, z1_old = 7 * m * m, 7 * m
    res.info(f'm={m} child: z-read totals -- old colors z0: {z0_old} '
             f'(one z0-plane per color, m^2 points), z1: {z1_old} '
             f'(one z0-pinned line per color, m points); leaf colors absorb '
             f'z0: {slots - z0_old}, z1: {slots - z1_old}, zero-step: '
             f'{z0_old + z1_old} of {slots}')
    min_cycles = K2 // (m * m)
    res.clause(f'm={m} child: KILL -- leaf returns preserve every x-fiber '
               f'{{x}} x (Z/m)^2, so each has >= K2/m^2 = {min_cycles} '
               'cycles; R3-new demands 1', False,
               detail=f'INFEASIBLE: {min_cycles} >> 1 (this clause records '
               'the decisive negative; FAIL is the verdict)')
    return dict(K2=K2, slots_per_direction=slots, old_x_reads=old_x,
                new_x_budget=budget, min_leaf_cycles=min_cycles,
                old_z0_reads=z0_old, old_z1_reads=z1_old)


# ---------------------------------------------------------------------------
# freedom count under literally pinned old reads (plan step 1 accounting)
# ---------------------------------------------------------------------------

def freedom_count(res, m):
    """with old reads kept pointwise (the strongest R3-old reading), RF1
    leaves per point one bit: which leaf color takes which leftover direction.
    Per (t, x)-fiber ((Z/m)^2 z-points) RF2 demands both leaf layer maps
    restricted to the fiber be bijections.  Count the legal bit-fields on a
    generic fiber (leftover pair {z0-step, z1-step} everywhere)."""
    if m != 4:
        res.info(f'm={m}: generic-fiber freedom enumeration skipped '
                 f'(2^(m^2) too large); the m=4 count plus the fiber bound '
                 'covers the argument at every m')
        return None
    good = 0
    msq = m * m
    for bits in range(1 << msq):
        ok = True
        for col in (0, 1):
            seen = bytearray(msq)
            for z0 in range(m):
                for z1 in range(m):
                    s = (bits >> (z0 + m * z1)) & 1
                    if col == 1:
                        s ^= 1
                    zz0, zz1 = (z0 + 1 - s) % m, (z1 + s) % m
                    seen[zz0 + m * zz1] += 1
            if any(v != 1 for v in seen):
                ok = False
                break
        if ok:
            good += 1
    res.info(f'm={m}: generic-fiber freedom = {good} legal leaf-bit fields '
             f'of 2^{msq} = {1 << msq} per (t, x)-fiber; every choice keeps '
             f'the leaf returns inside the {msq}-point fiber (max cycle '
             f'{msq} << K2) -- the freedom is real but useless for R3-new')
    return good


# ---------------------------------------------------------------------------
# relaxation analysis (the contingency branch of plan step 1)
# ---------------------------------------------------------------------------

def relaxation(res, m, K):
    K2 = K * m * m
    shed_per_dir = 2 * m
    res.info(f'm={m} relaxation (R3-old conjugate, i.e. old returns single '
             f'{K2}-cycles with growthDir carry shape but not pointwise '
             'equal): NECESSARY budget conditions --')
    res.info(f'  (a) each leaf color needs >= m direction-i transitions per '
             f'x-direction i (a single cycle visits all {m} values of '
             f'coordinate i across >= {m} constant blocks), so the old '
             f'colors must shed >= 2m = {shed_per_dir} i-reads per '
             f'direction, >= 12m = {12 * m} in total; R3-old-equal sheds 0')
    res.info('  (b) parity: a modified old return R\'\' with R\'\' single '
             'differs from the growthDir return by an EVEN permutation, so '
             'every modified old color changes on >= 3 points')
    res.info('  (c) O3 (recorded machine fact) still applies: leaf reads '
             'must be z-gated, else (z0,z1)-monodromy order <= m gives >= m '
             'cycles per leaf color')
    res.info('  (d) the rotor constellation in growth_step_replay.py is the '
             'minimal known shape satisfying (a)-(c); its Lean cost is '
             'rebuilding the old-color return proofs (oldReturns_eq is not '
             'reusable verbatim at ANY chained step, by the same saturation '
             'argument at d -> d+2)')
    return dict(min_shed_per_x_direction=shed_per_dir,
                min_shed_total=12 * m,
                min_changed_points_per_modified_old_color=3)


# ---------------------------------------------------------------------------
# direct child evidence: build growthDir over the PROPER base and verify the
# budget facts on the actual schedule (cross-check, not part of the proof)
# ---------------------------------------------------------------------------

def child_evidence(m):
    print(f'=== child evidence at (7,{m}): growthDir over the proper base ===')
    d, dirs = proper_base(m)
    K = m ** (d - 1); K2 = K * m * m
    lam = last_reads(d, m, dirs)
    print(f'  [info] last-read counts per color: {[len(l) for l in lam]}')
    # the replay's deterministic placement (selector avoidance only at m=4
    # where the HED74 witness lives; GrowthPlacement.order wants t1 < t0
    # strictly -- when a color's last-reads sit in a single layer (the (7,6)
    # base, Finding 2) fall back to two distinct sites in that layer and
    # record the placement as non-strict: the budget facts checked here are
    # placement-independent, only the old-return decomposition shape needs
    # the strict order)
    used = set()
    cross0, cross1 = {}, {}
    nonstrict = []
    for c in range(d):
        pick1 = pick0 = None
        for (t, x) in lam[c]:
            if (t, x) in used:
                continue
            if pick1 is None and t < m - 1:
                pick1 = (t, x); used.add((t, x)); continue
            if pick0 is None and pick1 is not None and t > pick1[0]:
                pick0 = (t, x); used.add((t, x)); break
        if not (pick0 and pick1):           # relaxed same-layer fallback
            free = [(t, x) for (t, x) in lam[c] if (t, x) not in used]
            assert len(free) >= 2, f'fewer than two free last-reads, color {c}'
            pick1, pick0 = free[0], free[1]
            used.update((pick1, pick0))
            nonstrict.append(c)
        cross0[c] = pick0
        cross1[c] = (pick1[0], pick1[1], 0)
    if nonstrict:
        print(f'  [info] strict t1 < t0 placement impossible for colors '
              f'{nonstrict}: same-layer fallback used (Finding 2); old '
              'returns below are informational, not the Lean growthDir shape')
    child = grow_two_crossings(d, m, dirs, cross0, cross1)
    rep = verify(d + 2, m, child)
    ok = rep['rf1'] and rep['rf2']
    print(f'  [{"PASS" if ok else "FAIL"}] child RF1={rep["rf1"]} '
          f'RF2={rep["rf2"]}')
    old_single = all(cycle_lengths(rep['returns'][c]) == [K2]
                     for c in range(d))
    if nonstrict:
        print(f'  [info] old child returns single {K2}-cycles under the '
              f'RELAXED placement: {old_single} (informational only)')
    else:
        print(f'  [{"PASS" if old_single else "FAIL"}] all 7 old child '
              f'returns single {K2}-cycles (R3-old target is '
              'fixed-point-free)')
    # new-color read alphabets + per-direction read totals of all colors
    totals = [[0] * (d + 2) for _ in range(d + 2)]   # totals[dir][color]
    for t in range(m):
        for c in range(d + 2):
            col = child[t][c]
            for i in range(K2):
                totals[col[i]][c] += 1
    leaf_alpha = sorted({i for i in range(d + 2)
                         if totals[i][d] or totals[i][d + 1]})
    print(f'  [{"PASS" if leaf_alpha == [6, 7, 8] else "FAIL"}] leaf colors '
          f'read only {{6,7,8}}: alphabet {leaf_alpha}')
    sat_ok = all(sum(totals[i][c] for c in range(d)) == m * K2
                 for i in range(NX))
    print(f'  [{"PASS" if sat_ok else "FAIL"}] old colors saturate every '
          f'x-direction budget: totals '
          f'{[sum(totals[i][c] for c in range(d)) for i in range(NX)]} '
          f'(slots {m * K2})')
    zero8 = totals[d + 1][d] + totals[d + 1][d + 1]
    print(f'  [info] leaf-color zero-step reads: {zero8} '
          f'(= 7*(m^2+m) = {7 * (m * m + m)} from the 7 plane + 7 line sites)')
    leaf_lens = [cycle_lengths(rep['returns'][d])[:2],
                 cycle_lengths(rep['returns'][d + 1])[:2]]
    ncyc = [len(cycle_lengths(rep['returns'][d])),
            len(cycle_lengths(rep['returns'][d + 1]))]
    print(f'  [info] leaf return cycle types (expected non-single): '
          f'{leaf_lens[0]}... x{ncyc[0]} / {leaf_lens[1]}... x{ncyc[1]}')
    allok = ok and leaf_alpha == [6, 7, 8] and sat_ok and \
        (old_single or bool(nonstrict))
    print(f'=== child evidence verdict at (7,{m}): '
          f'{"PASS" if allok else "FAIL"} ===')
    return dict(m=m, rf1=rep['rf1'], rf2=rep['rf2'], old_single=old_single,
                placement_strict=not nonstrict,
                nonstrict_colors=nonstrict,
                leaf_alphabet=leaf_alpha, saturation=sat_ok,
                leaf_cycle_counts=ncyc, ok=allok)


# ---------------------------------------------------------------------------
# driver
# ---------------------------------------------------------------------------

def budget_gate():
    res = Res()
    summary = dict(
        question='child schedule for chained 7->9 with R1+R2+R3-old(EQUAL '
                 'growthDir returns)+R3-new(both leaf returns single m^8 '
                 'cycles)?',
        verdict='INFEASIBLE',
        argument='displacement-budget saturation: L1 count-vector uniqueness '
                 '(fixed-point-free returns determine per-direction read '
                 'totals) + L2 (totals are return invariants) + L3 (base '
                 'Latin rows saturate every x-direction: D_i = m*K) => new '
                 'colors get x-read budget 0, leaf returns preserve x-fibers,'
                 ' >= m^6 cycles each; uniform in d and m, kills every '
                 'chained step under R3-old equality',
        bases={})
    print('=== budget/parity gate for the 7->9 new-color repair ===')
    for m in (4, 6):
        print(f'--- L1 (count-vector uniqueness) at m={m} ---')
        lemma_unique_counts(res, m)
        print(f'--- base facts + saturation at (7,{m}) ---')
        sat, K, d, stuck = base_gate(res, m)
        print(f'--- child budget at (7,{m}) ---')
        b = child_budget(res, m, sat, K)
        print(f'--- pinned-read freedom accounting at (7,{m}) ---')
        fr = freedom_count(res, m)
        print(f'--- relaxation (R3-old conjugate) necessary conditions ---')
        rel = relaxation(res, m, K)
        summary['bases'][f'(7,{m})'] = dict(
            K=K, base_displacement_totals_Di=sat, m_times_K=m * K,
            saturated=all(D == m * K for D in sat),
            growth_placement_strict_unsatisfiable_colors=stuck,
            child=b, generic_fiber_freedom=fr, relaxation_necessary=rel)
    # expected fails: exactly the two KILL clauses (the recorded verdict)
    kill = [f for f in res.fails if 'KILL' in f]
    other = [f for f in res.fails if 'KILL' not in f]
    ok = not other and len(kill) == 2
    print()
    print(f'=== budget-gate verdict: INFEASIBLE under R3-old EQUALITY at both '
          f'bases ({len(kill)} kill clause(s), {len(other)} unexpected '
          f'failure(s)) ===')
    summary['records'] = res.records
    summary['unexpected_failures'] = other
    summary['child_evidence'] = (
        'direct cross-checks: scripts/growth_repair_child_evidence_m{4,6}'
        '.json (m=4: strict placement, all clauses PASS incl. old returns '
        'single; m=6: strict GrowthPlacement.order unsatisfiable for colors '
        '[0,1,4], same-layer fallback still gives RF1+RF2+old returns '
        'single 1679616-cycles, leaf alphabet {6,7,8}, saturation exact)')
    summary['finding_growth_placement_7_6'] = (
        'GrowthPlacement.order (t1 < t0 strict, GrowthStepCore.lean:407) is '
        'unsatisfiable over the proper (7,6) base: colors 0/1/4 have '
        'last-reads in a single layer (3/2/0).  Relaxing order to pairwise '
        'site-distinctness is numerically sufficient for the old-color side')
    summary['finding_load_seed'] = (
        'growth_step_replay.load_seed ignores seed `stages`; D7_m6_seed '
        'reconstructed through it fails RF3 (cycle counts 7776/7669/7655/'
        '7671 per color) -- recorded m=6 ledgers in check_oldgens_span*.py '
        'used that broken base; this gate uses the proper reconstruction '
        '(RF1/RF2/RF3 PASS)')
    out = HERE / 'growth_repair_gate_summary.json'
    out.write_text(json.dumps(summary, indent=1))
    print(f'[json] {out}')
    return ok


def main():
    argv = sys.argv[1:]
    m = 4
    if '--m' in argv:
        m = int(argv[argv.index('--m') + 1])
    if '--child-evidence' in argv:
        rep = child_evidence(m)
        out = HERE / f'growth_repair_child_evidence_m{m}.json'
        out.write_text(json.dumps(rep, indent=1))
        print(f'[json] {out}')
        sys.exit(0 if rep['ok'] else 1)
    ok = budget_gate()
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
