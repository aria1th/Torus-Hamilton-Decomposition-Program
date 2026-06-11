#!/usr/bin/env python3
"""Endpoint-reserve semantics verifier for the D9 bundle.

Audit reinforcement task 2 (docs/D9_ADVERSARIAL_AUDIT_20260611.md, item 3):
the shipped bundle verifiers check only that the 12 reserve points are
distinct and plane-separated; the marked comparison cycle C, its protected
neighborhood N(C), the condition Q_R cap N(C) = empty, and the ordered-family
site labels are outside machine verification.  This script closes that gap.

  (a) Reconstruction of C and N(C).  The marked comparison cycle of the D9
      anchor is the terminal carrier's standard-block selector
      (lem:terminal-interlacing for m >= 6 on the marked pair (F_0,F_1);
      lem:small-terminal-marked-parents for m = 4 on (F_1,F_2) with
      C_4 = {(0,3),(3,0),(3,3)}), embedded in the carrier plane
      q_T + <06,01> by the carrier chart.  The protected neighborhood is
      N(C) = C u R_a(C) u R_b(C) u R_a^-1(C) u R_b^-1(C)
      (lem:phase-product-rootflat / product_phase_doubling.tex).  Both the
      direct chart and the alignment-twisted chart (M = [[1,1],[0,1]] from
      verify_d9_terminal_a2_block.py check C2) are exercised; N(C) lies in
      the carrier plane under either convention.

  (b) Q_R cap N(C) = empty.
      m > 9 (symbolic): N(C) is contained in the carrier plane; the
      reserve/terminal separation functional of the certificate is
      independently recomputed (kernel property on all four direction
      vectors, difference value, 0 < |diff| <= 9), an independent separator
      is searched from scratch, and the claim is instantiated by direct
      enumeration at the representative even moduli m = 10, 12.
      m in {4,6,8}: full enumeration in K_{9,m} using the lowmod placement
      certificate (terminal/reserve base points per modulus).

  (c) Ordered endpoint-reserve family (def:endpoint-ready-reserve,
      lem:admissible-singleton-reserve, lem:affine-reserve-plane): the 12
      sites must consistently carry the ordered family
      (U0,U1,U2,U1^c,...,U8^c,U_*) -- 3 terminal-exchange sites, d-1 = 8
      renewal sites, 1 next-reserve site, d+3 = 12 total.  The high-even
      certificate's row-major labeling of the {0,1,2,3} x {0,1,2} grid is
      verified against all defining constraints (distinct coefficient
      pairs, pairwise distinct points for EVERY even m >= 4, points on the
      reserve plane, fixed-fiber form, separation from N(C) and the
      terminal carrier).  Two documented findings are re-checked
      programmatically: the published D5/D7 high-even single-fiber renewal
      layout does not extend to d = 9 on this grid, and the lowmod
      certificate carries no family labels at all (positional labeling is
      verified instead).

  --chain-fields: validates every numeric entry of
      scripts/d9_chain_datum_fields.json (audit reinforcement task 3)
      against the vendor certificates and the G7g midpoint-collision
      machinery (check_hed_clauses.py semantics) recomputed in Z/11.

  --self-test: negative controls; corrupts certificates / chain JSON in
      memory and confirms the verifier FAILS each corruption.

Stdlib only.  Reads vendor certificates read-only; writes nothing.
"""
from __future__ import annotations
import copy
import json
import sys
from itertools import combinations
from math import gcd
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
BUNDLE = REPO / 'vendor' / 'd9_all_even_proof_bundle_20260611'
FRAME_CERT = BUNDLE / 'certificates' / 'd9_terminal_reserve_frame_candidate.json'
LOWMOD_CERT = BUNDLE / 'certificates' / 'd9_lowmod_finite_placement_candidate.json'
LEDGER_CERT = BUNDLE / 'certificates' / 'd9_affine_splice_placement_ledger.json'
CHAIN_JSON = REPO / 'scripts' / 'd9_chain_datum_fields.json'

D = 9
LOW_MODULI = (4, 6, 8)
REPRESENTATIVE_HIGH = (10, 12)

CANONICAL_FAMILY = ['U0', 'U1', 'U2', 'U1_c', 'U2_c', 'U3_c', 'U4_c',
                    'U5_c', 'U6_c', 'U7_c', 'U8_c', 'U_star']
CANONICAL_GRID = [(a, b) for b in range(3) for a in range(4)]  # row-major
ALIGN_M = ((1, 1), (0, 1))  # carrier -> block coords (T1 check C2); det 1


def edge_vec(e):
    i, j = int(e[0]), int(e[1])
    v = [0] * D
    v[i] -= 1
    v[j] += 1
    return v


V06, V01 = edge_vec('06'), edge_vec('01')
V24, V35 = edge_vec('24'), edge_vec('35')

# ----------------------------------------------------------------------
# standard terminal A2 block on (Z/m)^2 (same conventions as
# verify_d9_terminal_a2_block.py; terminal_A2_block.tex / TerminalA2LowMod.lean)

WORDS = {'default': (0, 1, 2), 'tau02': (2, 1, 0), 'tau12': (0, 2, 1),
         'tau01': (1, 0, 2), 'chip': (1, 2, 0), 'chim': (2, 0, 1)}
AVEC = [(1, 0), (0, 1), (0, 0)]
DELTA = [(0, 1), (1, 0), (1, -1)]
PUNCT = (1, 2)


def qadd(m, z, w):
    return ((z[0] + w[0]) % m, (z[1] + w[1]) % m)


def qsub(m, z, w):
    return ((z[0] - w[0]) % m, (z[1] - w[1]) % m)


def omega(m, z):
    p = (PUNCT[0] % m, PUNCT[1] % m)
    if z == p:
        return 'default'
    if z == qsub(m, p, (1, 0)):
        return 'chim'
    if z == qadd(m, p, (1, 0)):
        return 'chip'
    if z == qsub(m, p, (0, 1)):
        return 'chip'
    if z == qadd(m, p, (0, 1)):
        return 'chim'
    if z == qsub(m, p, (-1, 1)):
        return 'chim'
    if z == qadd(m, p, (-1, 1)):
        return 'chip'
    if z[1] == 2 % m:
        return 'tau02'
    if z[0] == 1 % m:
        return 'tau12'
    if (z[0] + z[1]) % m == 3 % m:
        return 'tau01'
    return 'default'


def t_return(m, i, z):
    z = qadd(m, z, DELTA[i])
    base = qsub(m, z, AVEC[i])
    w = WORDS[omega(m, base)]
    return qadd(m, base, AVEC[w[i]])


def return_map(m, i):
    return {(x, y): t_return(m, i, (x, y)) for x in range(m) for y in range(m)}


def marked_pair(m):
    """lem:small-terminal-marked-parents (m=4) / thm:terminal-A2 (m>=6)."""
    return (1, 2) if m == 4 else (0, 1)


def selector(m):
    if m == 4:
        return [(0, 3), (3, 0), (3, 3)]
    L = m - 1
    return ([(0, 0), ((-1) % m, 1 % m)]
            + [((-j - 1) % m, j % m) for j in range(2, L)])


def protected_neighborhood_block(m):
    """C and N(C) = C u R_a(C) u R_b(C) u R_a^-1(C) u R_b^-1(C) in block
    coordinates (lem:phase-product-rootflat)."""
    C = selector(m)
    a, b = marked_pair(m)
    Fa, Fb = return_map(m, a), return_map(m, b)
    Fainv = {v: k for k, v in Fa.items()}
    Fbinv = {v: k for k, v in Fb.items()}
    pts = set(C)
    for c in C:
        pts |= {Fa[c], Fb[c], Fainv[c], Fbinv[c]}
    return C, pts


def embed_carrier(m, base, pt, twist):
    """Block point -> K_{9,m} point of the carrier plane.  twist=None: direct
    chart; twist='M': block coords pulled back by the alignment unimodular
    map M = [[1,1],[0,1]] (carrier = M^-1 block)."""
    x, y = pt
    if twist == 'M':
        x, y = x - y, y
    return tuple((base[k] + x * V06[k] + y * V01[k]) % m for k in range(D))


def plane_points(m, base, w1, w2):
    return {tuple((base[k] + a * w1[k] + b * w2[k]) % m for k in range(D))
            for a in range(m) for b in range(m)}

# ----------------------------------------------------------------------

class Checker:
    def __init__(self, quiet=False):
        self.failures = []
        self.total = 0
        self.quiet = quiet

    def check(self, name, ok, detail=''):
        self.total += 1
        if not self.quiet:
            print(f"  [{'PASS' if ok else 'FAIL'}] {name}"
                  + (f"  ({detail})" if detail else ''))
        if not ok:
            self.failures.append((name, detail))

    def info(self, msg):
        if not self.quiet:
            print(f'  [info] {msg}')

# ----------------------------------------------------------------------
# (b) symbolic m > 9

def coordinate_groups(direction_vectors):
    """Partition of coordinates on which a functional vanishing on all the
    direction vectors must be constant (connected components of the edge
    graph)."""
    parent = list(range(D))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for v in direction_vectors:
        sup = [k for k in range(D) if v[k]]
        for k in sup[1:]:
            parent[find(sup[0])] = find(k)
    groups = {}
    for k in range(D):
        groups.setdefault(find(k), []).append(k)
    return sorted(groups.values())


def verify_symbolic(frame, ck):
    qT = frame['terminal_carrier']['base']
    qR = frame['reserve_plane']['base']
    dirs = [V06, V01, V24, V35]
    groups = coordinate_groups(dirs)
    ck.info(f'kernel coordinate groups for <06,01> + <24,35>: {groups}')

    # certificate separator, recomputed (not trusted)
    entry = next((e for e in frame['reserve_plane']['separations']
                  if e.get('name') == 'terminal_carrier'), None)
    ok_entry = entry is not None
    ck.check('S1 reserve/terminal separator entry present', ok_entry)
    if ok_entry:
        w = entry['separator']['w']
        kern = all(sum(w[k] * v[k] for k in range(D)) == 0 for v in dirs)
        diff = sum(w[k] * (qR[k] - qT[k]) for k in range(D))
        ck.check('S2 separator vanishes on all four plane directions', kern)
        ck.check('S3 separator difference recomputed, equals certificate, '
                 '0 < |diff| <= 9', diff == entry['separator']['diff']
                 and 0 < abs(diff) <= 9,
                 f'recomputed {diff}, certificate {entry["separator"]["diff"]}')
    else:
        ck.check('S2 separator vanishes on all four plane directions', False)
        ck.check('S3 separator difference recomputed, equals certificate, '
                 '0 < |diff| <= 9', False)

    # independent separator search (coefficients on the coordinate groups)
    diffvec = [qR[k] - qT[k] for k in range(D)]
    gsums = [sum(diffvec[k] for k in g) for g in groups]
    found = None
    rng = range(-2, 3)
    for coeffs in _tuples(rng, len(groups)):
        val = sum(c * s for c, s in zip(coeffs, gsums))
        if 0 < abs(val) <= 9:
            found = (coeffs, val)
            break
    ck.check('S4 independent separator found from scratch '
             '(group coefficients, 0 < |value| <= 9)', found is not None,
             f'coeffs {found[0]}, value {found[1]}' if found else '')
    ck.info('=> Q_T and Q_R disjoint for every even m > 9; N(C) lies in the '
            'carrier plane Q_T, hence Q_R cap N(C) = empty symbolically')

    # representative direct enumeration
    for m in REPRESENTATIVE_HIGH:
        C, NC = protected_neighborhood_block(m)
        QR = plane_points(m, qR, V24, V35)
        for twist in (None, 'M'):
            QT = plane_points(m, qT, V06, V01)
            NCpts = {embed_carrier(m, qT, p, twist) for p in NC}
            ck.check(f'S5 m={m} chart={"direct" if twist is None else "twisted"}: '
                     'N(C) inside carrier plane and Q_R cap N(C) = empty',
                     NCpts <= QT and not (QR & NCpts),
                     f'|C|={len(C)}, |N(C)|={len(NCpts)}')


def _tuples(rng, n):
    if n == 0:
        yield ()
        return
    for head in rng:
        for tail in _tuples(rng, n - 1):
            yield (head,) + tail

# ----------------------------------------------------------------------
# (b) lowmod m in {4, 6, 8}

def verify_lowmod(lowmod, ck):
    for m in LOW_MODULI:
        mm = lowmod['moduli'][str(m)]
        bT = mm['terminal_carrier']['base']
        bR = mm['reserve_plane']['base']
        ck.check(f'L1 m={m}: terminal and reserve base points root-flat in '
                 f'K_(9,{m})', sum(bT) % m == 0 and sum(bR) % m == 0)
        ck.check(f'L2 m={m}: lowmod carrier/reserve direction edges match the '
                 'symbolic frame (06,01 / 24,35)',
                 list(mm['terminal_carrier']['edges']) == ['06', '01']
                 and list(mm['reserve_plane']['edges']) == ['24', '35'])
        QT = plane_points(m, bT, V06, V01)
        QR = plane_points(m, bR, V24, V35)
        ck.check(f'L3 m={m}: Q_T cap Q_R = empty (enumerated, '
                 f'{len(QT)}+{len(QR)} points)', not (QT & QR))
        C, NC = protected_neighborhood_block(m)
        a, b = marked_pair(m)
        ck.info(f'm={m}: marked pair (F_{a},F_{b}), |C|={len(C)}, '
                f'|N(C)|={len(NC)} block points')
        ck.check(f'L4 m={m}: |C| is a unit mod {m}', gcd(len(C), m) == 1,
                 f'|C|={len(C)}')
        sites = [tuple(x % m for x in s['point']) for s in mm['reserve_sites']]
        coeffs = [tuple(s['coeff']) for s in mm['reserve_sites']]
        ck.check(f'L5 m={m}: 12 reserve sites, pairwise distinct points and '
                 'coefficient pairs (mod m)',
                 len(sites) == 12 and len(set(sites)) == 12
                 and len({(ca % m, cb % m) for ca, cb in coeffs}) == 12)
        ok_pts = all(
            tuple((bR[k] + ca * V24[k] + cb * V35[k]) % m for k in range(D)) == s
            for (ca, cb), s in zip(coeffs, sites))
        ck.check(f'L6 m={m}: every site = base + a*24 + b*35 (in Q_R)', ok_pts)
        for twist in (None, 'M'):
            NCpts = {embed_carrier(m, bT, p, twist) for p in NC}
            cname = 'direct' if twist is None else 'twisted'
            ck.check(f'L7 m={m} chart={cname}: N(C) inside carrier plane',
                     NCpts <= QT)
            ck.check(f'L8 m={m} chart={cname}: Q_R cap N(C) = empty '
                     '(full enumeration)', not (QR & NCpts))
            ck.check(f'L9 m={m} chart={cname}: no reserve site in N(C)',
                     not (set(sites) & NCpts))

# ----------------------------------------------------------------------
# (c) ordered endpoint-reserve family

def verify_family(frame, lowmod, ck):
    sites = frame['reserve_sites']
    names = [s['name'] for s in sites]
    coeffs = [tuple(s['coeff']) for s in sites]
    qR = frame['reserve_plane']['base']

    ck.check('F1 high-even certificate carries the canonical ordered family '
             '(U0,U1,U2,U1^c..U8^c,U_*), d+3 = 12 sites',
             names == CANONICAL_FAMILY, str(names))
    ck.check('F2 role count: 3 terminal-exchange + 8 renewal + 1 next-reserve',
             len(names) == 12 and names[:3] == ['U0', 'U1', 'U2']
             and names[-1] == 'U_star'
             and all(n.endswith('_c') for n in names[3:11]))
    ck.check('F3 coefficients are the row-major {0,1,2,3} x {0,1,2} grid',
             coeffs == CANONICAL_GRID, str(coeffs))
    ck.check('F4 coefficient pairs pairwise distinct with |da| <= 3, |db| <= 2 '
             '=> sites pairwise distinct for EVERY even m >= 4',
             len(set(coeffs)) == 12
             and max(abs(a1 - a2) for (a1, _), (a2, _) in
                     combinations(coeffs, 2)) <= 3
             and max(abs(b1 - b2) for (_, b1), (_, b2) in
                     combinations(coeffs, 2)) <= 2)
    ok_pts = all(
        [qR[k] + a * V24[k] + b * V35[k] for k in range(D)] == list(s['point'])
        for (a, b), s in zip(coeffs, sites))
    ck.check('F5 every site point = q_R + a*24 + b*35 (integer identity)', ok_pts)
    ck.check('F6 every site root-flat', all(sum(s['point']) == 0 for s in sites))

    # fixed-fiber transport form: every functional vanishing on <24,35> is
    # constant across the family (chain-datum item 6)
    groups = coordinate_groups([V24, V35])
    fib_ok = True
    for g in groups:
        vals = {sum(s['point'][k] for k in g) for s in sites}
        if len(vals) != 1 and g not in ([2, 4], [3, 5]):
            fib_ok = False
    # for groups {2,4} and {3,5} constancy holds because v24/v35 sum to zero
    for g in ([2, 4], [3, 5]):
        vals = {sum(s['point'][k] for k in g) for s in sites}
        if len(vals) != 1:
            fib_ok = False
    ck.check('F7 fixed-fiber form: all 12 sites in one fiber of every '
             'functional vanishing on <24,35>', fib_ok)

    # separation of the family from N(C) / terminal plane at representative m
    qT = frame['terminal_carrier']['base']
    for m in REPRESENTATIVE_HIGH:
        QT = plane_points(m, qT, V06, V01)
        _, NC = protected_neighborhood_block(m)
        NCpts = {embed_carrier(m, qT, p, None) for p in NC}
        spts = {tuple(x % m for x in s['point']) for s in sites}
        ck.check(f'F8 m={m}: family disjoint from terminal plane and from N(C)',
                 not (spts & QT) and not (spts & NCpts))

    # finding 1: the D5/D7 high-even single-fiber renewal layout
    # (renewal sites at (j-1, 1), j = 1..d-1) does not extend to d = 9
    needed_a = list(range(8))     # 8 renewal sites at fiber b = 1
    grid_a = sorted({a for a, _ in CANONICAL_GRID})
    extends = set(needed_a) <= set(grid_a)
    ck.check('F9 (finding, expected True): published D5/D7 single-fiber '
             'renewal layout requires a-range 0..7, infeasible on the '
             '{0,1,2,3} x {0,1,2} grid', not extends,
             f'needed a-values {needed_a}, grid a-values {grid_a}')

    # finding 2: lowmod certificate has no family labels; positional
    # canonical labeling is consistent (verified in L5/L6); record shape
    for m in LOW_MODULI:
        mm = lowmod['moduli'][str(m)]
        lnames = [s['name'] for s in mm['reserve_sites']]
        generic = lnames == [f'U{i}' for i in range(12)]
        ck.check(f'F10 m={m} (finding, expected True): lowmod certificate '
                 'carries only generic site names U0..U11 (no family roles); '
                 'canonical family labeling applied positionally',
                 generic, str(lnames))

# ----------------------------------------------------------------------
# --chain-fields: validate scripts/d9_chain_datum_fields.json

MOD11 = 11
INV2_11 = 6


def window_of(s, d, mod=MOD11):
    return [s % mod, (s + d) % mod, (s - d) % mod, (s - 2 * d) % mod]


def guide(rho, d, mod=MOD11):
    return [(rho - d) % mod, rho % mod, (rho + d) % mod]


def chain_row_recompute(row, G11, old_labels):
    s, d = row['s'], row['delta']
    W = window_of(s, d)
    th = {int(k): v for k, v in row['theta'].items()}
    red = {int(k): v for k, v in row['reduce_map'].items()}

    def cut(pair):
        i, j = (red.get(x, x) for x in pair)
        return th[i] - th[j]

    gen_diffs = ({(a - b) % MOD11 for a, b in G11}
                 | {(b - a) % MOD11 for a, b in G11})
    C_old, C_lit, unreal = set(), set(), []
    for x, y in combinations(W, 2):
        if not cut((x, y)):
            continue
        if (x - y) % MOD11 not in gen_diffs:
            unreal.append((x, y))
            continue
        ctr = ((x + y) * INV2_11) % MOD11
        C_lit.add(ctr)
        if x in old_labels and y in old_labels:
            C_old.add(ctr)

    def visible(rho):
        win = set(W)
        for (a, b) in G11:
            half = ((b - a) * INV2_11) % MOD11
            for lam in guide(rho, d):
                i_l, j_l = (lam + half) % MOD11, (lam - half) % MOD11
                if i_l in win and j_l in win:
                    yield (a, b), lam, (i_l, j_l), (i_l in old_labels
                                                    and j_l in old_labels)

    disch_old, disch_lit, cex = [], [], 0
    for rho in range(MOD11):
        nzo = nzl = False
        for _, _, pair, oe in visible(rho):
            if cut(pair):
                nzl = True
                if oe:
                    nzo = True
        if not nzo:
            disch_old.append(rho)
        if not nzl:
            disch_lit.append(rho)
        Gp = set(guide(rho, d))
        if not (Gp & C_old) and nzo:
            cex += 1
        if not (Gp & C_lit) and nzl:
            cex += 1
    pred_old = [r for r in range(MOD11) if not set(guide(r, d)) & C_old]
    pred_lit = [r for r in range(MOD11) if not set(guide(r, d)) & C_lit]
    B = sorted(set(W) & old_labels)
    adm = [r for r in range(MOD11) if not set(guide(r, d)) & set(B)]
    return dict(window=W, B=B, C_old=sorted(C_old), C_lit=sorted(C_lit),
                unreal=unreal, disch_old=disch_old, disch_lit=disch_lit,
                pred_old=pred_old, pred_lit=pred_lit, adm=adm, cex=cex)


def verify_chain(chain, ledger, frame, ck):
    gi = chain['growth_interface']
    # label chart
    ck.check('K1 label chart W9 = Z/9 with labels 0..8',
             chain['label_chart']['labels'] == list(range(9)))
    # relabelling
    phi = {int(k): v for k, v in gi['relabelling_W9_to_W11']['map'].items()}
    old_set = gi['old_label_set']
    ck.check('K2 relabelling injective, image = Z/11 \\ {0,3} = old_label_set',
             sorted(phi) == list(range(9))
             and sorted(phi.values()) == sorted(old_set)
             and sorted(old_set) == [x for x in range(11) if x not in (0, 3)])
    enum = [x for x in range(11) if x not in (0, 3)]
    ck.check('K3 relabelling matches its stated rule (order-preserving '
             'enumeration)', [phi[i] for i in range(9)] == enum)
    ck.check('K4 new labels are {0,3}', sorted(gi['new_labels']) == [0, 3])
    ck.check('K5 1/2 = 6 in Z/11', (2 * gi['inv2_mod_11']) % 11 == 1)

    # G^- derivation from the vendor ledger
    w9 = set()
    for st in ledger['stages']:
        for part in st['parts']:
            for e in part['active_edges']:
                a, b = int(e[0]), int(e[1])
                w9.add((min(a, b), max(a, b)))
    w9 = sorted(w9)
    ck.check('K6 W9 ledger active-edge set recomputed (27 distinct lines)',
             [list(e) for e in w9] == gi['G_minus_derivation']['W9_edges']
             and len(w9) == gi['G_minus_derivation']['count'],
             f'{len(w9)} lines')
    G11 = sorted(tuple(sorted((phi[a], phi[b]))) for a, b in w9)
    old_labels = set(old_set)

    leaves = []
    for row in gi['rows']:
        rn = row['name']
        rec = chain_row_recompute(row, G11, old_labels)
        ck.check(f'K7 [{rn}] G_minus equals the relabelled ledger lines',
                 sorted(tuple(e) for e in
                        (tuple(x) for x in row['G_minus'])) == G11)
        ck.check(f'K8 [{rn}] window from (s,delta) matches; leaf and quotient '
                 'directions match lem:growth-old-generator-invariant',
                 row['window'] == rec['window']
                 and set(row['leaf_line']) ==
                 {row['s'] % 11, (row['s'] + row['delta']) % 11}
                 and set(row['quotient_direction']) ==
                 {(row['s'] - row['delta']) % 11,
                  (row['s'] - 2 * row['delta']) % 11})
        th = {int(k): v for k, v in row['theta'].items()}
        qd = row['quotient_direction']
        th_ok = (sorted(th) == sorted(row['window'])
                 and th[qd[0]] - th[qd[1]] == 1
                 and th[row['leaf_line'][0]] == th[row['leaf_line'][1]])
        ck.check(f'K9 [{rn}] theta is the printed cut: 1 on the quotient '
                 'head, 0 elsewhere, constant on the leaf line', th_ok)
        ck.check(f'K10 [{rn}] boundary set B_r = window cap old labels',
                 sorted(row['boundary_set_B']) == rec['B'])
        ck.check(f'K11 [{rn}] midpoint collision sets: C_old={rec["C_old"]}, '
                 f'C_lit={rec["C_lit"]}; all cut-separated pairs realized',
                 row['C_old_endpoint'] == rec['C_old']
                 and row['C_literal'] == rec['C_lit']
                 and row['unrealized_cut_pairs'] == rec['unreal'] == [])
        ck.check(f'K12 [{rn}] boundary-avoiding phases',
                 row['boundary_avoiding_phases'] == rec['adm'])
        ck.check(f'K13 [{rn}] discharging phases (old/literal) by full '
                 'enumeration == C_r-avoidance prediction == stored',
                 rec['disch_old'] == rec['pred_old']
                 == row['discharging_phases_old_endpoint']
                 and rec['disch_lit'] == rec['pred_lit']
                 == row['discharging_phases_literal'])
        ck.check(f'K14 [{rn}] corrected collision lemma: zero counterexamples '
                 'over all 11 phases', rec['cex'] == 0
                 and row['collision_lemma_counterexamples'] == 0)
        ck.check(f'K15 [{rn}] recommended phase discharges (literal) AND '
                 'avoids B_r', row['recommended_phase'] in rec['disch_lit']
                 and row['recommended_phase'] in rec['adm'],
                 f"phase {row['recommended_phase']}")
        leaves.append(tuple(row['leaf_line']))

    # terminal carrier field
    tcf = chain['terminal_carrier']
    win_all = set(gi['rows'][0]['window']) | set(gi['rows'][1]['window'])
    ck.check('K16 growth window labels recomputed',
             sorted(tcf['growth_window_labels']) == sorted(win_all))
    unused = sorted(set(old_set) - win_all)
    ck.check('K17 unused old labels = old labels minus window',
             tcf['unused_old_labels_in_growth'] == unused)
    carrier = tcf['output_chart_carrier_labels']
    ck.check('K18 carrier labels: 3 unused old labels, disjoint from the '
             'growth window and from the new labels',
             len(carrier) == 3 and set(carrier) <= set(unused)
             and not (set(carrier) & win_all)
             and not (set(carrier) & set(gi['new_labels']))
             and tcf['disjoint_from_growth_window'] is True,
             str(carrier))
    ck.check('K19 anchor carrier labels (W9) match the frame certificate '
             'root vertices',
             tcf['anchor_carrier_labels_W9']
             == list(frame['terminal_alignment']['root_vertices']))

    # reserve transport field
    rt = chain['reserve_transport_form']
    ck.check('K20 incoming family names match the frame certificate',
             rt['incoming_family'] ==
             [s['name'] for s in frame['reserve_sites']])
    vals = (rt['leaf_trace_values'] + [rt['transported_leaf_value'],
                                       rt['new_site_leaf_value']])
    ck.check('K21 leaf values {0,1} u {2} u {3}, max < 4 => pairwise distinct '
             'mod m for every even m >= 4',
             sorted(vals) == [0, 1, 2, 3] and max(vals) < 4)
    ck.check('K22 output family size: 12 transported + 2 new = 14 = (D+2)+3',
             rt['output_family_size'] == 14 == len(rt['incoming_family'])
             + len(rt['new_renewal_sites']) and (9 + 2) + 3 == 14)
    ck.check('K23 new renewal sites in the two new leaf fibers (labels 0, 3)',
             sorted(x['leaf_fiber_of_label'] for x in rt['new_renewal_sites'])
             == sorted(gi['new_labels'])
             and [x['name'] for x in rt['new_renewal_sites']]
             == ['U9_c', 'U10_c'])

    # underivable entries are declared
    ck.check('K24 UNDERIVABLE entries declared (relabelling, G^- scope, '
             'carrier choice)', len(chain['underivable_entries']) == 3)

# ----------------------------------------------------------------------

def run_all(frame, lowmod, ledger, chain, quiet=False):
    ck = Checker(quiet)
    if not quiet:
        print('--- (a)/(b) symbolic m > 9 ---')
    verify_symbolic(frame, ck)
    if not quiet:
        print('--- (b) lowmod m in {4,6,8} (full enumeration) ---')
    verify_lowmod(lowmod, ck)
    if not quiet:
        print('--- (c) ordered endpoint-reserve family ---')
    verify_family(frame, lowmod, ck)
    if not quiet:
        print('--- chain-datum fields (T3 JSON) ---')
    verify_chain(chain, ledger, frame, ck)
    return ck


def corruption_matrix():
    """name -> (target, mutator).  target in {frame, lowmod, chain}."""
    def f_qr_to_qt(fr):
        fr['reserve_plane']['base'] = list(fr['terminal_carrier']['base'])
        for (a, b), s in zip(CANONICAL_GRID, fr['reserve_sites']):
            s['point'] = [fr['reserve_plane']['base'][k] + a * V24[k]
                          + b * V35[k] for k in range(D)]

    def f_site_off_plane(fr):
        fr['reserve_sites'][5]['point'][7] += 1
        fr['reserve_sites'][5]['point'][8] -= 1

    def f_dup_coeff(fr):
        fr['reserve_sites'][2]['coeff'] = list(fr['reserve_sites'][1]['coeff'])
        fr['reserve_sites'][2]['point'] = list(fr['reserve_sites'][1]['point'])

    def f_name_order(fr):
        fr['reserve_sites'][3]['name'] = 'U1'

    def f_separator(fr):
        for e in fr['reserve_plane']['separations']:
            if e['name'] == 'terminal_carrier':
                e['separator']['w'][2] += 1

    def l_site_in_NC(lm):
        m = 6
        mm = lm['moduli'][str(m)]
        bT = mm['terminal_carrier']['base']
        _, NC = protected_neighborhood_block(m)
        pt = embed_carrier(m, bT, sorted(NC)[0], None)
        mm['reserve_sites'][4]['point'] = list(pt)

    def c_cold(chj):
        chj['growth_interface']['rows'][0]['C_old_endpoint'] = [0, 5]

    def c_gminus(chj):
        for row in chj['growth_interface']['rows']:
            row['G_minus'] = row['G_minus'][:-1]
        chj['growth_interface']['G_minus_derivation']['W9_edges'] = \
            chj['growth_interface']['G_minus_derivation']['W9_edges'][:-1]
        chj['growth_interface']['G_minus_derivation']['count'] = 26

    def c_carrier(chj):
        chj['terminal_carrier']['output_chart_carrier_labels'] = [4, 6, 7]

    def c_relabel(chj):
        chj['growth_interface']['relabelling_W9_to_W11']['map']['8'] = 1

    def c_phases(chj):
        chj['growth_interface']['rows'][1][
            'discharging_phases_literal'] = [0, 1, 5, 9, 10]

    def c_recommended(chj):
        chj['growth_interface']['rows'][0]['recommended_phase'] = 4

    return {
        'frame: q_R moved onto q_T (planes coincide)': ('frame', f_qr_to_qt),
        'frame: site U3_c point pushed off the reserve plane':
            ('frame', f_site_off_plane),
        'frame: duplicate coefficient pair U2 = U1': ('frame', f_dup_coeff),
        'frame: family name order corrupted (U1_c -> U1)':
            ('frame', f_name_order),
        'frame: separator w no longer in the kernel': ('frame', f_separator),
        'lowmod: m=6 reserve site replaced by an N(C) point':
            ('lowmod', l_site_in_NC),
        'chain: C_old of row 1 wrong': ('chain', c_cold),
        'chain: G_minus missing one line': ('chain', c_gminus),
        'chain: carrier labels meet the growth window': ('chain', c_carrier),
        'chain: relabelling not injective': ('chain', c_relabel),
        'chain: discharging phases wrong': ('chain', c_phases),
        'chain: recommended phase neither discharging nor B-avoiding':
            ('chain', c_recommended),
    }


def self_test(frame, lowmod, ledger, chain):
    print('=== self-test: pristine inputs must PASS ===')
    base = run_all(copy.deepcopy(frame), copy.deepcopy(lowmod), ledger,
                   copy.deepcopy(chain), quiet=True)
    ok = not base.failures
    print(f"  pristine: {'PASS' if ok else 'FAIL'} "
          f"({base.total - len(base.failures)}/{base.total})")
    if base.failures:
        for n, d in base.failures:
            print(f'    pristine failure: {n} ({d})')
    print('=== self-test: corruption matrix (each must FAIL) ===')
    for name, (target, mut) in corruption_matrix().items():
        fr = copy.deepcopy(frame)
        lm = copy.deepcopy(lowmod)
        chj = copy.deepcopy(chain)
        {'frame': lambda: mut(fr), 'lowmod': lambda: mut(lm),
         'chain': lambda: mut(chj)}[target]()
        res = run_all(fr, lm, ledger, chj, quiet=True)
        caught = bool(res.failures)
        ok = ok and caught
        first = res.failures[0][0] if res.failures else '-'
        print(f"  [{'CAUGHT' if caught else 'MISSED'}] {name}"
              + (f"  (first failing check: {first})" if caught else ''))
    print()
    print('SELF-TEST RESULT:', 'OK' if ok else 'FAILED')
    return ok


def main(argv):
    frame = json.loads(FRAME_CERT.read_text())
    lowmod = json.loads(LOWMOD_CERT.read_text())
    ledger = json.loads(LEDGER_CERT.read_text())
    chain = json.loads(CHAIN_JSON.read_text())
    if '--self-test' in argv:
        return 0 if self_test(frame, lowmod, ledger, chain) else 1
    if '--chain-fields' in argv:
        print('=== D9 chain-datum field validation ===')
        ck = Checker()
        verify_chain(chain, ledger, frame, ck)
    else:
        print('=== D9 marked comparison cycle / endpoint reserve verification ===')
        ck = run_all(frame, lowmod, ledger, chain)
    print()
    print(f'RESULT: {ck.total - len(ck.failures)}/{ck.total} checks passed'
          + (f', {len(ck.failures)} FAILED' if ck.failures else ''))
    for name, detail in ck.failures:
        print(f'  FAILED: {name}' + (f'  ({detail})' if detail else ''))
    return 1 if ck.failures else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
