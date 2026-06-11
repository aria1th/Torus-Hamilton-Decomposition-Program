#!/usr/bin/env python3
"""Terminal A2 algebra verifier for the D9 terminal/reserve frame certificate.

Audit reinforcement task 1 (docs/D9_ADVERSARIAL_AUDIT_20260611.md, item 2):
the shipped bundle verifier (vendor/.../verify_d9_terminal_reserve_frame.py)
checks only the separation functionals; the `terminal_alignment` block
(rows / permutation / signs) is printed but never checked.  This script
actually verifies the terminal A2 algebra:

  (A) terminal triple consistency: chronological (8,2,3) + height shift 7
      = shifted root vertices (6,0,1) in Z/9; (t,0,1) form; cross-checked
      against the active-anchor certificate (shift list, stage-7 row,
      stage-7 affected colors P).
  (B) carrier basis: basis_edges == ("0t","01") == terminal_carrier.edges,
      rank 2, and the pairwise differences of the root vertices lie in the
      integer span of the two basis edge vectors; q_T is root-flat.
  (C) alignment rows / permutation / signs:
      C1 rows are an A2 selector packet: integer, primitive, sum zero,
         all pairwise determinants +-1;
      C2 rows are bound to the actual terminal triple: the three physical
         increment vectors g_i (tail->head of the stage-7 triple row, per
         affected color, decomposed in the carrier basis) are carried to
         the printed rows by a single unimodular matrix M (M g_i = row_i,
         det M = +-1) -- the corruption experiment of the audit breaks this;
      C3 permutation is a permutation of {0,1,2}; signs are +-1;
      C4 (rows, permutation, signs) equal the standard terminal-block
         alignment datum, identical for the D5 / D7 anchors in the paper
         appendix tables (tab:D5-terminal-alignment, tab:D7-terminal-alignment):
         rows (-1,0),(1,1),(0,-1), permutation (0,1,2), signs (1,1,-1);
      C5 signs match (up to a global orientation flip) the recomputed
         terminal-stage unit closing carries: the lambda values of the three
         terminal colors (8,2,3) on the stage-7 support coordinate, computed
         from the active-anchor certificate, are (-1,-1,1) = -(signs);
      C6 the standard terminal A2 block these data feed (Theorem
         thm:terminal-A2 / lem:terminal-interlacing /
         lem:small-terminal-marked-parents; Lean: EvenV11.TerminalA2LowMod,
         EvenV11.V28Hard.TerminalA2*) is verified by direct computation on
         (Z/m)^2 for m in {4,6,8,10,12}:
           - the three returns F_0,F_1,F_2 are single m^2-cycles
             (m=4 orbits equal the printed lemma table);
           - for m >= 6, the marked pair (perm[0],perm[1]) = (F_0,F_1) has
             the interlacing selector C_m: sigma = F_1^{-1}F_0 advances C_m
             by +1, the first-return successors advance by +2 / -2,
             |C_m| = m-1 is a unit mod m, and both switched returns are
             single m^2-cycles;
           - for m = 4, the marked-parent pair (F_1,F_2) with
             C_4 = {(0,3),(3,0),(3,3)} satisfies the printed common-head /
             successor table and both switched returns are single 16-cycles.

  --self-test: negative-control mode.  Programmatically corrupts rows /
  permutation / signs / triple data (the audit's decisive experiment) and
  confirms this verifier FAILS each corruption.

Stdlib only.  Reads vendor certificates read-only; writes nothing.
"""
from __future__ import annotations
import copy
import json
import sys
from fractions import Fraction
from math import gcd
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
BUNDLE = REPO / 'vendor' / 'd9_all_even_proof_bundle_20260611'
FRAME_CERT = BUNDLE / 'certificates' / 'd9_terminal_reserve_frame_candidate.json'
ANCHOR_CERT = BUNDLE / 'certificates' / 'd9_active_anchor_candidate_v1.json'

D = 9
BLOCK_MODULI = (4, 6, 8, 10, 12)

# Standard terminal-block alignment datum, transcribed from the published
# D5 / D7 anchor tables (tab:D5-terminal-alignment, tab:D7-terminal-alignment,
# even_modulus rewrite subtex/appendix/D{5,7}_anchor_tables.tex; identical in
# the v28 source).  The datum is dimension-independent.
CANONICAL_ROWS = [[-1, 0], [1, 1], [0, -1]]
CANONICAL_PERMUTATION = [0, 1, 2]
CANONICAL_SIGNS = [1, 1, -1]

# ----------------------------------------------------------------------
# small linear algebra over Z

def edge_vec(e):
    i, j = int(e[0]), int(e[1])
    v = [0] * D
    v[i] -= 1
    v[j] += 1
    return v


def solve_2d_int(b1, b2, target):
    """Solve x*b1 + y*b2 = target over Q for D-vectors; return (x, y) if the
    solution exists, is unique on the span, and is integral; else None."""
    det = None
    for i in range(D):
        for j in range(i + 1, D):
            d = b1[i] * b2[j] - b1[j] * b2[i]
            if d:
                det = (i, j, d)
                break
        if det:
            break
    if det is None:
        return None
    i, j, d = det
    x = Fraction(target[i] * b2[j] - target[j] * b2[i], d)
    y = Fraction(b1[i] * target[j] - b1[j] * target[i], d)
    if any(x * b1[k] + y * b2[k] != target[k] for k in range(D)):
        return None
    if x.denominator != 1 or y.denominator != 1:
        return None
    return (int(x), int(y))


def det2(v, w):
    return v[0] * w[1] - v[1] * w[0]

# ----------------------------------------------------------------------
# active-anchor quotient machinery (re-implementation of the bundle
# verifier's coforest contraction; used for the C5 closing-carry check)

def row_perm(row):
    p = list(range(D))
    a, b, c = row['triple']
    p[a] = b
    p[b] = c
    p[c] = a
    for x, y in row['pairs']:
        p[x] = y
        p[y] = x
    return tuple(p)


def comps_before(anchor, color, upto):
    shifts = anchor['shifts']
    perms = [row_perm(r) for r in anchor['rows_shifted']]
    parent = list(range(D))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for r in range(upto):
        s = shifts[r]
        p = perms[r]
        t = (color + s) % D
        parent[find(t)] = find(p[t])
    comp, idx = {}, {}
    for x in range(D):
        rt = find(x)
        if rt not in idx:
            idx[rt] = len(idx)
        comp[x] = idx[rt]
    return comp


def terminal_closing_lambdas(anchor):
    """Unit descendant increments of the three terminal colors on the
    stage-7 support coordinate (edge "02"), recomputed from the anchor
    certificate exactly as the bundle's `lam` does."""
    stage = 6  # stage 7, 0-indexed
    shifts = anchor['shifts']
    perms = [row_perm(r) for r in anchor['rows_shifted']]
    s = shifts[stage]
    p = perms[stage]
    item = anchor['supports_unshifted'][stage]['parts'][0]
    P = item['P']
    M = [tuple(sorted(e)) for e in item['M']]
    out = []
    for c in P:
        comp = comps_before(anchor, c, stage)
        n = max(comp.values()) + 1
        root = comp[c]
        # quotient support edges; remove the (single) active edge, flood from root
        se = None
        adj = [set() for _ in range(n)]
        removed = False
        for f in M:
            qa, qb = comp[f[0]], comp[f[1]]
            if qa == qb:
                return None
            qe = (qa, qb) if qa < qb else (qb, qa)
            if se is None:
                se = qe  # single support edge at the terminal stage
            if qe == se and not removed:
                removed = True
                continue
            adj[qe[0]].add(qe[1])
            adj[qe[1]].add(qe[0])
        if not removed:
            return None
        seen = {root}
        stack = [root]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if v not in seen:
                    seen.add(v)
                    stack.append(v)
        desc = set(range(n)) - seen
        tail = (c + s) % D
        head = p[tail]
        out.append(int(comp[head] in desc) - int(comp[tail] in desc))
    return out

# ----------------------------------------------------------------------
# standard terminal A2 block on Q_m = (Z/m)^2
# (terminal_A2_block.tex eq:terminal-word; EvenV11/TerminalA2LowMod.lean)

WORDS = {'default': (0, 1, 2), 'tau02': (2, 1, 0), 'tau12': (0, 2, 1),
         'tau01': (1, 0, 2), 'chip': (1, 2, 0), 'chim': (2, 0, 1)}
AVEC = [(1, 0), (0, 1), (0, 0)]
DELTA = [(0, 1), (1, 0), (1, -1)]
PUNCT = (1, 2)
EHV = {'eH': (1, 0), 'eV': (0, 1), 'eD': (-1, 1)}


def qadd(m, z, w):
    return ((z[0] + w[0]) % m, (z[1] + w[1]) % m)


def qsub(m, z, w):
    return ((z[0] - w[0]) % m, (z[1] - w[1]) % m)


def omega(m, z):
    p = (PUNCT[0] % m, PUNCT[1] % m)
    if z == p:
        return 'default'
    if z == qsub(m, p, EHV['eH']):
        return 'chim'
    if z == qadd(m, p, EHV['eH']):
        return 'chip'
    if z == qsub(m, p, EHV['eV']):
        return 'chip'
    if z == qadd(m, p, EHV['eV']):
        return 'chim'
    if z == qsub(m, p, EHV['eD']):
        return 'chim'
    if z == qadd(m, p, EHV['eD']):
        return 'chip'
    if z[1] == 2 % m:
        return 'tau02'
    if z[0] == 1 % m:
        return 'tau12'
    if (z[0] + z[1]) % m == 3 % m:
        return 'tau01'
    return 'default'


def eta(m, i, z):
    base = qsub(m, z, AVEC[i])
    w = WORDS[omega(m, base)]
    return qadd(m, base, AVEC[w[i]])


def t_return(m, i, z):
    """First-return convention of lem:terminal-m4-finite-check:
    F_i(z) = eta_i(z + Delta_i)."""
    return eta(m, i, qadd(m, z, DELTA[i]))


def return_map(m, i):
    return {(x, y): t_return(m, i, (x, y)) for x in range(m) for y in range(m)}


def is_single_cycle(perm, n):
    start = next(iter(perm))
    z = perm[start]
    k = 1
    while z != start:
        z = perm[z]
        k += 1
    return k == n


def interlacing_selector(m):
    """C_m of lem:terminal-interlacing (m >= 6)."""
    L = m - 1
    pts = [(0, 0), ((-1) % m, 1 % m)]
    pts += [((-j - 1) % m, j % m) for j in range(2, L)]
    return pts


M4_SELECTOR = [(0, 3), (3, 0), (3, 3)]            # lem:small-terminal-marked-parents
M4_TABLE = {  # c -> (sigma(c), common head, s_{F1,C}(c), s_{F2,C}(c))
    (0, 3): ((3, 0), (1, 3), (3, 3), (3, 0)),
    (3, 0): ((3, 3), (0, 3), (0, 3), (3, 3)),
    (3, 3): ((0, 3), (1, 2), (3, 0), (0, 3)),
}
M4_PRINTED_ORBITS = {
    0: [(0, 0), (0, 1), (3, 2), (3, 3), (3, 0), (2, 1), (2, 2), (1, 3),
        (1, 0), (1, 1), (0, 2), (0, 3), (3, 1), (2, 3), (2, 0), (1, 2)],
    1: [(0, 0), (2, 3), (3, 3), (1, 2), (3, 1), (0, 1), (1, 0), (2, 0),
        (3, 0), (0, 3), (1, 3), (2, 2), (3, 2), (0, 2), (1, 1), (2, 1)],
    2: [(0, 0), (1, 0), (2, 3), (0, 2), (2, 1), (3, 0), (1, 3), (3, 2),
        (0, 1), (1, 1), (2, 0), (3, 3), (0, 3), (1, 2), (2, 2), (3, 1)],
}


def first_return_to(perm, Cset, c):
    z = perm[c]
    while z not in Cset:
        z = perm[z]
    return z

# ----------------------------------------------------------------------
# verification

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


def verify(frame, anchor, quiet=False):
    ck = Checker(quiet)
    al = frame['terminal_alignment']
    tc = frame['terminal_carrier']
    chrono = list(al['terminal_triple_chronological'])
    shift = al['height_shift']
    rv = list(al['root_vertices'])
    basis = list(al['basis_edges'])
    rows = [list(r) for r in al['rows']]
    perm = list(al['permutation'])
    signs = list(al['signs'])

    # ----- (A) terminal triple consistency -----
    ck.check('A1 chronological triple + height shift == root vertices (Z/9)',
             len(chrono) == 3 and len(rv) == 3
             and [(x + shift) % D for x in chrono] == rv,
             f'{chrono} + {shift} vs {rv}')
    ck.check('A2 root vertices distinct, of terminal form (t,0,1), t not in {0,1}',
             len(set(rv)) == 3 and rv[1:] == [0, 1] and rv[0] not in (0, 1),
             str(rv))
    sh7 = anchor['shifts'][6]
    tri7 = list(anchor['rows_shifted'][6]['triple'])
    P7 = list(anchor['supports_unshifted'][6]['parts'][0]['P'])
    ck.check('A3 cross-certificate: shift == anchor stage-7 shift; shifted triple '
             '== anchor stage-7 triple; chronological triple == stage-7 colors P',
             shift == sh7 and tri7 == rv and P7 == chrono,
             f'anchor shift {sh7}, triple {tri7}, P {P7}')

    # ----- (B) carrier basis -----
    t = rv[0]
    want_basis = [f'0{t}', '01']
    ck.check('B1 basis_edges == ("0t","01") == terminal_carrier.edges',
             basis == want_basis and list(tc['edges']) == basis,
             f'basis {basis}, carrier {tc["edges"]}')
    ok_b1 = basis == want_basis
    v1 = edge_vec(basis[0]) if len(basis) == 2 and len(basis[0]) == 2 else None
    v2 = edge_vec(basis[1]) if len(basis) == 2 and len(basis[1]) == 2 else None
    rank2 = (v1 is not None and v2 is not None
             and solve_2d_int(v1, v2, [0] * D) == (0, 0)
             and any(v1) and any(v2)
             and solve_2d_int(v1, [0] * D, v2) is None)
    ck.check('B2 basis edge vectors have rank 2', bool(rank2))
    if rank2:
        diffs_ok = True
        for i in range(3):
            for j in range(i + 1, 3):
                dvec = [0] * D
                dvec[rv[j]] += 1
                dvec[rv[i]] -= 1
                if solve_2d_int(v1, v2, dvec) is None:
                    diffs_ok = False
        ck.check('B3 pairwise root-vertex differences lie in Z-span<basis edges>',
                 diffs_ok)
    else:
        ck.check('B3 pairwise root-vertex differences lie in Z-span<basis edges>',
                 False, 'basis not rank 2')
    ck.check('B4 terminal carrier base point is root-flat',
             sum(tc['base']) == 0, str(tc['base']))

    # ----- (C1) rows: A2 selector packet -----
    rows_shape = (len(rows) == 3 and all(len(r) == 2 for r in rows)
                  and all(isinstance(x, int) for r in rows for x in r))
    ck.check('C1a rows are three integer 2-vectors', rows_shape)
    if rows_shape:
        ck.check('C1b rows sum to zero',
                 [sum(r[0] for r in rows), sum(r[1] for r in rows)] == [0, 0],
                 str(rows))
        ck.check('C1c each row is primitive (nonzero, gcd 1)',
                 all(gcd(abs(r[0]), abs(r[1])) == 1 for r in rows))
        dets = [det2(rows[i], rows[j]) for i in range(3) for j in range(i + 1, 3)]
        ck.check('C1d all pairwise row determinants are +-1',
                 all(abs(d) == 1 for d in dets), f'dets {dets}')
    else:
        for nm in ('C1b rows sum to zero', 'C1c each row is primitive (nonzero, gcd 1)',
                   'C1d all pairwise row determinants are +-1'):
            ck.check(nm, False, 'bad row shape')

    # ----- (C2) rows bound to the actual terminal triple -----
    # physical increments of the stage-7 triple row, per affected color,
    # decomposed in the carrier basis
    c2_ok = False
    c2_detail = ''
    if rows_shape and rank2 and ok_b1 and tri7 == rv:
        p7 = row_perm(anchor['rows_shifted'][6])
        gvecs = []
        for c in P7:
            tail = (c + sh7) % D
            head = p7[tail]
            dvec = [0] * D
            dvec[head] += 1
            dvec[tail] -= 1
            g = solve_2d_int(v1, v2, dvec)
            gvecs.append(g)
        if all(g is not None for g in gvecs):
            # unique M with M g_0 = row_0, M g_1 = row_1 (g_0,g_1 independent)
            dg = det2(gvecs[0], gvecs[1])
            if dg:
                # columns of M from Cramer on the transposed system
                num_a = rows[0][0] * gvecs[1][1] - rows[1][0] * gvecs[0][1]
                num_b = rows[1][0] * gvecs[0][0] - rows[0][0] * gvecs[1][0]
                num_c = rows[0][1] * gvecs[1][1] - rows[1][1] * gvecs[0][1]
                num_d = rows[1][1] * gvecs[0][0] - rows[0][1] * gvecs[1][0]
                if all(n % dg == 0 for n in (num_a, num_b, num_c, num_d)):
                    Ma, Mb = num_a // dg, num_b // dg
                    Mc, Md = num_c // dg, num_d // dg
                    detM = Ma * Md - Mb * Mc
                    img2 = (Ma * gvecs[2][0] + Mb * gvecs[2][1],
                            Mc * gvecs[2][0] + Md * gvecs[2][1])
                    c2_ok = abs(detM) == 1 and list(img2) == rows[2]
                    c2_detail = (f'g={gvecs}, M=[[{Ma},{Mb}],[{Mc},{Md}]], '
                                 f'det {detM}, M g_2 = {img2}')
                else:
                    c2_detail = f'M not integral for g={gvecs}'
            else:
                c2_detail = f'g_0, g_1 dependent: {gvecs}'
        else:
            c2_detail = f'triple increments not in carrier span: {gvecs}'
    else:
        c2_detail = 'prerequisite (rows shape / basis / triple) failed'
    ck.check('C2 rows = unimodular image of the terminal triple increments '
             '(single M, det +-1, all three colors)', c2_ok, c2_detail)

    # ----- (C3) structural permutation / signs -----
    ck.check('C3a permutation is a permutation of {0,1,2}',
             sorted(perm) == [0, 1, 2], str(perm))
    ck.check('C3b signs are all +-1', len(signs) == 3
             and all(s in (-1, 1) for s in signs), str(signs))

    # ----- (C4) canonical standard-block datum -----
    ck.check('C4 (rows, permutation, signs) equal the standard terminal-block '
             'alignment shared with the published D5/D7 anchors',
             rows == CANONICAL_ROWS and perm == CANONICAL_PERMUTATION
             and signs == CANONICAL_SIGNS,
             f'rows {rows}, perm {perm}, signs {signs}')

    # ----- (C5) signs vs recomputed terminal closing carries -----
    lams = terminal_closing_lambdas(anchor)
    lam_ok = (lams is not None and all(v in (-1, 1) for v in lams)
              and (signs == [-v for v in lams] or signs == list(lams)))
    ck.check('C5 signs == +-(recomputed stage-7 unit closing carries of colors '
             f'{P7})', lam_ok, f'lambda = {lams}, signs = {signs}')

    # ----- (C6) terminal block semantics on (Z/m)^2 -----
    perm_valid = sorted(perm) == [0, 1, 2]
    for m in BLOCK_MODULI:
        maps = [return_map(m, i) for i in range(3)]
        single = [is_single_cycle(maps[i], m * m) for i in range(3)]
        ck.check(f'C6a m={m}: returns F_0,F_1,F_2 are single {m * m}-cycles',
                 all(single), str(single))
        if m == 4:
            orb_ok = True
            for i in range(3):
                z = (0, 0)
                orb = [z]
                for _ in range(15):
                    z = maps[i][z]
                    orb.append(z)
                if orb != M4_PRINTED_ORBITS[i]:
                    orb_ok = False
            ck.check('C6b m=4: orbits equal the printed table of '
                     'lem:terminal-m4-finite-check', orb_ok)
            # marked-parent pair (F_1, F_2) with C_4
            C = M4_SELECTOR
            Cset = set(C)
            F1, F2 = maps[1], maps[2]
            F2inv = {v: k for k, v in F2.items()}
            tab_ok = True
            for c in C:
                sig, head, s1, s2 = M4_TABLE[c]
                if F2inv[F1[c]] != sig or F1[c] != head:
                    tab_ok = False
                if first_return_to(F1, Cset, c) != s1:
                    tab_ok = False
                if first_return_to(F2, Cset, c) != s2:
                    tab_ok = False
            ck.check('C6c m=4: (F_1,F_2) marked-parent table '
                     '(sigma, common heads, +-2 successors)', tab_ok)
            G = {z: (F2[z] if z in Cset else F1[z]) for z in F1}
            H = {z: (F1[z] if z in Cset else F2[z]) for z in F2}
            ck.check('C6d m=4: switched returns cyclic; |C_4| = 3 unit mod 4',
                     is_single_cycle(G, 16) and is_single_cycle(H, 16)
                     and gcd(3, 4) == 1)
        else:
            if not perm_valid:
                ck.check(f'C6b m={m}: interlacing selector for marked pair',
                         False, 'invalid permutation')
                continue
            a, b = perm[0], perm[1]
            C = interlacing_selector(m)
            L = m - 1
            Cset = set(C)
            Fa, Fb = maps[a], maps[b]
            Fbinv = {v: k for k, v in Fb.items()}
            sig_ok = all(Fbinv[Fa[C[j]]] == C[(j + 1) % L] for j in range(L))
            sa_ok = all(first_return_to(Fa, Cset, C[j]) == C[(j + 2) % L]
                        for j in range(L))
            sb_ok = all(first_return_to(Fb, Cset, C[j]) == C[(j - 2) % L]
                        for j in range(L))
            ck.check(f'C6b m={m}: marked pair (F_{a},F_{b}) selector C_m: '
                     'sigma advance +1, successors +2/-2',
                     sig_ok and sa_ok and sb_ok,
                     f'sigma {sig_ok}, s_a {sa_ok}, s_b {sb_ok}')
            ck.check(f'C6c m={m}: |C_m| = {L} is a unit mod {m}',
                     gcd(L, m) == 1)
            G = {z: (Fb[z] if z in Cset else Fa[z]) for z in Fa}
            H = {z: (Fa[z] if z in Cset else Fb[z]) for z in Fb}
            ck.check(f'C6d m={m}: both switched returns single {m * m}-cycles',
                     is_single_cycle(G, m * m) and is_single_cycle(H, m * m))
    return ck

# ----------------------------------------------------------------------
# negative controls (audit experiment)

def corruption_matrix():
    """name -> mutator(frame_cert) applied to a deep copy."""
    def set_al(key, value):
        def f(fr):
            fr['terminal_alignment'][key] = value
        return f

    def rows_swap(fr):
        r = fr['terminal_alignment']['rows']
        r[1], r[2] = r[2], r[1]

    def basis_corrupt(fr):
        fr['terminal_alignment']['basis_edges'] = ['05', '01']

    return {
        'rows: first row zeroed': set_al('rows', [[0, 0], [1, 1], [0, -1]]),
        'rows: sum broken': set_al('rows', [[-1, 0], [1, 1], [0, 1]]),
        'rows: swap rows 2,3': rows_swap,
        'rows: doubled (non-primitive)': set_al('rows', [[-2, 0], [2, 2], [0, -2]]),
        'rows: sign flip of row 1': set_al('rows', [[1, 0], [1, 1], [0, -1]]),
        'rows: garbage': set_al('rows', [[5, 7], [3, 3], [2, 9]]),
        'permutation: not a permutation': set_al('permutation', [0, 0, 1]),
        'permutation: swapped (1,0,2)': set_al('permutation', [1, 0, 2]),
        'signs: all +1': set_al('signs', [1, 1, 1]),
        'signs: out of range': set_al('signs', [2, 1, -1]),
        'signs: single flip (1,-1,-1)': set_al('signs', [1, -1, -1]),
        'root_vertices: (6,0,2)': set_al('root_vertices', [6, 0, 2]),
        'height_shift: 5': set_al('height_shift', 5),
        'basis_edges: ("05","01")': basis_corrupt,
        'chronological triple: (8,2,4)':
            set_al('terminal_triple_chronological', [8, 2, 4]),
    }


def self_test(frame, anchor):
    print('=== self-test: pristine certificate must PASS ===')
    base = verify(copy.deepcopy(frame), anchor, quiet=True)
    ok_base = not base.failures
    print(f"  pristine: {'PASS' if ok_base else 'FAIL'} "
          f"({base.total - len(base.failures)}/{base.total})")
    print('=== self-test: corruption matrix (each must FAIL) ===')
    all_ok = ok_base
    for name, mut in corruption_matrix().items():
        fr = copy.deepcopy(frame)
        mut(fr)
        res = verify(fr, anchor, quiet=True)
        caught = bool(res.failures)
        all_ok = all_ok and caught
        first = res.failures[0][0] if res.failures else '-'
        print(f"  [{'CAUGHT' if caught else 'MISSED'}] {name}"
              + (f"  (first failing check: {first})" if caught else ''))
    print()
    print('SELF-TEST RESULT:', 'OK' if all_ok else 'FAILED')
    return all_ok


def main(argv):
    frame = json.loads(FRAME_CERT.read_text())
    anchor = json.loads(ANCHOR_CERT.read_text())
    if '--self-test' in argv:
        return 0 if self_test(frame, anchor) else 1
    print('=== D9 terminal A2 block verification ===')
    ck = verify(frame, anchor)
    print()
    print(f'RESULT: {ck.total - len(ck.failures)}/{ck.total} checks passed'
          + (f', {len(ck.failures)} FAILED' if ck.failures else ''))
    for name, detail in ck.failures:
        print(f'  FAILED: {name}' + (f'  ({detail})' if detail else ''))
    return 1 if ck.failures else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
