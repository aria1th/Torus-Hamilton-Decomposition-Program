#!/usr/bin/env python3
"""Numeric gate for the `oldGensSpec` chain-field extension (G5a):
the span structure of paper lemma `lem:growth-old-generator-invariant`
(/data/angel/repos/etc/even_modulus_rewrite_20260610/subtex/high_even_growth.tex,
with `lem:chain-old-span` of subtex/high_even_chain_datum.tex and
`def:growth-midpoint-translate`), checked against the ACTUAL chain-field
literals of `EvenV11/V28Hard/HEDBaseWitnesses.lean` (`hedWitness74/76`,
chained 7->9 chart, labels in Z_9) and the ACTUAL old-line incidences of the
two dimension-7 base blobs (D7_m4_seed.json / D7_m6_seed.json).

Subcommands
  --span-gate          parts (a)+(b): chain-field extraction cross-check and
                       the span/discharge clauses, both bases; JSON summary.
  --new-color-replay   part (c), the decisive check: build the re-realized
                       chained 7->9 child schedule from the span structure and
                       verify the two leaf returns (new colors 0 and 1 of the
                       Z_9 chart) are single K-cycles.  [--m 4|6]

Conventions (identical to scripts/growth_step_replay.py and the rewrite's
companion verifier): states little-endian radix m; old direction j < 6 adds
e_j, old direction 6 adds nothing.  Chained chart: old label l = (old color
or direction) + 2 in Z_9 \\ {0, 1}; new labels 0, 1; child direction
semantics u_0 = e_6 (leaf0/z0), u_1 = e_7 (leaf1/z1), u_l = e_{l-2} for
2 <= l <= 7, u_8 = 0 (zero step).

VERDICTS (2026-06-10, both bases):

  --span-gate  PASS with findings.  All extraction clauses (a) PASS: the
    Lean chain-field literals are exactly the four-point-row formulas
    (window, leaf line, quotient direction incl. the triangular identity
    u_0 - u_8 = (u_0 - u_2) + (u_2 - u_8) in Z^8, cut data, nonzero pairs =
    SymmetricEndpointPairs, carrier = complement of the used labels).  The
    discharge clauses (b) PASS in the GuideLocality-certified collision form
    (G_(r,rho) disjoint from B_r, in fact from the WHOLE window A_r, making
    the translate test vacuous at the certified phases rho = 1, 5).
    FINDING: the literal midpoint-translate formula of
    def:growth-midpoint-translate (centers = midpoints i_lam = lam+(i-j)/2,
    j_lam = lam-(i-j)/2) is NOT discharged by the certified phases: at
    rho = 1 row 1 the old differences {2, 7} land nonzero on (0,7)/(7,0)
    (center 8 in G), and at rho = 5 row 2 the differences {1, 3, 6, 8} land
    nonzero on (2,1)/(2,8)/(8,2)/(1,2) (centers 5, 6 in G) -- at BOTH bases
    (the m=4 ledger saturates all 42 ordered old-label pairs; the m=6 ledger
    has 6 pairs with differences {1,2,3,6,7,8}).  The Lean formalization
    (GuideLocality, audited) uses the endpoint-collision form throughout, so
    the formal chain is consistent; the paper text's midpoint formula is the
    loose spot.

  --new-color-replay  FAIL at BOTH bases (the decisive 1c check): see
    check_oldgens_span_newcolor.py for the three machine obstructions
    (alphabet confinement of the displayed row words; non-extendability +
    RF2 failure of the canonical Z_7 -> Z_9 \\ {0,1} shift transport;
    the (z0,z1)-monodromy order bound killing every z-independent child).
    Consequence: GrowthRealization cannot be closed from the displayed
    chained rows over these bases as the paper states them; the witness
    needs new-color row data beyond `oldGens`/span clauses.  Reported
    upstream; the Lean oldGensSpec extension is gated OFF until the paper
    construction is repaired.

Stdlib only.
"""
from __future__ import annotations
from array import array
import json, sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from growth_step_replay import load_seed, dec, enc, cycle_lengths

D9 = 9
HALF = 5            # 2^{-1} in Z_9

# ---------------------------------------------------------------------------
# The chain-field literals of HEDBaseWitnesses.lean (chainedChainFields):
# rows are GuideLocality's audited chained tables verbatim.
# ---------------------------------------------------------------------------
LEAN_ROWS = [
    dict(s=0, delta=2, support=[0, 2, 7, 5], leafLine=(0, 2),
         quotientGen=(7, 5), oldGens=[(7, 2), (2, 7), (7, 5), (5, 7)],
         phase=1, boundary=[2, 7, 5], cutVisible=7, cutZeroSide=[2, 5]),
    dict(s=1, delta=1, support=[1, 2, 0, 8], leafLine=(1, 2),
         quotientGen=(2, 8), oldGens=[(2, 8), (8, 2)],
         phase=5, boundary=[2, 8], cutVisible=2, cutZeroSide=[8]),
]
NEW_LABELS = (0, 1)
CARRIER = [3, 4, 6]
OLD_LABELS = [2, 3, 4, 5, 6, 7, 8]

def u_vec(label: int):
    """child vector of a Z_9 chart label (length-8 integer tuple)."""
    v = [0] * 8
    if label == 0:
        v[6] = 1
    elif label == 1:
        v[7] = 1
    elif label != 8:
        v[label - 2] = 1
    return tuple(v)

def pair_vec(p):
    return tuple(a - b for a, b in zip(u_vec(p[0]), u_vec(p[1])))

def z_span_rank(vecs):
    """rank of an integer span (fraction-free Gaussian elimination)."""
    rows = [list(v) for v in vecs if any(v)]
    rank = 0
    ncol = 8
    r = 0
    for col in range(ncol):
        piv = next((i for i in range(r, len(rows)) if rows[i][col] != 0), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        for i in range(len(rows)):
            if i != r and rows[i][col] != 0:
                a, b = rows[r][col], rows[i][col]
                rows[i] = [b_ * a - a_ * b for a_, b_ in zip(rows[r], rows[i])]
        r += 1
        rank += 1
    return rank

# ---------------------------------------------------------------------------
# part (a): extraction cross-check of the Lean literals against the
# four-point row formulas of def:four-point-growth-row.
# ---------------------------------------------------------------------------

def sym_pairs(visible, zeros):
    out = []
    for z in zeros:
        out += [(visible, z), (z, visible)]
    return out

def check_extraction(res):
    for r, row in enumerate(LEAN_ROWS):
        s, d = row['s'], row['delta']
        win = [s % D9, (s + d) % D9, (s - d) % D9, (s - 2 * d) % D9]
        res.clause(f'row{r}.support == [s, s+d, s-d, s-2d] = {win}',
                   row['support'] == win)
        res.clause(f'row{r}.leafLine == (s, s+d)',
                   row['leafLine'] == (s % D9, (s + d) % D9))
        if r == 0:
            res.clause('row0.quotientGen == (s-d, s-2d) (the raw quotient edge)',
                       row['quotientGen'] == ((s - d) % D9, (s - 2 * d) % D9))
        else:
            # triangular row: the raw local edge is (s-d, s-2d) = (0, 8); the
            # quotient direction is u_2 - u_8 via u_0 - u_8 = (u_0-u_2)+(u_2-u_8)
            raw = ((s - d) % D9, (s - 2 * d) % D9)
            res.clause('row1 raw local edge (s-d, s-2d) == (0, 8)', raw == (0, 8))
            res.clause('row1.quotientGen == (leafLine0.snd, s-2d) = (2, 8)',
                       row['quotientGen'] == (LEAN_ROWS[0]['leafLine'][1], raw[1]))
            lhs = pair_vec(raw)
            rhs = tuple(a + b for a, b in
                        zip(pair_vec(LEAN_ROWS[0]['leafLine']), pair_vec(row['quotientGen'])))
            res.clause('triangular identity u_0 - u_8 = (u_0 - u_2) + (u_2 - u_8) '
                       'in the child lattice Z^8', lhs == rhs)
        # cut data: visible = quotient tail, zero side = window old labels minus it
        res.clause(f'row{r}.cutVisible == quotientGen.fst',
                   row['cutVisible'] == row['quotientGen'][0])
        old_in_win = [l for l in row['support'] if l in OLD_LABELS]
        # for row 1 the earlier leaf label 0 is in the window but is not an
        # old boundary label (it is L_0's leaf, handled by the triangular lemma)
        zside = [l for l in old_in_win if l != row['cutVisible']]
        res.clause(f'row{r}.cutZeroSide == window old labels minus visible = {zside}',
                   sorted(row['cutZeroSide']) == sorted(zside))
        res.clause(f'row{r}.boundary == {{visible}} + zeroSide',
                   sorted(row['boundary']) == sorted([row['cutVisible']] + row['cutZeroSide']))
        res.clause(f'row{r}.oldGens == SymmetricEndpointPairs(visible, zeroSide)',
                   row['oldGens'] == sym_pairs(row['cutVisible'], row['cutZeroSide']))
        res.clause(f'row{r}.boundary subset of support',
                   all(b in row['support'] for b in row['boundary']))
    used = sorted({l for row in LEAN_ROWS for l in row['support'] if l in OLD_LABELS})
    res.clause('carrier {3,4,6} == old labels minus used row labels '
               f'(used={used})', sorted(CARRIER) ==
               sorted(set(OLD_LABELS) - set(used)))
    res.clause('newLabels == (0, 1), oldLabel i -> i+2 covers Z9 minus {0,1}',
               NEW_LABELS == (0, 1) and
               sorted((i + 2) % D9 for i in range(7)) == OLD_LABELS)

# ---------------------------------------------------------------------------
# part (b): the span / projection-discharge clauses against the base blobs.
# ---------------------------------------------------------------------------

def old_incidences(m):
    """the base blob's old-line incidence ledger in the chained chart:
    oriented pairs (actual head label, skeleton head label) over all reads
    that deviate from the layer's chronological skeleton c -> c + s_t, plus
    the set of differences (i - j) mod 9 present."""
    d, dirs = load_seed(m)
    K = m ** (d - 1)
    seed = json.loads((Path('/data/angel/repos/etc/even_modulus_rewrite_20260610'
                            '/certificates/certs') / f'D7_m{m}_seed.json').read_text())
    shifts = seed['layer_shifts']
    pairs = set()
    for t in range(m):
        for c in range(d):
            default = (c + shifts[t]) % d
            col = dirs[t][c]
            for x in range(K):
                a = col[x]
                if a != default:
                    pairs.add((a + 2, default + 2))
    diffs = sorted({(i - j) % D9 for (i, j) in pairs})
    return pairs, diffs

def theta(row, label):
    """the local cut of tab:growth-row-projection-data on the window."""
    return 1 if label == row['cutVisible'] else 0

def guide_centers(row):
    rho, d = row['phase'], row['delta']
    return [(rho - d) % D9, rho % D9, (rho + d) % D9]

def landings_midpoint(row, diffs):
    """def:growth-midpoint-translate literal reading: for an old difference
    i-j and center lam, the translate has endpoints lam +- (i-j)/2; it is
    tested if both endpoints lie in the window."""
    out = []
    for diff in diffs:
        h = (diff * HALF) % D9
        for lam in guide_centers(row):
            i_l, j_l = (lam + h) % D9, (lam - h) % D9
            if i_l in row['support'] and j_l in row['support']:
                out.append((diff, lam, (i_l, j_l), theta(row, i_l) - theta(row, j_l)))
    return out

def landings_endpoint(row, pairs):
    """the GuideLocality-certified reading (the value-by-value audited form):
    a guide center can produce a nonzero old value only by colliding with an
    ENDPOINT of a nonzero pair, i.e. only when it lies in the boundary set;
    operationally: translate the old generator with TAIL at the center
    (endpoints lam, lam + (i-j))."""
    out = []
    for (i, j) in pairs:
        diff = (i - j) % D9
        for lam in guide_centers(row):
            i_l, j_l = (lam + diff) % D9, lam
            if i_l in row['support'] and j_l in row['support']:
                out.append((diff, lam, (i_l, j_l), theta(row, i_l) - theta(row, j_l)))
    return out

def leaf_pairs_before(r):
    out = []
    for r2 in range(r):
        a, b = LEAN_ROWS[r2]['leafLine']
        out += [(a, b), (b, a)]
    return out

def check_span(res, m):
    pairs, diffs = old_incidences(m)
    res.info(f'm={m}: old-incidence ledger has {len(pairs)} oriented pairs, '
             f'differences mod 9 present: {diffs}')
    all_pairs = len(pairs) == 42
    res.info(f'm={m}: ledger {"saturates" if all_pairs else "does NOT saturate"} '
             'all 42 ordered old-label pairs')
    # span accounting (lem:chain-old-span at lattice level, recorded honestly)
    h_in_rank = z_span_rank([pair_vec(p) for p in pairs])
    for r, row in enumerate(LEAN_ROWS):
        gens = [pair_vec(p) for p in row['oldGens']]
        gens += [pair_vec(p) for p in leaf_pairs_before(r)]
        g_rank = z_span_rank(gens)
        res.info(f'm={m} row{r}: rank H_in = {h_in_rank}, '
                 f'rank <oldGens, earlier leaf lines> = {g_rank} '
                 '(the chain-datum span is the WINDOW-LOCAL flag, not the full '
                 'lattice: the row only ever tests window translates)')
    # the discharge clauses
    for r, row in enumerate(LEAN_ROWS):
        G = guide_centers(row)
        res.clause(f'm={m} row{r}: phase boundary-avoiding '
                   f'G_(r,rho)={G} disjoint from B_r={row["boundary"]} '
                   '(chainedHighEvenBoundaryAvoidingPhaseChoice_spec reading)',
                   not set(G) & set(row['boundary']))
        res.clause(f'm={m} row{r}: guide centers avoid the WHOLE window '
                   f'G_(r,rho)={G} disjoint from A_r={row["support"]} '
                   '(the stronger fact making the endpoint-translate test '
                   'vacuous at the certified phases)',
                   not set(G) & set(row['support']))
        exempt = set(leaf_pairs_before(r))
        # endpoint (audited) reading
        lend = landings_endpoint(row, pairs)
        bad_e = [l for l in lend if l[3] != 0 and l[2] not in exempt]
        leaf_e = [l for l in lend if l[3] != 0 and l[2] in exempt]
        res.info(f'm={m} row{r}: endpoint reading tested {len(lend)} '
                 f'in-window translates; zero-valued {sum(1 for l in lend if l[3] == 0)}, '
                 f'leaf-exempt {len(leaf_e)}, offending {len(bad_e)}')
        res.clause(f'm={m} row{r}: ENDPOINT-translate discharge: every tested '
                   'old translate has zero cut value (earlier leaf lines exempt, '
                   'lem:triangular-two-leaf)'
                   + (' [vacuous: no in-window translate at the certified phase]'
                      if not lend else ''),
                   not bad_e,
                   detail=f'nonzero non-exempt landings: {bad_e[:6]}'
                   + (f' ... leaf-line landings (expected, triangular): {leaf_e[:4]}'
                      if leaf_e else ''))
        # midpoint (def:growth-midpoint-translate literal) reading
        lmid = landings_midpoint(row, diffs)
        bad_m = [l for l in lmid if l[3] != 0 and l[2] not in exempt]
        leaf_m = [l for l in lmid if l[3] != 0 and l[2] in exempt]
        res.clause(f'm={m} row{r}: MIDPOINT-translate discharge '
                   '(literal def:growth-midpoint-translate reading)',
                   not bad_m,
                   detail=f'nonzero non-exempt landings (diff, center, landing, value): '
                   f'{bad_m[:6]}'
                   + (f' ; leaf-line landings (exempt): {leaf_m[:4]}' if leaf_m else ''),
                   severity='finding')
        # quotient functional normalisation on the row's own plane.  Row 0 is
        # the plain four-point normalisation Theta(e) = 0, Theta(g) = 1; for
        # the triangular row 1 the leaf-line kill is NOT a label-cut statement
        # (it is the formalized triangular kernel,
        # EvenV11.HighEvenSuccessorBridge.triangularKernel*), so the checkable
        # normalisation there is theta(new leaf s) = 0 and Theta(g_1) = 1.
        e_pair, g_pair = row['leafLine'], row['quotientGen']
        if r == 0:
            res.clause(f'm={m} row{r}: cut normalisation Theta(e_0) = 0, '
                       'Theta(g_0) = 1',
                       theta(row, e_pair[0]) - theta(row, e_pair[1]) == 0 and
                       theta(row, g_pair[0]) - theta(row, g_pair[1]) == 1)
        else:
            res.clause(f'm={m} row{r}: triangular cut normalisation '
                       'theta(s) = 0, Theta(g_1) = 1, raw edge (0,8) on the '
                       'zero side',
                       theta(row, row['s']) == 0 and
                       theta(row, g_pair[0]) - theta(row, g_pair[1]) == 1 and
                       theta(row, 0) == 0 and theta(row, 8) == 0)

# ---------------------------------------------------------------------------
# result collector
# ---------------------------------------------------------------------------

class Res:
    def __init__(self):
        self.fails = 0
        self.findings = []
        self.records = []
    def clause(self, name, ok, detail='', severity='gate'):
        tag = 'PASS' if ok else ('FINDING' if severity == 'finding' else 'FAIL')
        print(f'  [{tag}] {name}' + ('' if ok or not detail else f'\n          {detail}'))
        self.records.append(dict(name=name, ok=bool(ok), detail=detail if not ok else '',
                                 severity=severity))
        if not ok:
            if severity == 'finding':
                self.findings.append(name + ' :: ' + detail)
            else:
                self.fails += 1
    def info(self, msg):
        print(f'  [info] {msg}')
        self.records.append(dict(info=msg))

def span_gate():
    res = Res()
    print('=== oldGensSpec numeric gate: part (a), chain-field extraction ===')
    check_extraction(res)
    for m in (4, 6):
        print(f'=== part (b), span/discharge clauses at the (7,{m}) base ===')
        check_span(res, m)
    print()
    verdict = 'PASS' if res.fails == 0 else 'FAIL'
    print(f'=== span-gate verdict: {verdict} '
          f'({res.fails} hard failure(s), {len(res.findings)} recorded finding(s)) ===')
    for f in res.findings:
        print(f'  finding: {f}')
    out = Path(__file__).resolve().parent / 'oldgens_span_gate_summary.json'
    out.write_text(json.dumps(dict(verdict=verdict, fails=res.fails,
                                   findings=res.findings, records=res.records),
                              indent=1))
    print(f'[json] {out}')
    return res.fails == 0

# ---------------------------------------------------------------------------
# part (c): the decisive new-color replay (defined in a second pass below)
# ---------------------------------------------------------------------------

def main():
    argv = sys.argv[1:]
    m = 4
    if '--m' in argv:
        m = int(argv[argv.index('--m') + 1])
    if '--new-color-replay' in argv:
        from check_oldgens_span_newcolor import new_color_replay
        ok = new_color_replay(m)
        sys.exit(0 if ok else 1)
    ok = span_gate()
    sys.exit(0 if ok else 1)

if __name__ == '__main__':
    main()
