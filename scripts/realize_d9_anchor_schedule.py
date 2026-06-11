#!/usr/bin/env python3
"""End-to-end realization gate for the D9 all-even proof bundle
(vendor/d9_all_even_proof_bundle_20260611): construct the D9(m) root-flat
layer schedule that the anchor-schedule realization criterion describes,
directly from the bundle certificates, and verify RF1/RF2/RF3 + marked
structure.  This is the gate of docs/D9_ROUTE_REALIGNMENT_20260611.md SS4:
the bundle suite verifies that the certificates satisfy the CRITERION
CLAUSES; this script tests the unverified implication
"criterion clauses => actual schedule".

CONVENTIONS (mirroring scripts/reconstruct_high_even_anchor_schedules.py,
the D5-fan / D7-two-rail gate that PASSED, and the v28 paper's
def:phase-normalized-realization-rule):
  * state x in (Z/m)^8 = first 8 coordinates of K_{9,m} (coordinate 8 is
    the dropped zero-sum coordinate); direction l<8 adds e_l, direction 8
    adds nothing; edge vector alpha(a,b) = u_b - u_a in this chart;
  * a schedule is m layer rows; the base row of a layer with type t in Z/9
    is the constant Latin row  c |-> (c+t) % 9;
  * stage r (shift s_r) substitutes, for the colors P of each physical
    part, the shifted stage row (label head_r(c) = sigma_r((c+s_r)%9))
    on an affine support  b_{r,P} + span_m(alpha_e : e in SUPP), with
    b_{r,P} the LOW-MOD placement basepoint and SUPP either the printed
    support forest M_{r,P} (rank-countdown tower, the D5/D7 reading that
    passed: reading R1) or the active edge set A_{r,P} (the literal
    coset the low-mod certificate verifies: reading R2);
  * stage r is placed at the layer of height s_r mod m (the certificate's
    own 'height' field; for m in {4,6,8} several stages FOLD onto one
    layer, the situation the low-mod note addresses);
  * the terminal triple (6,0,1) at stage 7 is realized as the omega_m
    terminal A2 block (shared-point convention) on the certified terminal
    carrier plane  q_T + <06,01>, carrier colors (8,2,3).

INTERPRETIVE CHOICES (everything the proof notes do not pin down), each
logged in the output:
  (C1) layer base types at folded heights: a layer has ONE base type
       t_h in Z/9; we enumerate every designation t_h in {s_r : r folded
       at h} (any other choice mismatches every stage at the row);
  (C2) support span: R1 = full printed forest M (load-bearing in the
       D5/D7 gate), R2 = active edges only (the literal low-mod coset);
  (C3) two fallback readings of a folded substitution are also tested so
       the verdict is not an artifact of one reading:
       R3 = re-based switch  c+t_h -> T_r(c)+t_h  (chronological packet
            re-shifted to the row type; row-Latin by construction), and
       R4 = full-row switch (all nine colors take stage row sigma_r on
            the support);
  (C4) terminal block: omega_m word, eta=0 (shared point), phi=(0,0),
       slot assignment (6,0,1), exactly the conventions that passed the
       D5/D7 gate.

Stdlib only.  Usage:
  python3 scripts/realize_d9_anchor_schedule.py --m 4  --verify
  python3 scripts/realize_d9_anchor_schedule.py --m 6  --verify   (ledger + witnesses)
  python3 scripts/realize_d9_anchor_schedule.py --m 10 --verify   (ledger; see STOP note)
"""
from __future__ import annotations
import argparse, collections, itertools, json, sys
from array import array
from pathlib import Path

D = 9
R8 = D - 1
HERE = Path(__file__).resolve().parent
BUNDLE = HERE.parent / 'vendor' / 'd9_all_even_proof_bundle_20260611'

# ---------------------------------------------------------------- certificates

def norm(e):
    if isinstance(e, str):
        e = (int(e[0]), int(e[1]))
    a, b = e
    return (a, b) if a < b else (b, a)

def load_certs():
    active = json.loads((BUNDLE / 'certificates' / 'd9_active_anchor_candidate_v1.json').read_text())
    low = json.loads((BUNDLE / 'certificates' / 'd9_lowmod_finite_placement_candidate.json').read_text())
    shifts = active['shifts']
    rows = active['rows_shifted']
    perms = []
    for row in rows:
        p = list(range(D))
        a, b, c = row['triple']
        p[a] = b; p[b] = c; p[c] = a
        for x, y in row['pairs']:
            p[x] = y; p[y] = x
        perms.append(tuple(p))
    supports = active['supports_unshifted']
    act = active['active_data']
    return dict(active=active, low=low, shifts=shifts, rows=rows, perms=perms,
                supports=supports, active_data=act)

def active_edges(C, stage0, part_index):
    """Active edge set of (stage, part), as in the bundle's lowmod verifier."""
    if part_index == 0:
        if stage0 <= 5:
            return [norm(e) for e in C['active_data'][stage0]['parts'][0]['active_edges']]
        return [norm(e) for e in C['supports'][stage0]['parts'][0]['M']]
    return [norm(C['rows'][stage0]['pairs'][part_index - 1])]

# -------------------------------------------------------------------- geometry

def alpha_vec(a, b, m):
    """u_b - u_a in the 8-coordinate chart (coordinate 8 dropped)."""
    v = [0] * R8
    if a < R8: v[a] = (v[a] - 1) % m
    if b < R8: v[b] = (v[b] + 1) % m
    return tuple(v)

def enc(coords, m):
    out = 0; p = 1
    for a in coords:
        out += (a % m) * p; p *= m
    return out

def dec(x, m):
    out = []
    for _ in range(R8):
        out.append(x % m); x //= m
    return out

def point9(x, m):
    co = dec(x, m)
    return co + [(-sum(co)) % m]

def build_add(m):
    K = m ** R8
    powm = [m ** i for i in range(R8)]
    add = []
    for l in range(D):
        arr = array('I', [0]) * K
        for x in range(K):
            if l == R8:
                arr[x] = x
            else:
                digit = (x // powm[l]) % m
                arr[x] = x + powm[l] if digit < m - 1 else x - (m - 1) * powm[l]
        add.append(arr)
    return add

def span_points(base8, edges, m):
    """All points of base + span_m(alpha_e : e in edges), encoded."""
    pts = {tuple(base8)}
    for e in edges:
        v = alpha_vec(*norm(e), m)
        new = set()
        for p in pts:
            cur = list(p)
            for _ in range(m):
                new.add(tuple(cur))
                cur = [(a + b) % m for a, b in zip(cur, v)]
        pts = new
    return {enc(p, m) for p in pts}

def cycle_lengths(perm):
    N = len(perm); seen = bytearray(N); lens = []
    for i in range(N):
        if not seen[i]:
            x = i; l = 0
            while not seen[x]:
                seen[x] = 1; l += 1; x = perm[x]
            lens.append(l)
    return sorted(lens, reverse=True)

# ------------------------------------------------------- structural ledgers

def forests_and_isolates(C):
    """Per-color final forest edges (tail_r, head_r) and the isolate label."""
    out = {}
    for c in range(D):
        edges = []
        for s, p in zip(C['shifts'], C['perms']):
            tail = (c + s) % D
            edges.append((tail, p[tail]))
        labels = set()
        for a, b in edges:
            labels |= {a, b}
        iso = sorted(set(range(D)) - labels)
        out[c] = dict(edges=edges, isolates=iso)
    return out

def row_budget_ledger(C, m):
    """FACT 1/3: row-count + closing-class budget of the realization rule."""
    shifts = C['shifts']
    F = forests_and_isolates(C)
    closing_classes = sorted({(F[c]['isolates'][0] - c) % D for c in range(D)
                              if len(F[c]['isolates']) == 1})
    by_row = collections.defaultdict(list)
    for r, s in enumerate(shifts, 1):
        by_row[s % m].append((r, s))
    free_rows = [h for h in range(m) if h not in by_row]
    need_rows = len(set(shifts)) + len(closing_classes)
    led = dict(
        m=m,
        stage_shifts=shifts,
        distinct_stage_types=len(set(shifts)),
        closing_classes_needed=closing_classes,
        rows_needed_by_rule=need_rows,
        rows_available=m,
        rule_feasible=(m >= need_rows),
        folded_rows={h: [f'stage{r}(shift {s})' for r, s in v]
                     for h, v in sorted(by_row.items()) if len(v) > 1},
        free_rows=free_rows,
        closing_classes_unhostable=[k for k in closing_classes
                                    if len(free_rows) < 1 or
                                    closing_classes.index(k) >= len(free_rows)],
    )
    return led

def closure_ledger(C, m):
    """FACT 4: is the physical switch vector alpha(tail, head) inside the
    support span?  (Necessary and sufficient for the single-switch layer of
    the realization rule to be bijective, i.e. for RF2.)  Checked as graph
    connectivity of tail~head inside the edge set (exact over Z and Z/m,
    since support forests are forests => saturated lattices)."""
    bad = []
    for stage0, sup in enumerate(C['supports']):
        s = C['shifts'][stage0]; p = C['perms'][stage0]
        for pi, item in enumerate(sup['parts']):
            M = [norm(e) for e in item['M']]
            A = active_edges(C, stage0, pi)
            for c in item['P']:
                tail = (c + s) % D; head = p[tail]
                def connected(edges):
                    par = list(range(D))
                    def find(x):
                        while par[x] != x:
                            par[x] = par[par[x]]; x = par[x]
                        return x
                    for a, b in edges:
                        ra, rb = find(a), find(b)
                        if ra != rb: par[rb] = ra
                    return find(tail) == find(head)
                in_M = connected(M)
                in_A = connected(A)
                if not in_M or not in_A:
                    bad.append(dict(stage=stage0 + 1, part=pi, color=c,
                                    tail=tail, head=head,
                                    M=[f'{a}{b}' for a, b in M],
                                    active=[f'{a}{b}' for a, b in A],
                                    in_span_M=in_M, in_span_active=in_A,
                                    note=('terminal triple: realized by the A2 block, '
                                          'not a switch — not an RF2 obstruction'
                                          if stage0 == 6 and pi == 0 else
                                          'genuine RF2 obstruction for the '
                                          'support-tube switch reading, every m')))
    return bad

# ------------------------------------------------------------ schedule build

TERM_WORDS = dict(default=(0, 1, 2), t02=(2, 1, 0), t12=(0, 2, 1),
                  t01=(1, 0, 2), chip=(1, 2, 0), chim=(2, 0, 1))

def terminal_word_table(m):
    """omega_m of subtex/terminal_A2_block.tex (verified D5/D7 conventions)."""
    p = (1, 2)
    tab = {}
    lines = [((1, 0), 't02', 'chim', 'chip'),
             ((0, 1), 't12', 'chip', 'chim'),
             ((m - 1, 1), 't01', 'chim', 'chip')]
    for vec, gen, minus, plus in lines:
        for t in range(1, m):
            z = ((p[0] + t * vec[0]) % m, (p[1] + t * vec[1]) % m)
            tab[z] = TERM_WORDS[plus if t == 1 else (minus if t == m - 1 else gen)]
    return tab

def lowmod_entry(C, m):
    data = C['low']['moduli'][str(m)]
    bases = {(o['stage'], o['part_index']): [x % m for x in o['base']]
             for o in data['splice_supports']}
    return data, bases

def terminal_block_patch(C, m, t_term):
    """Terminal A2 block on the certified carrier plane; returns
    {chrono color: {x: label}} plus the block point set."""
    data, _ = lowmod_entry(C, m)
    qT = [x % m for x in data['terminal_carrier']['base']][:R8]
    L = tuple(C['rows'][6]['triple'])             # (6,0,1)
    assert L[1:] == (0, 1)
    v1 = alpha_vec(L[2], L[0], m)                 # step(L0)-step(L2)
    v2 = alpha_vec(L[2], L[1], m)                 # step(L1)-step(L2)
    s7 = C['shifts'][6]
    carrier = [(l - s7) % D for l in L]           # chrono colors (8,2,3)
    tab = terminal_word_table(m)
    out = {c: {} for c in carrier}
    pts = set()
    for z1 in range(m):
        for z2 in range(m):
            q = [(qT[k] + z1 * v1[k] + z2 * v2[k]) % m for k in range(R8)]
            x = enc(q, m)
            pts.add(x)
            w = tab.get((z1, z2))
            if w is None:
                continue
            for i in range(3):
                if w[i] != i:
                    out[carrier[i]][x] = L[w[i]]
    return out, pts, carrier, L

def build_schedule(C, m, designation, reading):
    """dirs[h][c] bytearray of labels; also support metadata per row."""
    K = m ** R8
    data, bases = lowmod_entry(C, m)
    heights = {}
    for o in data['splice_supports']:
        heights[o['stage']] = o['height']
    row_types = dict(designation)               # h -> t_h in Z/9
    dirs = [[bytearray([(c + row_types.get(h, 0)) % D]) * K for c in range(D)]
            for h in range(m)]
    row_meta = [collections.defaultdict(list) for _ in range(m)]  # x -> [(stage, part)]
    for stage0 in range(7):
        r = stage0 + 1
        s = C['shifts'][stage0]; p = C['perms'][stage0]
        h = heights[r]
        t_h = row_types[h]
        for pi, item in enumerate(C['supports'][stage0]['parts']):
            if r == 7 and pi == 0:
                continue                          # terminal triple -> A2 block
            edges = ([norm(e) for e in item['M']] if reading in ('R1', 'R3', 'R4')
                     else active_edges(C, stage0, pi))
            base8 = bases[(r, pi)][:R8]
            pts = span_points(base8, edges, m)
            for x in pts:
                row_meta[h][x].append((r, pi))
            if reading in ('R1', 'R2'):
                for c in item['P']:
                    head = p[(c + s) % D]
                    arr = dirs[h][c]
                    for x in pts:
                        arr[x] = head
            elif reading == 'R3':
                for c in item['P']:
                    head = (p[(c + s) % D] - s + t_h) % D
                    arr = dirs[h][c]
                    for x in pts:
                        arr[x] = head
            elif reading == 'R4':
                for c in range(D):
                    head = p[(c + s) % D]
                    arr = dirs[h][c]
                    for x in pts:
                        arr[x] = head
    # terminal A2 block at the stage-7 row
    h7 = heights[7]
    patch, tpts, carrier, L = terminal_block_patch(C, m, row_types[h7])
    for x in tpts:
        row_meta[h7][x].append((7, 'terminal_block'))
    for c, pat in patch.items():
        arr = dirs[h7][c]
        for x, lab in pat.items():
            arr[x] = lab
    return dirs, row_meta, row_types

# ------------------------------------------------------------------ verifier

def verify_schedule(C, m, dirs, row_meta, max_witnesses=5):
    K = m ** R8
    add = build_add(m)
    res = dict(rf1=True, rf2=True, rf3=True)
    # RF1: every row Latin at every point
    rf1_fail = 0; rf1_wit = []
    for h in range(m):
        cols = dirs[h]
        for x in range(K):
            labs = [cols[c][x] for c in range(D)]
            if len(set(labs)) != D:
                rf1_fail += 1
                if len(rf1_wit) < max_witnesses:
                    cnt = collections.Counter(labs)
                    clash = sorted(l for l, k in cnt.items() if k > 1)
                    rf1_wit.append(dict(
                        row=h, x=x, point=point9(x, m),
                        supports_here=[str(t) for t in row_meta[h].get(x, [])],
                        labels_by_color=labs, repeated_labels=clash,
                        missing_labels=sorted(set(range(D)) - set(labs))))
    res['rf1'] = (rf1_fail == 0)
    res['rf1_violating_points'] = rf1_fail
    res['rf1_witnesses'] = rf1_wit
    # RF2: per-layer bijectivity per color
    rf2_fail = []; layer_maps = {}
    for h in range(m):
        for c in range(D):
            seen = bytearray(K)
            arr = array('I', [0]) * K
            dc = dirs[h][c]
            ok = True
            for x in range(K):
                y = add[dc[x]][x]
                arr[x] = y
                if seen[y]:
                    ok = False
                seen[y] = 1
            if not ok:
                rf2_fail.append(dict(row=h, color=c))
            layer_maps[(h, c)] = arr
    res['rf2'] = not rf2_fail
    res['rf2_failures'] = rf2_fail
    # RF3: returns (only meaningful where RF2 holds; reported regardless)
    lens_by_color = {}
    for c in range(D):
        Rr = array('I', range(K))
        for h in range(m):
            P = layer_maps[(h, c)]
            for x in range(K):
                Rr[x] = P[Rr[x]]
        if any(d['color'] == c for d in rf2_fail):
            lens_by_color[c] = 'n/a (layer not bijective)'
        else:
            lens = cycle_lengths(list(Rr))
            lens_by_color[c] = lens if len(lens) <= 8 else lens[:4] + [f'...({len(lens)} cycles)']
            if lens != [K]:
                res['rf3'] = False
    if rf2_fail:
        res['rf3'] = False
    res['return_cycle_lengths'] = {str(c): v for c, v in lens_by_color.items()}
    return res

def marked_structure_checks(C, m, reading='R1'):
    """Terminal carrier / reserve plane / 12 sites, plus the clause-gap check:
    intersections of FULL-forest-span supports (the schedule's actual switch
    sets under R1) across distinct stages folded at one height, and of the
    terminal/reserve planes with the full-span supports."""
    data, bases = lowmod_entry(C, m)
    sets = {}
    for o in data['splice_supports']:
        r, pi = o['stage'], o['part_index']
        item = C['supports'][r - 1]['parts'][pi]
        if reading == 'R1':
            edges = [norm(e) for e in item['M']]
        else:
            edges = active_edges(C, r - 1, pi)
        sets[(r, pi)] = (o['height'], span_points(bases[(r, pi)][:R8], edges, m))
    byh = collections.defaultdict(list)
    for key, (h, S) in sets.items():
        byh[h].append((key, S))
    cross = []
    for h, grp in sorted(byh.items()):
        for (k1, S1), (k2, S2) in itertools.combinations(grp, 2):
            if k1[0] == k2[0]:
                continue  # same stage: parts are label-disjoint, overlap harmless for RF1
            inter = S1 & S2
            if inter:
                cross.append(dict(row=h, a=f'r{k1[0]}_p{k1[1]}', b=f'r{k2[0]}_p{k2[1]}',
                                  size=len(inter),
                                  example_point=point9(min(inter), m)))
    qT = [x % m for x in data['terminal_carrier']['base']][:R8]
    Tset = span_points(qT, [norm(e) for e in data['terminal_carrier']['edges']], m)
    qR = [x % m for x in data['reserve_plane']['base']][:R8]
    Rset = span_points(qR, [norm(e) for e in data['reserve_plane']['edges']], m)
    site_pts = set()
    sites_on_plane = True
    for site in data['reserve_sites']:
        pt = tuple(x % m for x in site['point'])
        site_pts.add(pt)
        if enc(list(pt)[:R8], m) not in Rset:
            sites_on_plane = False
    plane_hits = dict(terminal=[], reserve=[])
    for key, (h, S) in sets.items():
        if Tset & S:
            plane_hits['terminal'].append(f'r{key[0]}_p{key[1]} ({len(Tset & S)} pts)')
        if Rset & S:
            plane_hits['reserve'].append(f'r{key[0]}_p{key[1]} ({len(Rset & S)} pts)')
    return dict(
        reserve_sites_distinct=(len(site_pts) == 12),
        reserve_sites_on_plane=sites_on_plane,
        terminal_reserve_disjoint=not (Tset & Rset),
        cross_stage_same_row_full_span_intersections=cross,
        plane_vs_full_span_support_hits=plane_hits)

# ------------------------------------------------------------------- driver

def designations(C, m):
    data, _ = lowmod_entry(C, m)
    by_row = collections.defaultdict(list)
    for o in data['splice_supports']:
        if o['height_shift'] not in [s for _, s in by_row[o['height']]]:
            by_row[o['height']].append((o['stage'], o['height_shift']))
    rows = sorted(by_row)
    choices = [[(h, s) for _, s in by_row[h]] for h in rows]
    for combo in itertools.product(*choices):
        yield dict(combo)

def gate_m4(C, args):
    m = 4
    print('=' * 78)
    print(f'D9 anchor-schedule realization gate, m={m}  (section 4^8 = {4**8})')
    print('=' * 78)
    led = row_budget_ledger(C, m)
    print('\n[structural ledger: realization-rule row budget]')
    for k, v in led.items():
        print(f'  {k} = {v}')
    bad = closure_ledger(C, m)
    n_genuine = sum(1 for b in bad if not (b['stage'] == 7 and b['part'] == 0))
    print(f'\n[switch-closure ledger (all m): physical increment alpha(tail,head) '
          f'in support span?]  violations = {len(bad)} '
          f'({n_genuine} genuine; stage-7 triple is block-realized)')
    for b in bad:
        print(f'  stage {b["stage"]} part {b["part"]} color {b["color"]}: '
              f'edge ({b["tail"]},{b["head"]})  in span(M)={b["in_span_M"]} '
              f'in span(active)={b["in_span_active"]}  M={b["M"]}  [{b["note"]}]')
    report = dict(m=m, section_size=4 ** 8, row_budget_ledger=led,
                  switch_closure_violations=bad, readings={})
    print('\n[interpretive choices]')
    print('  C1: folded-row base type enumerated over the folded stage shifts;')
    print('  C2: spans R1=forest-M (D5/D7 precedent) and R2=active-only (certificate-literal);')
    print('  C3: fallback readings R3 (re-based) and R4 (full-row) also tested;')
    print('  C4: terminal A2 block = omega_m, shared-point, slots (6,0,1), carrier (8,2,3).')

    for reading in (['R1', 'R2', 'R3', 'R4'] if args.all_readings else ['R1', 'R2', 'R3', 'R4']):
        print(f'\n----- reading {reading} -----')
        best = None
        for di, desig in enumerate(designations(C, m)):
            dirs, row_meta, row_types = build_schedule(C, m, desig, reading)
            res = verify_schedule(C, m, dirs, row_meta)
            rec = dict(designation={str(h): t for h, t in sorted(row_types.items())},
                       rf1=res['rf1'], rf1_violating_points=res['rf1_violating_points'],
                       rf2=res['rf2'], rf2_failures=res['rf2_failures'],
                       rf3=res['rf3'])
            print(f'  designation {rec["designation"]}: RF1={res["rf1"]} '
                  f'(violating points={res["rf1_violating_points"]}), '
                  f'RF2={res["rf2"]} (bad layers={len(res["rf2_failures"])}), RF3={res["rf3"]}')
            if best is None or (res['rf1_violating_points'],
                                len(res['rf2_failures'])) < (best[1]['rf1_violating_points'],
                                                             len(best[1]['rf2_failures'])):
                best = (rec, res, desig)
        rec, res, desig = best
        print(f'  best designation for {reading}: {rec["designation"]}')
        if res['rf1_witnesses']:
            print('  first RF1 witnesses:')
            for w in res['rf1_witnesses']:
                print(f'    row {w["row"]} point {w["point"]} supports={w["supports_here"]}')
                print(f'      labels by color = {w["labels_by_color"]}  repeated={w["repeated_labels"]} '
                      f'missing={w["missing_labels"]}')
        if res['rf2_failures']:
            print(f'  RF2-failing (row,color) pairs: '
                  f'{[(d["row"], d["color"]) for d in res["rf2_failures"]]}')
        print(f'  return cycle lengths: {res["return_cycle_lengths"]}')
        if reading == 'R3':
            # realized forests under re-basing no longer match the certificate
            data, _ = lowmod_entry(C, m)
            heights = {o['stage']: o['height'] for o in data['splice_supports']}
            iso_bad = []
            for c in range(D):
                edges = set()
                dup = False
                for stage0 in range(7):
                    s = C['shifts'][stage0]; p = C['perms'][stage0]
                    t_h = desig[heights[stage0 + 1]]
                    tail = (c + t_h) % D
                    head = (p[(c + s) % D] - s + t_h) % D
                    e = norm((tail, head)) if tail != head else None
                    if e is None or e in edges:
                        dup = True
                    edges.add(e)
                labels = set()
                for e in edges:
                    if e: labels |= set(e)
                iso = sorted(set(range(D)) - labels)
                if dup or len(iso) != 1:
                    iso_bad.append(dict(color=c, duplicate_or_degenerate=dup, isolates=iso))
            print(f'  R3 realized-forest audit (one-isolate trees required): '
                  f'{len(iso_bad)} colors broken: {iso_bad}')
            rec['realized_forest_broken_colors'] = iso_bad
        rec['rf1_witnesses'] = res['rf1_witnesses']
        rec['return_cycle_lengths'] = res['return_cycle_lengths']
        report['readings'][reading] = rec

    print('\n[marked structure / clause-gap checks]')
    ms = marked_structure_checks(C, m, 'R1')
    for k, v in ms.items():
        if k == 'cross_stage_same_row_full_span_intersections':
            print(f'  {k}: {len(v)} colliding pairs')
            for d in v[:10]:
                print(f'    row {d["row"]}: {d["a"]} x {d["b"]} size={d["size"]} '
                      f'example={d["example_point"]}')
        else:
            print(f'  {k} = {v}')
    report['marked_structure'] = ms

    verdict_pass = all(report['readings'][r]['rf1'] and report['readings'][r]['rf2']
                       and report['readings'][r]['rf3'] for r in ['R1'])
    report['verdict'] = 'PASS' if verdict_pass else 'FAIL'
    print('\n' + '=' * 78)
    print(f'VERDICT m=4: {report["verdict"]}')
    print('=' * 78)
    out = HERE / 'd9_realization_gate_m4.json'
    out.write_text(json.dumps(report, indent=1, default=str))
    print(f'wrote {out}')
    return report

def ledger_m(C, m, witness=True):
    print('=' * 78)
    print(f'D9 anchor-schedule realization gate, m={m}: structural ledger')
    print('=' * 78)
    led = row_budget_ledger(C, m)
    for k, v in led.items():
        print(f'  {k} = {v}')
    bad = closure_ledger(C, m)
    genuine = sorted({b['stage'] for b in bad if not (b['stage'] == 7 and b['part'] == 0)})
    print(f'  switch-closure violations (independent of m): {len(bad)} '
          f'(genuine RF2 obstructions at stages {genuine} triple parts; '
          f'stage-7 triple is block-realized)')
    report = dict(m=m, row_budget_ledger=led,
                  switch_closure_violations=bad, witnesses=[])
    if witness and m in (6, 8):
        # exact RF1 witnesses on folded supports, no full sweep needed: off
        # supports each row is the cyclic base row, which is Latin.
        data, bases = lowmod_entry(C, m)
        by_row = collections.defaultdict(list)
        for o in data['splice_supports']:
            by_row[o['height']].append(o)
        for h, grp in sorted(by_row.items()):
            stages = sorted({o['stage'] for o in grp})
            if len(stages) < 2:
                continue
            for t_stage in stages:
                t_h = next(o['height_shift'] for o in grp if o['stage'] == t_stage)
                for o in grp:
                    if o['stage'] == t_stage:
                        continue
                    r = o['stage']; pi = o['part_index']
                    s = C['shifts'][r - 1]; p = C['perms'][r - 1]
                    P = C['supports'][r - 1]['parts'][pi]['P']
                    heads = sorted(p[(c + s) % D] for c in P)
                    others = sorted((c + t_h) % D for c in range(D) if c not in P)
                    latin = sorted(heads + others) == list(range(D))
                    if not latin:
                        w = dict(row=h, designated_type=t_h, mismatched=f'r{r}_p{pi}',
                                 P=P, switched_labels=heads,
                                 base_labels_of_others=others,
                                 collisions=sorted(set(heads) & set(others)))
                        report['witnesses'].append(w)
        print(f'  RF1 label-collision witnesses at folded rows '
              f'(every designation, every mismatched part): {len(report["witnesses"])}')
        for w in report['witnesses'][:8]:
            print(f'    row {w["row"]} type {w["designated_type"]}: {w["mismatched"]} P={w["P"]} '
                  f'switched={w["switched_labels"]} collide with base labels {w["collisions"]}')
    out = HERE / f'd9_realization_gate_m{m}.json'
    out.write_text(json.dumps(report, indent=1, default=str))
    print(f'wrote {out}')
    return report

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--m', type=int, default=4, choices=[4, 6, 8, 10])
    ap.add_argument('--verify', action='store_true')
    ap.add_argument('--all-readings', action='store_true', default=True)
    args = ap.parse_args()
    C = load_certs()
    if args.m == 4:
        rep = gate_m4(C, args)
        sys.exit(0 if rep['verdict'] == 'PASS' else 1)
    elif args.m in (6, 8):
        ledger_m(C, args.m)
    else:
        print('m=10 (symbolic-range representative):')
        ledger_m(C, 10, witness=False)
        print('\nNOTE: full m=10 construction/verification NOT run.  The primary')
        print('gate (m=4) FAILED, and per the gate protocol the failure is pinned')
        print('and reported without improvising repairs.  The switch-closure ledger')
        print('above already shows the precedent (D5/D7) reading cannot give RF2 at')
        print('stages 3/5/6 triple parts for ANY m, so the high-even realization')
        print('mechanism for those stages is not specified by the bundle either.')

if __name__ == '__main__':
    main()
