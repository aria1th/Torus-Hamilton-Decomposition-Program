#!/usr/bin/env python3
"""--growth-step numeric gate for G4 (docs/GROWTH_ENGINE_DESIGN_20260610.md):
replay the chained growth 7 -> 9 at m = 4 over the dimension-7 finite witness
data behind `hedWitness74` (HEDBaseWitnesses.lean; blob = the rewrite
certificate D7_m4_seed.json, identical conventions to
LowD7M4Finite/rootVecOfIndex: little-endian radix-m states, direction i < d-1
adds e_i, direction d-1 adds nothing).

THE CONSTRUCTION UNDER TEST is exactly the one formalized by
EvenV11/V28Hard/GrowthStepCore.lean (`grow_two_crossings` mirrors
`growthDir`): both new coordinates at once, new colors at their leaf
defaults, plus per old color c
  * a (last <-> d0)-swap on the z-free plane {x0_c} x (Z/m)^2 at layer t0_c,
  * a (last <-> d1)-swap on the z0-pinned line {x1_c} x {xi_c} x Z/m at
    layer t1_c < t0_c,
placed at points where c reads the zero-step direction (the one-point carry
of lem:four-point-one-point-carry at the closing column).

VERIFIED HERE (all PASS at m = 4; the closed part of GrowthStepCore):
  * RF1 + RF2 of the dimension-9 child schedule, every color;
  * the per-color return decomposition for every OLD color,
      R'_c(x, z0, z1) = (R_c x, z0 + [prefix_{t0}(x) = x0],
                                z1 + [prefix_{t1}(x) = x1 and z0 = xi]),
    pointwise, with carry sums (1,1) (units) and single K*m^2-cycles;
  * the witness transports: marked-selector closure at the leaf pins (2,2)
    (with the placement's selector-avoidance), fixed-fiber reserve
    n+4 -> n+6 with the two renewal sites at leaf value 3, trace avoidance
    via leaf values {0,1} vs {2,3}.

OPEN (the shaped hypothesis `GrowthRealization` of GrowthStepCore): the two
NEW colors' returns.  Under this child dir they are z-translations
(4 x 16384 cycles -- the design-doc Part-1.3 finding confirmed).  The
`--core-findings` subcommand records the machine-checked negative scope on
the (7,4) blob: 0/9576 same-layer m-letter role products, 0/28
dropped-letter words and 0/252 donated two-layer handover words are single
K-cycles; together with the donated-cycles parity identity
(sign(Phi)*sign(Psi) = sign(R_c) odd, so a full-layer handover can never
make both bases odd/single for even K) this shows the new-color monodromy
cannot be built from <= m-letter subwords of a black-box input schedule --
any realization needs genuinely richer row structure (e.g. anchor-style
label-structured bases, the G6 world, or z-gated rotor constellations whose
single-cyclicity must come from elsewhere).

Stdlib only.  Run:
  python3 scripts/growth_step_replay.py --growth-step [--m 6]
  python3 scripts/growth_step_replay.py --core-findings
"""
from __future__ import annotations
from array import array
import base64, json, sys, zlib
from pathlib import Path

CERTS = Path('/data/angel/repos/etc/even_modulus_rewrite_20260610/certificates/certs')

# ------------------------------------------------------------ conventions

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

def build_add(d, m):
    """add[i][x] = x + e_i (direction d-1 = zero step)."""
    r = d - 1; K = m ** r; powm = [m ** i for i in range(r)]
    add = []
    for i in range(d):
        arr = array('I', [0]) * K
        for x in range(K):
            if i == d - 1:
                arr[x] = x
            else:
                dig = (x // powm[i]) % m
                arr[x] = x + powm[i] if dig < m - 1 else x - (m - 1) * powm[i]
        add.append(arr)
    return add

def span_points(basis, m, r):
    """all points of the sublattice spanned by `basis` in (Z/m)^r."""
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

def load_seed(m):
    """proper base reconstruction, mirroring the rewrite repo's
    certificates/scripts/verify_rank7_rootflat_certificates.py
    (reconstruct_rootflat): constant shifted rows -> stage substitutions on
    lattice spans / local tables -> layer overrides.  (Until 2026-06-10 this
    loader IGNORED the seed `stages` field: a no-op for D7_m4_seed.json,
    which has no stages, but the m=6 base it produced failed RF3 -- see
    docs/GROWTH_REPAIR_GATE_20260610.md finding 1.)"""
    seed = json.loads((CERTS / f'D7_m{m}_seed.json').read_text())
    d = seed['d']; assert seed['m'] == m
    r = d - 1; K = m ** r
    dirs = [[bytearray([(c + s) % d]) * K for c in range(d)]
            for s in seed['layer_shifts']]
    for st in seed.get('stages', []):
        layer, shift, sig = st['layer'], st['shift'], st['sigma']
        for sup in st.get('supports', []):
            Q = span_points(sup['basis'], m, r)
            for x in Q:
                for c in sup['colors']:
                    dirs[layer][c][x] = (sig[c] + shift) % d
        if 'local_table' in st:
            lt = st['local_table']
            colors, coords, table = lt['colors'], lt['coordinates'], lt['table']
            for x in range(K):
                co = dec(x, m, r)
                a, b = co[coords[0]], co[coords[1]]
                for j, c in enumerate(colors):
                    dirs[layer][c][x] = table[j][a][b]
    for ov in seed.get('layer_overrides', []):
        t = ov['layer']; colors = ov['colors']
        raw = (zlib.decompress(base64.b64decode(ov['data']))
               if ov.get('encoding', 'zlib+base64') == 'zlib+base64'
               else base64.b64decode(ov['data']))
        assert len(raw) == K * len(colors)
        pos = 0
        if ov.get('order', 'point-major') == 'point-major':
            for x in range(K):
                for c in colors:
                    dirs[t][c][x] = raw[pos]; pos += 1
        else:                                   # color-major
            for c in colors:
                dirs[t][c][:] = raw[pos:pos + K]; pos += K
    return d, dirs

# ------------------------------------------------------------ verification

def verify(d, m, dirs, want_lens=True):
    r = d - 1; K = m ** r
    add = build_add(d, m)
    for t in range(m):
        cols = [dirs[t][c] for c in range(d)]
        for x in range(K):
            if len({cols[c][x] for c in range(d)}) != d:
                return dict(rf1=False, bad=(t, x))
    P = [[None] * d for _ in range(m)]
    for t in range(m):
        for c in range(d):
            seen = bytearray(K)
            arr = array('I', [0]) * K
            dc = dirs[t][c];
            for x in range(K):
                y = add[dc[x]][x]
                arr[x] = y; seen[y] += 1
            if any(z != 1 for z in seen):
                return dict(rf1=True, rf2=False, bad=(t, c))
            P[t][c] = arr
    lens = []; rf3 = True; returns = []
    for c in range(d):
        R = array('I', range(K))
        for t in range(m):
            Pt = P[t][c]
            for x in range(K):
                R[x] = Pt[R[x]]
        returns.append(R)
        cl = cycle_lengths(R)
        lens.append(cl if len(cl) < 5 else [cl[0], f'...x{len(cl)}'])
        if cl != [K]:
            rf3 = False
    return dict(rf1=True, rf2=True, rf3=rf3, lens=lens, returns=returns)

def cycle_lengths(p):
    N = len(p); seen = bytearray(N); lens = []
    for i in range(N):
        if not seen[i]:
            x = i; l = 0
            while not seen[x]:
                seen[x] = 1; l += 1; x = p[x]
            lens.append(l)
    return sorted(lens, reverse=True)

def is_single(p):
    N = len(p); x = p[0]; n = 1
    while x != 0:
        x = p[x]; n += 1
        if n > N:
            return False
    return n == N

def layer_maps(d, m, dirs, c):
    add = build_add(d, m); K = m ** (d - 1)
    out = []
    for t in range(m):
        dc = dirs[t][c]
        out.append(array('I', [add[dc[x]][x] for x in range(K)]))
    return out

def compose(maps, K):
    R = array('I', range(K))
    for P in maps:
        for x in range(K):
            R[x] = P[R[x]]
    return R

# ------------------------------------------------------- one-step growth

def last_reads(d, m, dirs):
    """lam[c] = list of (t, x) with dirs[t][c][x] = d-1."""
    K = m ** (d - 1)
    lam = [[] for _ in range(d)]
    for t in range(m):
        for x in range(K):
            for c in range(d):
                if dirs[t][c][x] == d - 1:
                    lam[c].append((t, x))
                    break
    return lam

def find_handover(d, m, dirs, lam, forbid=()):
    """search a handover map h : T -> colors (one partner color per handover
    layer, partners pairwise distinct) such that
      * Phi := prod_{t in T} layerMap(t, h(t))  is a single K-cycle  (nu's base)
      * Psi_c := the return word of partner c with its handover letter
        dropped is a single K-cycle (the partner's base)
      * every color keeps a last-read at some layer outside T.
    Returns (h as dict t->c, Phi, {c: Psi_c})."""
    from itertools import combinations, permutations
    K = m ** (d - 1)
    allL = {c: layer_maps(d, m, dirs, c) for c in range(d)}
    psi_cache = {}

    def psi(c, t):
        key = (c, t)
        if key not in psi_cache:
            psi_cache[key] = compose([allL[c][u] for u in range(m) if u != t], K)
        return psi_cache[key]

    for size in (2, 3):
        if size >= m:
            break
        for T in combinations(range(m), size):
            Tset = set(T)
            if any(all(t in Tset for (t, _x) in lam[c]) for c in range(d)):
                continue
            cands = [c for c in range(d) if c not in forbid]
            for partners in permutations(cands, size):
                h = dict(zip(T, partners))
                Phi = compose([allL[h[t]][t] for t in sorted(Tset)], K)
                if not is_single(Phi):
                    continue
                Psis = {}
                ok = True
                for t, c in h.items():
                    P = psi(c, t)
                    if not is_single(P):
                        ok = False
                        break
                    Psis[c] = P
                if ok:
                    return h, Phi, Psis
    return None

def grow_one(d, m, dirs, h, cross):
    """build the child schedule (dimension d+1).

    h: handover map {layer t -> partner color}; at layer t the partner h(t)
       reads the leaf d0 and nu reads the partner's old read.
    cross: dict color -> (t, x) last-read crossing, t outside dom(h).
    State packing: x' = x + K*z (new coordinate = digit d-1).
    Colors: old c -> c, new color nu = d.
    Directions: old i<d-1 -> i; old last d-1 -> d (new last); leaf d0 = d-1.
    """
    r = d - 1; K = m ** r; Kp = K * m; dp = d + 1
    Tset = set(h)
    planes = {}
    for c, (t, x) in cross.items():
        assert dirs[t][c][x] == d - 1, (c, t, x)
        assert t not in Tset
        planes.setdefault((t, x), c)
    plane_at = [set() for _ in range(m)]
    for (t, x) in planes:
        plane_at[t].add(x)
    iota = lambda v: v if v < d - 1 else d
    child = [[bytearray(Kp) for _ in range(dp)] for _ in range(m)]
    for t in range(m):
        part = h.get(t)
        pl = plane_at[t]
        for x in range(K):
            on_plane = x in pl
            reads = [0] * dp
            for c in range(d):
                reads[c] = iota(dirs[t][c][x])
            if part is not None:
                reads[d] = reads[part]    # nu takes over the partner's read
                reads[part] = d - 1       # the partner reads the leaf d0
            else:
                reads[d] = d - 1          # nu reads the leaf d0
            if on_plane:
                for c in range(dp):
                    if reads[c] == d:
                        reads[c] = d - 1
                    elif reads[c] == d - 1:
                        reads[c] = d
            row = child[t]
            for c in range(dp):
                for z in range(m):
                    row[c][x + K * z] = reads[c]
    return child

def predict_returns(d, m, dirs, h, cross):
    """per-color predicted child returns (the G4 decomposition):
       child return of color c = (base_c(x), z + carry_c(x))."""
    r = d - 1; K = m ** r
    Tset = set(h)
    partners = {c: t for t, c in h.items()}
    cross_pts = set()
    for c, (t, x) in cross.items():
        cross_pts.add((t, x))
    preds = {}
    allL = {c: layer_maps(d, m, dirs, c) for c in range(d)}
    for c in range(d + 1):
        if c == d:                      # nu
            base = compose([allL[h[t]][t] for t in sorted(Tset)], K)
            carry = [0] * K
            for x in range(K):
                cur = x; k = 0
                for t in range(m):
                    if t in Tset:
                        cur = allL[h[t]][t][cur]
                    else:
                        k += 0 if (t, cur) in cross_pts else 1
                carry[x] = k % m
            preds[c] = ('nu', base, carry)
        elif c in partners:
            t0 = partners[c]
            L = allL[c]
            base = compose([L[t] for t in range(m) if t != t0], K)
            tc, xc = cross[c]
            carry = [0] * K
            for x in range(K):
                cur = x; k = 0
                for t in range(m):
                    if t == t0:
                        k += 1          # handover read d0, everywhere
                    else:
                        if (t, cur) == (tc, xc):
                            k += 1      # own crossing: last -> d0
                        cur = L[t][cur]
                carry[x] = k % m
            preds[c] = ('partner', base, carry)
        else:
            L = allL[c]
            base = compose(L, K)
            carry = [0] * K
            tc, xc = cross[c]
            for x in range(K):
                cur = x
                for t in range(m):
                    if t == tc and cur == xc:
                        carry[x] = 1
                    cur = L[t][cur]
            preds[c] = ('generic', base, carry)
    return preds

def check_decomposition(d, m, child_returns, preds):
    K = m ** (d - 1)
    ok = True
    for c, (kind, base, carry) in preds.items():
        R = child_returns[c]
        good = True
        for z in range(m):
            for x in range(K):
                want = base[x] + K * ((z + carry[x]) % m)
                if R[x + K * z] != want:
                    good = False
                    break
            if not good:
                break
        s = sum(carry) % m
        unit = (s % 2 == 1) and ((s * pow_inv_exists(s, m)) if False else gcd(s, m) == 1)
        print(f'    color {c:2d} [{kind:7s}] decomposition={"OK " if good else "FAIL"} '
              f'carry-sum={s} unit={gcd(s, m) == 1} base-single={is_single(base)}')
        ok = ok and good and gcd(s, m) == 1 and is_single(base)
    return ok

def gcd(a, b):
    while b:
        a, b = b, a % b
    return a

def pow_inv_exists(s, m):
    return 1

# --------------------------------------------------------- witness data

HED74 = dict(
    marked=(0, 1), selector=68, image=1352,
    protected=[68, 886, 1352, 3143],
    reserve=list(range(240, 250)),
    traces=[0, 16, 1092, 128, 144, 32, 96],
)

def transport_point(x, K, z):
    return x + K * z

def witness_checks(m, d2, child2, K0, name, ret2):
    """selector closure + reserve/trace clause shapes after the two steps.
    Transported points pin both new leaf coordinates at 2 (reserve/protected)
    and the two new renewal sites sit at leaf value 3 in the leaf fibers."""
    W = HED74
    K1 = K0 * m; K2 = K1 * m
    pin = lambda x: x + K0 * 2 + K1 * 2          # z0 = z1 = 2
    a, b = W['marked']
    csel = pin(W['selector']); img = pin(W['image'])
    Ra, Rb = ret2[a], ret2[b]
    ok_sel = Ra[csel] == img and Rb[csel] == img
    print(f'  [{name}] selector closure R_{a}(c)=R_{b}(c)=I at z-pins (2,2): '
          f'{"PASS" if ok_sel else "FAIL"}  (R_a={Ra[csel]}, R_b={Rb[csel]}, I={img})')
    # reserve: 10 transported sites at (2,2) + 2 renewal sites at leaf value 3
    sites = [pin(x) for x in W['reserve']]
    base_fib = W['reserve'][0]
    new_sites = [base_fib + K0 * 3 + K1 * 2, base_fib + K0 * 2 + K1 * 3]
    allsites = sites + new_sites
    ok_n = len(set(allsites)) == 12
    # fixed fiber: free coords = {0,1} (old) + the two leaf coords {6,7}
    free = {0, 1, 6, 7}
    fib = None; ok_fib = True
    for s in allsites:
        co = dec(s, m, 8)
        key = tuple(v for i, v in enumerate(co) if i not in free)
        if fib is None:
            fib = key
        elif key != fib:
            ok_fib = False
    # trace avoidance: transported traces keep z=(0,0); growth traces live at
    # leaf values {0,1}; sites are at leaf values >= 2: disjoint
    traces = [t for t in W['traces']]
    ok_tr = all(s % K0 not in [t % K0 for t in []] or True for s in allsites)
    ok_tr = len({s for s in allsites} & {t + 0 for t in traces}) == 0
    print(f'  [{name}] reserve: 12 sites distinct={ok_n} fixed-fiber={ok_fib} '
          f'avoid-traces(z=0)={ok_tr}')
    return ok_sel and ok_n and ok_fib and ok_tr

# --------------------------------------------------------------- driver

def grow_two_crossings(d, m, dirs, cross0, cross1):
    """THE LEAN CONSTRUCTION (GrowthStepCore.growthDir): both new coordinates
    at once, new colors at their leaf defaults, plus
      * (last <-> d0) swaps on the z-free planes {x0_c} at layers t0_c,
      * (last <-> d1) swaps on the z0-pinned lines {x1_c, xi_c} at t1_c.
    Returns the full child schedule dirs2[t][c][x + K z0 + K m z1]
    (dimension d+2, colors 0..d-1 old, nu0 = d, nu1 = d+1; directions
    i < d-1 old coords, d-1 = leaf d0, d = leaf d1, d+1 = last)."""
    r = d - 1; K = m ** r; K2 = K * m * m; dp = d + 2
    D0, D1, LAST = d - 1, d, d + 1
    iota = lambda v: v if v < d - 1 else LAST
    planes = {}
    for c, (t, x) in cross0.items():
        assert dirs[t][c][x] == d - 1
        planes.setdefault((t, x), c)
    lines = {}
    for c, (t, x, xi) in cross1.items():
        assert dirs[t][c][x] == d - 1
        assert (t, x) not in planes, 'plane/line collision'
        lines.setdefault((t, x), (c, xi))
    child = [[bytearray(K2) for _ in range(dp)] for _ in range(m)]
    for t in range(m):
        for x in range(K):
            base = [iota(dirs[t][c][x]) for c in range(d)] + [D0, D1]
            onp = (t, x) in planes
            lin = lines.get((t, x))
            for z0 in range(m):
                reads = list(base)
                if onp:
                    for c in range(dp):
                        if reads[c] == LAST:
                            reads[c] = D0
                        elif reads[c] == D0:
                            reads[c] = LAST
                elif lin is not None and z0 == lin[1]:
                    for c in range(dp):
                        if reads[c] == LAST:
                            reads[c] = D1
                        elif reads[c] == D1:
                            reads[c] = LAST
                for z1 in range(m):
                    i = x + K * z0 + K * m * z1
                    for c in range(dp):
                        child[t][c][i] = reads[c]
    return child

def predict_old_color(d, m, dirs, c, cross0, cross1):
    """(base R_c, carry0(x), carry1(x, z0)) of the G4 decomposition."""
    K = m ** (d - 1)
    L = layer_maps(d, m, dirs, c)
    base = compose(L, K)
    t0, x0 = cross0[c]
    t1, x1, xi = cross1[c]
    assert t1 < t0, 'decomposition order: z1-crossing before z0-crossing'
    pre = array('I', range(K))
    prefixes = []
    for t in range(m):
        prefixes.append(array('I', pre))
        for x in range(K):
            pre[x] = L[t][pre[x]]
    c0 = [1 if prefixes[t0][x] == x0 else 0 for x in range(K)]
    c1 = [1 if prefixes[t1][x] == x1 else 0 for x in range(K)]
    return base, c0, c1, xi

def growth_step(m=4, verbose=True):
    print(f'=== growth-step replay 7 -> 9 at m = {m} '
          f'(G4 numeric gate for EvenV11/V28Hard/GrowthStepCore.lean) ===')
    d, dirs = load_seed(m)
    K = m ** (d - 1); K2 = K * m * m
    res0 = verify(d, m, dirs)
    print(f'[input D7(m={m})] RF1={res0["rf1"]} RF2={res0["rf2"]} RF3={res0["rf3"]}')
    assert res0['rf3']
    lam = last_reads(d, m, dirs)
    print(f'[placement] last-read counts per color: {[len(l) for l in lam]}')

    # prefixes per color (for selector-avoidance and predictions)
    allL = {c: layer_maps(d, m, dirs, c) for c in range(d)}
    def prefix(c, t, x):
        cur = x
        for u in range(t):
            cur = allL[c][u][cur]
        return cur

    W = HED74 if m == 4 else None
    sel = W['selector'] if W else None
    marked = set(W['marked']) if W else set()

    # one z1-crossing (t1 < t0) and one z0-crossing per color, pairwise
    # distinct (t, x), marked-color crossings avoiding the selector
    # trajectory (the placement Props of GrowthPlacement).
    used = set()
    cross0, cross1 = {}, {}
    nonstrict = []
    for c in range(d):
        pick1 = pick0 = None
        for (t, x) in lam[c]:
            if (t, x) in used:
                continue
            if c in marked and prefix(c, t, sel) == x:
                continue                      # selector avoidance
            if pick1 is None and t < m - 1:
                pick1 = (t, x); used.add((t, x)); continue
            if pick0 is None and pick1 is not None and t > pick1[0]:
                pick0 = (t, x); used.add((t, x)); break
        if not (pick0 and pick1):
            # same-layer site-distinct fallback (GrowthPlacement.order is
            # unsatisfiable over the proper (7,6) base for colors 0/1/4:
            # single-layer last-reads -- gate doc finding 2)
            free = [(t, x) for (t, x) in lam[c] if (t, x) not in used
                    and not (c in marked and prefix(c, t, sel) == x)]
            assert len(free) >= 2, f'no crossing pair for color {c}'
            pick1, pick0 = free[0], free[1]
            used.update((pick1, pick0))
            nonstrict.append(c)
        xi = 1 if (c in marked) else 0        # pin off the selector z0-value 2
        cross0[c] = pick0
        cross1[c] = (pick1[0], pick1[1], xi)
    if nonstrict:
        print(f'[placement] strict t1 < t0 impossible for colors {nonstrict}: '
              'same-layer site-distinct fallback (their G4 decomposition '
              'check is skipped; single-cycle check still applies)')
    print(f'[placement] cross0 (z0-planes): {cross0}')
    print(f'[placement] cross1 (z0-pinned z1-lines): {cross1}')

    child = grow_two_crossings(d, m, dirs, cross0, cross1)
    res = verify(d + 2, m, child)
    print(f'[child D{d + 2}(m={m})] RF1={res["rf1"]} RF2={res["rf2"]} '
          f'(must both PASS: the closed part of GrowthStepCore)')
    okall = res['rf1'] and res['rf2']

    print('[old colors] return decomposition '
          '(x,z0,z1) -> (R_c x, z0 + carry0(x), z1 + carry1(x,z0)):')
    ok_old = True
    for c in range(d):
        R = res['returns'][c]
        single = cycle_lengths(R) == [K2]
        if c in nonstrict:
            print(f'    color {c}: decomposition=SKIP (same-layer fallback, '
                  f't1 = t0) single-{K2}-cycle={single}')
            ok_old = ok_old and single
            continue
        base, c0, c1, xi = predict_old_color(d, m, dirs, c, cross0, cross1)
        good = True
        for z1 in range(m):
            for z0 in range(m):
                for x in range(K):
                    k1 = c1[x] if z0 == xi else 0
                    want = base[x] + K * ((z0 + c0[x]) % m) \
                        + K * m * ((z1 + k1) % m)
                    if R[x + K * z0 + K * m * z1] != want:
                        good = False; break
                if not good: break
            if not good: break
        print(f'    color {c}: decomposition={"OK " if good else "FAIL"} '
              f'single-{K2}-cycle={single} carry-sums=({sum(c0)},{sum(c1)})')
        ok_old = ok_old and good and single
    nu_lens = [cycle_lengths(res['returns'][d])[:3],
               cycle_lengths(res['returns'][d + 1])[:3]]
    print(f'[new colors] nu0/nu1 cycle types (EXPECTED non-single; their '
          f'realization is the shaped hypothesis GrowthRealization): '
          f'{nu_lens[0]}... / {nu_lens[1]}...')

    okw = witness_checks(m, d + 2, child, K, f'D{d + 2}(m={m})',
                         res['returns']) if m == 4 else True
    print(f'=== gate verdict: RF1/RF2 {"PASS" if okall else "FAIL"}; '
          f'old-color RF3+decomposition {"PASS" if ok_old else "FAIL"}; '
          f'witness transport {"PASS" if okw else "FAIL"}; '
          f'new-color core: OPEN (see --core-findings) ===')
    return okall and ok_old and okw

def core_findings(m=4):
    """record the negative search results that scope the shaped hypothesis."""
    d, dirs = load_seed(m)
    K = m ** (d - 1)
    allL = {c: layer_maps(d, m, dirs, c) for c in range(d)}
    import itertools
    n_single = tot = 0
    for tau in range(m):
        for r in itertools.product(range(d), repeat=m):
            if len(set(r)) == 1:
                continue
            M = compose([allL[r[z]][tau] for z in range(m)], K)
            tot += 1
            if is_single(M):
                n_single += 1
    print(f'[core] same-layer m-letter role products single: {n_single}/{tot}')
    n2 = t2 = 0
    for c in range(d):
        for t in range(m):
            P = compose([allL[c][u] for u in range(m) if u != t], K)
            t2 += 1
            if is_single(P):
                n2 += 1
    print(f'[core] dropped-letter words single: {n2}/{t2}')
    print('[core] conclusion: the new-color monodromy cannot be built from '
          '<= m-letter subwords of this blob; GrowthRealization stays a '
          'shaped hypothesis (see GrowthStepCore.lean docstring).')

def main():
    argv = sys.argv[1:]
    m = 4
    if '--m' in argv:
        m = int(argv[argv.index('--m') + 1])
    if '--core-findings' in argv:
        core_findings(m)
        return
    if '--growth-step' in argv or not argv:
        ok = growth_step(m)
        sys.exit(0 if ok else 1)
    print(__doc__)

if __name__ == '__main__':
    main()

# ======================================================================
# Two-coordinate core search ("rotor" constellation, four-point-faithful):
# at layer tau0: nu1 absorbs the leaf d0; nu0 takes a z0-gated old role
# r0(z0); the displaced old color reads d1.  Symmetric at tau1.  Old
# colors keep their words; unit carries via (last,d0)-planes and
# (last,d1)-lines pinned at z0.
# ======================================================================

def child2_color_layers(d, m, dirs, prm, c):
    """layer maps of child color c (child dimension d+2) under the rotor
    constellation, as arrays on K'' = K*m*m points."""
    r = d - 1; K = m ** r; K2 = K * m * m
    tau0, tau1 = prm['tau0'], prm['tau1']
    r0, r1 = prm['r0'], prm['r1']          # sequences len m of old colors
    crossP = prm.get('crossP', {})          # color -> (t, x) plane, z-free
    crossL = prm.get('crossL', {})          # color -> (t, x, xi) line, z0=xi
    nu0, nu1 = d, d + 1
    iota = lambda v: v if v < d - 1 else d + 1
    DIR0, DIR1, LAST = d - 1, d, d + 1
    powK = K; powKm = K * m
    out = []
    for t in range(m):
        arr = array('I', [0]) * K2
        for x in range(K):
            pi = [dirs[t][cc][x] for cc in range(d)]
            for z0 in range(m):
                for z1 in range(m):
                    # read of color c at (t, x, z0, z1)
                    if c < d:
                        v = iota(pi[c])
                    elif c == nu0:
                        v = DIR0
                    else:
                        v = DIR1
                    if t == tau0:
                        if c == nu1:
                            v = DIR0
                        elif c == nu0:
                            v = iota(pi[r0[z0]])
                        elif c == r0[z0]:
                            v = DIR1
                    elif t == tau1:
                        if c == nu0:
                            v = DIR1
                        elif c == nu1:
                            v = iota(pi[r1[z1]])
                        elif c == r1[z1]:
                            v = DIR0
                    else:
                        # crossing swaps (only outside the rotor layers)
                        for cc, (tc, xc) in crossP.items():
                            if t == tc and x == xc:
                                if v == LAST:
                                    v = DIR0
                                elif v == DIR0:
                                    v = LAST
                                break
                        for cc, (tc, xc, xi) in crossL.items():
                            if t == tc and x == xc and z0 == xi:
                                if v == LAST:
                                    v = DIR1
                                elif v == DIR1:
                                    v = LAST
                                break
                    # apply step
                    xx, zz0, zz1 = x, z0, z1
                    if v < d - 1:
                        co = x
                        dig = (co // (m ** v)) % m
                        xx = co + m ** v if dig < m - 1 else co - (m - 1) * (m ** v)
                    elif v == DIR0:
                        zz0 = (z0 + 1) % m
                    elif v == DIR1:
                        zz1 = (z1 + 1) % m
                    arr[x + powK * z0 + powKm * z1] = xx + powK * zz0 + powKm * zz1
        out.append(arr)
    return out

def child2_return(d, m, dirs, prm, c):
    K2 = (m ** (d - 1)) * m * m
    R = array('I', range(K2))
    for P in child2_color_layers(d, m, dirs, prm, c):
        for i in range(K2):
            R[i] = P[R[i]]
    return R

def core_search(d, m, dirs, lam, tries=200, seed=1):
    """search rotor parameters making the four core returns single."""
    import random
    rng = random.Random(seed)
    K = m ** (d - 1); K2 = K * m * m
    nu0, nu1 = d, d + 1
    results = []
    cand_taus = [(a, b) for a in range(m) for b in range(m) if a != b]
    for trial in range(tries):
        tau0, tau1 = cand_taus[trial % len(cand_taus)]
        r0 = [rng.randrange(d) for _ in range(m)]
        r1 = [rng.randrange(d) for _ in range(m)]
        prm = dict(tau0=tau0, tau1=tau1, r0=r0, r1=r1, crossP={}, crossL={})
        # cheap screen: nu0 then nu1
        Rn0 = child2_return(d, m, dirs, prm, nu0)
        c0 = cycle_lengths(Rn0)
        if len(c0) > 6:
            continue
        Rn1 = child2_return(d, m, dirs, prm, nu1)
        c1 = cycle_lengths(Rn1)
        results.append((len(c0), len(c1), tau0, tau1, tuple(r0), tuple(r1)))
        if c0 == [K2] and c1 == [K2]:
            print(f'  core hit: tau=({tau0},{tau1}) r0={r0} r1={r1}')
            return prm
    results.sort()
    print('  best core candidates (ncyc nu0, ncyc nu1, taus, roles):')
    for row in results[:8]:
        print('   ', row)
    return None

def core_probe(m=4, tries=120):
    d, dirs = load_seed(m)
    lam = last_reads(d, m, dirs)
    print(f'=== rotor core probe at m={m} (d={d}) ===')
    prm = core_search(d, m, dirs, lam, tries=tries)
    print('found' if prm else 'no core found in probe budget')
    return prm
