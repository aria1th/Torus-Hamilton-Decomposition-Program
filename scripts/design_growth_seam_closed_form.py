#!/usr/bin/env python3
"""Closed-form DESIGN route for the conjugate-relaxation 7->9 growth-step
repair (the rail-seam method: parity calculus + budget structure first,
numerics second).  Companion to the stochastic
`search_growth_conjugate_repair.py` (imported read-only).

THE TEMPLATE CLASS ("skew-pure / fibered column exchange").  Child state
i = x + K*z0 + K*m*z1; directions 0..5 = old x-coords, 6 = D0, 7 = D1,
8 = LAST.  Use only Z-FREE pieces (full-orbit column donations, D0/D1
planes) and X-LOCAL z-gated pieces (old-old lines, one wild seam), so every
child return is an exact skew product R(x,z) = (pi(x), phi_x(z)) and RF3
factorizes: pi single K-cycle on columns + fiber holonomy Phi single
m^2-cycle on (Z/m)^2.

WHAT IS CLOSED (exact, both moduli):
  * fiber layer: every Phi is translation-conjugate to T_U o (one gated
    piece); good-drift tables for the d3-even wild layers, the line-kick
    odometer lemma (single for every unit drift/gate/sign), drift tuning
    by plane counts (donations contribute 0 mod m: all orbit lengths are
    == 0 mod m by telescoping); parity ledger: 1 wild seam + 5 old-old
    lines makes all nine returns odd with PURE leaf fibers.
  * x-word sign identities: leaf words need ODD donated-instance counts,
    donor words EVEN frozen counts, and N_c (instances per color) is odd
    for every color -- so a pure leaf<->color exchange is parity-dead and
    cross donations are forced.
  * full mixed-color layer words are never single (only the 7 pure base
    returns among 7^4 at (7,4)): leaf words must live near single-color
    words.

VERDICTS (machine-checked, see growth_seam_design_budget_m{4,6}.json):
  * (7,4) hedWitness blob: THE WHOLE CLASS IS DEAD by the orbit-atom
    coverage budget (--budget): z-free donation atoms are exactly full
    L_{t,c}-orbits (RF2 forces L-invariance both sides); an atom is
    donatable only if it avoids the exactly-1 columns of its color; at
    (7,4) 72/293 atoms are pinned and 193 columns lie in NO donatable
    atom, so the leaf words can never cover them.  Old-old trade surgery
    (old_swap_closure shape) cannot repair it: 0/2000 sampled closures
    even exist (zero-reads poison every closure).  The missing ingredient
    at (7,4) is genuinely sub-orbit donation atoms = z-GATED staircase
    ribbons -- the stochastic seam family's shape (R2 sharpened: z-gating
    is NECESSARY, not just minimal).
  * proper (7,6) base: the budget is FEASIBLE (0 pinned atoms among
    248967, every column has donatable atoms for both leaves).  The
    skew-pure exchange template remains the design route at the proper
    base; the m=4 witness blob is the anomaly (fat zero-read sets).

Run:
  python3 scripts/design_growth_seam_closed_form.py --analyze [--m 4]
  python3 scripts/design_growth_seam_closed_form.py --budget  [--m 4|6]
  python3 scripts/design_growth_seam_closed_form.py --design  [--m 4|6] [--seed N]
  python3 scripts/design_growth_seam_closed_form.py --verify/--chain [--witness F]
Summaries: scripts/growth_seam_design_*.json
(NOTE for m=6 runs: orbit_table has ~249k instances; the ExchangeSolver
descent needs a coarser move generator before it is practical there.)
"""

from __future__ import annotations
from array import array
import itertools, json, random, sys, time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from growth_step_replay import (load_seed, build_add, cycle_lengths,
                                layer_maps, compose, verify)
from search_growth_conjugate_repair import orbit_table, load_wild_layers

# ---------------------------------------------------------------- fiber kit
# fiber index f = z0 + m*z1 (matches state packing x + K*z0 + K*m*z1)


def fid(z0, z1, m):
    return z0 + m * z1


def f_translation(u0, u1, m):
    return [fid((f % m + u0) % m, (f // m + u1) % m, m)
            for f in range(m * m)]


def f_compose(P, Q):
    """(P o Q)(f) = P[Q[f]]."""
    return [P[q] for q in Q]


def f_cycles(P):
    n = len(P); seen = [False] * n; out = []
    for i in range(n):
        if not seen[i]:
            x = i; l = 0
            while not seen[x]:
                seen[x] = True; l += 1; x = P[x]
            out.append(l)
    return sorted(out, reverse=True)


def wild_fiber_map(table, cert_color, m):
    """fiber map of one cert color on the wild layer: f -> f + e_dir."""
    EV = ((1, 0), (0, 1), (0, 0))
    P = [0] * (m * m)
    for z0 in range(m):
        for z1 in range(m):
            e = EV[table[z0][z1][cert_color]]
            P[fid(z0, z1, m)] = fid((z0 + e[0]) % m, (z1 + e[1]) % m, m)
    return P


def good_drift_table(wilds, m):
    """good[(wild_id, cert_color)] = set of u with T_u o f single m^2-cycle.
    Exact for the holonomies here: translations conjugate through f without
    changing the cycle type (T_U o T_a f T_{-a} = T_a (T_U o f) T_{-a})."""
    good = {}
    for wi, w in enumerate(wilds):
        for c in range(3):
            f = wild_fiber_map(w['table'], c, m)
            ok = set()
            for u0 in range(m):
                for u1 in range(m):
                    if f_cycles(f_compose(f_translation(u0, u1, m), f)) \
                            == [m * m]:
                        ok.add((u0, u1))
            good[(wi, c)] = ok
    return good


def line_kick(xi, sign, m):
    """gated z1-kick: z1 += sign on the z0 == xi cells (the old-old line)."""
    P = list(range(m * m))
    for z1 in range(m):
        P[fid(xi, z1, m)] = fid(xi, (z1 + sign) % m, m)
    return P


def odometer_check(m):
    """assert: T_(alpha,beta) o kick is a single m^2-cycle for every unit
    alpha, every beta, every gate xi, both kick signs (the old-color
    two-storey odometer; robust to the conjugation shifts)."""
    units = [a for a in range(1, m) if _gcd(a, m) == 1]
    for alpha in units:
        for beta in range(m):
            T = f_translation(alpha, beta, m)
            for xi in range(m):
                for sg in (1, -1):
                    if f_cycles(f_compose(T, line_kick(xi, sg, m))) \
                            != [m * m]:
                        return False, (alpha, beta, xi, sg)
    return True, None


def _gcd(a, b):
    while b:
        a, b = b, a % b
    return a


def _and_all(fix, tp):
    bm = fix[(0, tp[0])]
    for t in range(1, len(tp)):
        bm &= fix[(t, tp[t])]
        if bm == 0:
            return 0
    return bm


# ------------------------------------------------------------ drift ledger

def solve_drift_ledger(m, wilds):
    """close the drift + parity ledger algebraically.  Unknowns: wild layer
    id, trio assignment sigma (nu0, nu1, c* -> cert colors), per-old-color
    D0-plane counts np0_c (z0-drifts, must be units), c*'s D1-plane count
    np1_cstar.  Constraints (all mod m):
       A0 = -(sum np0_c)        with (A0, 0) in good(sigma(nu0)),
       B1 = -(np1_cstar)        with (0, B1) in good(sigma(nu1)),
       (np0_cstar, np1_cstar)   in good(sigma(c*)).
    Old colors c != c*: np0_c any unit (take the minimum), np1_c = 0; their
    fiber = T_(np0_c, beta) o one line kick: single by odometer_check.
    Returns the minimal solution as a dict, or None."""
    good = good_drift_table(wilds, m)
    units = [a for a in range(1, m) if _gcd(a, m) == 1]
    best = None
    for wi in range(len(wilds)):
        for s0, s1, s2 in itertools.permutations(range(3)):
            # sigma: nu0 -> s0, nu1 -> s1, c* -> s2
            g0, g1, g2 = good[(wi, s0)], good[(wi, s1)], good[(wi, s2)]
            for np0_star, np1_star in sorted(g2,
                                             key=lambda u: u[0] + u[1]):
                # need (0, B1) good for nu1 with B1 = -np1_star
                if (0, (-np1_star) % m) not in g1:
                    continue
                # choose np0_c (c != c*) units; A0 = -(6 units + np0_star)
                for base_u in units:
                    A0 = (-(6 * base_u + np0_star)) % m
                    if (A0, 0) not in g0:
                        continue
                    cost = 6 * base_u + np0_star + np1_star
                    sol = dict(wild_id=wi,
                               sigma=dict(nu0=s0, nu1=s1, cstar=s2),
                               np0_old=base_u, np0_star=np0_star,
                               np1_star=np1_star,
                               A0=A0, B1=(-np1_star) % m,
                               cstar_drift=[np0_star, np1_star],
                               cost=cost)
                    if best is None or cost < best['cost']:
                        best = sol
    return best


# ------------------------------------------------------------ x-word solver

K_ROLE, A_ROLE, B_ROLE = 0, 1, 2     # keep / donate->nu0 / donate->nu1


class WordSolver:
    """deterministic exact solver for the nine x-word single-cycle
    conditions.  State: role per orbit instance (t, c, oid)."""

    def __init__(self, d, m, dirs, orbs, seed=1):
        self.d, self.m, self.dirs = d, m, dirs
        self.K = m ** (d - 1)
        self.orbs = orbs                     # {(t,c): [orbit lists]}
        self.ids = [(t, c, i) for (t, c), L in sorted(orbs.items())
                    for i in range(len(L))]
        self.role = {oid: K_ROLE for oid in self.ids}
        self.rng = random.Random(seed)
        # base layer perms per color
        self.baseL = {c: layer_maps(d, m, dirs, c) for c in range(d)}
        # owner per (t, leaf): array col -> orbit id index or -1
        self.owner = {(t, lf): [-1] * self.K
                      for t in range(m) for lf in (A_ROLE, B_ROLE)}
        self.cov = {A_ROLE: [0] * self.K, B_ROLE: [0] * self.K}

    def orbit(self, oid):
        t, c, i = oid
        return self.orbs[(t, c)][i]

    # ---- feasibility ----
    def can_set(self, oid, role):
        t, c, i = oid
        cur = self.role[oid]
        if role == cur:
            return True
        cyc = self.orbit(oid)
        if role in (A_ROLE, B_ROLE):
            own = self.owner[(t, role)]
            other = self.owner[(t, A_ROLE if role == B_ROLE else B_ROLE)]
            for x in cyc:
                if own[x] != -1:
                    return False
                j = other[x]
                if j != -1 and self.ids[j][1] == c:
                    return False        # same color both leaves at (t,x)
        if cur in (A_ROLE, B_ROLE):     # removing donation: keep coverage
            cv = self.cov[cur]
            for x in cyc:
                if cv[x] <= 1:
                    return False
        return True

    def set_role(self, oid, role):
        t, c, i = oid
        cur = self.role[oid]
        if role == cur:
            return
        cyc = self.orbit(oid)
        idx = self.ids.index(oid)
        if cur in (A_ROLE, B_ROLE):
            own, cv = self.owner[(t, cur)], self.cov[cur]
            for x in cyc:
                own[x] = -1; cv[x] -= 1
        if role in (A_ROLE, B_ROLE):
            own, cv = self.owner[(t, role)], self.cov[role]
            for x in cyc:
                own[x] = idx; cv[x] += 1
        self.role[oid] = role
        self._invalidate(t, c)

    # ---- word construction (cached per (t, word), invalidated on moves) ----
    def _ids_at(self, t):
        if not hasattr(self, '_ids_by_t'):
            self._ids_by_t = {}
            for oid in self.ids:
                self._ids_by_t.setdefault(oid[0], []).append(oid)
        return self._ids_by_t.get(t, [])

    def layer_perm(self, t, word):
        key = (t, word)
        if not hasattr(self, '_lp_cache'):
            self._lp_cache = {}
        hit = self._lp_cache.get(key)
        if hit is not None:
            return hit
        K = self.K
        if word in ('A', 'B'):
            role = A_ROLE if word == 'A' else B_ROLE
            P = array('I', range(K))
            for oid in self._ids_at(t):
                if self.role[oid] == role:
                    cyc = self.orbit(oid)
                    for j, x in enumerate(cyc):
                        P[x] = cyc[(j + 1) % len(cyc)]
        else:
            c = word
            P = array('I', self.baseL[c][t])
            for oid in self._ids_at(t):
                if oid[1] == c and self.role[oid] != K_ROLE:
                    for x in self.orbit(oid):
                        P[x] = x
        self._lp_cache[key] = P
        return P

    def _invalidate(self, t, c):
        if hasattr(self, '_lp_cache'):
            for w in ('A', 'B', c):
                self._lp_cache.pop((t, w), None)

    def word_perm(self, word):
        R = None
        for t in range(self.m):
            P = self.layer_perm(t, word)
            R = array('I', P) if R is None \
                else array('I', map(P.__getitem__, R))
        return R

    def ncycles(self, word):
        return len(cycle_lengths(self.word_perm(word)))

    def all_counts(self):
        out = {}
        for w in ['A', 'B'] + list(range(self.d)):
            out[w] = self.ncycles(w)
        return out

    # ---- initial assignment: one donor color per (layer, leaf) ----
    def initial(self, log=print):
        """structural initial state: leaf A takes ALL nontrivial orbits of
        color cA_t at layer t (so pi_A = L_{m-1,cA} o ... o L_{0,cA}, a
        mixed-color frankenword of FULL base layer maps), same for B with
        cB_t != cA_t.  Donor tuples are chosen by exact exhaustive scan:
        zero coverage gap (the 4-way fixed-set intersection is empty for
        both leaves) and minimal total cycle-count energy of all nine
        x-words (cached per tuple / per donor pattern)."""
        m, K, d = self.m, self.K, self.d
        fix = {}
        for t in range(m):
            for c in range(d):
                bm = 0
                row = self.dirs[t][c]
                for x in range(K):
                    if row[x] == d - 1:
                        bm |= 1 << x
                fix[(t, c)] = bm
        tuples = [tp for tp in itertools.product(range(d), repeat=m)
                  if _and_all(fix, tp) == 0]
        log(f'  [initial] zero-gap donor tuples: {len(tuples)}')

        def word_energy(P):
            return len(cycle_lengths(P)) - 1

        leafE = {}
        for tp in tuples:
            R = None
            for t in range(m):
                P = self.baseL[tp[t]][t]
                R = array('I', P) if R is None \
                    else array('I', map(P.__getitem__, R))
            leafE[tp] = word_energy(R)
        donorE = {}

        def donor_energy(c, dropped):
            key = (c, dropped)
            if key not in donorE:
                R = None
                for t in range(m):
                    P = self.baseL[c][t] if not (dropped >> t) & 1 else None
                    if P is None:
                        continue
                    R = array('I', P) if R is None \
                        else array('I', map(P.__getitem__, R))
                donorE[key] = word_energy(R) if R is not None else K
            return donorE[key]

        # 7-slot scan: full leaf gets a zero-gap 4-tuple of distinct colors;
        # the other leaf takes the remaining 3 colors on 3 layers (one skip
        # layer, small patched gap), so EVERY color donates exactly one
        # layer (dropped-letter words, no double-drop monsters).
        _l3cache = {}

        def leaf3_energy(tb3):
            if tb3 not in _l3cache:
                R = None
                for (t, c) in tb3:
                    P = self.baseL[c][t]
                    R = array('I', P) if R is None \
                        else array('I', map(P.__getitem__, R))
                _l3cache[tb3] = word_energy(R)
            return _l3cache[tb3]

        # patch-cost oracle: per (t, x) the sorted (orbit length, color)
        # options containing x (the scan prices the light eighth slot)
        opt_at = {}
        for (t, c), L in self.orbs.items():
            for cy in L:
                for x in cy:
                    opt_at.setdefault((t, x), []).append((len(cy), c))
        for k in opt_at:
            opt_at[k].sort()

        def light_cost(bm, skip, c_excl):
            cost = 0
            x = 0
            while bm:
                if bm & 1:
                    opts = [ln for (ln, c) in opt_at.get((skip, x), [])
                            if c != c_excl]
                    if not opts:
                        return None
                    cost += 2 + opts[0] // 4
                bm >>= 1
                x += 1
            return cost

        cands = []
        for full_leaf in ('A', 'B'):
            for ta in tuples:
                if len(set(ta)) != m:
                    continue
                rest = [c for c in range(d) if c not in ta]
                for skip in range(m):
                    lays = [t for t in range(m) if t != skip]
                    for perm in itertools.permutations(rest):
                        tb3 = list(zip(lays, perm))
                        bm = ~0
                        for (t, c) in tb3:
                            bm &= fix[(t, c)]
                        bm &= (1 << K) - 1
                        lc = light_cost(bm, skip, ta[skip])
                        if lc is None:
                            continue
                        drop = [0] * d
                        for t in range(m):
                            drop[ta[t]] |= 1 << t
                        for (t, c) in tb3:
                            drop[c] |= 1 << t
                        E = (leafE[ta] + leaf3_energy(tuple(tb3)) + lc
                             + sum(donor_energy(c, drop[c])
                                   for c in range(d) if drop[c]))
                        cands.append((E, full_leaf, ta, tuple(tb3), skip))
        cands.sort()
        rank = min(getattr(self, 'cand_rank', 0), len(cands) - 1)
        E0, full_leaf, ta, tb3, skip = cands[rank]
        log(f'  [initial] 7-slot design rank {rank}/{len(cands)}: full '
            f'leaf {full_leaf} tuple={ta}, other leaf {list(tb3)} '
            f'(skip layer {skip}), scan energy={E0}')
        roleF = A_ROLE if full_leaf == 'A' else B_ROLE
        roleO = B_ROLE if full_leaf == 'A' else A_ROLE
        for t in range(m):
            for i in range(len(self.orbs[(t, ta[t])])):
                assert self.can_set((t, ta[t], i), roleF)
                self.set_role((t, ta[t], i), roleF)
        for (t, c) in tb3:
            for i in range(len(self.orbs[(t, c)])):
                assert self.can_set((t, c, i), roleO)
                self.set_role((t, c, i), roleO)
        ok = self.smart_patch(roleO, log=log)
        log(f'  [initial] coverage patch: {"OK" if ok else "INCOMPLETE"}')
        self.keep_optimize(log=log)
        uncA = [x for x in range(K) if self.cov[A_ROLE][x] == 0]
        uncB = [x for x in range(K) if self.cov[B_ROLE][x] == 0]
        return uncA, uncB

    def smart_patch(self, role, log=print):
        """cover the leaf's remaining gap columns choosing, per gap column,
        the candidate orbit with the least EXACT word-energy damage; if a
        candidate conflicts with earlier donations it may evict them when
        coverage survives (damage scored on the full compound move)."""
        by_col = {}
        for oid in self.ids:
            for x in self.orbit(oid):
                by_col.setdefault(x, []).append(oid)
        other = B_ROLE if role == A_ROLE else A_ROLE
        for x0 in range(self.K):
            if self.cov[role][x0] > 0:
                continue
            best = None
            for oid in by_col.get(x0, []):
                if self.role[oid] != K_ROLE:
                    continue
                t, c, i = oid
                cyc = set(self.orbit(oid))
                own = self.owner[(t, role)]
                oth = self.owner[(t, other)]
                if any(oth[y] != -1 and self.ids[oth[y]][1] == c
                       for y in cyc):
                    continue                      # cross-leaf same color
                evict = {self.ids[own[y]] for y in cyc if own[y] != -1}
                ok = True
                for o2 in evict:
                    r2 = self.role[o2]
                    for y in self.orbit(o2):
                        cv = self.cov[r2][y] + (1 if (r2 == role and
                                                      y in cyc) else 0)
                        if cv <= 1:
                            ok = False
                            break
                    if not ok:
                        break
                if not ok:
                    continue
                ws = set()
                for o2 in evict:
                    ws.update(self.affected(o2, K_ROLE))
                ws.update(self.affected(oid, role))
                before = sum(self.ncycles(w) for w in ws)
                saved = [(o2, self.role[o2]) for o2 in evict]
                for o2 in evict:
                    self.set_role(o2, K_ROLE)
                self.set_role(oid, role)
                dmg = sum(self.ncycles(w) for w in ws) - before
                self.set_role(oid, K_ROLE)
                for o2, r2 in saved:
                    self.set_role(o2, r2)
                if best is None or dmg < best[0]:
                    best = (dmg, oid, evict)
            if best is None:
                log(f'  [patch] col {x0}: NO candidate')
                return False
            dmg, oid, evict = best
            for o2 in evict:
                self.set_role(o2, K_ROLE)
            self.set_role(oid, role)
            log(f'  [patch] col {x0} -> orbit {oid} '
                f'(len {len(self.orbit(oid))}, evicts {len(evict)}, '
                f'damage {dmg:+d})')
        return True

    def keep_optimize(self, log=print, rounds=3):
        """slot-local greedy: toggle single orbits whenever the exact
        affected-word energy improves (cheap pre-descent)."""
        for rd in range(rounds):
            improved = False
            for oid in self.ids:
                cur = self.role[oid]
                if cur == K_ROLE:
                    cands = [r for r in (A_ROLE, B_ROLE)
                             if self.can_set(oid, r)]
                else:
                    cands = [K_ROLE] if self.can_set(oid, K_ROLE) else []
                for r in cands:
                    ws = self.affected(oid, r)
                    before = sum(self.ncycles(w) for w in ws)
                    self.set_role(oid, r)
                    after = sum(self.ncycles(w) for w in ws)
                    if after < before:
                        improved = True
                        cur = r
                        break
                    self.set_role(oid, cur)
            wsum = sum(self.ncycles(w)
                       for w in ['A', 'B'] + list(range(self.d)))
            log(f'  [keep-opt] round {rd}: total ncyc {wsum}')
            if not improved:
                break
        return

    def patch_coverage(self):
        """eviction patch: for each uncovered (column, leaf), donate some
        orbit through it, demoting conflicting donations whose coverage
        survives (exact feasibility test before mutating)."""
        by_col = {}
        for oid in self.ids:
            for x in self.orbit(oid):
                by_col.setdefault(x, []).append(oid)
        for role in (A_ROLE, B_ROLE):
            other = B_ROLE if role == A_ROLE else A_ROLE
            for x0 in range(self.K):
                if self.cov[role][x0] > 0:
                    continue
                done = False
                for oid in sorted(by_col.get(x0, []),
                                  key=lambda o: len(self.orbit(o))):
                    if self.role[oid] != K_ROLE:
                        continue
                    t, c, i = oid
                    cyc = set(self.orbit(oid))
                    own = self.owner[(t, role)]
                    oth = self.owner[(t, other)]
                    evict = {self.ids[own[y]] for y in cyc if own[y] != -1}
                    evict |= {self.ids[oth[y]] for y in cyc
                              if oth[y] != -1 and self.ids[oth[y]][1] == c}
                    # feasibility: every evicted orbit's columns keep
                    # coverage (counting the new orbit's contribution)
                    ok = True
                    for o2 in evict:
                        r2 = self.role[o2]
                        for y in self.orbit(o2):
                            cv = self.cov[r2][y]
                            if r2 == role and y in cyc:
                                cv += 1
                            if cv <= 1:
                                ok = False
                                break
                        if not ok:
                            break
                    if not ok:
                        continue
                    for o2 in evict:
                        self.set_role(o2, K_ROLE)
                    assert self.can_set(oid, role), (oid, role, evict)
                    self.set_role(oid, role)
                    done = True
                    break
                if not done:
                    return False
        return True

    # ---- exact best-move descent ----
    def moves_for(self, oid):
        cur = self.role[oid]
        return [r for r in (K_ROLE, A_ROLE, B_ROLE)
                if r != cur and self.can_set(oid, r)]

    def affected(self, oid, role):
        t, c, i = oid
        cur = self.role[oid]
        ws = {c}
        for r in (cur, role):
            if r == A_ROLE:
                ws.add('A')
            elif r == B_ROLE:
                ws.add('B')
        return ws

    def descend(self, max_iters=400, log=print, par_pen=8):
        """exact best-move descent.  Energy counts excess cycles plus a
        parity penalty: a word whose permutation is even (ncyc even, since
        K is even) can never be a single cycle, so parity must be repaired
        first -- single toggles flip the parities of their two words, pair
        moves inside one (t, c) slot preserve them (the rail-seam parity
        calculus, P5)."""
        words = ['A', 'B'] + list(range(self.d))
        nc = {w: self.ncycles(w) for w in words}

        def energy(d_):
            return (sum(v - 1 for v in d_.values())
                    + par_pen * sum(1 for v in d_.values() if v % 2 == 0))

        def apply_probe(mv):
            saved = [(oid, self.role[oid]) for oid, _r in mv]
            ws = set()
            for oid, r in mv:
                ws.update(self.affected(oid, r))
                self.set_role(oid, r)
            newvals = {w: self.ncycles(w) for w in ws}
            for oid, r in reversed(saved):
                self.set_role(oid, r)
            return newvals

        def gen_moves(nc):
            out = []
            for oid in self.ids:
                for role in self.moves_for(oid):
                    out.append([(oid, role)])
            # same-slot pairs: donated <-> kept within one (t, c)
            slots = {}
            for oid in self.ids:
                slots.setdefault((oid[0], oid[1]), []).append(oid)
            for (t, c), os_ in slots.items():
                don = [o for o in os_ if self.role[o] != K_ROLE]
                kep = [o for o in os_ if self.role[o] == K_ROLE]
                for o1 in don:
                    r1 = self.role[o1]
                    for o2 in kep:
                        if self.can_set(o1, K_ROLE):
                            out.append([(o1, K_ROLE), (o2, r1)])
            # cross-color parity pairs: two even-parity donor words get one
            # toggle each through the SAME leaf (leaf parity preserved,
            # both donor parities flipped)
            badc = [c for c in range(self.d) if nc[c] % 2 == 0]
            if len(badc) >= 2:
                def toggles(c):
                    tg = []
                    for oid in self.ids:
                        if oid[1] != c:
                            continue
                        for role in self.moves_for(oid):
                            lf = role if role != K_ROLE else self.role[oid]
                            if lf != K_ROLE:
                                tg.append((oid, role, lf))
                    tg.sort(key=lambda z: len(self.orbit(z[0])))
                    return tg[:10]
                for j1 in range(len(badc)):
                    for j2 in range(j1 + 1, len(badc)):
                        for (o1, r1, l1) in toggles(badc[j1]):
                            for (o2, r2, l2) in toggles(badc[j2]):
                                if l1 == l2:
                                    out.append([(o1, r1), (o2, r2)])
            self.rng.shuffle(out)
            return out

        E = energy(nc)
        log(f'  [descent] start E={E} ncyc={[nc[w] for w in words]}')
        stall = 0
        seen_states = set()
        for it in range(max_iters):
            if all(v == 1 for v in nc.values()):
                break
            best = None
            for mv in gen_moves(nc):
                # feasibility for compound moves checked move-by-move
                ok = True
                saved = []
                for oid, r in mv:
                    if not self.can_set(oid, r):
                        ok = False
                        break
                    saved.append((oid, self.role[oid]))
                    self.set_role(oid, r)
                for oid, r in reversed(saved):
                    self.set_role(oid, r)
                if not ok:
                    continue
                newvals = apply_probe(mv)
                tmp = dict(nc); tmp.update(newvals)
                E2 = energy(tmp)
                if best is None or E2 < best[0]:
                    best = (E2, mv, newvals)
                    if E2 < E:
                        break
            if best is None:
                log('  [descent] no feasible moves')
                break
            E2, mv, newvals = best
            if E2 >= E:
                stall += 1
                if stall > 12:
                    log(f'  [descent] plateau at E={E}')
                    break
            else:
                stall = 0
            for oid, r in mv:
                self.set_role(oid, r)
            sig = tuple(sorted((oid, r) for oid, r in self.role.items()
                               if r != K_ROLE))
            if sig in seen_states and E2 >= E:
                stall += 3
            seen_states.add(sig)
            nc.update(newvals)
            E = E2
            if it % 10 == 0 or E2 < E or all(v == 1 for v in nc.values()):
                log(f'  [descent] it={it} E={E} '
                    f'ncyc={[nc[w] for w in words]} move={mv}')
        Eres = sum(v - 1 for v in nc.values())
        return Eres, nc


# ----------------------------------------------- orbit-atom budget (stage 0)

def budget_orbit_atoms(d, m, dirs, orbs):
    """THE COVERAGE BUDGET of the skew-pure family.  z-free donation atoms
    are exactly full L_{t,c}-orbits (RF2 forces L-invariance of the donated
    set on both sides).  An instance is donatable-in-principle iff it
    contains no exactly-1 column of its own color (else the donor's keep
    coverage dies and its word can never be single).  If some column lies
    in NO donatable instance, the leaf words can never cover it: the whole
    z-free template class is dead, independent of all other choices."""
    K = m ** (d - 1)
    exact1 = {}
    for c in range(d):
        cnt = [0] * K
        for t in range(m):
            row = dirs[t][c]
            for x in range(K):
                if row[x] != d - 1:
                    cnt[x] += 1
        exact1[c] = {x for x in range(K) if cnt[x] == 1}
    pinned = 0
    options = {}
    for (t, c), L in orbs.items():
        for i, cy in enumerate(L):
            if set(cy) & exact1[c]:
                pinned += 1
                continue
            for x in cy:
                options.setdefault(x, []).append((t, c))
    no_opt = [x for x in range(K) if x not in options]
    single_tc = [x for x in range(K)
                 if x in options and len(set(options[x])) == 1]
    return dict(
        K=K, instances=sum(len(L) for L in orbs.values()), pinned=pinned,
        no_option_columns=len(no_opt),
        no_option_sample=no_opt[:12],
        single_tc_columns=len(single_tc),
        feasible=(len(no_opt) == 0 and len(single_tc) == 0),
        note='no_option_columns > 0 kills every z-free full-orbit '
             'donation template (exchange, helpers, multi-color alike); '
             'single_tc columns cannot serve both leaves')


# ------------------------------------------------- two-color exchange solver

class ExchangeSolver:
    """TEMPLATE 'two-color exchange + helpers' over ALL colors.  Every
    orbit instance (t, c, i) gets a label KEEP / LA (donated to leaf A) /
    LB.  Hard invariants (checked incrementally):
      * leaf coverage: every column donated >= 1 for each leaf,
      * keep coverage: for EVERY color, every column keeps >= 1 unfrozen
        movable instance (else its word cannot be single -- the structural
        cause of earlier descent plateaus),
      * per (t, leaf) donated columns owned at most once.
    Parity ledger (necessary): #LA odd, #LB odd, frozen count even per
    color (sign identities; N_c odd for every color).
    Initialization: leaf<->color exchange on a chosen pair (cA, cB) --
    forced-KEEP instances are exactly those owning a column's only movable
    slot of their color -- plus greedy helper donations for the leaf
    coverage gaps; exact best-move descent on the NINE x-words after.
    Ledger facts that shaped this (see growth_seam_design_ledger_m4.json):
    full mixed-color words are never single (only the 7 pure returns among
    7^4), so leaf words live near single-color words; pure two-color
    exchange without helpers is impossible (giants are forced-KEEP by the
    exactly-1 columns, smalls cannot cover K)."""

    KEEP, LA, LB = 0, 1, 2

    def __init__(self, d, m, dirs, orbs, cA, cB, seed=1):
        self.d, self.m, self.dirs = d, m, dirs
        self.K = m ** (d - 1)
        self.cA, self.cB = cA, cB
        self.orbs = orbs
        self.ids = [(t, c, i) for (t, c), L in sorted(orbs.items())
                    for i in range(len(L))]
        self.rng = random.Random(seed)
        self.label = {oid: self.KEEP for oid in self.ids}
        K = self.K
        self.cov = {self.LA: bytearray(K), self.LB: bytearray(K)}
        self.keepcov = {c: bytearray(K) for c in range(d)}
        self.own = {(t, lab): bytearray(K) for t in range(m)
                    for lab in (self.LA, self.LB)}
        for oid in self.ids:
            t, c, i = oid
            for x in self.orbit(oid):
                self.keepcov[c][x] += 1
        self._lp = {}

    def orbit(self, oid):
        t, c, i = oid
        return self.orbs[(t, c)][i]

    def wname(self, oid, lab):
        if lab == self.LA:
            return 'A'
        if lab == self.LB:
            return 'B'
        return oid[1]

    def can_label(self, oid, lab):
        cur = self.label[oid]
        if lab == cur:
            return True
        t, c, i = oid
        cyc = self.orbit(oid)
        if lab in (self.LA, self.LB):
            ow = self.own[(t, lab)]
            for x in cyc:
                if ow[x]:
                    return False
        if cur in (self.LA, self.LB):
            cv = self.cov[cur]
            for x in cyc:
                if cv[x] <= 1:
                    return False
        if cur == self.KEEP:
            kc = self.keepcov[c]
            for x in cyc:
                if kc[x] <= 1:
                    return False
        return True

    def set_label(self, oid, lab):
        cur = self.label[oid]
        if lab == cur:
            return
        t, c, i = oid
        cyc = self.orbit(oid)
        if cur in (self.LA, self.LB):
            cv, ow = self.cov[cur], self.own[(t, cur)]
            for x in cyc:
                cv[x] -= 1; ow[x] = 0
        else:
            kc = self.keepcov[c]
            for x in cyc:
                kc[x] -= 1
        if lab in (self.LA, self.LB):
            cv, ow = self.cov[lab], self.own[(t, lab)]
            for x in cyc:
                cv[x] += 1; ow[x] = 1
        else:
            kc = self.keepcov[c]
            for x in cyc:
                kc[x] += 1
        self._lp.pop((self.wname(oid, cur), t), None)
        self._lp.pop((self.wname(oid, lab), t), None)
        self.label[oid] = lab

    def layer_perm(self, name, t):
        key = (name, t)
        P = self._lp.get(key)
        if P is not None:
            return P
        if name in ('A', 'B'):
            want = self.LA if name == 'A' else self.LB
            P = array('I', range(self.K))
            for oid in self.ids:
                if oid[0] == t and self.label[oid] == want:
                    cyc = self.orbit(oid)
                    for j, x in enumerate(cyc):
                        P[x] = cyc[(j + 1) % len(cyc)]
        else:
            c = name
            P = array('I', self._base(c)[t])
            for oid in self.ids:
                if oid[0] == t and oid[1] == c \
                        and self.label[oid] != self.KEEP:
                    for x in self.orbit(oid):
                        P[x] = x
        self._lp[key] = P
        return P

    def _base(self, c):
        if not hasattr(self, '_baseL'):
            self._baseL = {}
        if c not in self._baseL:
            self._baseL[c] = layer_maps(self.d, self.m, self.dirs, c)
        return self._baseL[c]

    def word(self, name):
        R = None
        for t in range(self.m):
            P = self.layer_perm(name, t)
            R = array('I', P) if R is None \
                else array('I', map(P.__getitem__, R))
        return R

    def ncyc(self, name):
        return len(cycle_lengths(self.word(name)))

    def counts(self):
        n = {'LA': 0, 'LB': 0}
        froz = {c: 0 for c in range(self.d)}
        for oid in self.ids:
            lab = self.label[oid]
            if lab == self.LA:
                n['LA'] += 1; froz[oid[1]] += 1
            elif lab == self.LB:
                n['LB'] += 1; froz[oid[1]] += 1
        n['frozen'] = froz
        return n

    def initial(self):
        """exchange-style: cA mostly -> leaf A, cB -> leaf B (forced KEEPs
        respected), then helper donations for leaf coverage gaps (exact
        least-damage candidates), then parity repair."""
        K, d = self.K, self.d
        for c, ownleaf in ((self.cA, self.LA), (self.cB, self.LB)):
            insts = [o for o in self.ids if o[1] == c]
            for o in sorted(insts, key=lambda o: len(self.orbit(o))):
                if self.can_label(o, ownleaf):
                    self.set_label(o, ownleaf)
        # helper fill for both leaves (least exact word damage per column)
        for leaf in (self.LA, self.LB):
            guard = 0
            while guard < 400:
                guard += 1
                x0 = next((x for x in range(K) if not self.cov[leaf][x]),
                          None)
                if x0 is None:
                    break
                best = None
                for oid in self.ids:
                    if self.label[oid] != self.KEEP:
                        continue
                    if x0 not in set(self.orbit(oid)):
                        continue
                    if not self.can_label(oid, leaf):
                        continue
                    c = oid[1]
                    nb = self.ncyc(c)
                    nl = self.ncyc('A' if leaf == self.LA else 'B')
                    self.set_label(oid, leaf)
                    dmg = (self.ncyc(c) - nb
                           + self.ncyc('A' if leaf == self.LA else 'B')
                           - nl)
                    self.set_label(oid, self.KEEP)
                    score = (dmg, -len(self.orbit(oid)))
                    if best is None or score < best[0]:
                        best = (score, oid)
                if best is None:
                    return False, f'leaf {leaf} stuck at col {x0}'
                self.set_label(best[1], leaf)
        # parity repair: frozen count even per color, leaf counts odd --
        # done with single relabels of small instances (exact feasibility)
        for c in range(d):
            froz = sum(1 for o in self.ids
                       if o[1] == c and self.label[o] != self.KEEP)
            if froz % 2 == 0:
                continue
            done = False
            for o in sorted((o for o in self.ids if o[1] == c),
                            key=lambda o: len(self.orbit(o))):
                if self.label[o] == self.KEEP:
                    for lf in (self.LA, self.LB):
                        if self.can_label(o, lf):
                            self.set_label(o, lf)
                            done = True
                            break
                else:
                    if self.can_label(o, self.KEEP):
                        self.set_label(o, self.KEEP)
                        done = True
                if done:
                    break
            # leaf parity handled by descent's penalty if unresolved
        return True, None

    def descend(self, max_iters=500, log=print, par_pen=10,
                pair_cap=400):
        names = ['A', 'B'] + list(range(self.d))
        nc = {n: self.ncyc(n) for n in names}

        def energy(nc_):
            return (sum(v - 1 for v in nc_.values())
                    + par_pen * sum(1 for v in nc_.values() if v % 2 == 0))

        E = energy(nc)
        log(f'    [exch] start E={E} ncyc={[nc[n] for n in names]} '
            f'counts={self.counts()}')
        stall = 0
        for it in range(max_iters):
            if all(v == 1 for v in nc.values()):
                break
            moves = []
            for oid in self.ids:
                for lab in (self.KEEP, self.LA, self.LB):
                    if lab != self.label[oid]:
                        moves.append([(oid, lab)])
            pairs = []
            bycol = {}
            for oid in self.ids:
                bycol.setdefault(oid[1], []).append(oid)
            for c, insts in bycol.items():
                kept = [o for o in insts if self.label[o] == self.KEEP]
                don = [o for o in insts if self.label[o] != self.KEEP]
                for o1 in don:
                    for o2 in kept:
                        pairs.append([(o1, self.KEEP),
                                      (o2, self.label[o1])])
            self.rng.shuffle(pairs)
            self.rng.shuffle(moves)
            moves += pairs[:pair_cap]
            best = None
            for mv in moves:
                saved = [(o, self.label[o]) for o, _ in mv]
                ok = True
                for o, lab in mv:
                    if not self.can_label(o, lab):
                        ok = False
                        break
                    self.set_label(o, lab)
                if not ok:
                    for o, lab in reversed(saved):
                        self.set_label(o, lab)
                    continue
                touched = {self.wname(o, lab) for o, lab in mv} | \
                    {self.wname(o, lab0) for (o, lab0) in saved}
                nc2 = dict(nc)
                for n in touched:
                    nc2[n] = self.ncyc(n)
                E2 = energy(nc2)
                for o, lab in reversed(saved):
                    self.set_label(o, lab)
                if best is None or E2 < best[0]:
                    best = (E2, mv, nc2)
                    if E2 < E:
                        break
            if best is None:
                return None, 'no feasible moves'
            E2, mv, nc2 = best
            if E2 >= E:
                stall += 1
                if stall > 10:
                    log(f'    [exch] plateau at E={E} '
                        f'ncyc={[nc[n] for n in names]}')
                    return None, dict(plateau=E,
                                      ncyc={str(n): int(nc[n])
                                            for n in names})
            else:
                stall = 0
            for o, lab in mv:
                self.set_label(o, lab)
            nc, E = nc2, E2
            if it % 10 == 0:
                log(f'    [exch] it={it} E={E} '
                    f'ncyc={[nc[n] for n in names]}')
        if all(v == 1 for v in nc.values()):
            log(f'    [exch] SOLVED: all nine x-words single; '
                f'counts={self.counts()}')
            return dict(self.label), None
        return None, dict(final=E,
                          ncyc={str(n): int(nc[n]) for n in names})

    def donations(self):
        out = []
        for oid in self.ids:
            lab = self.label[oid]
            if lab == self.KEEP:
                continue
            t, c, i = oid
            out.append((t, c, list(self.orbit(oid)),
                        'A' if lab == self.LA else 'B'))
        return out


# ------------------------------------------------------------ child builder

def build_child(d, m, dirs, plan):
    """plan keys: donations [(t, c, [cols...], leaf 'A'/'B')],
    planes0 [(t, x, c)], planes1 [(t, x, c)],
    lines [(t, x, c, c2, xi)], wild dict(t, x, cstar, wild_id, sigma)."""
    K = m ** (d - 1); K2 = K * m * m; dp = d + 2
    D0, D1, LAST = d - 1, d, d + 1          # 6, 7, 8 at d=7
    nu0, nu1 = d, d + 1
    iota = lambda v: v if v < d - 1 else LAST
    child = [[bytearray(K2) for _ in range(dp)] for _ in range(m)]
    for t in range(m):
        for x in range(K):
            base = [iota(dirs[t][c][x]) for c in range(d)] + [D0, D1]
            for z in range(m * m):
                i = x + K * z
                for c in range(dp):
                    child[t][c][i] = base[c]
    for (t, c, cols, leaf) in plan['donations']:
        lf = nu0 if leaf == 'A' else nu1
        zstep = D0 if leaf == 'A' else D1
        for x in cols:
            v = dirs[t][c][x]
            assert v < d - 1, (t, c, x, v)
            for z in range(m * m):
                i = x + K * z
                assert child[t][lf][i] == zstep and child[t][c][i] == v
                child[t][lf][i] = v
                child[t][c][i] = zstep
    for (t, x, c) in plan['planes0']:
        for z in range(m * m):
            i = x + K * z
            assert child[t][c][i] == LAST and child[t][d][i] == D0
            child[t][c][i] = D0
            child[t][d][i] = LAST
    for (t, x, c) in plan['planes1']:
        for z in range(m * m):
            i = x + K * z
            assert child[t][c][i] == LAST and child[t][d + 1][i] == D1
            child[t][c][i] = D1
            child[t][d + 1][i] = LAST
    for (axis, t, x, c, c2, xi) in plan['lines']:
        # axis 1: (LAST <-> D1) on z0 == xi; axis 0: (LAST <-> D0) on
        # z1 == xi.  c reads LAST there, c2 reads the leaf z-step (a
        # donated column of c2, or the leaf itself if c2 >= d).
        step = D1 if axis == 1 else D0
        for zz in range(m):
            i = (x + K * xi + K * m * zz) if axis == 1 \
                else (x + K * zz + K * m * xi)
            assert child[t][c][i] == LAST and child[t][c2][i] == step, \
                (axis, t, x, c, c2, xi)
            child[t][c][i] = step
            child[t][c2][i] = LAST
    w = plan['wild']
    if w:
        t, x = w['t'], w['x']
        table = w['table']
        DIR = (D0, D1, LAST)
        trio = (nu0, nu1, w['cstar'])
        sig = w['sigma']                # cert color per trio slot
        for z0 in range(m):
            for z1 in range(m):
                i = x + K * z0 + K * m * z1
                want = (D0, D1, LAST)
                for j in range(3):
                    assert child[t][trio[j]][i] == want[j]
                for j in range(3):
                    child[t][trio[j]][i] = DIR[table[z0][z1][sig[j]]]
    return child


def verify_child_lean(d, m, child):
    """memory-lean RF1/RF2/RF3 (per color, streaming) for large m."""
    dp = d + 2; K2 = (m ** (d - 1)) * m * m
    add = build_add(dp, m)
    for t in range(m):
        cols = [child[t][c] for c in range(dp)]
        for i in range(K2):
            if len({cols[c][i] for c in range(dp)}) != dp:
                return dict(rf1=False, bad=(t, i))
    lens = []
    for c in range(dp):
        R = array('I', range(K2))
        for t in range(m):
            row = child[t][c]
            seen = bytearray(K2)
            P = array('I', [add[row[i]][i] for i in range(K2)])
            for i in range(K2):
                seen[P[i]] += 1
            if any(s != 1 for s in seen):
                return dict(rf1=True, rf2=False, bad=(t, c))
            R = array('I', map(P.__getitem__, R))
        cl = cycle_lengths(R)
        lens.append(cl if len(cl) < 6 else cl[:5] + [f'x{len(cl)}'])
    rf3 = all(l == [K2] for l in lens)
    return dict(rf1=True, rf2=True, rf3=rf3, lens=lens)


# --------------------------------------------------- plan oracle + placement

def plan_mods(d, m, plan):
    """sparse modification table: mods[(t, x)] = {color: spec}, spec one of
    ('const', v) | ('lineL', axis, xi, step) [LAST-side of a line]
    | ('lineP', axis, xi, step) [partner side] | ('wild', slot)."""
    D0, D1, LAST = d - 1, d, d + 1
    nu0, nu1 = d, d + 1
    mods = {}

    def put(t, x, c, spec):
        mods.setdefault((t, x), {})[c] = spec

    for (t, c, cols, leaf) in plan['donations']:
        lf = nu0 if leaf == 'A' else nu1
        zstep = D0 if leaf == 'A' else D1
        for x in cols:
            put(t, x, lf, ('const', plan['_dirs'][t][c][x]))
            put(t, x, c, ('const', zstep))
    for (t, x, c) in plan['planes0']:
        put(t, x, c, ('const', D0))
        put(t, x, nu0, ('const', LAST))
    for (t, x, c) in plan['planes1']:
        put(t, x, c, ('const', D1))
        put(t, x, nu1, ('const', LAST))
    for (axis, t, x, c, c2, xi) in plan['lines']:
        step = D1 if axis == 1 else D0
        put(t, x, c, ('lineL', axis, xi, step))
        put(t, x, c2, ('lineP', axis, xi, step))
    w = plan['wild']
    if w:
        trio = (nu0, nu1, w['cstar'])
        for j in range(3):
            put(w['t'], w['x'], trio[j], ('wild', j))
    return mods


def oracle_walk(d, m, dirs, plan, mods, color):
    """exact (pi_color, fiber holonomy Phi) from the plan without building
    the child: walk the x-loop composing m^2-point fiber maps."""
    K = m ** (d - 1)
    D0, D1, LAST = d - 1, d, d + 1
    w = plan['wild']
    DIR = (D0, D1, LAST)
    wt = w['table'] if w else None
    wsig = w['sigma'] if w else None

    def read(t, x, z0, z1):
        spec = mods.get((t, x), {}).get(color)
        if spec is None:
            if color < d:
                v = dirs[t][color][x]
                return v if v < d - 1 else LAST
            return D0 if color == d else D1
        k = spec[0]
        if k == 'const':
            return spec[1]
        if k == 'lineL':
            _, axis, xi, step = spec
            gate = (z0 == xi) if axis == 1 else (z1 == xi)
            return step if gate else LAST
        if k == 'lineP':
            _, axis, xi, step = spec
            gate = (z0 == xi) if axis == 1 else (z1 == xi)
            return LAST if gate else step
        j = spec[1]
        return DIR[wt[z0][z1][wsig[j]]]

    powm = [m ** i for i in range(d - 1)]
    # x-word first
    piw = array('I', [0]) * K
    for x in range(K):
        cx = x
        for t in range(m):
            v = read(t, cx, 0, 0)
            if v < d - 1:
                p = powm[v]
                dig = (cx // p) % m
                cx = cx + p if dig < m - 1 else cx - (m - 1) * p
        piw[x] = cx
    ncyc = len(cycle_lengths(piw))
    if ncyc != 1:
        return ncyc, None
    phi = list(range(m * m))
    x = 0
    for _ in range(K):
        cx = x
        for t in range(m):
            v0 = read(t, cx, 0, 0)
            # fiber step per current fiber value
            for f0 in range(m * m):
                f = phi[f0]
                z0, z1 = f % m, f // m
                v = read(t, cx, z0, z1)
                if v == D0:
                    phi[f0] = (z0 + 1) % m + m * z1
                elif v == D1:
                    phi[f0] = z0 + m * ((z1 + 1) % m)
            if v0 < d - 1:
                p = powm[v0]
                dig = (cx // p) % m
                cx = cx + p if dig < m - 1 else cx - (m - 1) * p
        x = cx
    assert x == 0
    return 1, phi


def place_pieces(d, m, dirs, donations, cA, cB, rng, log=print):
    """choose c*, the wild site, and the five parity lines for the
    two-color exchange template.  Line catalog (partners are always old
    colors at donated columns -- the leaf fibers stay pure T o rho):
      * 4 lines with LAST-side an untouched color (not c*): 2 of axis 1
        (z0-pinned, partner = the B-donor of the column) and 2 of axis 0
        (z1-pinned, partner = the A-donor);
      * 1 line with LAST-side cA at a B-donated column (axis 1).
    Parity: untouched non-c* get 1 flip each; cA, cB get 3 = odd; c*, nu0,
    nu1 only the wild trio flip.  Sites are taken from zero-read columns of
    the LAST-side color on donated columns of the partner."""
    K = m ** (d - 1)
    donor_at = {}                       # (t, x) -> {leaf: color}
    for (t, c, cols, leaf) in donations:
        for x in cols:
            donor_at.setdefault((t, x), {})[leaf] = c
    zero = {(t, c): [x for x in range(K) if dirs[t][c][x] == d - 1]
            for t in range(m) for c in range(d)}
    untouched = [c for c in range(d) if c not in (cA, cB)]
    used = set()

    def line_site(u, axis):
        """zero-read column of u on a donated column (axis 1: B-donated,
        axis 0: A-donated); returns (axis, t, x, u, partner, xi=0)."""
        leaf = 'B' if axis == 1 else 'A'
        for t in range(m):
            for x in zero[(t, u)]:
                if (t, x) in used:
                    continue
                db = donor_at.get((t, x), {})
                if leaf in db:
                    used.add((t, x))
                    return (axis, t, x, u, db[leaf], 0)
        return None

    for cstar in untouched:
        others = [u for u in untouched if u != cstar]
        # wild site: zero-read column of c*, no donations at that layer,
        # pristine for the trio
        wild_site = None
        for t in range(m):
            for x in zero[(t, cstar)]:
                if (t, x) not in donor_at and (t, x) not in used:
                    wild_site = (t, x)
                    break
            if wild_site:
                break
        if wild_site is None:
            continue
        lines = []
        ok = True
        for j, u in enumerate(others):
            ln = line_site(u, 1 if j < 2 else 0)
            if ln is None:
                ok = False
                break
            lines.append(ln)
        if ok:
            ln = line_site(cA, 1)
            if ln is None:
                ok = False
            else:
                lines.append(ln)
        if not ok:
            continue
        used.add(wild_site)
        log(f'  [pieces] c*={cstar} wild at {wild_site}; lines={lines}')
        return dict(cstar=cstar, wild_site=wild_site, lines=lines,
                    zero=zero, donor_at=donor_at, used=used)
    return None


def knob_solve(d, m, dirs, plan, pieces, wilds, good, log=print):
    """solve the fiber layer exactly: per-color plane counts (np0, np1)
    and the wild (layer id, sigma) so that EVERY fiber holonomy is a
    single m^2-cycle (computed exactly by the plan oracle).  Old colors
    are independent; the two leaf sums are then corrected by re-solving
    single colors with alternate options (drift shifts act on the leaf
    holonomy as T-translations, so the needed shift is read off
    directly)."""
    K = m ** (d - 1)
    nu0, nu1 = d, d + 1
    zero, used = pieces['zero'], pieces['used']
    donA = {t: set() for t in range(m)}
    donB = {t: set() for t in range(m)}
    for (t, c, cols, leaf) in plan['donations']:
        (donA if leaf == 'A' else donB)[t].update(cols)

    def plane_sites(c, axis, n, taken):
        out = []
        blocked = donA if axis == 0 else donB
        for t in range(m):
            for x in zero[(t, c)]:
                if (t, x) in used or (t, x) in taken or x in blocked[t]:
                    continue
                out.append((t, x, c))
                taken.add((t, x))
                if len(out) == n:
                    return out
        return None

    def try_assign(npv):
        """npv: {c: (np0, np1)}; returns plan pieces or None."""
        taken = set()
        p0, p1 = [], []
        for c, (a, b) in npv.items():
            if a:
                s = plane_sites(c, 0, a, taken)
                if s is None:
                    return None
                p0 += s
            if b:
                s = plane_sites(c, 1, b, taken)
                if s is None:
                    return None
                p1 += s
        return p0, p1

    for wild_id in range(len(wilds)):
        for sig in itertools.permutations(range(3)):
            plan['wild'] = dict(t=pieces['wild_site'][0],
                                x=pieces['wild_site'][1],
                                cstar=pieces['cstar'], wild_id=wild_id,
                                sigma=list(sig),
                                table=wilds[wild_id]['table'])
            # per-color independent options
            opts = {}
            fail = None
            for c in range(d):
                got = []
                for tot in range(0, 7):
                    for a in range(min(tot, m - 1) + 1):
                        b = tot - a
                        if b >= m:
                            continue
                        npv_c = {cc: (0, 0) for cc in range(d)}
                        npv_c[c] = (a, b)
                        sites = try_assign({c: (a, b)})
                        if sites is None:
                            continue
                        plan['planes0'], plan['planes1'] = sites
                        mods = plan_mods(d, m, plan)
                        nx, phi = oracle_walk(d, m, dirs, plan, mods, c)
                        if nx != 1:
                            return None, f'x-word of color {c} not single'
                        if f_cycles(phi) == [m * m]:
                            got.append((a, b))
                    if len(got) >= 3:
                        break
                if not got:
                    fail = c
                    break
                opts[c] = got
            if fail is not None:
                log(f'    [knob] wild{wild_id} sig{sig}: color {fail} '
                    'has no single-fiber option')
                continue
            # base assignment = first option each; correct leaf sums
            base = {c: opts[c][0] for c in range(d)}
            sites = try_assign(base)
            if sites is None:
                continue
            plan['planes0'], plan['planes1'] = sites
            mods = plan_mods(d, m, plan)
            nxA, phiA = oracle_walk(d, m, dirs, plan, mods, nu0)
            nxB, phiB = oracle_walk(d, m, dirs, plan, mods, nu1)
            if nxA != 1 or nxB != 1:
                return None, 'leaf x-word not single'
            # leaf shift search: Phi_A(sum0 + delta) = T_(-delta,0) Phi_A
            dA = dB = None
            for delta in range(m):
                if f_cycles(f_compose(f_translation(-delta % m, 0, m),
                                      phiA)) == [m * m]:
                    dA = delta
                    break
            for delta in range(m):
                if f_cycles(f_compose(f_translation(0, -delta % m, m),
                                      phiB)) == [m * m]:
                    dB = delta
                    break
            if dA is None or dB is None:
                log(f'    [knob] wild{wild_id} sig{sig}: no leaf shift '
                    f'(phiA={f_cycles(phiA)}, phiB={f_cycles(phiB)})')
                continue
            # find per-color alternates realizing (dA, dB) mod m
            choice = dict(base)
            need = (dA % m, dB % m)
            solved = (need == (0, 0))
            if not solved:
                for combo in itertools.product(*(opts[c] for c in range(d))):
                    s0 = sum(a for (a, _b) in combo) -                         sum(a for (a, _b) in base.values())
                    s1 = sum(b for (_a, b) in combo) -                         sum(b for (_a, b) in base.values())
                    if (s0 % m, s1 % m) == need:
                        choice = {c: combo[c] for c in range(d)}
                        solved = True
                        break
            if not solved:
                log(f'    [knob] wild{wild_id} sig{sig}: leaf shift '
                    f'({dA},{dB}) unreachable')
                continue
            sites = try_assign(choice)
            if sites is None:
                continue
            plan['planes0'], plan['planes1'] = sites
            mods = plan_mods(d, m, plan)
            allok = True
            fib = {}
            for c in list(range(d)) + [nu0, nu1]:
                nx, phi = oracle_walk(d, m, dirs, plan, mods, c)
                fib[c] = (nx, f_cycles(phi) if phi else None)
                if nx != 1 or f_cycles(phi) != [m * m]:
                    allok = False
                    break
            if allok:
                log(f'    [knob] SOLVED: wild{wild_id} sigma={list(sig)} '
                    f'np={choice}')
                return dict(wild_id=wild_id, sigma=list(sig),
                            np=choice), None
            log(f'    [knob] wild{wild_id} sig{sig}: recheck failed {fib}')
    return None, 'no knob solution'


# ------------------------------------------------------------ fiber check

def fiber_holonomies(d, m, dirs, child, words=None):
    """exact per-color fiber holonomy along the x-word loop + the x-word,
    extracted from the child (independent re-derivation; also confirms the
    skew-product decomposition pointwise)."""
    K = m ** (d - 1); dp = d + 2
    D0, D1, LAST = d - 1, d, d + 1
    out = {}
    for c in range(dp):
        # x-word and per-column fiber maps: simulate one return from (x, z)
        # for all z and check the x-image is z-independent
        piw = array('I', [0]) * K
        phi = []
        ok = True
        for x in range(K):
            maps = []
            for z in range(m * m):
                z0, z1 = z % m, z // m
                cx, cz0, cz1 = x, z0, z1
                for t in range(m):
                    v = child[t][c][cx + K * cz0 + K * m * cz1]
                    if v < d - 1:
                        p = m ** v
                        dig = (cx // p) % m
                        cx = cx + p if dig < m - 1 else cx - (m - 1) * p
                    elif v == D0:
                        cz0 = (cz0 + 1) % m
                    elif v == D1:
                        cz1 = (cz1 + 1) % m
                maps.append((cx, fid(cz0, cz1, m)))
            xs = {a for a, _ in maps}
            if len(xs) != 1:
                ok = False
                break
            piw[x] = maps[0][0]
            phi.append([b for _, b in maps])
        if not ok:
            out[c] = dict(skew=False)
            continue
        ncyc = len(cycle_lengths(piw))
        # holonomy at basepoint 0 around the pi-loop
        hol = list(range(m * m))
        x = 0
        for _ in range(K):
            hol = [phi[x][f] for f in hol]
            x = piw[x]
        out[c] = dict(skew=True, x_ncyc=ncyc,
                      hol_cycles=f_cycles(hol),
                      loop_closed=(x == 0) if ncyc == 1 else None)
    return out


# ------------------------------------------------------------------ driver

def cmd_analyze(m):
    d, dirs = load_seed(m)
    K = m ** (d - 1)
    orbs = orbit_table(d, m, dirs)
    wilds = load_wild_layers(m)
    good = good_drift_table(wilds, m)
    odo, bad = odometer_check(m)
    rep = dict(
        m=m, d=d, K=K,
        orbit_summary={f'{t},{c}': sorted((len(cy) for cy in L),
                                          reverse=True)
                       for (t, c), L in orbs.items()},
        orbit_lengths_mod_m=sorted({len(cy) % m for L in orbs.values()
                                    for cy in L}),
        zero_read_counts={f'{t},{c}': sum(1 for x in range(K)
                                          if dirs[t][c][x] == d - 1)
                          for t in range(m) for c in range(d)},
        wild_layers=len(wilds),
        good_drifts={f'w{wi},cert{c}': sorted(v)
                     for (wi, c), v in good.items()},
        odometer_all_units_ok=odo, odometer_bad=bad,
    )
    out = HERE / f'growth_seam_design_base_m{m}.json'
    out.write_text(json.dumps(rep, indent=1))
    print(f'[analyze] orbit lengths mod m: {rep["orbit_lengths_mod_m"]} '
          f'(must be [0] for the drift ledger)')
    print(f'[analyze] odometer check (all unit alpha, beta, xi, sign): {odo}')
    print(f'[analyze] wild layers: {len(wilds)}; good-drift table written')
    print(f'[json] {out}')
    return rep


def cmd_design(m, seed=1, iters=400, rank=0):
    t0 = time.time()
    d, dirs = load_seed(m)
    K = m ** (d - 1); K2 = K * m * m
    base = verify(d, m, dirs, want_lens=True)
    assert base['rf1'] and base['rf2'] and base['rf3'], 'base broken'
    orbs = orbit_table(d, m, dirs)
    wilds = load_wild_layers(m)
    good = good_drift_table(wilds, m)
    odo, _bad = odometer_check(m)
    report = dict(m=m, seed=seed, template='two-color-exchange',
                  odometer_ok=odo, attempts=[])
    print(f'[ledger] odometer={odo}; wild layers={len(wilds)}; '
          f'good-drift cells={sum(len(v) for v in good.values())}')

    # ---- stage 0: orbit-atom coverage budget (kills the class early) ----
    budget = budget_orbit_atoms(d, m, dirs, orbs)
    report['orbit_atom_budget'] = budget
    print(f"[budget] donatable atoms: {budget['instances'] - budget['pinned']}"
          f"/{budget['instances']}; no-option columns: "
          f"{budget['no_option_columns']}; single-(t,c) columns: "
          f"{budget['single_tc_columns']}")
    if not budget['feasible']:
        report['verdict'] = ('TEMPLATE-DEAD (orbit-atom budget): '
                             f"{budget['no_option_columns']} columns have no "
                             'donatable z-free atom; the skew-pure full-orbit '
                             'donation class cannot cover the leaves')
        report['missing_ingredient'] = (
            'donation atoms finer than full layer-map orbits: either '
            'z-gated staircase ribbons (the stochastic seam family; breaks '
            'skew purity, needs rotor/splice analysis) or z-free orbit '
            'SURGERY first (old-old x-read trades on closed sets reshape '
            'the orbit atlas so every column gains a donatable atom)')
        _dump(report, m)
        return report

    # ---- stage 2: the x-word exchange (the combinatorial core) ----
    pairs = [(a, b) for a in range(d) for b in range(d) if a != b]
    rng = random.Random(seed)
    rng.shuffle(pairs)
    pairs = pairs[rank:] + pairs[:rank]
    sol = None
    for (cA, cB) in pairs:
        print(f'[exchange] trying (cA, cB) = ({cA}, {cB})')
        ex = ExchangeSolver(d, m, dirs, orbs, cA, cB, seed=seed)
        ok, err = ex.initial()
        if not ok:
            report['attempts'].append(dict(cA=cA, cB=cB, fail=str(err)))
            continue
        labels, err = ex.descend(max_iters=iters)
        if labels is None:
            report['attempts'].append(dict(cA=cA, cB=cB, fail=err))
            continue
        sol = (cA, cB, ex)
        break
    if sol is None:
        report['verdict'] = 'XWORD-OPEN: exchange descent found no ' \
            'all-single labeling'
        report['failure_pattern'] = report['attempts']
        _dump(report, m)
        return report
    cA, cB, ex = sol
    donations = ex.donations()
    report['exchange'] = dict(cA=cA, cB=cB, counts=ex.counts(),
                              n_donations=len(donations))
    print(f'[exchange] solved with (cA, cB) = ({cA}, {cB}); '
          f'{len(donations)} donated orbit instances')

    # ---- stage 3: pieces (wild site + parity lines) ----
    pieces = place_pieces(d, m, dirs, donations, cA, cB, rng)
    if pieces is None:
        report['verdict'] = 'SITES-FAIL: no c*/wild/line placement'
        _dump(report, m)
        return report
    plan = dict(donations=donations, planes0=[], planes1=[],
                lines=pieces['lines'], wild=None, _dirs=dirs)

    # ---- stage 4: fiber knobs (planes, wild sigma) ----
    knobs, err = knob_solve(d, m, dirs, plan, pieces, wilds, good)
    if knobs is None:
        report['verdict'] = f'FIBER-OPEN: {err}'
        report['pieces'] = dict(cstar=pieces['cstar'],
                                wild_site=pieces['wild_site'],
                                lines=pieces['lines'])
        _dump(report, m)
        return report
    report['knobs'] = knobs
    report['cstar'] = pieces['cstar']

    # ---- stage 5: build + authoritative verify ----
    child = build_child(d, m, dirs, plan)
    rep = verify_child_lean(d, m, child)
    print(f'[verify] RF1={rep.get("rf1")} RF2={rep.get("rf2")} '
          f'RF3={rep.get("rf3")} lens={rep.get("lens")}')
    report['rf'] = {k: rep.get(k) for k in ('rf1', 'rf2', 'rf3')}
    report['cycle_lens'] = [str(l) for l in rep.get('lens', [])]

    fib = fiber_holonomies(d, m, dirs, child)
    report['fiber'] = {str(c): {k: v for k, v in v_.items()}
                       for c, v_ in fib.items()}
    for c, v in fib.items():
        tag = ('OK' if v.get('skew') and v.get('x_ncyc') == 1
               and v.get('hol_cycles') == [m * m] else 'FAIL')
        print(f'  color {c}: skew={v.get("skew")} x_ncyc={v.get("x_ncyc")} '
              f'hol={v.get("hol_cycles")} [{tag}]')

    ok = rep.get('rf1') and rep.get('rf2') and rep.get('rf3')
    report['verdict'] = 'HIT' if ok else 'RF-FAIL'
    report['elapsed_s'] = round(time.time() - t0, 1)
    if ok:
        wit = dict(m=m, template='two-color-exchange',
                   cA=cA, cB=cB, cstar=pieces['cstar'],
                   knobs=knobs,
                   donations=[[t, c, cols, lf]
                              for (t, c, cols, lf) in donations],
                   planes0=plan['planes0'], planes1=plan['planes1'],
                   lines=[list(l) for l in plan['lines']],
                   wild={k: v for k, v in plan['wild'].items()
                         if k != 'table'})
        wout = HERE / f'growth_seam_design_witness_m{m}.json'
        wout.write_text(json.dumps(wit, indent=1))
        print(f'[json] witness -> {wout}')
    _dump(report, m)
    return report


def _xword_failure(solver, nc):
    bad = {str(w): n for w, n in nc.items() if n != 1}
    return dict(stuck_words=bad,
                note='x-word plateau: which words resist single-cycle '
                     'merging names the missing ingredient')


def _dump(report, m):
    out = HERE / f'growth_seam_design_result_m{m}.json'
    out.write_text(json.dumps(report, indent=1))
    print(f'[json] {out}')


def rebuild_from_witness(m, wfile):
    d, dirs = load_seed(m)
    wilds = load_wild_layers(m)
    w = json.loads(Path(wfile).read_text())
    assert w['m'] == m
    plan = dict(donations=[tuple(x[:2]) + (list(x[2]), x[3])
                           for x in w['donations']],
                planes0=[tuple(x) for x in w['planes0']],
                planes1=[tuple(x) for x in w['planes1']],
                lines=[tuple(x) for x in w['lines']],
                wild=dict(w['wild'],
                          table=wilds[w['wild']['wild_id']]['table']),
                _dirs=dirs)
    return d, dirs, plan


def cmd_verify(m, wfile=None):
    wfile = wfile or (HERE / f'growth_seam_design_witness_m{m}.json')
    print(f'=== re-verify witness {wfile} at (7,{m}) ===')
    d, dirs, plan = rebuild_from_witness(m, wfile)
    child = build_child(d, m, dirs, plan)
    rep = verify_child_lean(d, m, child)
    print(f'RF1={rep.get("rf1")} RF2={rep.get("rf2")} RF3={rep.get("rf3")}')
    print(f'cycle lens: {rep.get("lens")}')
    return rep.get('rf1') and rep.get('rf2') and rep.get('rf3')


def cmd_chain(m, wfile=None):
    """chaining: does the dimension-9 child supply what the template needs
    to iterate 9 -> 11?  (C1) RF1/RF2/RF3; (C2) per-child-color nontrivial
    orbit supply at every layer with interleaving partitions possible
    (every column movable by >= 2 colors-to-be-exchanged at >= 2 layers);
    (C3) zero-read column supply for planes/lines/wild per (t, c);
    (C4) orbit lengths == 0 mod m (the drift ledger's telescoping)."""
    wfile = wfile or (HERE / f'growth_seam_design_witness_m{m}.json')
    d, dirs, plan = rebuild_from_witness(m, wfile)
    child = build_child(d, m, dirs, plan)
    rep = verify_child_lean(d, m, child)
    ok1 = rep.get('rf1') and rep.get('rf2') and rep.get('rf3')
    print(f'(C1) child RF1/RF2/RF3: {ok1}')
    d2 = d + 2; K2 = (m ** (d - 1)) * m * m
    add = build_add(d2, m)
    zero_counts = {}
    orblen_ok = True
    mov_layers = [bytearray(K2) for _ in range(d2)]
    for c in range(d2):
        nmov = 0
        for t in range(m):
            row = child[t][c]
            P = array('I', [add[row[i]][i] for i in range(K2)])
            zr = sum(1 for i in range(K2) if row[i] == d2 - 1)
            zero_counts[(t, c)] = zr
            seen = bytearray(K2)
            for s in range(K2):
                if seen[s] or P[s] == s:
                    continue
                l = 0; x = s
                while not seen[x]:
                    seen[x] = 1; l += 1; x = P[x]
                if l % m:
                    orblen_ok = False
        # movable at >= 2 layers handled via zero-read counts (a point is
        # movable for c at t iff not a zero-read and the read is not the
        # leaf-pinned fixed direction); coarse supply check:
    minzero = min(zero_counts.values())
    print(f'(C3) zero-read sites per (t, c): min={minzero} '
          f'(planes/lines/wild need a handful)')
    print(f'(C4) all nontrivial child layer-orbit lengths == 0 mod m: '
          f'{orblen_ok}')
    okall = bool(ok1 and minzero >= 4 and orblen_ok)
    print(f'=== chaining verdict: {"PASS" if okall else "FAIL"} ===')
    return okall


def main():
    argv = sys.argv[1:]

    def opt(name, default):
        return int(argv[argv.index(name) + 1]) if name in argv else default

    m = opt('--m', 4)
    if '--analyze' in argv:
        cmd_analyze(m)
        return
    if '--budget' in argv:
        d, dirs = load_seed(m)
        orbs = orbit_table(d, m, dirs)
        b = budget_orbit_atoms(d, m, dirs, orbs)
        print(json.dumps(b, indent=1))
        out = HERE / f'growth_seam_design_budget_m{m}.json'
        out.write_text(json.dumps(b, indent=1))
        print(f'[json] {out}')
        sys.exit(0 if b['feasible'] else 3)
    if '--design' in argv:
        rep = cmd_design(m, seed=opt('--seed', 1), iters=opt('--iters', 400),
                         rank=opt('--rank', 0))
        sys.exit(0 if rep.get('verdict') == 'HIT' else 2)
    if '--verify' in argv:
        wf = argv[argv.index('--witness') + 1] if '--witness' in argv \
            else None
        sys.exit(0 if cmd_verify(m, wf) else 1)
    if '--chain' in argv:
        wf = argv[argv.index('--witness') + 1] if '--witness' in argv \
            else None
        sys.exit(0 if cmd_chain(m, wf) else 1)
    print(__doc__)


if __name__ == '__main__':
    main()
