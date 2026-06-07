#!/usr/bin/env python3
"""
Root-flat certificate verifier for the even-modulus directed tori formalization.

Purpose (independent of the Lean proof): take the paper's finite tables / the
constructions used by the Lean holes and check, computationally, that they are
*correct root-flat certificates* in the exact sense the Lean schedule uses:

  RF1  rowLatin        : at every (t, w) the colors -> directions map is a bijection
  RF2  layerBijective  : every layer map  w |-> rootStep(dir(t,w,c), w)  is a bijection
  RF3  returnsSingleCycle : every colour first-return (compose m layers) is one
                            single (m^n)-cycle on the section (Fin n -> ZMod m)

These are *exactly* `Shared.RootFlatSchedule.{rowLatin,layerBijective,returnsSingleCycle}`
with `step = StandardRootFlatLift.rootStep`.  So a `dir` table that passes
`verify_rootflat` here is a valid `RootFlatCycle.RootFlatCycleData n m` candidate:
the user can check any Lean `dir` *before* attempting the kernel proof.

Sections:
  A. re-run the paper's finite checks (independent confirmation of printed tables)
  B. terminal A2 carriers F_i are m^2-cycles for even m  (H1 / D3-base content)
  C. D5(4) section-11 reset returns R_hat_i are 256-cycles (H2 / matches LowD5M4Seed)
  D. generic RF1/RF2/RF3 verifier (the reusable tool)
  E. worked, verified example: the D2(m) anti-diagonal root-flat schedule
     (validates the verifier on a known-good certificate; template for new dirs)

Dependency-free; pure Python.
"""
from __future__ import annotations
from itertools import product
from typing import Callable, Dict, List, Tuple

# ---------------------------------------------------------------------------
# A. paper finite checks (re-used verbatim from scripts/verify_finite_checks.py)
# ---------------------------------------------------------------------------

def add(p, q, m): return ((p[0] + q[0]) % m, (p[1] + q[1]) % m)
def sub(p, q, m): return ((p[0] - q[0]) % m, (p[1] - q[1]) % m)

def omega(q, m):
    """Terminal A2 row word omega_m(q) in S_3 (terminal_A2_block.tex)."""
    p = (1 % m, 2 % m)
    eH, eV, eD = (1, 0), (0, 1), (-1, 1)
    tau02, tau12, tau01 = (2, 1, 0), (0, 2, 1), (1, 0, 2)
    chi_plus, chi_minus = (1, 2, 0), (2, 0, 1)
    default = (0, 1, 2)
    for e, tau, minus_turn, plus_turn in [
        (eH, tau02, chi_minus, chi_plus),
        (eV, tau12, chi_plus, chi_minus),
        (eD, tau01, chi_minus, chi_plus),
    ]:
        for t in range(m):
            if add(p, ((t * e[0]) % m, (t * e[1]) % m), m) == q:
                if t == 0: return default
                if t == 1 % m: return plus_turn
                if t == (-1) % m: return minus_turn
                return tau
    return default

def F(i, z, m):
    """Run-collapsed terminal first return F_i (terminal_A2_block.tex)."""
    a = [(1, 0), (0, 1), (0, 0)]
    Delta = [(0, 1), (1, 0), (1, -1)]
    z2 = add(z, Delta[i], m)
    q = sub(z2, a[i], m)
    w = omega(q, m)[i]
    return add(q, a[w], m)

def orbit_len(f, start, m):
    seen = set(); x = start
    while x not in seen:
        seen.add(x); x = f(x, m)
    return len(seen), x

# ---------------------------------------------------------------------------
# B. terminal cyclicity for even m  (the H1 / D3-base RF3 content)
# ---------------------------------------------------------------------------

def check_terminal_cyclicity(moduli=(4, 6, 8, 10, 12)) -> None:
    for m in moduli:
        for i in range(3):
            length, back = orbit_len(lambda z, mm: F(i, z, mm), (0, 0), m)
            assert length == m * m and back == (0, 0), (m, i, length)
    print(f"  [B] terminal F_0,F_1,F_2 are m^2-cycles for even m in {moduli}  OK")

# ---------------------------------------------------------------------------
# C. D5(4) section-11 reset returns  (the H2 RF3 content; matches LowD5M4Seed)
# ---------------------------------------------------------------------------

def check_d5m4_reset_returns() -> None:
    m = 4
    p = [(0, 0), (1, 0), (2, 2)]            # reset sites p0,p1,p2
    def T(i, qy):
        q, y = qy
        return (F(i, q, m), (y + (1 if q == p[i] else 0)) % m)
    def P0(qy):
        q, y = qy
        return (F(0, q, m) if y == 0 else q, (y + 1) % m)
    def P1(qy):
        q, y = qy
        if   y == 1: q2 = F(0, q, m)
        elif y == 2: q2 = F(2, q, m)
        elif y == 3: q2 = F(1, q, m)
        else:        q2 = q
        return (q2, (y + 1) % m)
    R = [lambda qy: T(0, qy), lambda qy: T(1, qy), lambda qy: T(2, qy), P0, P1]
    a = [((0, 0), 0), ((0, 0), 1), ((0, 0), 2), ((0, 0), 3), ((0, 1), 0)]  # z-sites
    def Rhat(i, xz):
        x, z = xz
        return (R[i](x), (z + (1 if x == a[i] else 0)) % m)
    # state = ((q, y), z); 16*4*4 = 256
    start = (((0, 0), 0), 0)
    for i in range(5):
        seen = set(); x = start
        f = lambda s, _i=i: Rhat(_i, s)
        while x not in seen:
            seen.add(x); x = f(x)
        assert len(seen) == 256 and x == start, (i, len(seen))
    print("  [C] D5(4) section-11 returns R_hat_0..R_hat_4 are 256-cycles  OK"
          "  (independent cross-check of LowD5M4Seed.fullReturn_singleCycle)")

# ---------------------------------------------------------------------------
# D. generic RF1/RF2/RF3 verifier  (exact Lean root-flat semantics)
# ---------------------------------------------------------------------------

Dir = Callable[[int, Tuple[int, ...], int], int]  # dir(t, w, c) -> direction 0..n

def root_step(n: int, m: int, d: int, w: Tuple[int, ...]) -> Tuple[int, ...]:
    """StandardRootFlatLift.rootStep: direction d<n increments coord d; d==n no-op."""
    if d == n:
        return w
    lw = list(w); lw[d] = (lw[d] + 1) % m
    return tuple(lw)

def verify_rootflat(n: int, m: int, dir_fn: Dir, verbose: bool = False) -> Dict[str, bool]:
    """Check RF1/RF2/RF3 for a root-flat schedule on (Fin n -> ZMod m), n+1 colors."""
    states = list(product(range(m), repeat=n))
    colors = directions = list(range(n + 1))
    layers = list(range(m))

    # RF1 rowLatin: for each (t,w), c |-> dir(t,w,c) is a bijection of {0..n}.
    rf1 = True
    for t in layers:
        for w in states:
            img = [dir_fn(t, w, c) for c in colors]
            if sorted(img) != directions:
                rf1 = False
                if verbose: print(f"    RF1 fail at t={t} w={w}: {img}")
                break
        if not rf1: break

    # RF2 layerBijective: for each (t,c), w |-> rootStep(dir(t,w,c), w) is a bijection.
    rf2 = True
    for t in layers:
        for c in colors:
            img = [root_step(n, m, dir_fn(t, w, c), w) for w in states]
            if len(set(img)) != len(states):
                rf2 = False
                if verbose: print(f"    RF2 fail at t={t} c={c}")
                break
        if not rf2: break

    # RF3 returnsSingleCycle: returnMap_c (compose m layers) is one (m^n)-cycle.
    def return_map(c, w):
        for t in layers:
            w = root_step(n, m, dir_fn(t, w, c), w)
        return w
    rf3 = True
    N = len(states)
    for c in colors:
        seen = set(); x = states[0]
        while x not in seen:
            seen.add(x); x = return_map(c, x)
        if len(seen) != N or x != states[0]:
            rf3 = False
            if verbose: print(f"    RF3 fail for color {c}: orbit {len(seen)}/{N}")
    return {"RF1": rf1, "RF2": rf2, "RF3": rf3}

# ---------------------------------------------------------------------------
# E. worked verified example: D2(m) anti-diagonal root-flat schedule
#    (root_flat_first_returns.tex, Prop "two-dimensional anti-diagonal base")
# ---------------------------------------------------------------------------

def d2_antidiagonal_dir(t: int, w: Tuple[int, ...], c: int) -> int:
    """n=1 (d=2). At the height-0 layer color 0 increments the free coord
    (direction 0); elsewhere it takes the no-op direction 1.  Color 1 is the
    complementary Latin choice.  returnMap_0 = +1, returnMap_1 = +(m-1)."""
    if c == 0:
        return 0 if t == 0 else 1
    else:
        return 1 if t == 0 else 0

def check_verifier_on_d2(moduli=(4, 6, 8)) -> None:
    for m in moduli:
        res = verify_rootflat(1, m, d2_antidiagonal_dir)
        assert all(res.values()), (m, res)
    print(f"  [E] D2(m) anti-diagonal passes RF1/RF2/RF3 for even m in {moduli}  OK"
          "  (validates the verifier on a known-good certificate)")

# ---------------------------------------------------------------------------

def main() -> None:
    print("Root-flat certificate verification")
    print("  [A] paper finite checks (scripts/verify_finite_checks.py): "
          "run that script separately; re-derived ingredients below.")
    check_terminal_cyclicity()
    check_d5m4_reset_returns()
    check_verifier_on_d2()
    print("All root-flat certificate checks passed.")
    print()
    print("To check a candidate Lean dir for a hole, call:")
    print("    verify_rootflat(n, m, dir_fn)   # n = d-1; returns {RF1,RF2,RF3}")
    print("e.g. D7(6): n=6, m=6 (m^n = 46656 states -- slow but exact)")

if __name__ == "__main__":
    main()
