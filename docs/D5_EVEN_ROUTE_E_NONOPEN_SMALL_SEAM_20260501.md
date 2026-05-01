# D5 Even Route-E Non-Open Small Seam

Date: 2026-05-01.

Source bundle:

- `/data/angel/repos/etc/d5_even_routeE_nonopen_small_seam_v0_4.zip`

This note records the small-seam update for the D5 even Route-E track.  It is
an audit and research-state note, not an all-even symbolic theorem.

## Main Update

For one-`Lambda_E` schedules

```text
C_0^nu0 C_1^nu1 C_2^nu2 C_3^nu3 C_4^nu4 E_s,
sum_i nu_i = m - 1,
```

the normalized return is

```text
F_{nu,s}(w) = w + nu + e_{p_s(w)},
p_s(w) = Lambda_E(Z(w)-1)(s).
```

The non-open schedules in the bundle do not require a large origin-excursion
chart.  For each E-slot `s`, use the cyclically shifted seam

```text
Theta_s = { rho_s(0,a,0,0,-a) : a != 0 }.
```

This seam has size `m-1`.  It is a port line for coordinate

```text
j = s + 2 mod 5.
```

For example, `s = 0` gives `(0,a,0,0,-a)` and `j = 2`; `s = 4` gives
`(a,0,0,-a,0)` and `j = 1`.

## Direct Criterion

Let `V` be the first-return map of `F_{nu,s}` to `Theta_s`.  If

```text
V is a single cycle on Theta_s
sum_{theta in Theta_s} tau(theta) = m^4,
```

then `F_{nu,s}` is a single cycle on `A5(m)`.

This is the standard first-return counting argument: one seam cycle stitches
all excursions into one closed orbit, and the return-time sum equal to `m^4`
forces that orbit to cover the whole root state space.

## Verified Range

The bundle supplies one-`Lambda_E` schedules for every even
`m = 6,8,...,60`.  Each satisfies:

- every seam start has the expected port `j = s+2`;
- the first return on `Theta_s` is one cycle of length `m-1`;
- the return-time sum is `m^4`.

The schedule table from the bundle is now embedded in
`scripts/verify_d5_even_routeE.py` as `SMALL_SEAM_CASES`.

The Lean-facing target for these traces is now:

```text
D5Odd/EvenRouteE.lean
```

It defines `RouteECounts`, the nonzero parameter seam
`RouteENonzeroSeam m = {a : ZMod m // a != 0}`, and proves that this seam has
cardinality `m-1`.  It also records the explicit shifted seam point
`routeEThetaPoint slot a`, matching the bundle's
`rho_s(0,a,0,0,-a)`, and proves that both the raw `ZMod m` parametrization and
the subtype `RouteENonzeroSeam m` parametrization are injective.  The generic
`RouteESmallSeamCertificate` now derives the needed root-return orbit target
from:

- an injective seam parametrization;
- first-return equations and no-earlier-return witnesses;
- a single cycle on the induced seam map;
- the return-time sum `m^4`.

There is a coordinate convention worth making explicit.  `D5Odd/Even.lean`
uses `Vec4` as the `rootZ` projection of `Vec5`, i.e. coordinates `1..4`, not
coordinates `0..3`.  Thus the bundle point `(0,a,0,0,-a)` is represented in
Lean as `![a,0,0,-a]`.  The file now defines the underlying `Vec5` point
`routeEThetaVec slot a` and proves:

- `Root5 m (routeEThetaVec slot a)`;
- `rootZ (routeEThetaVec slot a) = routeEThetaPoint slot a`;
- `(rootOfZ (routeEThetaPoint slot a)).1 = routeEThetaVec slot a`.
- the coordinate identities `routeEThetaVec_pos_param`,
  `routeEThetaVec_neg_param`, and `routeEThetaVec_port_zero`;
- the verifier's `start_ok` port statement
  `LambdaE (zeroMaskMinusOne (routeEThetaVec slot a)) slot = slot+2 mod 5`
  for `a != 0`, as `LambdaE_routeEThetaVec` and
  `LambdaE_routeEThetaSeam`.

The Route-E zero-set table `LambdaE` is therefore no longer only an `m=4`
implementation detail: it is part of the general Route-E interface in
`D5Odd/EvenRouteE.lean`, where `LambdaE_latin` and `LambdaE_cyclic` record
its finite table invariants.  `D5Odd/EvenRouteEM4.lean` reuses that
definition.

The canonical wrapper `RouteEThetaSmallSeamCertificate` now fixes both the
seam type `RouteENonzeroSeam m` and the seam map
`routeEThetaSeamPoint slot`, i.e. the exact `Theta_s` seam from the bundle.
It lowers to `RouteENonopenSmallSeamCertificate` and then routes any completed
Route-E certificate through the existing `D5Odd.Even` seam endpoint to D5
Hamilton, torus, and Cayley decompositions.

It also records the finite-exception packaging shape.  The target
`D5EvenRouteEM4FiniteTarget` is now closed in `D5Odd/EvenRouteEM4.lean` by a
finite `C/E/O/O` four-layer schedule.  Lean verifies exact cover and Latin
conditions by finite decision, proves the five color returns are single cycles
using generated `ZMod 256` rank tables, and packages the unconditional
Hamilton witness.

With that finite branch available, Lean proves that:

- `D5EvenRouteEAllLargeEvenTarget` gives
  all even `m >= 4` Hamilton, torus, and Cayley targets;
- the same conclusion follows from the non-open specialized target
  `D5EvenRouteENonopenAllLargeEvenTarget`;
- and also from the canonical bundle-seam target
  `D5EvenRouteEThetaAllLargeEvenTarget`.

Thus the remaining D5 even Route-E obligation is isolated to the all-large
`m >= 6` small-seam proof.

The repo-side verification command used for this absorption was:

```bash
python3 scripts/verify_d5_even_routeE.py --mode section \
  --small-seam-moduli all \
  --json-out /tmp/d5_even_routeE_small_seam_all.json
```

It reported:

```text
cases = 28
range = 6..60
all_ok = True
seam_sizes_ok = True
return_sums_ok = True
```

The v0.4 bundle was also re-read directly: its
`outputs/d5_even_routeE_small_seam_extended_cases.tsv` table has the same
`28` rows as the repo's `SMALL_SEAM_CASES`, with matching `(slot, counts)` for
every even `m = 6,8,...,60`.  The standalone C++ checker compiled from
`scripts/fast_d5_routeE_small_seam_verify.cpp` reports `ok 1` for all `28`
embedded cases.

The verifier now also emits proof-facing data for the induced seam map:

- `translation_blocks`: maximal intervals in `a = 1,...,m-1` on which
  `V(a)-a mod m` is constant;
- `translation_block_count`: the number of such blocks;
- `orbit_prefix_from_1`: a short prefix of the single seam cycle.

This is intended as the finite trace format for the next symbolic
block-splice proof.  For example, the recorded `m = 44` schedule has only two
translation blocks:

```text
[1,20]  -> delta 23
[21,43] -> delta 24
```

The C++ checker from the bundle is also retained as
`scripts/fast_d5_routeE_small_seam_verify.cpp`.  It verifies one recorded
`(m, slot, counts)` case at a time and gives an implementation-independent
cross-check of the same `start_ok`, one-cycle, and return-time-sum criterion.

The follow-up family scanner:

```bash
python3 scripts/analyze_d5_routeE_small_seam_families.py \
  --json-out /tmp/d5_routeE_small_seam_family_scan.json
```

tests whether the finite `m = 6,8,...,60` table is already compatible with
simple affine normalized count vectors on residue classes.  It reports that
periods `4,6,...,26` all fail exact affine fits on at least one residue class,
while periods `28` and `30` have no robust affine class because each class has
at most two samples.  Thus the current table is strong evidence for the
small-seam criterion, but it should not be treated as an extracted all-even
count formula.

## Revised D5 Even Route-E Gap

The non-open branch should no longer be described as an unresolved
`m^4`-state chart problem.  The evidence now reduces it to a one-dimensional
small-seam first-return problem.

The remaining symbolic propositions are:

1. construct residue-class formulas for `(s,nu)` covering every even
   `m >= 6`;
2. for each residue family, prove the induced small-seam map on
   `a = 1,...,m-1` is one cycle;
3. prove the return-time sum identity `sum tau = m^4` for each family;
4. provide the Lean first-return equations/minimality witnesses needed by
   `RouteEThetaSmallSeamCertificate`.

The finite `m = 4` witness required by `D5EvenRouteEM4FiniteTarget` is now
closed separately and no longer belongs to the open symbolic gap.

This is closer to the final lane-map proof shape in the D3 even Route-E
argument than to a high-dimensional SAT/chart certificate.
