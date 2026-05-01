# A5 to A7 and D5 Even Bundle Absorption

Date: 2026-05-01.

Source bundles:

- `/data/angel/repos/etc/A5_to_A7_induction_hypothesis_bundle_v0_1.zip`
- `/data/angel/repos/etc/d5_even_routeE_bundle_v0_1.zip`

This note records the goal-level changes after reading both bundles.  It is a
research-state update, not a completion certificate.

## Goal Adjustment

The active goal should be sharpened in two places.

First, the D7 odd additive explanation remains the central structural target,
but the missing theorem is now better described as two independent targets:

- **Target A:** construct all-odd multi-`P` base row schedules for `A5(m)`,
  with seven row words, column exact cover, and single `m^4` base returns.
- **Target B':** for a chosen Target-A schedule, construct a zero-set-only
  fiber compiler `K_m(Z)` whose two `A3` scalar monodromy invariants are units.

This replaces the weaker description "find an arbitrary state-dependent
fiber compiler" with a more formalization-ready split: base primitiveity by a
section-splice proof, and fiber primitiveity by finite zero-set stratum scalar
counts.

Second, the D5 even track should no longer be described only as a generic
seam-orbit certificate search.  The bundle supplies a more concrete Route-E
track:

- one perturbed zero-set table `Lambda_E`, obtained from the odd `Lambda_1`
  table by changing two representative rows;
- schedules of the form constant layers plus one `Lambda_E` layer for even
  `m >= 6`, with `m = 4` handled as a separate finite `C/E/O` witness;
- a symbolic reduction to a one-map return `F_{nu,s}`;
- an open-port section theorem where `nu = (0,A,B,C,0)` and `gcd(C,m)=1`;
- the remaining all-even gap as residue-class count/drift families plus
  origin-excursion affine chart certificates.

Thus the D5 even item in the project goal should be revised to:

> D5 even is a separate Route-E periodic-excursion certificate track: prove
> all-even one-`Lambda_E` count/drift coverage and origin-excursion chart
> certificates, with `m = 4` packaged as a finite witness.

## A5 to A7 Findings

The A5-to-A7 bundle confirms that the direct lift of the original mixed D5
schedule is obstructed.  In the `4+2` bridge, one `P`-type layer contributes
exactly five base `P` occurrences, while seven one-`P` rows would require seven
occurrences.  The impossible equation is `5k = 7`.  Therefore the bridge must
use all-zero-set spread with multi-`P` base words, or leave this local bridge
model.

The bundle also gives a finite stratum-count reduction for zero-set-only
fiber tables.  For exact zero-set `S` in `A5(m)`, the count modulo `m` depends
only on `|S|`:

```text
|S| = 0 ->  4
|S| = 1 -> -3
|S| = 2 ->  2
|S| = 3 -> -1
|S| = 4 ->  0
|S| = 5 ->  1
```

For a fixed row schedule and zero-set-only `K_m(Z)`, the two A3 monodromy
scalars are therefore finite mask sums.  Target B' is exactly the condition
that those scalar pairs are units modulo `m` for every color.

The `m = 9` scalar certificate records the same zero-set-only `K(Z)` table
already checked in the current baseline, with scalar invariants:

```text
A = (5,7,2,1,1,1,1)
E = (2,2,2,4,4,5,8)
```

All entries are units modulo `9`.  This strengthens the interpretation that
the fiber problem is a finite mask-design problem once Target A supplies the
base schedule.

The current Target-A proof interface is a section-splice theorem on

```text
Sigma = {(0,a,b,0,-a-b) : a+b != 0}.
```

For a base word family `W_m`, the desired symbolic facts are:

- every point of `Sigma` returns positively to `Sigma`;
- the induced first-return map on `Sigma` is one cycle;
- the total excursion length is `m^4`.

Candidate short patterns mentioned by the bundle include:

```text
332
01302
4204204
```

The existing `m=5,7,9` finite rows should be used as trace data, not as a
substitute for this symbolic Target-A proof.

The repo now has `scripts/analyze_targetA_section.py` for this interface.  It
checks a candidate base word for primitiveity, first return to `Sigma`,
section-cycle structure, total excursion length, all-state segment coverage,
and coarse partition diagnostics for possible symbolic first-return tables.

Initial finite audit:

- `01302` is primitive and passes the `Sigma` section audit at `m = 5`.
- `332`, `01302`, and `4204204` are all primitive and pass the section audit
  at `m = 9`.
- none of `332`, `01302`, `4204204` is primitive for
  `m = 7,11,13,15,17`.
- the first length-5 `m = 17` primitive examples
  `01121`, `01214`, `10112`, `11210`, and `12101` all pass the section audit
  at `m = 17`, but do not work unchanged for `m = 5,7,9,11,13,15`.

This reinforces that Target A likely needs a congruence-dependent or
constructed row family, not one fixed short word.

A primitive-word scan up to length `5` for odd `m = 5,7,...,21` gives a more
nuanced picture:

- `23` and `32` appear as primitive words for
  `m = 5,9,11,13,15,19,21`;
- `m = 7` first needs length `3` words such as `004`, `040`, `400`;
- `m = 17` first needs length `5` words in the current scan;
- the `m = 17` length-5 examples are not reusable unchanged at
  `m = 5,7,9,11,13,15`.

So a plausible Target-A route is not a single base word.  It is either a
finite congruence family of primitive words, or a constructive/padding theorem
that produces seven exact-cover rows from a small pool of modulus-dependent
primitive words.

## D5 Even Route-E Findings

The Route-E bundle verifies finite schedules for

```text
m = 4,6,8,10,12,14,16,18,20.
```

For each listed `m`, all five color returns are single cycles of length
`m^4` on `A5(m)`.

The symbolic core now written down is:

- one-`Lambda_E` schedules have return map
  `F_{nu,s}(w) = w + nu + e_{p_s(w)}`;
- cyclic equivariance reduces the five color returns to a single color-0
  return map;
- for `s = 0` and `nu = (0,A,B,C,0)`, the completed open-port section map is
  `H_{A,C}(sigma,a) = (sigma-C, a+A+1-1_{sigma=0})`;
- if `gcd(C,m)=1`, this completed section map is a single `m^2` cycle;
- the remaining primitiveity proof is the origin-excursion lemma outside the
  section.

The all-even proof gap is therefore concrete:

- find residue-class affine count/drift families covering every even `m >= 6`;
- prove the origin-excursion affine chart certificates for those families;
- package `m = 4` as a finite witness theorem.

The bundle's periodic probe shows why this is not yet solved: one signed drift
family works for some even moduli but fails for others.  For example, the
drift pattern `[0, -4, 2, 1, 0]` is single for `m=10,22,34,40`, but fails for
`m=12,46` in the recorded probe.

## Verification Performed

The A5-to-A7 bridge certificates from the bundle were replayed with the repo
verifier:

```text
verified m=5 product_states=15625 rows=7 base_rank_steps=ok section_rank_steps=ok return_cycles=single
verified m=7 product_states=117649 rows=7 base_rank_steps=ok section_rank_steps=ok return_cycles=single
verified m=9 product_states=531441 rows=7 base_rank_steps=ok section_rank_steps=ok return_cycles=single
```

The D5 even Route-E verifier from the bundle was absorbed as
`scripts/verify_d5_even_routeE.py`.  It independently checks:

- the finite schedule table through `m = 20`;
- the normalized Route-E core first-return formula through `m = 20`, including
  the expected `m = 2` failure;
- the open-port section formula and `H`-cycle criterion on the bundle's
  recorded examples.

## Revised Missing Propositions

The clearest proof obligations are now:

1. **D7 Target A:** for every odd `m >= 5`, construct seven all-zero-set
   `A5` base rows with column exact cover and base rank step into
   `ZMod (m^4)`.
2. **D7 Target B':** for each Target-A schedule family, construct a
   zero-set-only or finite congruence-family `K_m(Z)` and prove the stratum
   scalar unit conditions giving the `A3` fiber rank step into `ZMod (m^2)`.
3. **D5 even Route-E count coverage:** for every even `m >= 6`, construct
   one-`Lambda_E` counts/slot data satisfying the symbolic section hypotheses.
4. **D5 even origin excursion:** prove the affine chart certificates that
   cover the complement of the open-port section and return to the correct
   re-entry point.
5. **Finite exceptional packaging:** keep D7 odd `m = 3` and D5 even `m = 4`
   as separate finite witness branches.

The D7 odd torus/Cayley endpoint remains a regression target; these new tasks
are structural explanations and even-track certificate construction, not
requirements for the already closed odd D7 theorem.
