# A5 to A7 and D5 Even Bundle Absorption

Date: 2026-05-01.

Source bundles:

- `/data/angel/repos/etc/A5_to_A7_induction_hypothesis_bundle_v0_1.zip`
- `/data/angel/repos/etc/d5_even_routeE_bundle_v0_1.zip`

Post-update bundle absorbed later:

- `/data/angel/repos/etc/A5_to_A7_post_bundle_update_v0_2.zip`
- `/data/angel/repos/etc/A5_to_A7_current_proofs_bundle_v0_3.zip`
- `/data/angel/repos/etc/A5_to_A7_current_proofs_bundle_note_v0_3.md`
- `/data/angel/repos/etc/d5_even_routeE_nonopen_small_seam_v0_4.zip`

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
- the initial all-even gap as residue-class count/drift families plus
  origin-excursion affine chart certificates, later sharpened by
  `d5_even_routeE_nonopen_small_seam_v0_4.zip` to a one-dimensional
  small-seam first-return problem.

Thus the D5 even item in the project goal should be revised to:

> D5 even is a separate Route-E periodic-excursion certificate track: prove
> all-even one-`Lambda_E` count/slot coverage and, for each residue family, a
> small-seam first-return cycle plus return-time sum certificate; package
> `m = 4` as a finite witness.

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

All entries are units modulo `9`.  `scripts/verify_zero_set_k_cert.py` now
checks this scalar-only certificate directly: it expands the shifted-mask
`K(Z)` table into a full kappa table, verifies these unit invariants, and then
runs the full bridge verifier.  This strengthens the interpretation that the
fiber problem is a finite mask-design problem once Target A supplies the base
schedule.

The paired check of the original zero-set table cert and the scalar cert gives
the expected mixed summary: the original cert has no scalar field, so it
reports `scalar_ok=False`, but both certs pass table expansion and full bridge
verification; the scalar cert additionally passes the unit-invariant check.

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
- direct testing of the short core `23` through odd `m <= 37` shows failures
  exactly at `m = 7,17,27,37` in that range.  The later post-update bundle
  sharpens this into the structural class `m == 2 mod 5`, equivalently
  `m == 7 mod 10` among odd moduli;
- the currently recorded `m = 7` and `m = 17` exceptional primitive words do
  not work unchanged at `m = 27` or `m = 37`.
- a faster C++ helper, `scripts/search_targetA_primitive_words.cpp`, found
  `m = 27` primitive words `22414`, `24142`, `441144`, and `332332`; all four
  pass the `Sigma` section audit at `m = 27`.
- those `m = 27` words do not work unchanged at `m = 7,17,37`; naive random
  search at `m = 37` is already heavy enough that the next search step should
  add pruning or a structural parametrization rather than simply increasing
  samples.
- after adding orbit-only and explicit-word modes to the C++ helper, the
  symmetry closure of the known `m=7,17,27` words still gives no `m = 37`
  primitive word, and an exhaustive length-5 chunk scan for `m = 37` found no
  hit.  A length-6 chunk search then found `m = 37` primitive words
  `404432`, `044324`, `324044`, `432404`, and `443240`; all five pass the
  `Sigma` section audit at `m = 37`.

The post-update bundle refines this conclusion.  A plausible Target-A route is
not a single base word for all odd `m`, but it may have a single generic short
core: `23` and `32` appear to work for all odd `m >= 5` with `m != 2 mod 5`.
The bad class `m == 2 mod 5` should be treated as a five-component seam
splicing problem, not just as a blind primitive-word search.

For both `23` and `32`, the post bundle records that the total excursion
length over

```text
Sigma = {(0,a,b,0,-a-b) : a+b != 0}
```

remains `m^4` in all tested odd moduli.  The failure in the bad class is that
the induced map on `Sigma` splits into five cycles.  The transversal
`Sigma0 = {(a,0) : a != 0}` has return law `a -> a+1`, so the generic proof
target is now seam connectivity to `Sigma0`, and the exceptional proof target
is the explicit five-cycle decomposition and a correction-word splice.

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
- before the non-open small-seam update, the remaining primitiveity proof for
  this open-port subfamily was an origin-excursion lemma outside the section.

The verifier now also has a section-scan mode.  In the tested even range
`m = 6,8,...,60`, the uniform open-port triple

```text
(A,B,C) = (0,m-2,1)
```

passes the section formula and gives a single `H` cycle, with one exception
point `(m-1,2)`.  This explains why the open-port section theorem is useful but
not by itself a full all-even proof.

A later open-port full-cycle scan separates this further.  Among section
passing open-port triples, full one-cycle returns are found at
`m = 10,12,14,18,20`, but no open-port full hit is found at `m = 6,8,16`.
Those missing residue classes explain why the Route-E track still needs
non-open-port count/slot families or another return section, not just the
`H`-cycle theorem.

A broader one-`Lambda_E` count/slot scan restores positive witnesses in those
missing cases.  It finds full one-cycle returns for `m = 6,8,16` outside the
open-port normal form, and also finds additional hits for the already-positive
moduli.  This sharpens the remaining task: extract symbolic residue-class
count/slot families from the larger one-`Lambda_E` hit set.  The later v0.4
small-seam bundle gives the preferred certificate shape for those families:
prove the induced map on `Theta_s` is one cycle and that the return-time sum is
`m^4`.

The scan also records normalized counts after cyclically rotating the E-slot
to `0`.  This is the right comparison layer for residue-family extraction:
some hits differ only by cyclic slot rotation, while the normalized first hits
at `m = 6,8,16` remain visibly non-open-port.

The normalized output now also records support/zero positions and whether a
hit matches the bundled finite schedule's normalized count vector.  This
separates rotated copies of known witnesses from genuinely different
count-vector hits, which is the data needed before guessing residue families.

A later non-open small-seam bundle changes the shape of this gap.  For the
one-`Lambda_E` schedule with E-slot `s`, the natural seam is

```text
Theta_s = { rho_s(0,a,0,0,-a) : a != 0 }.
```

It has size `m-1` and is a port line for `j = s+2 mod 5`.  The direct
criterion is: if the first return to `Theta_s` is one cycle and the return-time
sum is `m^4`, then the full normalized return is a single `m^4` cycle.

The bundle verifies this criterion for recorded schedules at every even
`m = 6,8,...,60`.  The repo verifier now embeds those cases and reproduces the
check with:

```bash
python3 scripts/verify_d5_even_routeE.py --mode section \
  --small-seam-moduli all \
  --json-out /tmp/d5_even_routeE_small_seam_all.json
```

The local absorption run reported `28` cases, range `6..60`, and
`all_ok=True`.

The all-even proof gap is therefore more concrete:

- find residue-class affine count/drift families covering every even `m >= 6`;
- prove the one-dimensional small-seam map and return-time sum identities for
  those families;
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
  recorded examples and the section-scan family through `m = 60`.
- the later non-open small-seam criterion for the recorded schedules
  `m = 6,8,...,60`, including seam port starts, first-return one-cycle, and
  return-time sum `m^4`.

## Revised Missing Propositions

The clearest proof obligations are now:

1. **D7 Target A:** for every odd `m >= 5`, construct seven all-zero-set
   `A5` base rows with column exact cover and base rank step into
   `ZMod (m^4)`.  The current split is: prove the `23/32` section theorem
   for `m != 2 mod 5`, and construct correction rows for `m == 2 mod 5`.
2. **D7 Target B':** for each Target-A schedule family, construct a
   zero-set-only or finite congruence-family `K_m(Z)` and prove the stratum
   scalar unit conditions giving the `A3` fiber rank step into `ZMod (m^2)`.
3. **D5 even Route-E count coverage:** for every even `m >= 6`, construct
   one-`Lambda_E` counts/slot data satisfying either the open-port section
   hypotheses or the small-seam hypotheses.
4. **D5 even small-seam arithmetic:** for each count/slot residue family,
   prove the induced size `m-1` seam map is one cycle and prove the
   return-time sum identity `m^4`.
5. **Finite exceptional packaging:** keep D7 odd `m = 3` and D5 even `m = 4`
   as separate finite witness branches.

The D7 odd torus/Cayley endpoint remains a regression target; these new tasks
are structural explanations and even-track certificate construction, not
requirements for the already closed odd D7 theorem.
