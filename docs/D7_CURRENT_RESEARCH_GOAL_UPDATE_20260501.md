# D7 Current Research Goal Update

Date: 2026-05-01

Source bundle:

- `/data/angel/repos/etc/D7_current_research_note_bundle_v1_1.zip`

This note records the revised project goal after reading the current D7 research
bundle. It is meant to keep the Lean state, the mathematical story, and the
next proof obligations in one place.

## Executive Update

The bundle changes the center of gravity of the project.

The D=7 odd Hamilton decomposition theorem should now be treated as a closed
Lean endpoint and regression target. The remaining research value is not to
reprove D=7 odd by the same direct route, but to explain why the D=5 and D=3
mechanisms combine into D=7. The sharp structural candidate is the additive
`4+2` bridge

```text
A7(m) ~= A5(m) x A3(m)
```

using the all-zero-set D5 layer deformation plus a D3 fiber compiler. This is a
better immediate target than a full prime-p abstraction of the D7 canonical
family.

## Current Repository State

The current committed Lean state contains these relevant pieces.

- D7 odd is available as a closed handoff theorem, including the torus/Cayley
  endpoint. The bundle agrees with the implemented split into the canonical
  odd branch for large odd `m` and finite branches for `m=3,5`.
- D7 even has a `RootFlatSchedule` target shape, but still needs an actual even
  certificate construction.
- D5 even seam compatibility is now automatic in Lean, but the orbit/cycle
  certificate is still missing. The current SAT seam encoding reports `unsat`
  for the small `m=2` smoke check, so it is a negative/debugging check rather
  than a positive certificate for the even theorem.
- A generic composite product theorem exists in `RoundComposite.lean`. It is
  useful as an abstract reduction.  The concrete graph-level Cayley product is
  now formalized for the standard Cayley target: the left-coordinatized product
  theorem is combined with finite single-cycle coordinate extraction to derive
  the standard Cayley pointwise composite expansion.
- A shared return-lift library exists in `Shared/ReturnLift.lean`, covering the
  periodic return lemmas that were previously duplicated in D3/D5/D7 style
  arguments.
- A D7 prime-interface regression exists for the current `Fin 7` canonical
  family. Full prime-p generalization is still premature.

## What The Bundle Adds

The bundle makes four points especially clear.

First, the D7 odd theorem is already closed by the direct D7 package:

- odd `m >= 7`: canonical reduced-count construction with `q=6`;
- `m=3,5`: finite zero-set selector and rank certificates;
- all colors pass the single-cycle return check.

Second, the D5-to-D7 story is not multiplicative. The promising route is
additive:

```text
A_{a+b+1}(m) ~= A_{a+1}(m) x A_{b+1}(m)
```

with a state-dependent B-slot permutation `kappa_{t,u}`. The product return is
a skew product, and single-cycle behavior is governed by the base return plus
the fiber monodromy over one base cycle.

Third, the original D5 odd packet is not directly suitable as the base of the
`4+2` bridge. The bundle identifies a structural obstruction: with the original
single nonconstant layer, rows using fiber-extra slots can collapse the base
projection to a translation of order at most `m`, not the required `m^4`.

Fourth, the all-zero-set D5 deformation is the live bridge candidate. For
`m=5,7,9`, the bundle reports successful `4+2` constructions on the full state
spaces:

```text
m=5:  5^6   states
m=7:  7^6   states
m=9:  9^6   states
```

All seven returns are single cycles in these searches. The evidence points to
an all-odd `m >= 5` structural lemma, but the current data does not yet amount
to a uniform proof.

## Revised Goal

The active goal should be revised as follows.

1. Keep the closed D7 odd theorem as a regression target, not as the main
   unresolved target.
2. Complete the concrete composite theorem by connecting the abstract
   `RoundComposite` product result to the actual torus/Cayley decomposition
   statement used by the paper.
3. Extract the root-flat return criterion into a shared theorem: row Latin,
   layer bijective, and single-cycle return imply a Hamilton decomposition.
4. Formalize the additive bridge interface separately from the multiplicative
   composite theorem.
5. Make the `4+2` all-zero-set bridge the central D7 structural explanation:
   prove it for all odd `m >= 5`, and keep `m=3` as a direct finite D7
   certificate branch.
6. Treat the `3+3` D4 route as diagnostic or negative unless a new D4 packet is
   found. The current root-fixed extracted D4 packet has an extra-capacity
   obstruction at `m=3`.
7. Keep D5 even as a separate seam-orbit certificate problem.
8. Keep D7 even as a separate `RootFlatSchedule` certificate construction
   problem.
9. Postpone the full prime-p canonical-family abstraction until the D7 `4+2`
   bridge and the D5/D7 certificate tracks are stable.

In short: the prime-p abstraction remains valuable, but it is no longer the
best next structural move. The all-zero-set additive bridge is the clearer
mathematical target.

## Proof Obligations Now Exposed

The following statements are the cleanest remaining proof obligations.

### Root-Flat Return Criterion

Statement shape:

```text
rowLatin(schedule)
layerBijective(schedule)
returnSingleCycle(schedule, c) for every color c
--------------------------------------------------
the schedule gives a Hamilton decomposition
```

The D7 handoff already uses this idea in fixed form. The next useful step is to
make it a shared theorem over the finite root-flat state space used by D3, D5,
and D7.

### Additive Local Bridge

Given a decomposition

```text
A_{a+b+1}(m) ~= A_{a+1}(m) x A_{b+1}(m),
```

prove that a base layer, a fiber layer, and a state-dependent B-slot
permutation `kappa_{t,u}` produce a valid product layer. The local obligations
are:

- source Latin property;
- layer bijectivity;
- preservation of the root-flat chart.

The bundle indicates that this local part is already mathematically solved in
the notes.

### Additive Monodromy Criterion

Formalize the skew-product return theorem:

```text
P(u,v) = (P_base(u), Psi(u)(v)).
```

The product return is a single cycle if and only if:

- `P_base` is a single cycle on the base states;
- the fiber monodromy over one full base cycle is a single cycle on the fiber.

This theorem is the conceptual bridge between finite symbolic searches and a
human-readable D5/D3-to-D7 proof.

### All-Zero-Set `4+2` Base Rows

For every odd `m >= 5`, construct seven row words over slots `0..6` such that:

- every column is a permutation of the seven slots;
- the base projection uses the all-zero-set D5 layer deformation;
- the induced base return on `A5(m)` has the required primitive behavior.

This is the first main open lemma for the structural D7 story.

### All-Zero-Set `4+2` Fiber Compiler

For the same rows, construct the state-dependent fiber slot permutation
`kappa` so that the A3 fiber monodromy is a single cycle.

The bundle gives simple formulas in small cases:

```text
m=5: kappa rotation depends on p(Z) + 2 |Z| mod 3
m=7: kappa rotation depends on 2 |Z| + 2 mod 3
```

No comparable restricted affine formula was found for `m=9`, so the theorem
may need a more flexible zero-set table or a first-return section argument.

### D7 Small Zero-Set Certificates

The `m=3,5` finite certificates should remain part of the D7 odd regression
suite. Their bundle form is:

```text
m=3: offsets s0=2, s2=4
m=5: offsets s0=1, s2=2, s3=5, s4=6
```

Each color has one return cycle of length `m^6`.

### D4 Packet Capacity Obstruction

The extracted D4 packet from the diagonal self-square is useful, but the
bundle records a concrete obstruction for the `3+3` route at `m=3` under
root-fixed coordinate conjugations. This can be formalized as a negative lemma
or kept as a search constraint.

### D5 Even Seam Orbit Certificate

D5 even is still missing the real orbit certificate. The Lean compatibility
interface has been simplified, but the theorem remains blocked on proving the
cycle structure of the even seam construction.

### Concrete Composite Expansion

This interface gap is now closed for the standard Cayley/Torus target used in
this repo.  The product construction still factors internally through explicit
left-factor cycle coordinates, but those coordinates are now extracted from any
nontrivial finite single-cycle Cayley endpoint, giving graph-level
`StandardCayleySolved` and `StandardTorusSolved` pointwise composite
expansions.

## Integrated Research Narrative

The cleaned-up story is now:

1. D=3 supplies the fully understood base case.
2. Composite dimensions reduce through the multiplicative product theorem once
   prime dimensions are known.
3. D=5 odd supplies the first nontrivial zero-set compiler and return-section
   method.
4. D=7 odd is already solved directly, but the explanation we want is the
   additive `4+2` bridge: all-zero-set D5 base plus D3 fiber monodromy.
5. A successful all-odd `m >= 5` `4+2` theorem would show how the finite D7
   proof is an instance of a reusable mechanism rather than an isolated
   certificate.

This separates three mechanisms that should not be conflated:

- multiplicative composite lifting for composite dimensions;
- additive bridge lifting for explaining D7 from D5 and D3;
- direct root-flat certificates for special odd/even dimension cases.

## Immediate Next Steps

Implementation progress after this goal update:

- `Shared/RootFlat.lean` now contains the generic schedule/certificate
  interface plus the layered full-step lift: row Latin gives edge partition,
  and layer bijective plus return single-cycle gives Hamiltonian full color
  steps via `rootFlatLayeredDecomposition_of_schedule`.
- `Shared/RankCycle.lean` now contains a reusable `ZMod` rank criterion for
  finite return-cycle certificates.
- `Shared/Monodromy.lean` now contains conjugacy transfer for bijective and
  single-cycle maps, plus a skew-product base-orbit monodromy criterion.
- `Shared/AdditiveBridge.lean` now packages the local bridge obligations:
  state-dependent direction reindexing preserves row Latin, and skew-product
  layer maps are bijective when the base and all fiber branches are bijective.
- `Shared/TorusCayley.lean` now supplies a standard dimension-indexed
  directed torus/Cayley Hamilton-decomposition proposition. The existing D5
  and D7 Cayley endpoints have adapters into this shared proposition, so the
  `RoundComposite` `Solved : Nat -> Nat -> Prop` slot can now be instantiated
  with an actual graph-level target rather than only a manuscript placeholder.
  It also contains the block-coordinate equivalence
  `TorusVertex (a * b) m ~= (Fin b -> TorusVertex a m)` and the corresponding
  basis-coordinate lemma needed by the graph-product construction.
  The `CycleCoordinate` structure records the extra coordinate data needed to
  identify an abstract Hamilton color with the standard `ZMod n` cycle used by
  the auxiliary dimension-`b` decomposition.  It now has constructors from
  rank-equivalence/rank-bijection data, matching the style of the existing
  generated rank certificates, and a finite single-cycle constructor that
  extracts coordinates from the ordinary Cayley Hamiltonian endpoint.
- `Shared/CayleyProduct.lean` begins the concrete graph-product formalization:
  it packages coordinate-bearing Cayley decompositions, turns A-color cycle
  coordinates into block-rank coordinates, defines the product color direction,
  and proves both its edge-partition condition and its color-wise Hamiltonian
  conjugacy to the auxiliary B-cycle.  It also has an adapter from a Cayley
  decomposition plus color-wise rank-step data to a coordinatized Cayley
  endpoint, and an adapter from an existing single-cycle Cayley decomposition.
- `D7Odd/Handoff/Additive4Plus2.lean` now contains the concrete
  `A7(m) ~= A5(m) x A3(m)` root equivalence, slot-step conjugacy, product
  layer wrapper, and transfer from a product-side return single-cycle
  certificate to the D7 root-flat, D7 handoff Hamilton, and shared layered-lift
  targets.  It also records the A3 prefix equivalence and `card_ARoot3 = m^2`,
  matching the fiber-rank target used by the concrete bridge package, together
  with `card_RootState7 = m^6` and `card_ProductRoot = m^6` for the full D7
  product state space.  Its `ProductRootSchedule` namespace also has the local bridge
  entrypoints needed by a future all-zero-set proof: raw direction plus
  state-dependent `kappa` implies row Latin, componentwise skew-product layers
  imply layer bijectivity, and color returns identified with skew products can
  use the shared monodromy criterion.  These are packaged by
  `ProductRootCertificate.ofLocalBridgeAndSkewReturns`, which turns those local
  and return assumptions into the product-side certificate consumed by the D7
  endpoints.
- `D7Odd/Handoff/Additive4Plus2D5Base.lean` records the concrete D5
  all-zero-set base slot rule used by the bundled bridge verifier, reusing
  `D5Odd.ZeroSetTable.Lambda1` and its row-Latin proof.  It also reuses the
  D5 exact-cover certificate to prove that each all-zero-set base slot step is
  bijective for `m >= 5`.
- `D7Odd/Handoff/Additive4Plus2D3Fiber.lean` records the concrete odd-D3
  affine fiber packet used by the bundled bridge verifier.  It defines the
  layer/fiber-dependent D3 direction rule and proves that the three fiber slots
  are row-Latin and that each D3 layer step is bijective whenever `0 != 1` in
  `ZMod m` (in particular for `m >= 2`).  It also packages the same facts after
  precomposing the D3 slots with an arbitrary bijective S3 permutation.
- `D7Odd/Handoff/Additive4Plus2BridgeKappa.lean` records the concrete
  state-dependent bridge `kappa`: the D5 base packet supplies the four base
  directions and the unique base-rest slot, while a bijective S3 fiber
  permutation fills the three bridge fiber directions.  The file proves that
  this combined `kappa` is bijective, and that any layerwise raw row
  permutation becomes a row-Latin bridge schedule after applying this concrete
  `kappa`.  It also adapts a base-dependent D3 fiber compiler into the `phi`
  input expected by `kappa`, exposing the resulting `phi` bijectivity and
  fiber-branch bijectivity facts.  The same file now records the component
  projection lemmas for the actual global direction selected by `kappa`, and
  proves that the resulting concrete bridge schedule has bijective layers for
  `m >= 5`.  These are bundled in a single concrete row/layer local-facts
  theorem.
- `D7Odd/Handoff/Additive4Plus2BridgeChart.lean` records the alternate `4+2`
  root chart used by the bundled all-zero-set bridge model.  In this chart,
  global D7 directions `0..3` act as the corresponding D5 base move together
  with the forced D3 `q0` fiber move, while directions `4,5,6` are the three
  D3 fiber slots.  This keeps the bundle bridge model separate from the direct
  product chart used by `ProductRootSchedule`.  It also defines
  `BridgeProductRootSchedule` and `BridgeProductRootCertificate`, with adapters
  back to the D7 root-flat handoff certificate.  The bridge chart now mirrors
  the direct chart's local bridge and skew-return entrypoints through
  `BridgeProductRootCertificate.ofLocalBridgeAndSkewReturns`.
- `D7Odd/Handoff/Additive4Plus2Endpoints.lean` carries that product-side
  certificate, in either direct-chart or bridge-chart form, through the existing
  D7 torus/Cayley wrappers, including the shared Cayley endpoint used by
  `RoundComposite`.
- `D7Odd/Handoff/Additive4Plus2Goal.lean` records the revised odd-D7 proof
  target as a conditional theorem: the finite `m = 3` certificate from
  `SmallBranches.lean`, plus a `BridgeProductRootCertificate` for every odd
  `m >= 5`, implies the D7 handoff, torus, Cayley, and shared Cayley endpoints.
  It also names the lower-level `BridgeOddLocalSkewTarget`, whose data are the
  local bridge and monodromy obligations needed to construct those certificates.
- `D7Odd/Handoff/Additive4Plus2ConcreteGoal.lean` specializes that target to
  the current all-zero-set bridge architecture.  A
  `BridgeConcreteSkewPackage` supplies row permutations, the D3
  fiber-layer/permutation compiler, return equality, base orbit coverage, and
  fiber monodromy; the file fills in the concrete row-Latin and layer
  bijectivity obligations from the D5 base, D3 fiber, and bridge-`kappa`
  lemmas, then routes the package to the same odd-D7 endpoint.  The lower-level
  `BridgeConcreteReturnPackage` uses the canonical folded base/fiber returns
  and proves the product-return equality automatically from the layerwise
  skew-product decomposition.  The lowest-level `BridgeConcreteOrbitPackage`
  also fills in the folded base/fiber return bijectivity, leaving the concrete
  odd-D7 route at row/fiber compiler data plus base orbit coverage and fiber
  monodromy.  The rank-based `BridgeConcreteRankPackage` goes one step further:
  a bijective base rank with `rank (R b) = rank b + 1` supplies both base
  return-to-base and base orbit coverage automatically.  The
  `BridgeConcretePowRankPackage` fixes the intended base period to `m^4`, the
  cardinality of `A5(m)`, so the remaining base-side statement has the expected
  D5 rank shape.  The `BridgeConcreteFullRankPackage` also replaces the fiber
  monodromy single-cycle witness with a bijective fiber rank into `ZMod (m^2)`
  stepped by the section return.
- `D7Odd/Even.lean` keeps the even case on a separate `RootFlatSchedule`
  certificate track; its targets now also expose the shared layered full-step
  lift before the existing torus/Cayley wrappers.
- `scripts/verify_4plus2_allN_bridge_cert.py` now independently replays the
  bundled `m=5,7,9` all-zero-set `4+2` certificates and checks that all seven
  base returns have canonical `m^4` orbit ranks stepped by `+1`, all seven
  fiber section returns have canonical `m^2` orbit ranks stepped by `+1`, and
  all seven product returns are single `m^6` cycles.  With
  `--rank-summary-json`, it also exports compact rank fingerprints and orbit
  prefixes for comparing future uniform formula candidates against the finite
  witnesses.
- `scripts/analyze_4plus2_base_rows.py` separates the base exact-cover
  subproblem: it confirms that the bundled row projections are base-primitive
  and can reassemble column exact-covers from fixed base words by choosing the
  extra-slot positions.  It also scans short primitive A5 base words for
  additional odd moduli and can run a bounded search that chooses seven words
  from the primitive-word pool before solving the extra-slot insertion problem;
  with the bundled `m=5` length pattern it finds an alternate base exact-cover
  using base words `23,23,002,0111,3044,14413,43220`.  The optional bundled
  kappa test shows that this alternate base cover does not work with the
  original `m=5` kappa, so the fiber compiler must be constructed for the
  chosen base row family rather than reused blindly.  A length-three scan over
  `m=5,7,9,11,13,15,17` reproduces the observed exceptional behavior at `m=7`
  and finds no length-three primitive word for `m=17`, matching the current
  need for a longer or congruence-dependent base row family.
- `scripts/search_4plus2_kappa_formulas.py` separates a first fiber-compiler
  subproblem.  It searches cyclic/reflected zero-set formulas
  `r = a*t + b*p(Z) + c*|Z| + d mod 3`; the bundled rows reproduce the
  known hits `m=5: r=p+2|Z|` and `m=7: r=2|Z|+2`, while `m=9` has no hit in
  this restricted family.  Thus the all-odd fiber compiler needs either a
  richer zero-set table or a section-return construction beyond this affine
  four-parameter family.
- `RoundComposite.lean` now has an odd-modulus version of the product reduction
  interface, plus named standard torus/Cayley instantiations, so odd-only prime
  endpoints such as the current D5/D7 theorems can be connected without
  pretending that the even branches are solved.  It also proves the concrete
  `standard_cayley_pointwise_composite_expansion`,
  `standard_torus_pointwise_composite_expansion`, and their odd-modulus
  variants.
- `RoundComposite/ConcreteEndpoints.lean` now performs that connection for the
  formalized D5 and D7 odd endpoints: the older conditional endpoints
  under an assumed pointwise expansion remain, but the concrete product theorem
  now gives direct shared Cayley/Torus composite endpoints for `35`, `49`, and
  any nonempty product of factors each equal to `5` or `7`.

## Artifact Checklist

Current status against the revised goal:

- D7 odd regression endpoint: closed in `D7Odd/Torus.lean` and
  `D7Odd/Cayley.lean`; regression build target is `lake build D7Odd`.
- Concrete composite Cayley/Torus theorem: closed for the shared standard
  targets by `standard_cayley_pointwise_composite_expansion` and
  `standard_torus_pointwise_composite_expansion` in `RoundComposite.lean`, with
  D5/D7 odd concrete endpoints in `RoundComposite/ConcreteEndpoints.lean`.
- Shared root-flat return criterion: closed at the layered full-step level in
  `Shared/RootFlat.lean`; D7-specific adapters are in
  `D7Odd/Handoff/ReturnCriterion.lean` and `D7Odd/Torus.lean`.
- Additive bridge interface: partially closed.  The `A7(m) ~= A5(m) x A3(m)`
  root equivalence and product-certificate adapters are in
  `D7Odd/Handoff/Additive4Plus2.lean`; the concrete D5 all-zero-set base rule
  is in `D7Odd/Handoff/Additive4Plus2D5Base.lean`; the bundle-compatible
  bridge-chart certificate constructor is in
  `D7Odd/Handoff/Additive4Plus2BridgeChart.lean`; the concrete odd-D3 fiber
  packet is in `D7Odd/Handoff/Additive4Plus2D3Fiber.lean`; the combined
  bridge `kappa` is in `D7Odd/Handoff/Additive4Plus2BridgeKappa.lean`; and the
  torus/Cayley wrappers are in `D7Odd/Handoff/Additive4Plus2Endpoints.lean`.
  The conditional odd-D7 target theorem and local/skew package target are in
  `D7Odd/Handoff/Additive4Plus2Goal.lean`; the concrete all-zero-set
  return/monodromy package constructor is in
  `D7Odd/Handoff/Additive4Plus2ConcreteGoal.lean`.  The all-odd `m >= 5`
  product certificate is still open.
- Local bridge and monodromy lemmas: available abstractly in
  `Shared/AdditiveBridge.lean` and `Shared/Monodromy.lean`, and exposed at the
  D7 product-schedule level in both `D7Odd/Handoff/Additive4Plus2.lean` and
  `D7Odd/Handoff/Additive4Plus2BridgeChart.lean`; they still need to be
  instantiated with the all-zero-set D5 rows and D3 fiber compiler.
- D5 even: separate seam-orbit track remains open.  `D5Odd/Even.lean` proves
  that a seam orbit certificate implies the model, torus, and Cayley endpoints,
  but the actual orbit certificate is not constructed.
- D7 even: separate `RootFlatSchedule` target remains open.
  `D7Odd/Even.lean` routes a future even certificate through the shared
  layered lift and then to torus/Cayley wrappers.
- Prime-p abstraction: deferred; the fixed D7 prime-interface regression is
  retained, but no general prime-p theorem is claimed.

## Prompt-To-Artifact Audit

This audit maps the current user-level goal to concrete repo evidence. It is
not a completion certificate for the full research goal; it marks which parts
are closed and which remain open.

| Goal item | Current artifact evidence | Status |
| --- | --- | --- |
| Keep D7 odd as regression target | `D7Odd/Torus.lean`, `D7Odd/Cayley.lean`; checked by `lake build D7Odd RoundComposite.ConcreteEndpoints` on 2026-05-01 | Closed regression endpoint |
| Raise composite theorem to concrete graph theorem | `RoundComposite.lean` has `standard_cayley_pointwise_composite_expansion` and `standard_torus_pointwise_composite_expansion`; `RoundComposite/ConcreteEndpoints.lean` has direct odd `35`, `49`, and 5/7-list Cayley/Torus endpoints | Closed for current shared standard Cayley/Torus target |
| Extract common root-flat return criterion | `Shared/RootFlat.lean` has `rootFlatLayeredDecomposition_of_schedule` from row Latin, layer bijective, and return single-cycle | Closed at shared layered full-step level |
| Move D7 explanation to additive `4+2` bridge | `D7Odd/Handoff/Additive4Plus2.lean` has `A7(m) ~= A5(m) x A3(m)` root equivalence, `card_ARoot3 = m^2`, `card_ProductRoot = card_RootState7 = m^6`, `ProductRootCertificate.ofLocalBridgeAndSkewReturns`, and product-certificate adapters; `Additive4Plus2BridgeChart.lean` has the bundle-compatible forced-`q0` bridge chart, `BridgeProductRootCertificate`, and `BridgeProductRootCertificate.ofLocalBridgeAndSkewReturns`; `Additive4Plus2Endpoints.lean` lifts both product-certificate forms to D7 torus/Cayley/shared Cayley; `Additive4Plus2Goal.lean` packages finite `m = 3` plus odd `m >= 5` bridge certificates, or local/skew packages, into the full D7 odd endpoints; `Additive4Plus2ConcreteGoal.lean` specializes this to the concrete all-zero-set bridge and reduces the remaining construction to row/fiber data plus canonical folded base/fiber rank steps into `ZMod (m^4)` and `ZMod (m^2)` | Interface and conditional goal theorem closed; uniform all-odd certificate open |
| Formalize local bridge lemma | `Shared/AdditiveBridge.lean` has `localBridge_rowLatin_and_layerBijective`; `ProductRootSchedule.rowLatin_of_stateDirectionPermutation`/`layerBijective_of_skewProductComponents` and `BridgeProductRootSchedule.rowLatin_of_stateDirectionPermutation`/`layerBijective_of_skewProductComponents` expose it to both D7 product charts; `Additive4Plus2D5Base.lean` proves row Latin and `m >= 5` layer bijectivity for the concrete D5 all-zero-set base packet; `Additive4Plus2D3Fiber.lean` proves row Latin, layer-step bijectivity, and S3-permuted compiler facts for the D3 fiber packet; `Additive4Plus2BridgeKappa.lean` proves bijectivity of the combined state-dependent bridge `kappa`, gives a concrete row-schedule row-Latin adapter, adapts the D3 compiler into the bridge `phi` interface, and proves concrete bridge layer bijectivity for `m >= 5`; `Additive4Plus2ConcreteGoal.lean` consumes these local facts automatically in `BridgeConcreteSkewPackage.toLocalSkewPackage` | Concrete local row/layer assembly closed; uniform return instantiation open |
| Formalize monodromy criterion | `Shared/Monodromy.lean` has `single_cycle_of_skewProduct_monodromy` and `single_cycle_of_skewProduct_base_orbit_monodromy`; `ProductRootSchedule.returnSingleCycle_of_skewReturn`/`returnsSingleCycle_of_skewReturns` and `BridgeProductRootSchedule.returnSingleCycle_of_skewReturn`/`returnsSingleCycle_of_skewReturns` expose it to product certificates | Abstract and product-schedule criteria closed; product-return instantiation open |
| Keep D5 even separate | `D5Odd/Even.lean` exposes seam-orbit certificate endpoints; `scripts/d5_even_seam_sat_search.py` is currently a negative/debugging smoke check | Actual orbit certificate open |
| Keep D7 even separate | `D7Odd/Even.lean` exposes `RootFlatSchedule` certificate endpoints and shared layered adapters | Actual even schedule certificate open |
| Defer prime-p abstraction | `D7Odd/Handoff/PrimeRoot*.lean`, `PrimeCanonical*.lean`, and this note keep it as a regression/future interface | Deferred by design |

Verification signals used in this audit:

- `lake build D7Odd RoundComposite.ConcreteEndpoints` succeeds, with only
  pre-existing `D5Odd/ReturnCycle.lean` linter warnings replayed.
- `grep -R "sorry" -n -- *.lean Shared D5Odd D7Odd RoundComposite` finds no
  Lean `sorry` in the active formalization files.
- `git diff --check` succeeds for the current tracked edits.

The remaining D7-structure gap is not the abstract composite interface. It is
the construction of the actual all-zero-set `4+2` product certificate for odd
`m >= 5`, including the base rows and the fiber compiler/monodromy proof.

The next useful Lean/research steps are:

1. Provide a uniform `BridgeConcreteFullRankPackage` for every odd `m >= 5`;
   after the latest interface, this means row permutations, D3
   fiber-layer/permutation data, a bijective base rank into `ZMod (m^4)`
   stepped by the canonical folded base return, and a bijective fiber rank into
   `ZMod (m^2)` stepped by the canonical section return.
2. Search for a uniform or finite-congruence description of the all-zero-set
   base rows for odd `m >= 5`.
3. Search for a zero-set-only or first-return-section formula for the fiber
   compiler `kappa`.
4. Use the concrete composite Cayley/torus endpoint as the baseline for future
   prime endpoints, instead of treating composite dimensions as fresh search
   problems.
5. Keep D7 even and D5 even on separate certificate tracks so their open
   obligations do not obscure the D7 odd structural bridge.
