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
  certificate is still missing. The small `m=2` SAT smoke test is not a proof
  of the even theorem.
- A generic composite product theorem exists in `RoundComposite.lean`. It is
  useful as an abstract reduction, but it is not yet the final concrete
  graph-level Cayley product expansion theorem.
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

The current composite theorem is abstract. The paper-level theorem still needs
the connection from the product construction to the concrete Cayley graph
Hamilton decomposition for composite dimensions.

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
  interface, including `rootFlatReturnCriterion_of_schedule`, for packaging
  row Latin, layer bijective, and return single-cycle data.
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
- `D7Odd/Handoff/Additive4Plus2.lean` now contains the concrete
  `A7(m) ~= A5(m) x A3(m)` root equivalence, slot-step conjugacy, product
  layer wrapper, and transfer from a product-side return single-cycle
  certificate to a D7 root-flat certificate.
- `scripts/verify_4plus2_allN_bridge_cert.py` now independently replays the
  bundled `m=5,7,9` all-zero-set `4+2` certificates and checks that all seven
  product returns are single cycles.
- `RoundComposite.lean` now has an odd-modulus version of the product reduction
  interface, plus named standard torus/Cayley instantiations, so odd-only prime
  endpoints such as the current D5/D7 theorems can be connected without
  pretending that the even branches are solved.

The remaining gap is not the abstract interface. It is the construction of the
actual all-zero-set `4+2` product certificate for odd `m >= 5`, including the
base rows and the fiber compiler/monodromy proof.

The next useful Lean/research steps are:

1. Instantiate the additive local bridge with the all-zero-set D5 base rows and
   the D3 fiber compiler.
2. Search for a uniform or finite-congruence description of the all-zero-set
   base rows for odd `m >= 5`.
3. Search for a zero-set-only or first-return-section formula for the fiber
   compiler `kappa`.
4. Finish the concrete composite Cayley/torus endpoint from the existing
   product reduction; the odd-modulus logical reduction is present, but the
   graph-product construction itself is still not formalized in Lean.
5. Keep D7 even and D5 even on separate certificate tracks so their open
   obligations do not obscure the D7 odd structural bridge.
