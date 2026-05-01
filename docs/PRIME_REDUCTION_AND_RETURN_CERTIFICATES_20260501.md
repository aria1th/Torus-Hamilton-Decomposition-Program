# Prime reduction and return-certificate narrative

Date: 2026-05-01

Scope: this note records the proof narrative connecting the nested
`Torus-Hamilton-Decomposition/` D=3 and composite-dimension work with the
Program repo's D=5 odd and D=7 odd Lean formalizations.

## Current theorem boundary

- D=3 is the all-case base model.  The odd branch is controlled by explicit
  first-return maps and odometer conjugacies in
  `Torus-Hamilton-Decomposition/formal/TorusD3Odd/ReturnMaps.lean` and
  `Cycles.lean`.  The even branch supplies the finite-defect/splice model in
  `Torus-Hamilton-Decomposition/formal/TorusD3Even/Splice.lean` and the
  odometer rewrite files under `formal/TorusD3Odometer/`.
- Composite dimensions are reduced theorem-level to prime dimensions by the
  product expansion in
  `Torus-Hamilton-Decomposition/RoundComposite/d_composite_expansion_theorem_revised.tex`.
  In particular, pointwise composite expansion has the shape:
  D_a(m) plus D_b(m^a) implies D_ab(m).  Uniformly, once all prime dimensions
  are solved for every modulus, all dimensions follow.
- The Lean `RoundComposite.lean` file now also separates the odd-modulus version
  of this reduction.  This is the right interface for currently odd-only prime
  endpoints such as D=5 and D=7: if the pointwise expansion and prime bases are
  known for odd moduli, then the prime-factor reduction is also available over
  odd moduli.
- `Shared/TorusCayley.lean` supplies the standard dimension-indexed
  torus/Cayley Hamilton-decomposition proposition, and `RoundComposite.lean`
  now exposes named standard torus/Cayley instantiations of the abstract
  reduction.  The concrete graph-product construction now yields standard
  Cayley and Torus pointwise composite expansions, since cycle coordinates can
  be extracted from any nontrivial finite single-cycle color endpoint.
- The same shared file now identifies composite torus coordinates by the block
  equivalence `TorusVertex (a * b) m ~= (Fin b -> TorusVertex a m)` and records
  how a standard basis direction lands in one block.  This is the concrete
  graph-isomorphism layer needed before transporting Hamilton factors.
- It also introduces `CycleCoordinate`, the product-lift data that turns a
  Hamilton color into an explicit `ZMod n` cycle coordinate.
  Rank-equivalence/rank-bijection constructors make this compatible with
  existing rank-certificate proofs, and the finite single-cycle constructor now
  supplies coordinates directly from the usual `IsSingleCycleMap` endpoint when
  the vertex set has size greater than one.
- `Shared/CayleyProduct.lean` now formalizes the first concrete graph-product
  layer: coordinate-bearing Cayley decompositions, block-rank coordinates, the
  product color-direction map, its edge-partition proof, and the color-wise
  Hamiltonian conjugacy from the product step to the auxiliary B-cycle.  It
  also packages a Cayley decomposition with color-wise rank-step data as a
  coordinatized endpoint, and packages an existing single-cycle Cayley
  decomposition as a coordinatized endpoint.
- `RoundComposite/ConcreteEndpoints.lean` connects the current D5 and D7 odd
  endpoints to this shared proposition.  It still records the older conditional
  pointwise-expansion endpoints, but the standard Cayley/Torus pointwise product
  expansions are now formalized, so it also gives direct graph-level odd
  endpoints for `35`, `49`, and every nonempty product of factors each equal to
  `5` or `7`.
- D=5 odd is Lean-formalized through the model, torus, and Cayley levels:
  `D5Odd/Main.lean`, `D5Odd/Torus.lean`, and `D5Odd/Cayley.lean`.
- D=7 odd is Lean-formalized through a root-flat certificate and then lifted to
  the full torus/Cayley statements:
  `D7Odd/Handoff/ReturnCriterion.lean`, `D7Odd/Handoff/CanonicalFamily.lean`,
  `D7Odd/Torus.lean`, and `D7Odd/Cayley.lean`.
- D=5 even, D=7 even, and general odd prime dimensions remain the main
  structural frontier.  D=5 even already has a Lean scaffold in
  `D5Odd/Even.lean`; D=7 even should probably reuse the D7 root-flat
  certificate API rather than start from raw torus walks.

## Proof narrative

The common idea is to push the infinite family of torus Hamilton-decomposition
problems down to finite return data.

1. Use a layer coordinate.  For each color, the step map advances the layer by
   one.  After m steps, the orbit returns to the root layer.
2. Prove that the induced return map on the root slice is a single cycle.  A
   generic lift theorem then turns that root-slice cycle into a full torus
   Hamilton cycle.
3. Prove exact cover and Latin conditions separately, so that the color maps
   cover every directed torus edge exactly once.
4. Use composite-dimension product expansion to avoid solving genuinely new
   constructions in composite dimensions.  Prime dimensions are the only base
   cases that must be constructed directly.

D=3 supplies the original odometer and even-splice evidence.  D=5 odd shows the
first large prime case where this strategy closes all the way to the Cayley
statement.  D=7 odd shows that the construction can be recast as a root-flat
certificate: once row Latin, layer bijective, and return-single-cycle facts are
proved, the shared `rootFlatLayeredDecomposition_of_schedule` gives the
abstract layered Hamiltonian full-step lift, `D7Odd/Torus.lean` transports this
to the concrete torus, and `D7_odd_cayley_unconditional` supplies the Cayley
wrapper.

## What D=3 contributes

D=3 is the conceptual source for two reusable patterns.

- Odd moduli: first-return maps are conjugate to odometer maps.  In
  `TorusD3Odd/ReturnMaps.lean`, the maps `F0`, `F1`, and `F2` are converted to
  odometer form by `psi0_conj`, `psi1_conj`, and `psi2_conj`; the last branch
  uses oddness through invertibility of 2.
- Even moduli: the obstruction is not ignored.  It is isolated as a finite
  defect and repaired by splice theorems such as `cycleOn_cyclicSpliceSucc` and
  `cycleOn_of_spliceBlocks` in `TorusD3Even/Splice.lean`.

This is the evidence that the right way to attack D=5 even and D=7 even is not
to search the full torus directly.  The expected object is an odometer outside a
small defect region, plus a finite splice certificate that repairs the defect
without breaking exact cover or Latinness.

## What the composite theorem contributes

The composite theorem turns a dimension problem into a base-prime problem.

- The square-torus lemma gives the primitive product mechanism.
- Cartesian-power lift and pointwise composite expansion move from D=a and
  D=b to D=ab after the required modulus change.
- The uniform corollary says that if each prime dimension is solved for all
  moduli, then every dimension is solved.

This explains why D=5 and D=7 matter as base cases.  Solving D=7 for all moduli
does not just close one dimension; it unlocks every composite dimension with a
factor 7 once the other prime factors are solved.

The product theorem is no longer only a theorem-level manuscript artifact:
Lean now has the graph-product interface and Hamilton-decomposition transport
for a left factor with explicit cycle coordinates.  The coordinate-extraction
step is now also formalized for finite nontrivial single-cycle Cayley endpoints,
so the standard Cayley product expansion is available directly at the shared
graph level.

## What D=5 odd contributes

D=5 odd is the strongest reusable prime template currently in Lean.

The useful package is:

- `D5Odd/Schedule.lean`: `LayerSchedule`, exact cover, Latinness, color return,
  and `AllColorHamiltonian`.
- `D5Odd/ReturnCycle.lean`: rank and semiconjugacy tools such as
  `single_cycle_of_rank`, `single_cycle_of_bijective_semiconj`,
  `single_cycle_of_return_cover`, and `single_cycle_of_first_return_sum`.
  It also exports the D5 `m = 3` root-return coordinate witnesses
  `m3ReturnQuad_cycleCoordinate` and `colorReturn_m3_cycleCoordinate`.
- `Shared/RankCycle.lean`: shared `ZMod` rank criterion
  `single_cycle_of_zmod_rank`, for finite certificates where a rank map
  increases by one on each return step.
- `D5Odd/Torus.lean`: the model-to-torus bridge, especially
  `single_cycle_of_layer_zero_return_cover`, `torusHamiltonDecomposition_of_model`,
  and `D5_odd_torus_unconditional`.
- `D5Odd/Cayley.lean`: the final Cayley wrapper
  `D5_odd_cayley_unconditional`.

For D=5 even, the missing theorem is not another torus lift.  The lift already
exists.  The missing mathematical object is a seam certificate:

- construct `S : D5EvenSeamData m`;
- prove `D5EvenSeamHamiltonian S`;
- apply `D5_even_from_seam_data` or `D5_even_from_target`.

The current SAT witness encoding for this exact seam target is useful as a
debugging tool, but it is not a proof artifact.  In particular, the small
`m=2` check currently returns `unsat` with both `cadical153` and `glucose3`, so
it should not be read as evidence for a positive even certificate.

The likely proof obligations are a parity obstruction ledger, an odometer
normal form away from the seam, exact seam entry/exit counting, and a finite
splice theorem on the reduced return index.

## What D=7 odd contributes

D=7 odd is the best template for higher odd primes because it separates the
construction from the torus lift.

The reusable abstraction is:

- `RootFlatSchedule`: finite root-state schedule data;
- `rowLatin`: one direction per color at every root state;
- `layerBijective`: exact cover on each layer/root fiber;
- `returnMap`: the m-step first return to the root layer;
- `returnsSingleCycle`: every color return map is a single cycle;
- `RootFlatCertificate`: the certificate packaging the above;
- `rootFlatLayeredDecomposition_of_schedule`: the shared layered full-step
  Hamiltonian lift, with D7's torus file providing the concrete coordinate
  transport.

The generic odd branch in `D7Odd/Handoff/CanonicalFamily.lean` suggests the
right higher-prime architecture: prefix coordinates, a canonical rho/first-hit
rule, count matrices or generated schedules, and a primitive-word theorem that
proves the return map is one cycle.

For the additive explanation route, `D7Odd/Handoff/Additive4Plus2.lean` now
also makes the product-side endpoint explicit: a `ProductRootCertificate`
transports through `A7(m) ~= A5(m) x A3(m)` to the D7 root-flat certificate,
the D7 handoff Hamilton target, and the shared layered full-step lift.  The
same file also exposes the local proof hooks for such a certificate: row Latin
from a state-dependent direction permutation, layer bijectivity from
componentwise skew-product branches, and return single-cycle from the shared
base-orbit monodromy criterion.  These hooks are bundled by
`ProductRootCertificate.ofLocalBridgeAndSkewReturns`.
`D7Odd/Handoff/Additive4Plus2D5Base.lean` records the concrete D5 all-zero-set
base slot rule from `D5Odd.ZeroSetTable.Lambda1`, including its row-Latin
proof, and reuses the D5 exact-cover certificate to prove that each
all-zero-set base slot step is bijective for `m >= 5`.
`D7Odd/Handoff/Additive4Plus2D3Fiber.lean` now records the concrete odd-D3
affine fiber packet used by the bundled bridge verifier and proves row Latin
and layer-step bijectivity for the three D3 fiber slots whenever `0 != 1` in
`ZMod m`; the same file packages these facts after any bijective S3
precomposition of the fiber slots.
`D7Odd/Handoff/Additive4Plus2BridgeKappa.lean` combines the D5 base slot rule
with a bijective S3 fiber permutation and proves that the resulting
state-dependent bridge `kappa` is bijective.  It also packages raw layerwise
row permutations as concrete bridge schedules and proves the resulting
row-Latin condition, and adapts base-dependent D3 fiber compilers into the
bridge `phi` interface with the expected bijectivity facts.  It now also
projects the selected global direction back to its D5/D3 components and proves
that the concrete bridge schedule has bijective layers for `m >= 5`, packaged
together with row-Latin as a concrete local-facts theorem.
`D7Odd/Handoff/Additive4Plus2BridgeChart.lean` records the alternate root chart
used by the bundled all-zero-set bridge certificates, where base non-root
directions carry the forced D3 `q0` fiber move.  Its
`BridgeProductRootCertificate` gives the same root-flat handoff endpoint for
certificates stated in that chart, and
`BridgeProductRootCertificate.ofLocalBridgeAndSkewReturns` packages the same
local bridge and monodromy obligations in the bundle-compatible chart.
`D7Odd/Handoff/Additive4Plus2Endpoints.lean` then carries the same certificate
through the D7 torus/Cayley wrappers and into the shared Cayley endpoint.
`D7Odd/Handoff/Additive4Plus2Goal.lean` packages the intended odd-D7 proof
route: the finite `m = 3` branch from `SmallBranches.lean`, together with
bridge-chart certificates for every odd `m >= 5`, implies the D7 handoff,
torus, Cayley, and shared Cayley endpoints.  Its `BridgeOddLocalSkewTarget`
records the lower-level alternative: provide the uniform local bridge and
monodromy packages, then obtain the same odd-D7 endpoint.
`D7Odd/Handoff/Additive4Plus2ConcreteGoal.lean` now specializes this lower-level
route to the concrete all-zero-set bridge.  Its `BridgeConcreteSkewPackage`
keeps the remaining assumptions exactly at the row/fiber-data, product-return,
base-cover, and fiber-monodromy level; the local row-Latin and layer-bijective
proofs are supplied automatically from the concrete D5, D3, and bridge-`kappa`
lemmas.  Its lower-level `BridgeConcreteReturnPackage` uses canonical folded
base/fiber returns, so product-return equality is now a theorem rather than a
separate witness.  Its `BridgeConcreteOrbitPackage` goes one step lower by
proving folded base/fiber return bijectivity automatically, leaving the
remaining concrete bridge assumptions at base orbit coverage and fiber
monodromy.  Its `BridgeConcreteRankPackage` reduces the base side further:
a bijective base rank stepped by the folded base return now implies both
return-to-base and base orbit coverage, so the structural D7 bridge target is
row/fiber compiler data plus base-rank and fiber-monodromy proofs.  Its
`BridgeConcretePowRankPackage` fixes that base rank target to `ZMod (m^4)`,
matching the cardinality of `A5(m)`.  Its `BridgeConcreteFullRankPackage`
also reduces the fiber monodromy to a rank-step witness into `ZMod (m^2)`,
matching the `card_ARoot3 = m^2` theorem for `A3(m)`.  On the product side,
`card_ProductRoot = card_RootState7 = m^6` records the expected total state
count for the D7 bridge.

The bundled finite verifier now checks the same decomposition shape for
`m=5,7,9`: base returns have canonical `m^4` orbit ranks stepped by `+1`,
fiber section returns have canonical `m^2` orbit ranks stepped by `+1`, and
product returns are single `m^6` cycles.  Its `--rank-summary-json` option
emits compact rank fingerprints and orbit prefixes, giving a concrete
comparison target for proposed uniform `BridgeConcreteFullRankPackage`
formulas.

The companion `scripts/analyze_4plus2_base_rows.py` isolates the base side:
it verifies bundled row projections as base-primitive and scans short A5 base
words by modulus.  It also searches the column exact-cover insertion problem
for fixed base words, and has a bounded primitive-pool assembly mode.  This
separates the base row-family problem from the D3 fiber compiler problem.

For D=7 even, `D7Odd/Even.lean` now keeps a separate certificate target around
`RootFlatSchedule`, with the same three obligations:

- row Latin;
- layer bijective;
- return single-cycle.

Once those are available, the module routes the certificate through the shared
layered lift and the existing full torus and Cayley wrappers.

## General odd prime target

The natural conjectural target is a prime-parameter version of the D7 handoff:

- define root-flat states for dimension p, with roots modeled by differences
  against one distinguished coordinate;
- define a canonical prefix coordinate system on p-1 root coordinates;
- define a canonical schedule by a rho/first-hit rule or an equivalent finite
  count-matrix schedule;
- prove row Latin and layer bijectivity uniformly;
- prove a primitive-word or carry theorem showing that each color return map is
  a single cycle for odd m;
- lift by the same layer/root return criterion to the full torus and then to
  the Cayley statement.

The hard reusable theorem is the primitiveity/carry theorem.  D=7 currently
contains this in a specialized form.  General odd prime work should extract
that statement first, before trying to formalize full torus-level behavior.

## Concrete next formalization tasks

1. Use the new standard Cayley product expansion as the composite baseline;
   as more prime endpoints are proved, instantiate the same graph-level product
   theorem rather than adding new composite-dimension searches.
2. Extract a shared return-lift library from the D3, D5, and D7 lift arguments.
3. Turn `D5Odd/Even.lean` into an actual D=5 even seam certificate proof.
4. Add a D7-even certificate target using the D7 `RootFlatSchedule` interface.
5. Abstract the D7 canonical family from fixed 7 coordinates to a prime
   parameter p, with D=7 as the first regression test.

The strategic point is that the proof should not grow by enumerating larger
tori.  It should grow by shrinking every dimension-prime problem to finite
return data and by using the composite theorem to make prime dimensions the
only genuinely new base cases.
