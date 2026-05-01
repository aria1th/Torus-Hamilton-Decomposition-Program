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
  reduction.  The concrete graph-product construction now yields a standard
  Cayley pointwise composite expansion, since cycle coordinates can be extracted
  from any nontrivial finite single-cycle color endpoint.
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
  Cayley endpoints to this shared proposition.  It still records the older
  conditional pointwise-expansion endpoints, but the standard Cayley pointwise
  product expansion is now formalized, so it also gives direct graph-level odd
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

For D=7 even, there is no separate Lean module analogous to `D5Odd/Even.lean`.
The next theorem should probably be a D7-even certificate target around
`RootFlatSchedule`, with the same three obligations:

- row Latin;
- layer bijective;
- return single-cycle.

Once those are available, the existing `D7Odd/Torus.lean` lift should be the
model for the full torus and Cayley statements.

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
