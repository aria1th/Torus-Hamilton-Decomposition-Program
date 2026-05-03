# D11 and A5-to-A7 Lean Handoff Plan

Date: 2026-05-02.

Update 2026-05-03:

The D11 half of this handoff plan is superseded by
`docs/PREFIX_COUNT_ODD_TORI_OVERHAULED_V2_20260503.md`.  The old plan treated
`m = 3,5,7,9` as D11 finite exceptions.  In the v2 manuscript these cases are
covered by the base-tail Hall-slack theorem from the uniform D5 input.  The
A5-to-A7 structural D7 handoff material below remains a separate track.

Source artifacts read:

- `/data/angel/repos/etc/D11_odd_canonical_schedule_certificate.md`
- `/data/angel/repos/etc/A5_to_A7_Lean_handoff_bundle_v1_0.zip`

This note is a Lean implementation plan, not a completion claim.  It records
how the D11 canonical certificate and the A5-to-A7 handoff bundle should be
absorbed into the repository without confusing them with the already-open
D7-odd and D5-even goals.

## Executive Split

There are two separate tracks.

1. D11 odd canonical schedule:
   formalize a direct positive canonical selector for all odd `m >= 11`,
   with `m = 3,5,7,9` left as finite exceptions.

2. A5-to-A7 additive handoff:
   continue the structural D7-odd proof through `A7 ~= A5 x A3`, now using
   the v1.0 handoff bundle as the source for Target-A non-exception
   formalization and Target-B zero-set scalar planning.

The tracks share useful infrastructure, especially first-return section
splicing and skew-cycle criteria, but their endpoints should stay separate.
D11 is a new prime-dimension canonical schedule theorem; A5-to-A7 remains the
structural explanation of D7.

## Track 1: D11 Odd Canonical Schedule

Legacy track description.  The large `m >= 11` canonical schedule remains a
valid special route, but v2 replaces the D11 exception handling with the
generic count branch plus the base-tail Hall-slack lift from D5.

The D11 certificate gives a complete mathematical recipe for directed positive
Hamilton decompositions of `(ZMod m)^11` for all odd `m >= 11`.

### Certificate Content

The certificate defines:

- `Color = Fin 11`, `Direction = Fin 11`, `V = (ZMod m)^11`.
- The root-flat section `Sigma = {x : V | sum x = 0}`.
- Prefix coordinates `Sigma ~= (ZMod m)^10`.
- A layer rule `rho(t,z) in {1,...,10}` using the first matching coordinate
  among `z_0,...,z_8`, with fallback `10`.
- A symbol-to-prefix-label permutation `lambda_rho`, and direction
  `d(t,z,s) = 10 - lambda_rho(s)`.
- Layer permutations `sigma_t : Color -> Symbol`.
- Count matrices whose rows and columns all sum to `m`.
- Primitive row criterion:

```text
gcd(N_0, m) = 1
gcd(N_k - N_1, m) = 1 for 2 <= k <= 10.
```

The branch table covers:

```text
m = 11 + 10h
m = 13 + 10h
m = 17 + 10h
m = 19 + 10h
m = 25 + 10h
m = 15
```

This is exactly all odd `m >= 11`.

### Lean Placement

Preferred module layout:

```text
D11Odd/
  Basic.lean
  CanonicalData.lean
  CanonicalCountMatrices.lean
  CanonicalSchedule.lean
  CanonicalReturn.lean
  Torus.lean
  Cayley.lean
```

The code should reuse the generic pieces already living under
`D7Odd.Handoff.PrimeRoot.PrimeDimension` before duplicating definitions.  In
particular, `PrimeDimension`, `RootState`, `Prefix`, `canonicalPrefixLabelOfRho`,
`CountMatrix`, `CountMatrixCertified`, `RootFlatSchedule`, and
`RootFlatCertificate` are already dimension-parametric.  The first Lean edit
should therefore add `eleven : PrimeDimension`, plus D11-facing wrappers only
where graph-level endpoint names require them.

### D11 Lean Milestones

1. Add `PrimeDimension.eleven`.

   Prove the basic simp lemmas analogous to the existing `seven` lemmas:
   sink value, zero/one, `q`, `sum`, root-state equivalence, and prefix
   equivalence.

2. Encode the D11 count data.

   Add `Block10`, `B1`, `B3`, `B7`, `B9`, `B5`, and `B15` as
   `eleven.CountMatrix`.  Prove row sums, column sums, and primitive row
   conditions.  The finite base matrices can initially use direct finite
   simplification; the infinite branches should use small arithmetic lemmas:

```text
gcd(10, m) = 1 for odd m
gcd(16, m) = 1 for odd m
base primitive differences in {1,2,4,5,7,8,10}
```

3. Avoid formal Hall matching at first.

   The certificate notes that valid count matrices decompose into layer
   permutations by regular bipartite matching.  That theorem is useful but
   not needed for the first formal route, because the certificate already
   lists explicit base layer decompositions and `Block10` layer permutations.
   Encode those explicit lists and prove their count matrices directly.

   The dimension-agnostic base-tail certificate plan is recorded separately in
   `docs/D_AGNOSTIC_BASE_TAIL_CERTIFICATE_PROGRAM_20260502.md`.  For D11 it
   should be used especially for the leftover finite cases `m = 3,5,7,9`,
   where the external canonical `b = 1` count-matrix certificate does not
   apply.

4. Define the D11 canonical selector.

   Implement the layer `rho(t,z)`, `lambda_rho`, `d(t,z,s)`, and selector
   `delta_c(x)`.  The row-Latin proof is just:

```text
c -> sigma_t(c) is bijective
s -> d(t,z,s) is bijective
```

5. Prove the triangular return criterion.

   Formalize the D11 version of certificate Sections 9-11:

   - first coordinate return is translation by `N_0`;
   - coordinate `z_r` is a skew extension over lower coordinates;
   - the total carry is `(-1)^r * (N_{r+1} - N_1)`;
   - the skew-cycle lemma upgrades one coordinate at a time when the total
     carry is a unit.

   This proof should be written dimension-parametrically if it remains
   manageable, but the acceptance target is D11 first.  A D11-specific proof is
   preferable to blocking on a general prime-dimension theorem.

6. Lift return cycles to the full torus/Cayley endpoint.

   The full selector increases the coordinate sum by `1` each step.  Therefore
   the `m`-step return on the root-flat section gives a full cycle of length
   `m * m^10 = m^11`.  Reuse the existing `Shared.RootFlat` and
   `Shared.TorusCayley` endpoint style rather than creating a new graph
   framework.

### D11 Blocking Propositions

- `D11CanonicalReturnTriangular`: the prefix return has the triangular form
  and carry sums stated in Sections 9-10 of the certificate.
- `D11PrimitiveRowsSingleCycle`: the primitive row count criterion implies a
  single cycle on `(ZMod m)^10`.
- `D11CanonicalCountSchedule`: the branch schedules produce certified layer
  permutations for all odd `m >= 11`.
- `D11OddCanonicalEndpoint`: the canonical selector lowers to the directed
  positive D11 torus/Cayley theorem.

Small moduli `m = 3,5,7,9` are explicitly outside this canonical certificate
and should be finite-table tasks, not hidden assumptions.

## Track 2: A5-to-A7 Lean Handoff

The v1.0 bundle clarifies the D7 structural proof as:

```text
A7(m) ~= A5(m) x A3(m)
Target A = A5 base primitive row problem
Target B = A3 fiber scalar/zero-set K problem
```

The main update is that the non-exception Target-A branch is no longer a
search problem.  It is a formal certificate problem for the words `23` and
`32`.

### What Is Already Close in Lean

The repository already has:

- `D7Odd/Handoff/Additive4Plus2*.lean`: bridge interfaces and endpoint
  adapters.
- `D7Odd/Handoff/TargetASeamQuotient.lean`: symbolic seam quotient arithmetic,
  including the non-exception one-cycle condition for the expected Q maps.
- `D7Odd/Handoff/Additive4Plus2TargetB.lean`: Target-B' triangular A3 scalar
  interface and zero-set scalar package wrappers.

The bundle should therefore be absorbed by adding missing Target-A and Target-B
certificates, not by rewriting the bridge endpoint layer.

### A5-to-A7 Lean Milestones

1. Add a shared finite section-splice lemma.

   Create a small shared module, for example `Shared/FirstReturnSection.lean`,
   proving the finite-permutation facts used by the bundle:

   - first-return segments from a section are disjoint;
   - length-sum equals full-space hitting;
   - section first-return single-cycle plus hitting implies full primitiveity;
   - repeating the same argument for `Q subset Sigma` gives the double-section
     criterion.

   This should be generic over a finite type and a permutation.

2. Name the exact Target-A primitiveity criterion.

   Add a Lean-facing structure for the A5 all-zero-set base word:

```text
structure TargetAPrimitiveCertificate (m : Nat) (W : List (Fin 5)) where
  sigmaLengthSum : ...
  qLengthSum : ...
  qFirstReturnSingleCycle : ...
```

   The theorem should state that this certificate implies the A5 base map is a
   single `m^4` cycle.  This is the formal counterpart of the handoff note's
   `Sigma`-hitting + `Q`-hitting + `Q` first-return criterion.

3. Finish the non-exception Q layer.

   `TargetASeamQuotient.lean` already proves the hard seam quotient
   arithmetic.  The next file should add the Q-return length formulas from the
   bundle:

```text
W = 23:
  B-line 2h, even A-line 2h-1, odd A-line table
W = 32:
  B-line 2h, odd A-line 2h, even A-line table
```

   The immediate Lean target is the arithmetic identity:

```text
sum_Q r_W(q) = m * (m - 1)
```

   Then the zero-itinerary lemmas can be filled in case-by-case.

4. Transcribe the Sigma affine-cell certificate.

   The v2.6 full affine certificate is complete computationally.  In Lean,
   split it into three layers:

   - data layer: named bucket multiplicity and return-time formulas;
   - arithmetic layer: multiplicities sum to `|Sigma|`, weighted sum is `m^4`;
   - geometric layer: cell predicates partition `Sigma` and each cell has the
     listed first-return time.

   The arithmetic layer should be formalized first because it is cheap and
   stabilizes names.  The geometric layer is the real workload.

5. Package the non-exception theorem.

   Target theorem:

```text
odd m, 11 <= m, m % 5 != 2, W in {23,32}
  + Sigma affine-cell certificate
  + Q-return certificate
  + seam quotient theorem
  -> A5 base word W is one m^4 cycle.
```

   This theorem should feed the existing
   `BridgeConcreteFullRankPackage`/A5-base rank-step interface instead of
   constructing a new endpoint.

6. Keep the exceptional branch as explicit targets.

   The bundle does not solve `m = 10*t+7`.  It gives the exact certificate
   shape:

   - global `Sigma` absorption;
   - internal `Q` absorption;
   - seam primitiveity.

   Add only named target structures for this branch until a uniform correction
   word is known.  Do not merge it into the non-exception proof.

7. Continue Target B through zero-set K.

   `Additive4Plus2TargetB.lean` already has the triangular scalar interface.
   The next Target-B file should encode the 27 feasible shifted zero-set masks,
   the permutation-index convention, and a finite `K` certificate structure.
   The verified `m=9` zero-set-only table should be kept as a regression
   example, while the all-odd theorem remains open.

### A5-to-A7 Blocking Propositions

- `FirstReturnSection.lengthSum_iff_hitting`.
- `FirstReturnSection.doubleSectionCriterion`.
- `TargetA23_32_QReturnLengthSum`.
- `TargetA23_32_SigmaAffineWeightedSum`.
- `TargetA23_32_SigmaAffinePartition`.
- `TargetA23_32_SigmaFirstReturnItineraries`.
- `TargetANonexceptionPrimitiveBase`.
- `TargetAExceptionalAbsorptionCertificate`.
- `TargetBZeroSetKScalarCertificate`.

## Suggested Commit Sequence

1. Documentation and target structures only.
2. Shared first-return section-splice lemmas.
3. D11 `eleven` dimension and D11 count/schedule data.
4. D11 triangular return theorem and endpoint.
5. A5 Target-A exact primitiveity criterion.
6. A5 non-exception Q-return arithmetic.
7. A5 Sigma affine-cell arithmetic and then cell geometry.
8. Target-B zero-set K finite certificate layer.

This ordering gives small, reviewable Lean commits and keeps the difficult
itinerary proofs isolated from endpoint plumbing.
