# Odd Tori Completion Goal

Date: 2026-05-05.

This note incorporates `responses_temp.md` and
`odd_tori_formalization_draft_20260504.zip`.  It supersedes the older draft
diagnosis where the signed half-penalty bridge was still treated as a local
blocker.  In the current repository, that bridge and the packet arithmetic are
already closed in Lean; the remaining work is theorem content, not wrapper
plumbing.

## Final Endpoint

The completion theorem remains:

```lean
∀ {d m : Nat}, 2 ≤ d → Odd m → 3 ≤ m →
  Shared.CayleyHamiltonDecomposition d m
```

The sharp existing adapter is:

```lean
theorem RoundComposite.Concrete
  .oddModulusToriAllDimensionsGoal_of_v4_seedProper_core_rawMatrix
    (hQge2Proper :
      PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hCore :
      OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal)
    (hMat :
      ActiveHall.FiniteHoffman.RawZeroOneMatrixGoal.{0, 0}) :
    OddModulusToriAllDimensionsGoal
```

Thus the completion goal is to prove the following package:

```lean
RoundComposite.Concrete.OddModulusToriV4CompletionCoreRawMatrixGoal
```

or equivalently its three fields:

```lean
PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal
OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal
ActiveHall.FiniteHoffman.RawZeroOneMatrixGoal.{0, 0}
```

The compatible-matrix or Hall-realization variants are equally sufficient:

```lean
ActiveHall.FiniteHoffman.CompatibleZeroOneMatrixGoal.{0, 0}
ActiveHall.HallRealizationGoal.{0, 0}
```

## Closed Context

The following should not be treated as current blockers.

```lean
PrefixCount.qge2SignedSupportHalfPenaltyGoal
PrefixCount.qge2IndicatorCutsHalfSlackToSupportGoal
PrefixCount.ordinaryQge2IndicatorToFullSupportGoal_of_internalHalfSlack
```

The q >= 2 branch has been reduced to seed/proper-cut closure:

```lean
PrefixCount.ordinaryQge2SignedFullSupportTrellisGoal_of_seedClosure
PrefixCount.ordinaryQge2SignedFullSupportTrellisGoal_iff_seedProperCutClosureGoal
PrefixCount.ordinaryQge2SignedTrellisHoffmanGoal_iff_seedProperCutClosureGoal
```

The ActiveHall extraction/adapters are already in place; proving a matrix,
exact edge-colouring, or Hall-realization theorem feeds the final endpoint
through existing Lean code.

The successor packet arithmetic is also closed, including packet shape,
proper-prefix unit facts, prefix slot counts, and tail-carry residue units.

## Absorbed Draft Corrections

`odd_tori_formalization_draft_20260504.zip` was written against an earlier
state where `PrefixCount.Qge2SignedSupportHalfPenaltyGoal` was still a local
blocker.  In the current repository this theorem is closed, and the q >= 2
branch has moved past the support bridge.  The draft's `SignedTrellisDraft`
therefore should be read as historical proof-splitting context, not as the
current target list.

The `responses_temp.md` recommendation is the current sharper route: avoid a
false arbitrary-row signed packing theorem and close the ordinary branch
through the exact seed/proper-cut closure interface.  Likewise, the draft
`BaseTailGeometryDraft` names have been absorbed into the stronger active-block
split in `RoundComposite/BaseTailGeometry.lean` and `RoundComposite/OddCore.lean`.

## Target 1: q >= 2 Signed Seed Closure

Preferred theorem:

```lean
PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal
```

Equivalent sufficient theorem:

```lean
PrefixCount.OrdinaryQge2SignedSeedClosureGoal
```

This is the finite integral signed-trellis/Rado-Edmonds content for the
ordinary q >= 2 branch.  It should not be replaced by the false arbitrary-row
packing theorem; the repository already records the counterexample direction.

Direct proof fallback: prove this theorem itself by finite trellis/submodular
flow, Rado-Edmonds extraction, or a specialized integral network theorem.  A
large direct proof is acceptable if it closes the exact ordinary/proper-cut
target above.

## Target 2: Finite de Werra / Active Hall Realization

Preferred theorem:

```lean
ActiveHall.FiniteHoffman.RawZeroOneMatrixGoal.{0, 0}
```

Equivalent sufficient targets:

```lean
ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal.{0, 0}
ActiveHall.FiniteHoffman.ExactEdgeColoringGoal.{0, 0}
ActiveHall.FiniteHoffman.CompatibleZeroOneMatrixGoal.{0, 0}
ActiveHall.FiniteHoffman.CompatibleDeWerraGoal.{0, 0}
ActiveHall.HallRealizationGoal.{0, 0}
ActiveHall.EraseLastHallCutsTokenLinearChoiceGoal.{0, 0}
ActiveHall.EraseLastHallCutsProperTokenLinearChoiceGoal.{0, 0}
ActiveHall.EraseLastHallCutsProperTokenQuotaSelectionGoal.{0, 0}
ActiveHall.EraseLastHallCutsTwoSingletonProperTokenCutSlackSelectionGoal.{0, 0}
ActiveHall.EraseLastHallCutsTwoSingletonProperTokenQuotaSelectionGoal.{0, 0}
```

The mathematical content is the finite compatible edge-colouring theorem.  The
existing Lean adapters already handle one-hot extraction and translation among
the copied-edge, exact-colouring, compatible-colouring, and Hall-realization
forms.

The next induction interface is also explicit: once the last-symbol erase
choice is supplied, the `T = 4` case reduces to the already closed `T <= 3`
pipeline based on singleton token cut-slack selection.

```lean
ActiveHall.hallRealization_succ_of_eraseLastHallCuts_and_lower_T_le_three
ActiveHall.hallRealization_four_of_eraseLastHallCuts_and_singletonTokenCutSlackSelection
ActiveHall.EraseLastHallCutsFourGoal
ActiveHall.hallRealization_four_of_eraseLastHallCutsFourGoal
ActiveHall.FiniteHoffman.rawZeroOneMatrix_four_of_eraseLastHallCutsFourGoal
ActiveHall.EraseLastHallCutsFourTokenCutSlackSelectionGoal
ActiveHall.EraseLastHallCutsFourSmallTokenCutSlackSelectionGoal
ActiveHall.EraseLastHallCutsFourSingletonPairTokenCutSlackSelectionGoal
ActiveHall.EraseLastHallCutsFourSingletonPairTokenQuotaSelectionGoal
ActiveHall.CountMatrix.choiceLowHitCount_univ_le_cutSlack_image_castSucc
ActiveHall.Incidence.cutCap_image_castSucc
ActiveHall.CountMatrix.cutMass_image_castSucc
ActiveHall.CountMatrix.cutSlack_image_castSucc
ActiveHall.Incidence.cutCap_image_castSucc_pair
ActiveHall.CountMatrix.cutMass_image_castSucc_pair
ActiveHall.CountMatrix.cutSlack_image_castSucc_pair
ActiveHall.CountMatrix.cutSlack_image_castSucc_pair_eq_min_two
ActiveHall.eraseLastHallCutsTokenLinearChoiceGoal_of_proper
ActiveHall.eraseLastHallCutsProperTokenLinearChoiceGoal_of_quota
ActiveHall.hallRealizationGoal_of_eraseLastHallCutsProperTokenLinearChoice
ActiveHall.eraseLastHallCutsProperTokenQuotaSelectionGoal_of_hallRealization
ActiveHall.hallRealizationGoal_of_eraseLastHallCutsProperTokenQuotaSelection
ActiveHall.hallRealizationGoal_iff_eraseLastHallCutsProperTokenLinearChoiceGoal
ActiveHall.hallRealizationGoal_iff_eraseLastHallCutsProperTokenQuotaSelectionGoal
ActiveHall.eraseLastHallCutsFourSingletonPairTokenCutSlackSelectionGoal_of_quota
ActiveHall.eraseLastHallCutsFourSmallTokenCutSlackSelectionGoal_of_singletonPair
ActiveHall.eraseLastHallCutsFourTokenCutSlackSelectionGoal_of_small
ActiveHall.eraseLastHallCutsFourGoal_of_tokenCutSlackSelection
ActiveHall.hallRealization_four_of_fourTokenCutSlackSelection
ActiveHall.hallRealization_four_of_fourSmallTokenCutSlackSelection
ActiveHall.hallRealization_four_of_fourSingletonPairTokenCutSlackSelection
ActiveHall.hallRealization_four_of_fourSingletonPairTokenQuotaSelection
ActiveHall.FiniteHoffman.rawZeroOneMatrixGoal_of_eraseLastHallCutsProperTokenLinearChoiceGoal
ActiveHall.FiniteHoffman.rawZeroOneMatrixGoal_iff_eraseLastHallCutsProperTokenLinearChoiceGoal
ActiveHall.eraseLastHallCutsTwoSingletonTokenCutSlackSelectionGoal_of_proper
ActiveHall.eraseLastHallCutsTwoSingletonProperTokenCutSlackSelectionGoal_of_quota
ActiveHall.hallRealization_three_of_singletonProperTokenCutSlackSelection
ActiveHall.hallRealization_of_T_le_three_of_singletonProperTokenCutSlackSelection
ActiveHall.hallRealization_three_of_singletonProperTokenQuotaSelection
ActiveHall.hallRealization_of_T_le_three_of_singletonProperTokenQuotaSelection
ActiveHall.FiniteHoffman.rawZeroOneMatrix_three_of_singletonProperTokenCutSlackSelection
ActiveHall.FiniteHoffman.rawZeroOneMatrix_of_T_le_three_of_singletonProperTokenCutSlackSelection
ActiveHall.FiniteHoffman.rawZeroOneMatrix_three_of_singletonProperTokenQuotaSelection
ActiveHall.FiniteHoffman.rawZeroOneMatrix_of_T_le_three_of_singletonProperTokenQuotaSelection
ActiveHall.FiniteHoffman.rawZeroOneMatrix_four_of_fourTokenCutSlackSelection
ActiveHall.FiniteHoffman.rawZeroOneMatrix_four_of_fourSmallTokenCutSlackSelection
ActiveHall.FiniteHoffman.rawZeroOneMatrix_four_of_fourSingletonPairTokenCutSlackSelection
ActiveHall.FiniteHoffman.rawZeroOneMatrix_four_of_fourSingletonPairTokenQuotaSelection
ActiveHall.FiniteHoffman.rawZeroOneMatrixGoal_of_eraseLastHallCutsProperTokenQuotaSelectionGoal
ActiveHall.FiniteHoffman.rawZeroOneMatrixGoal_iff_eraseLastHallCutsProperTokenQuotaSelectionGoal
```

The new proper-token target is a genuine reduction of the general erase step:
the case `S = Finset.univ : Finset (Fin T)` is automatic from the erased
matrix identity below, so the hard finite theorem only has to control
nonempty proper symbol cuts.

The proper-token target also has an explicit quota form:

```lean
ActiveHall.EraseLastHallCutsProperTokenQuotaSelectionGoal
```

For every nonempty proper color cut `U` and nonempty proper symbol cut `S`, its
right-hand side is

```lean
(∑ x : X, min ((I.active x ∩ U).card) S.card)
  - ∑ c ∈ U, ∑ σ ∈ S, M.val c (Fin.castSucc σ)
```

The adapter `eraseLastHallCutsProperTokenLinearChoiceGoal_of_quota` rewrites
this quota inequality to the old cut-slack form using
`CountMatrix.cutSlack_image_castSucc`.  Thus a proof of the quota target is
already enough for the full `RawZeroOneMatrixGoal` route.  Lean also records
the reverse implication from `HallRealizationGoal`, so this quota formulation
is not a weaker side condition but an equivalent form of the ActiveHall core.

The new `SmallToken` target applies the same idea to the `T = 4` erase step:
the case `S = Finset.univ : Finset (Fin 3)` is automatic from the erased
matrix identity

```lean
CountMatrix.choiceLowHitCount_univ_le_cutSlack_image_castSucc
```

so the remaining `T = 4` token-selection proof only has to control nonempty
proper symbol cuts with `S.card ≤ 2`.  This has been split further into the
explicit finite cases `S = {σ}` and `S = {σ, τ}` with `σ ≠ τ`.
The pair case now also has an explicit quota form using
`CountMatrix.cutSlack_image_castSucc_pair_eq_min_two`, so the next proof target
can work directly with
`∑ x, min ((I.active x ∩ U).card) 2` and avoid unfolding cutSlack for
two-symbol cuts.

The `T = 3` base selection target has also been sharpened: for singleton
symbol cuts, `U = ∅` and `U = univ` are automatic.  The remaining low-rank
selection theorem can therefore be stated with nonempty proper color cuts:

```lean
ActiveHall.EraseLastHallCutsTwoSingletonProperTokenCutSlackSelectionGoal
```

Lean proves that this proper version supplies the older singleton-token target
and the corresponding `T <= 3` raw zero-one matrix adapters.
The singleton slack has also been calculated explicitly:

```lean
CountMatrix.cutSlack_symbol_singleton
CountMatrix.cutSlack_image_castSucc_singleton
Incidence.sum_colorDegree_on_le_hitCount_mul
```

Thus the low-rank target can be stated in the concrete quota form

```lean
ActiveHall.EraseLastHallCutsTwoSingletonProperTokenQuotaSelectionGoal
```

where the right-hand side is `I.hitCount U - ∑ c ∈ U, M.val c (Fin.castSucc σ)`.
This quota theorem implies the cut-slack theorem by the two displayed
`cutSlack` identities.

Direct proof fallback: prove `RawZeroOneMatrixGoal.{0,0}` or
`HallRealizationGoal.{0,0}` directly.  Ordinary one-column Hall matching is not
enough by itself, because the last-symbol choice must preserve all residual
Hall cut inequalities.

## Target 3: Successor Small-Modulus Base-Tail Geometry

Preferred theorem:

```lean
Concrete.OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal
```

Current Lean split:

```lean
Concrete.OddSuccessorBaseTailCylinderConstructionGoal
Concrete.OddSuccessorBaseTailResidueRoundingGoal
Concrete.OddSuccessorBaseTailPrimitiveActiveLiftGoal
```

The new important point from `responses_temp.md` is that the weak cylinder
interface is probably not enough for the rounding proof.  The current
`BaseTail.IsCylinder` records active fiber cardinality, ordinary direction
uniqueness, color Hamiltonicity, and active degree congruence modulo `m`.
From this we have proved positivity/divisibility consequences, but controlled
rounding needs the stronger paper data:

```text
activeBlock c = α_c
0 < α_c < m
Nat.Coprime α_c m
colorDegree c = (m - α_c) * m ^ b
```

The Lean file `RoundComposite/BaseTailGeometry.lean` now contains the helper
structure:

```lean
Concrete.BaseTail.ActiveBlockData
```

and derives the reusable consequences:

```lean
ActiveBlockData.activeBlock_isUnit
ActiveBlockData.active_complement_coprime
ActiveBlockData.active_complement_isUnit
ActiveBlockData.active_degree_mod
ActiveBlockData.active_degree_lower_bound
ActiveBlockData.active_degree_upper_bound
ActiveBlockData.sum_colorDegree_lower_bound
ActiveBlockData.sum_colorDegree_nonempty_lower_bound
ActiveBlockData.sum_colorDegree_compl_lower_bound
ActiveBlockData.slack_error_lt_sum_colorDegree_nonempty
ActiveBlockData.slack_error_lt_sum_colorDegree_compl
ActiveBlockData.slack_error_lt_sum_colorDegree_nonempty_min
ActiveBlockData.slack_error_lt_sum_colorDegree_compl_min
ActiveBlockData.sum_colorDegree_le_T_mul_hitCount
ActiveBlockData.slack_error_lt_T_mul_hitCount_nonempty
ActiveBlockData.slack_error_lt_T_mul_hitCount_compl
ActiveBlockData.slack_error_lt_T_mul_hitCount_nonempty_min
ActiveBlockData.slack_error_lt_T_mul_hitCount_compl_min
ActiveHall.Incidence.mixedCount
ActiveHall.Incidence.mixedCount_eq_card_filter
ActiveHall.Incidence.mixedCount_le_hitCount
ActiveHall.Incidence.mixedCount_le_hitCount_compl
ActiveHall.Incidence.scaled_bary_point_le_cutCap_point
ActiveHall.Incidence.scaled_bary_point_add_mixed_le_cutCap_point
ActiveHall.Incidence.scaled_bary_cutMass_le_cutCap
ActiveHall.Incidence.scaled_bary_cutMass_add_mixed_le_cutCap
ActiveHall.CountMatrix.hallCuts_of_scaled_bary_error_le_mixed
ActiveHall.CountMatrix.hallCuts_of_nontrivial_scaled_bary_error_le_mixed
ActiveBlockData.sum_active_complement_eq
ActiveBlockData.sum_activeBlock_eq
ActiveBlockData.isCylinder_of_activeBlockData
exists_universalResidueSpec_compatible_primitive_of_activeBlockData
exists_universalResidueSpec_compatible_primitive_of_successor_activeBlockData
feasiblePrimitiveResidues_of_successor_activeBlockData_feasible_compatible
primitiveActiveSymboling_of_successor_activeBlockData_feasible_compatible
```

The new `scaled_bary` lemmas are the integer-scaled replacement for rational
barycenter language.  The uniform barycenter lies in the Hall polytope, and
each mixed active vertex contributes at least `min S.card (T - S.card)` units
of scaled slack.  Consequently, a controlled rounding theorem only has to prove

```lean
T * M.cutMass U S
  ≤ S.card * (∑ c ∈ U, I.colorDegree c)
      + I.mixedCount U * min S.card (T - S.card)
```

for all cuts; `CountMatrix.hallCuts_of_scaled_bary_error_le_mixed` then turns
that estimate into `M.HallCuts`.

Therefore the base-tail proof should expose this data deliberately, either by
strengthening the cylinder-construction subgoal with an internal
`BlockCylinder`/`StrongCylinder` predicate or by proving the active-block
formula as part of `OddSuccessorBaseTailCylinderConstructionGoal` and carrying
it into rounding and lift.  It should not be hidden behind another opaque
abstract endpoint.

`RoundComposite/OddCore.lean` now records this stronger split explicitly:

```lean
OddSuccessorBaseTailActiveBlockCylinderConstructionGoal
OddSuccessorBaseTailActiveBlockResidueRoundingGoal
OddSuccessorBaseTailActiveBlockCompatibleResidueRoundingGoal
OddSuccessorBaseTailActiveBlockPrimitiveLiftGoal
oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_activeBlockPieces
oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_activeBlockCompatiblePieces
```

The practical target decomposition is:

1. Cylinder construction with active-block data:
   construct the base-tail cylinder from `StandardCayleySolved b m` and packet
   data, and prove the active-degree formula above.
2. Controlled residue rounding:
   use the active-degree formula and `m ^ b > m * (b + T) * T` to prove the
   sharper compatible-residue theorem:

   ```lean
   OddSuccessorBaseTailActiveBlockCompatibleResidueRoundingGoal
   ```

   This says that every row/column compatible primitive residue specification
   has a nonnegative count matrix satisfying Hall cuts and the required
   residues.  Lean now proves

   ```lean
   oddSuccessorBaseTailActiveBlockResidueRoundingGoal_of_compatible
   ```

   so this sharper theorem immediately supplies
   `OddSuccessorBaseTailActiveBlockResidueRoundingGoal` and hence
   `BaseTail.HasFeasiblePrimitiveResidues hT2 Cyl`.
3. Primitive active lift:
   use a primitive active symboling plus packet proper-prefix units to prove
   `StandardCayleySolved (b + T) m`.

Direct proof fallback: prove
`Concrete.OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal` or the
stronger `Concrete.OddCoreSmallModulusSlackPacketLiftAddGoal` directly.  This
is acceptable only if it contains the actual cylinder construction, residue
rounding/Hall cuts, and base-tail Hamilton lift.

## Goal Statement To Pursue

The active proof goal should be:

```text
Prove OddModulusToriV4CompletionCoreRawMatrixGoal, hence for all d >= 2 and
odd m >= 3 construct Shared.CayleyHamiltonDecomposition d m.

Concretely close:
  1. PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal.
  2. ActiveHall.FiniteHoffman.RawZeroOneMatrixGoal.{0,0}
     or an equivalent Hall/de Werra theorem.
  3. Concrete.OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal,
     with the base-tail proof allowed to introduce a stronger active-block
     cylinder interface carrying colorDegree c = (m - activeBlock c) * m^b.
```

## Direct-Proof Fallback Policy

Large direct proofs are acceptable, but only when they close one of the exact
interfaces consumed by the final endpoint.  A direct proof should not introduce
another opaque theorem unless it is immediately wrapped into one of the three
fields below.

### Direct q >= 2 Target

The direct target is:

```lean
PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal
```

This may be proved by a finite signed-trellis theorem, a Rado-Edmonds
extraction, or a specialized integral flow argument.  The proof must preserve
the ordinary-row hypotheses and the proper-cut reduction; it must not assert
the false arbitrary-row signed packing theorem.

### Direct ActiveHall Target

The direct target is one of:

```lean
ActiveHall.FiniteHoffman.RawZeroOneMatrixGoal.{0, 0}
ActiveHall.HallRealizationGoal.{0, 0}
```

The direct theorem may be proved as finite de Werra/Hoffman compatible
edge-colouring, a 0-1 matrix theorem, or a finite integral flow theorem.  The
important constraint is that the result realizes the whole count matrix under
all rectangle/Hall cuts; a single ordinary matching lemma is not sufficient
unless it also proves preservation of all residual cuts.

### Direct Base-Tail Geometry Target

The direct target is:

```lean
Concrete.OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal
```

The direct proof must still expose the mathematical content internally:

```text
1. cylinder construction from StandardCayleySolved b m and packet data,
2. active-block degree formula colorDegree c = (m - activeBlock c) * m^b,
3. controlled residue rounding using m^b > m * (b + T) * T,
4. primitive active lift to StandardCayleySolved (b + T) m.
```

If the active-block split becomes too cumbersome, proving this core theorem
directly is permitted, but the proof should keep the active-block degree
calculation visible so that the rounding and primitive-residue steps remain
auditable.

## Completion Gate

Do not call the formalization complete until all of the following pass:

```bash
lake build RoundComposite
git diff --check
grep -R -n -E '\b(sorry|admit|axiom|constant)\b' \
  RoundComposite Shared TorusD3Odd D5Odd D7Odd --include='*.lean'
```

The final grep must return no matches.
