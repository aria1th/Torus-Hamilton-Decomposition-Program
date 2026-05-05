# Odd Tori Remaining Three Targets

Date: 2026-05-04.

This note records the current three Lean-facing theorem-content targets for
closing the odd-modulus torus Hamilton decomposition formalization.  It is a
compact handoff document for independent mathematical or Lean review.

## Final Endpoint

The final package goal is:

```lean
RoundComposite.Concrete.OddModulusToriAllDimensionsGoal
```

equivalently, pointwise:

```lean
∀ {d m : Nat}, 2 ≤ d → Odd m → 3 ≤ m →
  Shared.CayleyHamiltonDecomposition d m
```

The current sharp Lean adapter is:

```lean
def RoundComposite.Concrete.OddModulusToriV4CompletionCoreRawMatrixGoal :
    Prop

theorem RoundComposite.Concrete
  .oddModulusToriAllDimensionsGoal_of_v4_seedProper_core_rawMatrix
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hCore : OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal)
    (hMat : ActiveHall.FiniteHoffman.RawZeroOneMatrixGoal.{0, 0}) :
    OddModulusToriAllDimensionsGoal
```

There is also a compatible-matrix variant:

```lean
def RoundComposite.Concrete.OddModulusToriV4CompletionCoreCompatibleMatrixGoal :
    Prop

theorem RoundComposite.Concrete
  .oddModulusToriAllDimensionsGoal_of_v4_seedProper_core_compatibleMatrix
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hCore : OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal)
    (hMat : ActiveHall.FiniteHoffman.CompatibleZeroOneMatrixGoal.{0, 0}) :
    OddModulusToriAllDimensionsGoal
```

There is also a Hall-realization variant:

```lean
def RoundComposite.Concrete.OddModulusToriV4CompletionCoreHallGoal :
    Prop

theorem RoundComposite.Concrete
  .oddModulusToriAllDimensionsGoal_of_v4_seedProper_core_hall
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hCore : OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal)
    (hHall : ActiveHall.HallRealizationGoal.{0, 0}) :
    OddModulusToriAllDimensionsGoal
```

Thus the remaining proof burden is exactly the three fields appearing in the
first adapter, or the compatible matrix/Hall realization field in place of the
raw matrix field.

As a final-resort direct-proof route, one may ignore the component split and
prove one of the bundled completion Props directly:

```lean
RoundComposite.Concrete.OddModulusToriV4CompletionCoreRawMatrixGoal
RoundComposite.Concrete.OddModulusToriV4CompletionCoreCompatibleMatrixGoal
RoundComposite.Concrete.OddModulusToriV4CompletionCoreHallGoal
```

Either theorem is intentionally large: it packages the q>=2 signed closure,
the successor-small geometry core, and the finite zero-one edge-colouring
content.  Proving one of these Props is exactly sufficient for the final
odd-tori endpoint.

## Closed Context

The half-slack/support branch is now closed in Lean:

```lean
PrefixCount.qge2SignedSupportHalfPenaltyGoal
PrefixCount.qge2IndicatorCutsHalfSlackToSupportGoal
PrefixCount.ordinaryQge2IndicatorToFullSupportGoal_of_internalHalfSlack
```

This supersedes the older draft diagnosis that treated
`Qge2SignedSupportHalfPenaltyGoal` as the immediate local blocker.  In the
current tree that bridge is proved; the q>=2 content left for completion is
the signed seed closure/proper-cut closure theorem itself.

The full-support q>=2 endpoint is reduced to seed closure:

```lean
theorem PrefixCount.ordinaryQge2SignedFullSupportTrellisGoal_of_seedClosure
    (hClosure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal) :
    PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal

PrefixCount.ordinaryQge2SignedTrellisHoffmanGoal_iff_signedSeedClosureGoal
PrefixCount.ordinaryQge2SignedTrellisHoffmanGoal_iff_seedProperCutClosureGoal
PrefixCount.ordinaryQge2SignedSeedProperCutClosureGoal_of_fullSupportTrellisGoal
PrefixCount.ordinaryQge2SignedFullSupportTrellisGoal_iff_seedProperCutClosureGoal
```

The return-tail/odometer chain is closed and supplies:

```lean
prefixCountFirstHitReturnTailMonodromyOrbitGoal
```

The active Hall extraction layer is closed:

```lean
ActiveHall.FiniteHoffman.rawExactEdgeColoringGoal_of_rawMatrix
ActiveHall.FiniteHoffman.rawZeroOneMatrix_zero
ActiveHall.FiniteHoffman.rawZeroOneMatrix_one
ActiveHall.FiniteHoffman.rawZeroOneMatrix_two
ActiveHall.FiniteHoffman.rawZeroOneMatrix_of_T_le_two
ActiveHall.FiniteHoffman.rawZeroOneMatrix_three_of_singletonSelection
ActiveHall.FiniteHoffman.rawZeroOneMatrix_three_of_singletonCutSlackSelection
ActiveHall.FiniteHoffman.rawZeroOneMatrix_of_T_le_three_of_singletonSelection
ActiveHall.FiniteHoffman.rawExactEdgeColoring_of_exactWitness
ActiveHall.FiniteHoffman.rawZeroOneMatrix_of_rawExactWitness
ActiveHall.FiniteHoffman.rawZeroOneMatrixGoal_of_rawExactEdgeColoringGoal
ActiveHall.FiniteHoffman.rawZeroOneMatrixGoal_iff_rawExactEdgeColoringGoal
ActiveHall.FiniteHoffman.rawExactEdgeColoringGoal_of_matrix
ActiveHall.FiniteHoffman.compatibleDeWerraGoal_of_matrix
ActiveHall.FiniteHoffman.compatibleZeroOneMatrixGoal_of_compatibleDeWerraGoal
ActiveHall.FiniteHoffman.compatibleZeroOneMatrixGoal_iff_compatibleDeWerraGoal
ActiveHall.FiniteHoffman.rawExactEdgeColoringGoal_of_exactEdgeColoringGoal
ActiveHall.FiniteHoffman.rawExactEdgeColoringGoal_iff_exactEdgeColoringGoal
ActiveHall.FiniteHoffman.exactEdgeColoringGoal_of_hoffmanOrderedSDRGoal
ActiveHall.FiniteHoffman.exactEdgeColoringGoal_iff_hoffmanOrderedSDRGoal
ActiveHall.FiniteHoffman.exactEdgeColoringGoal_of_hallRealizationGoal
ActiveHall.FiniteHoffman.exactEdgeColoringGoal_iff_hallRealizationGoal
ActiveHall.FiniteHoffman.rawExactEdgeColoringGoal_of_hallRealizationGoal
ActiveHall.FiniteHoffman.rawZeroOneMatrixGoal_of_hallRealizationGoal
ActiveHall.FiniteHoffman.rawZeroOneMatrixGoal_iff_hallRealizationGoal
ActiveHall.FiniteHoffman.rawZeroOneMatrixGoal_of_eraseLastHallCutsTokenLinearChoiceGoal
ActiveHall.FiniteHoffman.rawZeroOneMatrixGoal_iff_eraseLastHallCutsTokenLinearChoiceGoal
ActiveHall.universalUnitResidueSpecOfTwoLe
ActiveHall.universalUnitResidueSpecOfTwoLe_rowCompatible
ActiveHall.universalUnitResidueSpecOfTwoLe_colCompatible
ActiveHall.exists_universalUnitResidueSpecOfTwoLe_compatible_primitive
ActiveHall.CountMatrix.hallCuts_one
ActiveHall.CountMatrix.finset_fin_two_nonempty_proper_eq_singleton
ActiveHall.CountMatrix.hallCuts_two_of_singleSymbol
ActiveHall.CountMatrix.hallCuts_two_iff_singleSymbol
ActiveHall.CountMatrix.eraseLastCountMatrix_hallCuts_two_of_singleton_cutCap_slack
ActiveHall.CountMatrix.eraseLastHallCuts_two_of_singleton_selection
ActiveHall.CountMatrix.eraseLastHallCuts_two_of_singleton_cutSlack_selection
ActiveHall.EraseLastHallCutsTwoSingletonSelectionGoal
ActiveHall.EraseLastHallCutsTwoSingletonCutSlackSelectionGoal
ActiveHall.EraseLastHallCutsTwoSingletonTokenCutSlackSelectionGoal
ActiveHall.eraseLastHallCutsTwoSingletonCutSlackSelectionGoal_of_token
ActiveHall.eraseLastHallCutsTwoSingletonSelectionGoal_of_cutSlack
ActiveHall.hallRealization_three_of_singletonSelection
ActiveHall.hallRealization_three_of_singletonCutSlackSelection
ActiveHall.hallRealization_three_of_singletonTokenCutSlackSelection
ActiveHall.hallRealization_of_T_le_three_of_singletonCutSlackSelection
ActiveHall.hallRealization_of_T_le_three_of_singletonTokenCutSlackSelection
ActiveHall.hallRealization_succ_of_eraseLastHallCuts
ActiveHall.eraseLastHallCuts_one
ActiveHall.hallRealization_two
ActiveHall.hallRealization_of_T_le_two
ActiveHall.hallRealization_of_T_le_three_of_singletonSelection
ActiveHall.FiniteHoffman.rawZeroOneMatrix_three_of_singletonTokenCutSlackSelection
ActiveHall.FiniteHoffman.rawZeroOneMatrix_of_T_le_three_of_singletonCutSlackSelection
ActiveHall.FiniteHoffman.rawZeroOneMatrix_of_T_le_three_of_singletonTokenCutSlackSelection
```

The successor packet arithmetic is closed:

```lean
Concrete.BaseTail.activeDir
Concrete.BaseTail.Cylinder
Concrete.BaseTail.Cylinder.incidence
Concrete.BaseTail.Cylinder.step
Concrete.BaseTail.Cylinder.active_fiber_card
Concrete.BaseTail.Cylinder.active_direction_exists_of_pos
Concrete.BaseTail.Cylinder.step_activeDir_eq_of_dir_ne
Concrete.BaseTail.Cylinder.dir_ne_activeDir_of_colorDegree_zero
Concrete.BaseTail.Cylinder.iterate_step_activeDir_eq_of_colorDegree_zero
Concrete.BaseTail.IsCylinder
Concrete.BaseTail.IsCylinder.ordinary_direction_exists
Concrete.BaseTail.IsCylinder.ordinary_fiber_card
Concrete.BaseTail.IsCylinder.dir_fiber_card
Concrete.BaseTail.IsCylinder.active_degree_pos
Concrete.BaseTail.IsCylinder.active_degree_dvd_modulus
Concrete.BaseTail.IsCylinder.modulus_le_active_degree
Concrete.BaseTail.ActiveSymboling
Concrete.BaseTail.IsActiveSymboling
Concrete.BaseTail.IsPrimitiveActiveSymboling
Concrete.BaseTail.HasFeasiblePrimitiveResidues
Concrete.BaseTail.activeSymboling_of_feasible_and_hallRealization
Concrete.BaseTail.primitiveActiveSymboling_of_feasible_primitiveResidue_and_hallRealization
Concrete.BaseTail.primitiveActiveSymboling_of_feasiblePrimitiveResidues_and_hallRealization
Concrete.BaseTail.exists_universalResidueSpec_compatible_primitive_of_cylinder
Concrete.BaseTail.exists_universalResidueSpec_compatible_primitive_of_successor_cylinder
Concrete.BaseTail.feasiblePrimitiveResidues_of_successor_cylinder_feasible_compatible
Concrete.BaseTail.primitiveActiveSymboling_of_successor_cylinder_feasible_compatible
Concrete.BaseTail.successorPacketLengthTwoOrThreeGoal
Concrete.BaseTail.successorPacketLengthThreeCountGoal
Concrete.BaseTail.successorPacketLengthThreePacketCountGoal
Concrete.BaseTail.successorPacketExistsUniqueLengthThreeGoal
Concrete.BaseTail.successorPacketNonExceptionalLengthTwoGoal
Concrete.BaseTail.successorPacketExceptionalShapeGoal
Concrete.BaseTail.successorPacketProperPrefixUnitsGoal
Concrete.BaseTail.successorPacketProperPrefixRangeGoal
Concrete.BaseTail.successorPacketProperPrefixSlotCountGoal
Concrete.BaseTail.PacketPrefixSlot
Concrete.BaseTail.packetPrefixSlot_card_eq_sum
Concrete.BaseTail.successorPacketPrefixSlotCardGoal
Concrete.BaseTail.successorPacketPrefixSlotEquivGoal
Concrete.BaseTail.packetPrefixSlotPrefixLength_lt
Concrete.BaseTail.successorPacketPrefixSlotUnitsGoal
Concrete.BaseTail.successorPacketPrefixSlotRangeGoal
Concrete.BaseTail.successorPacketTailCarryDataGoal
Concrete.BaseTail.PacketTailCarryData
Concrete.BaseTail.PacketTailCarryData.residue_isUnit
Concrete.BaseTail.successorPacketTailCarryStructureGoal
Concrete.BaseTail.successorPacketTailCarryResidueUnitsGoal
```

and is used by:

```lean
theorem oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_core
    (hCore : OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal) :
    OddSuccessorSmallModulusBaseTailGeometryFromHallGoal
```

## Target 1: q>=2 Seed Proper-Cut Closure

Preferred Lean target:

```lean
PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal
```

Equivalent sufficient target:

```lean
PrefixCount.OrdinaryQge2SignedSeedClosureGoal
PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal
PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal
PrefixCount.OrdinaryQge2SignedMatrixGoal
```

Meaning: this is the remaining signed trellis/seed closure theorem for the
high-modulus prefix-count branch.  The matrix formulation is the narrowest
paper-facing version: prove the signed matrix for each
`OrdinaryQge2PlanData`, after the already-closed row-cut estimates.  It should
not be replaced by the false arbitrary-row `Qge2SignedColumnPackingGoal`; the
repository already proves a counterexample to that stronger-looking statement.
The practical direct-proof endpoint is therefore the ordinary/proper-cut seed
closure, not a general full-support HEG theorem and not the already closed
half-penalty support bridge.

Completion criterion: a theorem with no `sorry/admit/axiom/constant` supplies
one of the two Props above, and the final adapter consumes it without extra
q>=2 hypotheses.

## Target 2: Finite Zero-One Edge Colouring

Preferred Lean target:

```lean
ActiveHall.FiniteHoffman.RawZeroOneMatrixGoal.{0, 0}
```

Equivalent target:

```lean
ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal.{0, 0}
ActiveHall.FiniteHoffman.ExactEdgeColoringGoal.{0, 0}
ActiveHall.HallRealizationGoal.{0, 0}
ActiveHall.EraseLastHallCutsTokenLinearChoiceGoal.{0, 0}
```

Sufficient alternative:

```lean
ActiveHall.FiniteHoffman.CompatibleZeroOneMatrixGoal.{0, 0}
ActiveHall.FiniteHoffman.CompatibleDeWerraGoal.{0, 0}
```

Meaning: this is the finite de Werra/Hoffman compatible edge-colouring theorem
in copied-edge or binary matrix form.  The two copied-edge formulations are
now Lean-equivalent, the ordered `ExactEdgeColoringGoal` form is Lean-equivalent
to the raw copied-edge form, and `ExactEdgeColoringGoal` is Lean-equivalent to
`HallRealizationGoal`.  The compatible matrix/function formulations are also
Lean-equivalent.  The induction-ready `EraseLastHallCutsTokenLinearChoiceGoal`
is also Lean-equivalent to the raw zero-one matrix form.  The remaining
mathematical content is the finite compatible edge-colouring/Hall realization
theorem itself, concretely the de Werra last-symbol selection theorem, not
extraction between representations.

The pointwise copied-edge base cases `T = 0`, `T = 1`, and `T = 2` are now
closed as `rawZeroOneMatrix_zero`, `rawZeroOneMatrix_one`, and
`rawZeroOneMatrix_two`.  The remaining proof work is therefore the genuine
induction/selection step for arbitrary `T + 1`, where the last-symbol choice
must preserve all residual Hall cuts.
The pointwise symboling induction step after such a choice is now isolated as
`hallRealization_succ_of_eraseLastHallCuts`; the missing content is exactly the
existence of the last-symbol token choice with the residual slack condition.

Completion criterion: prove either matrix theorem at universe zero.  A
universe-polymorphic proof is cleaner but not required for the odd-tori final
endpoint.

## Target 3: Successor Small-Modulus Base-Tail Geometry Core

Preferred Lean target:

```lean
OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal
OddCoreSmallModulusSlackPacketLiftAddGoal
OddSuccessorBaseTailCylinderConstructionGoal
OddSuccessorBaseTailResidueRoundingGoal
OddSuccessorBaseTailPrimitiveActiveLiftGoal
```

Meaning: this is the project-specific geometry construction for the
small-modulus successor branch after packet arithmetic has been separated out.
The core theorem may assume the proper-prefix-unit condition directly; the raw
successor hypotheses plus `T = b + 1` are converted to that condition by the
closed packet lemmas.  The stronger `OddCoreSmallModulusSlackPacketLiftAddGoal`
also suffices, since Lean proves
`oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_coreAdd`.

The remaining proof work inside this target is:

```text
OddSuccessorBaseTailCylinderConstructionGoal
OddSuccessorBaseTailResidueRoundingGoal
OddSuccessorBaseTailPrimitiveActiveLiftGoal
```

The Hall realization part of active residue rounding is now separated.  For a
successor cylinder, Lean already proves that compatible primitive universal
residues exist, and that any theorem producing
`FeasibleWithResidues Cyl.incidence R` for every compatible primitive residue
gives a primitive active symboling via `HallRealizationGoal`.  Thus the active
residue subproblem left for this target is the controlled rounding/Hall-cuts
construction of the feasible count matrix, not the extraction of a symboling
from such a matrix.

The current `BaseTail.Cylinder` interface records active fibre cardinality,
ordinary direction uniqueness, color Hamiltonicity, and active degree
congruence modulo `m`.  If the direct proof needs the paper's stronger
active-block/active-degree formula, it should be introduced as internal data
inside the cylinder construction/lift proof, or by deliberately strengthening
this concrete subgoal.  It should not be hidden behind a new abstract endpoint:
the completion target remains the three displayed base-tail subgoals.

Lean now has the adapter
`oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_baseTailPieces`.
It proves `OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal` from the
three displayed subgoals above.  This is the current preferred proof split for
the base-tail geometry theorem.

Completion criterion: prove the core theorem with no forbidden proof holes; the
existing wrapper supplies `OddSuccessorSmallModulusBaseTailGeometryFromHallGoal`
and the final adapter consumes it.

## Direct-Proof Fallback

If no smaller imported theorem can be used cleanly, the remaining work should
be attacked as three direct Lean proof developments, not by adding more
abstract endpoints.

1. Prove the finite de Werra/Hoffman theorem directly, preferably as
   `ActiveHall.FiniteHoffman.RawZeroOneMatrixGoal.{0, 0}` or
   `ActiveHall.FiniteHoffman.ExactEdgeColoringGoal.{0, 0}`.  The local
   `EraseLastHallCutsTokenLinearChoiceGoal` is equivalent and useful as an
   induction interface, but ordinary one-column Hall matching alone is not
   enough because the last-symbol choice must also preserve all residual cut
   slack inequalities.

2. Prove the q>=2 signed trellis closure directly as
   `PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal`.  This is the
   finite integral signed-trellis/Rado-Edmonds content.  Avoid the known-false
   `Qge2SignedColumnPackingGoal`; the ordinary-row/proper-cut target is the
   safe theorem shape.

3. Prove the small-modulus successor geometry directly as
   `Concrete.OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal`, or the
   stronger `Concrete.OddCoreSmallModulusSlackPacketLiftAddGoal`.  This should
   contain the actual cylinder construction, residue rounding via Hall, and
   base-tail Hamilton lift.  Packet length, unique length-three count, and
   proper-prefix unit/count arithmetic are already closed and should be reused
   rather than reproved inside the geometry theorem.

## Verification Gate

Before declaring the full formalization complete, run:

```text
lake build RoundComposite
git diff --check
grep -R -n -E '\b(sorry|admit|axiom|constant)\b' \
  RoundComposite Shared TorusD3Odd D5Odd D7Odd --include='*.lean'
```

The final grep command must return no matches.
