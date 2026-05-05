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

This adapter is still useful as a map of the old Lean plumbing, but the latest
finite counterexamples show that its raw matrix input cannot remain the
mathematical target in this unrestricted form.  The completion goal therefore
has to be restated before the final wrapper can be closed.

Former package:

```lean
RoundComposite.Concrete.OddModulusToriV4CompletionCoreRawMatrixGoal
```

or equivalently its three fields:

```lean
PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal
OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal
ActiveHall.FiniteHoffman.RawZeroOneMatrixGoal.{0, 0}
```

The compatible-matrix or Hall-realization variants were formerly treated as
equally sufficient:

```lean
ActiveHall.FiniteHoffman.CompatibleZeroOneMatrixGoal.{0, 0}
ActiveHall.HallRealizationGoal.{0, 0}
```

The current v7.5 replacement route is the direct small-modulus modular-trade
surface.  It bypasses the false unrestricted ActiveHall/de Werra theorem and
the older controlled count-matrix rounding route.  The live successor branch is
active residue trade scheduling, a finite coactive-site reservoir, and a
lower-triangular base-tail lift:

```lean
BaseTail.Trades.activeBlockResidueSpec
BaseTail.Trades.activeBlockResidueScheduleGoal
BaseTail.Trades.SuccessorActiveBlockCanonicalLocalSymbolTradeGoal
BaseTail.Trades.SuccessorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal
BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal
BaseTail.PrimitiveActivePrefixLiftAssemblyGoal
BaseTail.PrimitiveActivePrefixLowerTriangularLiftAssemblyGoal
BaseTail.ExpandedColorDirLowerTriangularMonodromyDataOfCountsPrimitiveGoal
BaseTail.CylinderBaseCycleData
BaseTail.cylinderBaseCycleData_of_isCylinder
BaseTail.ExpandedColorDirFiberLowerTriangularMonodromyGoal
BaseTail.primitiveActivePrefixLiftAssemblyGoal_of_expandedMonodromy
Concrete.OddSuccessorSmallModulusBaseTailGeometryFromModularTradesGoal
Concrete.OddSuccessorBaseTailWorker1CanonicalLocalTradeResidualGoal
Concrete.OddSuccessorBaseTailWorker1CanonicalLocalTradeLowerTriangularResidualGoal
Concrete.OddSuccessorBaseTailWorker1CanonicalFeasibleLocalTradeLowerTriangularResidualGoal
Concrete.OddSuccessorBaseTailWorker1CanonicalLocalTradeExpandedMonodromyResidualGoal
Concrete.OddSuccessorBaseTailWorker1CanonicalLocalTradeFiberMonodromyResidualGoal
Concrete.OddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeBlocksGoal
Concrete.OddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeLowerTriangularBlocksGoal
Concrete.OddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalFeasibleLocalTradeLowerTriangularBlocksGoal
Concrete.OddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeExpandedMonodromyBlocksGoal
Concrete.OddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeFiberMonodromyBlocksGoal
Concrete.oddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeBlocksGoal_of_lowerTriangularBlocks
Concrete.oddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeLowerTriangularBlocksGoal_of_feasibleLocalTradeLowerTriangularBlocks
Concrete.oddModulusToriAllDimensionsGoal_of_v73_returnTailClosedFullSupportTrellisCanonicalLocalTrade_blocks
Concrete.oddModulusToriAllDimensionsGoal_of_v73_returnTailClosedFullSupportTrellisCanonicalFeasibleLocalTradeLowerTriangular_blocks
Concrete.oddModulusToriAllDimensionsGoal_of_v73_returnTailClosedFullSupportTrellisCanonicalLocalTradeExpandedMonodromy_blocks
```

The planned top-level import for this paper-facing route is:

```lean
import RoundComposite.V75Endpoints
```

That file exposes the v7.5 theorem surfaces:

```lean
Concrete.OddModulusToriV75DirectModularTradeInputsGoal
Concrete.OddModulusToriV75DirectModularTradeBlocksGoal
Concrete.OddModulusToriV75GeneralLocalTradeInputsGoal
Concrete.oddModulusToriV75DirectModularTradeBlocksGoal_of_inputs
Concrete.oddModulusToriV75DirectModularTradeBlocksGoal_of_localTrade_lowerTriangular
Concrete.oddModulusToriV75DirectModularTradeBlocksGoal_of_generalInputs
Concrete.oddSuccessorClosureGoal_of_v75_directModularTrade_blocks
Concrete.odd_modulus_tori_all_dimensions_of_v75_directModularTrade_blocks
Concrete.oddModulusToriAllDimensionsGoal_of_v75_directModularTrade_blocks
Concrete.oddModulusToriAllDimensionsGoal_of_v75_directModularTrade_inputs
```

The implementation goal and success criteria are recorded in:

```text
docs/ODD_TORI_V75_DIRECT_MODULAR_TRADE_GOAL_20260505.md
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

The ActiveHall extraction/adapters are already in place as plumbing.  They must
now be treated carefully: the unrestricted matrix, exact edge-colouring, and
Hall-realization theorem shapes are refuted by finite counterexamples unless
additional successor-specific hypotheses are added.

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

## Target 2: Successor-Specific Modular Trade Realization

Current preferred theorem package:

```lean
BaseTail.Trades.SuccessorActiveBlockCanonicalLocalSymbolTradeGoal
BaseTail.PrimitiveActivePrefixLiftAssemblyGoal
BaseTail.PrimitiveActivePrefixLowerTriangularLiftAssemblyGoal
```

The paper-facing reservoir name for the first item is:

```lean
BaseTail.Trades.SuccessorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal
BaseTail.Trades.successorActiveBlockCanonicalLocalSymbolTradeGoal_of_finiteCoactiveSiteReservoir
```

The broader `BaseTail.Trades.SuccessorActiveBlockLocalSymbolTradeGoal` is still
a sufficient optional fallback, but the current proof surface only asks for the
canonical schedule selected by `BaseTail.Trades.activeBlockResidueSpec`.
Lean records this fallback explicitly via
`BaseTail.Trades.successorActiveBlockCanonicalLocalSymbolTradeGoal_of_successorLocalTrade`.
The same fallback is also wired into the sharper lower-triangular residual:

```lean
Concrete.oddSuccessorBaseTailWorker1CanonicalLocalTradeLowerTriangularResidualGoal_of_successorLocalTrade_lowerTriangular
Concrete.oddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeLowerTriangularBlocksGoal_of_successorLocalTrade_lowerTriangular
```

There is also a weaker feasibility split point:

```lean
BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleResidueGoal
BaseTail.Trades.successorActiveBlockCanonicalLocalSymbolTradeGoal_of_feasible_and_localTrade
BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal
BaseTail.Trades.successorActiveBlockCanonicalLocalSymbolTradeGoal_of_feasible_and_feasibleLocalTrade
```

`SuccessorActiveBlockCanonicalFeasibleResidueGoal` alone only supplies a count
matrix.  Paired with the successor-scoped feasible-to-symboling bridge
`SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal`, it closes the
canonical local-trade endpoint without invoking the known-false unrestricted
Hall-realization layer.

The active-block residue scheduler itself is now closed in Lean:

```lean
BaseTail.Trades.activeBlockResidueSpec
BaseTail.Trades.activeBlockResidueScheduleGoal
BaseTail.Trades.successorActiveBlockResidueScheduleGoal
```

Equivalently, Worker 2 may prove the already packaged residual:

```lean
Concrete.OddSuccessorBaseTailWorker1CanonicalLocalTradeResidualGoal
Concrete.OddSuccessorBaseTailWorker1CanonicalLocalTradeLowerTriangularResidualGoal
Concrete.OddSuccessorBaseTailWorker1CanonicalFeasibleLocalTradeLowerTriangularResidualGoal
Concrete.OddSuccessorBaseTailWorker1CanonicalLocalTradeExpandedMonodromyResidualGoal
Concrete.OddSuccessorBaseTailWorker1CanonicalLocalTradeFiberMonodromyResidualGoal
```

This is sufficient for the final all-dimensional route through:

```lean
Concrete.OddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeBlocksGoal
Concrete.OddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeLowerTriangularBlocksGoal
Concrete.OddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalFeasibleLocalTradeLowerTriangularBlocksGoal
Concrete.oddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeBlocksGoal_of_lowerTriangularBlocks
Concrete.oddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeLowerTriangularBlocksGoal_of_feasibleLocalTradeLowerTriangularBlocks
Concrete.OddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeExpandedMonodromyBlocksGoal
Concrete.OddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeFiberMonodromyBlocksGoal
Concrete.oddModulusToriAllDimensionsGoal_of_v73_returnTailClosedFullSupportTrellisCanonicalLocalTrade_blocks
Concrete.oddModulusToriAllDimensionsGoal_of_v73_returnTailClosedFullSupportTrellisCanonicalFeasibleLocalTradeLowerTriangular_blocks
Concrete.oddModulusToriAllDimensionsGoal_of_v73_returnTailClosedFullSupportTrellisCanonicalLocalTradeExpandedMonodromy_blocks
```

The remaining hard mathematical endpoint in the trade layer is the
canonical successor-scoped local-symbol trade theorem.  It must be proved for
the actual base-tail cylinder incidence data and canonical residue schedule;
it should not be replaced by the
unrestricted finite Hall theorem below.

Paper-to-Lean correspondence for the v7.5 modular-trade branch:

```text
lem:trade-reservoir
  -> BaseTail.Trades.SuccessorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal
     and the missing finite reservoir/coactive-site proof for the actual cylinder

thm:active-residue-scheduling
  -> BaseTail.Trades.SuccessorActiveBlockLocalSymbolTradeGoal

thm:active-realization
  -> BaseTail.Trades.SuccessorActiveBlockCanonicalLocalSymbolTradeGoal
     plus BaseTail.Trades.activeBlockResidueSpec

thm:base-tail-lift
  -> BaseTail.PrimitiveActivePrefixLiftAssemblyGoal
     via BaseTail.PrimitiveActivePrefixLowerTriangularLiftAssemblyGoal
```

The sharpest current Lean target for the prefix lift is the generic
lower-triangular projected-lift endpoint:

```lean
BaseTail.PrimitiveActivePrefixLowerTriangularLiftAssemblyGoal
Concrete.OddSuccessorBaseTailWorker1CanonicalLocalTradeLowerTriangularResidualGoal
Concrete.OddSuccessorBaseTailWorker1CanonicalFeasibleLocalTradeLowerTriangularResidualGoal
Concrete.OddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeLowerTriangularBlocksGoal
Concrete.OddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalFeasibleLocalTradeLowerTriangularBlocksGoal
Concrete.oddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeBlocksGoal_of_lowerTriangularBlocks
Concrete.oddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeLowerTriangularBlocksGoal_of_feasibleLocalTradeLowerTriangularBlocks
```

Existing adapters already prove:

```lean
BaseTail.PrimitiveActivePrefixLowerTriangularLiftAssemblyGoal
  -> BaseTail.PrimitiveActivePrefixProjectedLiftAssemblyGoal
  -> BaseTail.PrimitiveActivePrefixLiftAssemblyGoal
```

Thus the remaining prefix-lift content is to construct the
lower-triangular/unit projected lift from the active symboling count data.
The compressed base-cycle part needed by such a construction is now closed:

```lean
BaseTail.CylinderBaseCycleData
BaseTail.cylinderBaseCycleData_of_isCylinder
```

`CylinderBaseCycleData` fixes `period c = m ^ (b + 1)`, so the remaining
prefix theorem can work over one compressed base cycle, not an arbitrary
multiple of that cycle.

The following expanded-color-direction monodromy surfaces are still present as
diagnostic adapters, but they should not be treated as the primary remaining
proof boundary.  The `expandedColorDir` return data depends only on the
collapsed base direction, so this route appears too weak for the final
primitive fiber lift unless an additional nontrivial fiber-return theorem is
supplied:

```lean
BaseTail.ExpandedColorDirLowerTriangularMonodromyDataOfCountsPrimitiveGoal
BaseTail.ExpandedColorDirFiberLowerTriangularMonodromyGoal
BaseTail.PrimitiveActivePrefixExpandedLowerTriangularMonodromyGoal
BaseTail.ExpandedColorDirFiberLowerTriangularMonodromyGoal
  -> BaseTail.PrimitiveActivePrefixExpandedLowerTriangularMonodromyGoal
BaseTail.PrimitiveActivePrefixExpandedLowerTriangularMonodromyGoal
  -> BaseTail.primitiveActivePrefixLiftAssemblyGoal_of_expandedMonodromy
  -> BaseTail.PrimitiveActivePrefixLowerTriangularLiftAssemblyGoal
```

Legacy target, no longer current:

Former preferred theorem:

```lean
ActiveHall.FiniteHoffman.RawZeroOneMatrixGoal.{0, 0}
```

Former equivalent targets:

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

Latest update: the general theorem shape above is false.  It should not be
pursued as a proof target without new hypotheses.

Two obstructions have been found.

1. The two-sided compatible de Werra form with allowed left and right sets
   satisfies all stated degree and rectangle-cut hypotheses on a `3 x 3` finite
   graph, but no compatible colouring exists.  A forced edge of colour `β`
   leaves colour `β` needing a missing edge.

2. The one-sided raw zero-one/Hall-realization form is also false.  In a
   `|R| = 3`, `|C| = 6`, `|X| = 5` instance, all row sums, column sums, and Hall
   rectangle cuts hold, but the support pattern forces `x1`, `x2`, and `x4` to
   use three copies of one cell `(c2,r3)` even though the matrix has only two.

The existing Lean adapters still describe how a valid active symboling theorem
would feed the rest of the code, but they do not supply the missing
mathematical content.  The legacy ActiveHall branch can only be revived by one
of:

```text
1. formalize the counterexamples and remove the false general endpoint from
   the final completion route; or
2. replace the finite theorem by a successor-specific active symboling theorem
   whose extra structural hypotheses rule out forced-cell capacity
   obstructions.
```

The intended successor-specific theorem should cover only the incidence/count
matrices produced by the base-tail construction and residue-compatible
rounding.  In that restricted setting it must still realize the full count
matrix, not just a one-column Hall matching.

The historical induction interface remains explicit: if a corrected
last-symbol erase choice is supplied under successor-specific hypotheses, the
`T = 4` case reduces to the already closed `T <= 3` pipeline based on singleton
token cut-slack selection.

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

Historical note: the proper-token target was a reduction of the general erase
step under the now-questioned ActiveHall theorem shape:
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
`CountMatrix.cutSlack_image_castSucc`.  Thus a proof of the quota target was
intended to feed the full `RawZeroOneMatrixGoal` route.  In light of the
counterexamples, this should be treated as an adapter/equivalence note, not as
evidence that the unrestricted theorem is true.

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

Direct proof fallback: prove a corrected successor-specific active symboling
theorem and wrap it into the small-modulus base-tail route.  Do not try to prove
`RawZeroOneMatrixGoal.{0,0}` or `HallRealizationGoal.{0,0}` as currently stated.
Ordinary one-column Hall matching is not enough by itself, because the
last-symbol choice must preserve all residual Hall cut inequalities and avoid
forced-cell capacity obstructions.

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
MixedExpansionData.mixed_lower
MixedExpansionData.slack_error_le_mixedCount_mul_proper_min
MixedExpansionData.hallCuts_of_scaled_error_le_slack
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

The active-block degree data alone does not imply the required `mixedCount`
lower bound.  The cylinder-construction side should therefore also expose
`MixedExpansionData`, whose core field is

```lean
m ^ b ≤ (Cyl.incidence).mixedCount U
```

for every nonempty proper color cut `U`.  The lemma
`MixedExpansionData.slack_error_le_mixedCount_mul_proper_min` converts this
mixed expansion plus `m ^ b > m * (b + T) * T` into the mixed slack margin
needed by the scaled-barycenter Hall proof.  The bridge theorem
`MixedExpansionData.hallCuts_of_scaled_error_le_slack` then turns the explicit
controlled-error estimate

```lean
T * M.cutMass U S
  ≤ S.card * (∑ c ∈ U, (Cyl.incidence).colorDegree c)
      + m * (b + T) * min S.card (T - S.card)
```

on nontrivial cuts into `M.HallCuts`.

Therefore the base-tail proof should expose this data deliberately, either by
strengthening the cylinder-construction subgoal with an internal
`BlockCylinder`/`StrongCylinder` predicate or by proving the active-block
formula as part of `OddSuccessorBaseTailCylinderConstructionGoal` and carrying
it into rounding and lift.  It should not be hidden behind another opaque
abstract endpoint.

`RoundComposite/OddCore.lean` now records this stronger split explicitly:

```lean
OddSuccessorBaseTailActiveBlockCylinderConstructionGoal
OddSuccessorBaseTailActiveBlockMixedCylinderConstructionGoal
OddSuccessorBaseTailActiveBlockResidueRoundingGoal
OddSuccessorBaseTailActiveBlockCompatibleResidueRoundingGoal
OddSuccessorBaseTailActiveBlockMixedCompatibleResidueRoundingGoal
OddSuccessorBaseTailActiveBlockMixedControlledResidueRoundingGoal
OddSuccessorBaseTailActiveBlockPrimitiveLiftGoal
oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_activeBlockPieces
oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_activeBlockCompatiblePieces
oddSuccessorBaseTailActiveBlockMixedCompatibleResidueRoundingGoal_of_controlled
oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_activeBlockMixedCompatiblePieces
```

The practical target decomposition is:

1. Cylinder construction with active-block and mixed-expansion data:
   construct the base-tail cylinder from `StandardCayleySolved b m` and packet
   data, prove the active-degree formula above, and prove
   `m ^ b ≤ mixedCount U` for every nonempty proper color cut `U`.
2. Controlled residue rounding:
   use the active-degree formula, mixed expansion, and
   `m ^ b > m * (b + T) * T` to prove the sharper compatible-residue theorem:

   ```lean
   OddSuccessorBaseTailActiveBlockMixedControlledResidueRoundingGoal
   ```

   This is the precise construction target: for every row/column compatible
   primitive residue specification, build a nonnegative count matrix with the
   requested residues and the explicit scaled-error bound above.  Lean now
   proves

   ```lean
   oddSuccessorBaseTailActiveBlockMixedCompatibleResidueRoundingGoal_of_controlled
   oddSuccessorBaseTailActiveBlockResidueRoundingGoal_of_compatible
   ```

   so this controlled theorem supplies the mixed compatible theorem, then
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

The old active proof goal was:

```text
Prove OddModulusToriV4CompletionCoreRawMatrixGoal, hence for all d >= 2 and
odd m >= 3 construct Shared.CayleyHamiltonDecomposition d m.

Concretely it asked to close:
  1. PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal.
  2. ActiveHall.FiniteHoffman.RawZeroOneMatrixGoal.{0,0}
     or an equivalent Hall/de Werra theorem.
  3. Concrete.OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal,
     with the base-tail proof allowed to introduce a stronger active-block
     cylinder interface carrying colorDegree c = (m - activeBlock c) * m^b.
```

Latest status correction: item 2 is not a valid target as stated.  The active
Goal 2 proof goal is now:

```text
Prove the small-modulus successor theorem:

  for b >= 5, odd m >= 3, and m < 2b + 1,
  StandardCayleySolved b m
  => StandardCayleySolved (2b + 1) m.

The proof must use:
  1. base-tail cylinder construction from the b-dimensional decomposition;
  2. successor-specific residue-compatible active symboling, not the false
     unrestricted RawZeroOneMatrixGoal;
  3. primitive lower-triangular tail lift.
```

## Direct-Proof Fallback Policy

Large direct proofs are acceptable, but only when they close a corrected
interface consumed by the final endpoint.  A direct proof should not introduce
another opaque theorem unless it is immediately wrapped into the replacement
successor route.

### Direct q >= 2 Target

The direct target is:

```lean
PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal
```

This may be proved by a finite signed-trellis theorem, a Rado-Edmonds
extraction, or a specialized integral flow argument.  The proof must preserve
the ordinary-row hypotheses and the proper-cut reduction; it must not assert
the false arbitrary-row signed packing theorem.

### Direct Successor Modular-Trade Target

The current direct targets are:

```lean
BaseTail.Trades.SuccessorActiveBlockCanonicalLocalSymbolTradeGoal
BaseTail.Trades.SuccessorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal
BaseTail.PrimitiveActivePrefixLiftAssemblyGoal
BaseTail.PrimitiveActivePrefixLowerTriangularLiftAssemblyGoal
```

Together with the already isolated geometry and lift interfaces, these imply:

```lean
Concrete.OddSuccessorBaseTailWorker1CanonicalLocalTradeResidualGoal
Concrete.OddSuccessorBaseTailWorker1CanonicalLocalTradeLowerTriangularResidualGoal
Concrete.OddSuccessorSmallModulusBaseTailGeometryFromModularTradesGoal
```

The former direct targets were:

```lean
ActiveHall.FiniteHoffman.RawZeroOneMatrixGoal.{0, 0}
ActiveHall.HallRealizationGoal.{0, 0}
```

These targets are no longer acceptable as currently stated.  The direct theorem
must be a corrected successor-specific active symboling theorem, or a formal
counterexample record followed by a replacement of the final completion route.
The important constraint remains that the result must realize the whole count
matrix under the successor structure; a single ordinary matching lemma is not
sufficient unless it also proves preservation of all residual cuts and cell
capacities.

### Direct Base-Tail Geometry Target

The direct target is now:

```lean
Concrete.OddSuccessorSmallModulusBaseTailGeometryCoreModularTradeGoal
```

The older Hall-shaped core target remains useful only as a legacy adapter:

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
