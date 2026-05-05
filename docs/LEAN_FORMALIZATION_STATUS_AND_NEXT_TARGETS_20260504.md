# Lean Formalization Status And Next Targets

Date: 2026-05-04.

Current commit when this audit was prepared:

```text
372d499
```

Verification at this audit point:

```text
lake build RoundComposite
git diff --check
grep -R -n -E '\b(sorry|admit|axiom|constant)\b' \
  RoundComposite Shared TorusD3Odd D5Odd D7Odd --include='*.lean'
```

The build and diff check passed.  The grep command returned no matches.

This note fixes the detailed Lean status and the next formalization targets.
It is intentionally narrower than the global proof goal: it distinguishes
already closed Lean wrappers from fields that still need direct proof work.

## Current Objective

Final theorem:

```lean
theorem odd_modulus_tori_all_dimensions
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

Lean packages this as:

```lean
RoundComposite.Concrete.OddModulusToriAllDimensionsGoal
```

Preferred current endpoint:

```lean
theorem RoundComposite.Concrete
  .oddModulusToriAllDimensionsGoal_of_v4_seedProper_core_rawMatrix
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hCore : OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal)
    (hMat : ActiveHall.FiniteHoffman.RawZeroOneMatrixGoal.{0, 0}) :
    OddModulusToriAllDimensionsGoal
```

There is also a compatible-matrix-facing variant:

```lean
theorem RoundComposite.Concrete
  .oddModulusToriAllDimensionsGoal_of_v4_seedProper_core_compatibleMatrix
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hCore : OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal)
    (hMat : ActiveHall.FiniteHoffman.CompatibleZeroOneMatrixGoal.{0, 0}) :
    OddModulusToriAllDimensionsGoal
```

There is also a Hall-realization-facing variant:

```lean
theorem RoundComposite.Concrete
  .oddModulusToriAllDimensionsGoal_of_v4_seedProper_core_hall
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hCore : OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal)
    (hHall : ActiveHall.HallRealizationGoal.{0, 0}) :
    OddModulusToriAllDimensionsGoal
```

The older geometry/raw-edge and de Werra endpoints remain available as
intermediate adapters, but the core/matrix/Hall endpoints are the sharpest
current Lean handoffs because packet arithmetic and representation extraction
are already closed.

## Closed In Lean

### Dispatcher

The D2/D3/D5/D7 seed plus product plus successor dispatcher is closed:

```lean
theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_357_and_successor
    (hSucc : OddSuccessorClosureGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

Lean also exposes the packaged goal form:

```lean
theorem RoundComposite.Concrete
  .oddModulusToriAllDimensionsGoal_of_357_and_successor
    (hSucc : OddSuccessorClosureGoal) :
    OddModulusToriAllDimensionsGoal
```

### Successor Wrapper

The high/small split is closed as a wrapper:

```lean
theorem RoundComposite.Concrete
  .oddSuccessorClosureGoal_of_successorHigh_and_successorSmall
    (hHigh : OddSuccessorHighModulusPrefixCountGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddSuccessorClosureGoal
```

and pointwise:

```lean
theorem RoundComposite.Concrete
  .odd_successor_closure_of_successorHigh_and_successorSmall
    (hHigh : OddSuccessorHighModulusPrefixCountGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {b m : Nat}
    (hb5 : 5 <= b)
    (hmodd : Odd m) (hm3 : 3 <= m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m
```

The branch split is exact:

```text
m >= 2*b + 1 : OddSuccessorHighModulusPrefixCountGoal
m <  2*b + 1 : OddSuccessorSmallModulusBaseTailGoal
```

### Return-Tail Chain

The first-hit return-tail chain needed by the high branch is now closed in
Lean.  In particular:

```lean
theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal :
    PrefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal

theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnLowResidualReindexGoal :
    PrefixCountFirstHitReturnLowResidualReindexGoal

theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnTailLocalHitConditionSumGoal :
    PrefixCountFirstHitReturnTailLocalHitConditionSumGoal

theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnTailCocycleSumGoal :
    PrefixCountFirstHitReturnTailCocycleSumGoal

theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnTailCocycleUnitGoal :
    PrefixCountFirstHitReturnTailCocycleUnitGoal

theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnTailMonodromyOrbitGoal :
    PrefixCountFirstHitReturnTailMonodromyOrbitGoal
```

The generic lower-triangular odometer ingredient is also closed:

```lean
theorem Shared.zmodVectorLowerTriangularUnitCycleCoordinate :
    Shared.ZModVectorLowerTriangularUnitCycleCoordinateGoal
```

### q>=2 Wrappers Already Exposed

The false overly-general target is blocked by a Lean counterexample:

```lean
theorem PrefixCount.not_qge2SignedColumnPackingGoal :
    not Qge2SignedColumnPackingGoal
```

The correct trellis split is exposed:

```lean
theorem PrefixCount.ordinaryQge2SignedTrellisHoffmanGoal_of_fullSupport
    (hFull : OrdinaryQge2SignedFullSupportTrellisGoal)
    (hLift : OrdinaryQge2IndicatorToFullSupportGoal) :
    OrdinaryQge2SignedTrellisHoffmanGoal
```

The half-slack bridge is exposed:

```lean
theorem PrefixCount.ordinaryQge2IndicatorToFullSupportGoal_of_halfSlackBridge
    (hBridge : Qge2IndicatorCutsHalfSlackToSupportGoal)
    (hHalf : Qge2OrdinaryHalfSlackGoal) :
    OrdinaryQge2IndicatorToFullSupportGoal
```

The internal half-slack/support branch is now closed in
`RoundComposite/PrefixCountHalfSlack.lean`:

```lean
theorem PrefixCount.qge2SignedColumnSupport_indicator_le_capacity
    {n c : Nat} (hnEven : Even n) (hn4 : 4 <= n)
    (hc : c = 1 ∨ c = 2) (J : Finset (Fin n)) :
    qge2SignedColumnSupport n c
        (fun i : Fin n => if i ∈ J then (1 : Int) else 0)
      <= qge2ColumnCapacity n J.card c

theorem PrefixCount.qge2SignedSupportHalfPenaltyGoal :
    PrefixCount.Qge2SignedSupportHalfPenaltyGoal

theorem PrefixCount.qge2IndicatorCutsHalfSlackToSupportGoal :
    PrefixCount.Qge2IndicatorCutsHalfSlackToSupportGoal

theorem PrefixCount.ordinaryQge2IndicatorToFullSupportGoal_of_internalHalfSlack :
    PrefixCount.OrdinaryQge2IndicatorToFullSupportGoal

theorem PrefixCount.ordinaryQge2SignedFullSupportTrellisGoal_of_seedClosure
    (hClosure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal) :
    PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal

theorem PrefixCount.ordinaryQge2SignedTrellisHoffmanGoal_of_signedSeedClosure
    (hClosure : PrefixCount.OrdinaryQge2SignedSeedClosureGoal) :
    PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal

theorem PrefixCount.ordinaryQge2SignedTrellisHoffmanGoal_iff_signedSeedClosureGoal :
    PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal ↔
      PrefixCount.OrdinaryQge2SignedSeedClosureGoal

theorem PrefixCount.ordinaryQge2SignedTrellisHoffmanGoal_of_seedProperCutClosure
    (hClosure : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal) :
    PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal

theorem PrefixCount.ordinaryQge2SignedTrellisHoffmanGoal_iff_seedProperCutClosureGoal :
    PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal ↔
      PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal
```

So `OrdinaryQge2IndicatorToFullSupportGoal` is closed by internal Lean proof
and is no longer a remaining q>=2 target.  The full-support trellis endpoint
is also reduced to the seed-closure theorem by indicator support upper bounds.
The seed/proper-cut and trellis-Hoffman formulations are now interchangeable
adapters; the remaining mathematical content is the ordinary signed trellis
decomposition theorem itself.

### ActiveHall Wrappers Already Exposed

The copied-edge and de Werra interfaces are connected internally:

```lean
theorem ActiveHall.FiniteHoffman.rawExactEdgeColoringGoal_of_compatibleDeWerra
    (hDW : ActiveHall.FiniteHoffman.CompatibleDeWerraGoal) :
    ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal

theorem ActiveHall.FiniteHoffman.exactEdgeColoringGoal_of_raw
    (hRaw : ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal) :
    ActiveHall.FiniteHoffman.ExactEdgeColoringGoal

theorem ActiveHall.hallRealizationGoal_of_exactEdgeColoring
    (hEdge : ActiveHall.FiniteHoffman.ExactEdgeColoringGoal.{0, 0}) :
    ActiveHall.HallRealizationGoal.{0, 0}

theorem ActiveHall.FiniteHoffman.rawExactEdgeColoringGoal_of_exactEdgeColoringGoal
    (hExact : ActiveHall.FiniteHoffman.ExactEdgeColoringGoal) :
    ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal

theorem ActiveHall.FiniteHoffman.rawExactEdgeColoringGoal_iff_exactEdgeColoringGoal :
    ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal ↔
      ActiveHall.FiniteHoffman.ExactEdgeColoringGoal

theorem ActiveHall.FiniteHoffman.exactEdgeColoringGoal_of_hoffmanOrderedSDRGoal
    (hHoffman : ActiveHall.HoffmanOrderedSDRGoal) :
    ActiveHall.FiniteHoffman.ExactEdgeColoringGoal

theorem ActiveHall.FiniteHoffman.exactEdgeColoringGoal_iff_hoffmanOrderedSDRGoal :
    ActiveHall.FiniteHoffman.ExactEdgeColoringGoal ↔
      ActiveHall.HoffmanOrderedSDRGoal

theorem ActiveHall.FiniteHoffman.exactEdgeColoringGoal_of_hallRealizationGoal
    (hHall : ActiveHall.HallRealizationGoal) :
    ActiveHall.FiniteHoffman.ExactEdgeColoringGoal

theorem ActiveHall.FiniteHoffman.exactEdgeColoringGoal_iff_hallRealizationGoal :
    ActiveHall.FiniteHoffman.ExactEdgeColoringGoal ↔
      ActiveHall.HallRealizationGoal
```

The zero-one matrix extraction layer is also closed:

```lean
theorem ActiveHall.FiniteHoffman.compatibleDeWerraGoal_of_matrix
    (hMat : ActiveHall.FiniteHoffman.CompatibleZeroOneMatrixGoal) :
    ActiveHall.FiniteHoffman.CompatibleDeWerraGoal

theorem ActiveHall.FiniteHoffman.compatibleZeroOneMatrixGoal_of_compatibleDeWerraGoal
    (hDW : ActiveHall.FiniteHoffman.CompatibleDeWerraGoal) :
    ActiveHall.FiniteHoffman.CompatibleZeroOneMatrixGoal

theorem ActiveHall.FiniteHoffman.compatibleZeroOneMatrixGoal_iff_compatibleDeWerraGoal :
    ActiveHall.FiniteHoffman.CompatibleZeroOneMatrixGoal ↔
      ActiveHall.FiniteHoffman.CompatibleDeWerraGoal

theorem ActiveHall.FiniteHoffman.rawExactEdgeColoringGoal_of_matrix
    (hMat : ActiveHall.FiniteHoffman.CompatibleZeroOneMatrixGoal) :
    ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal

theorem ActiveHall.FiniteHoffman.rawExactEdgeColoringGoal_of_rawMatrix
    (hMat : ActiveHall.FiniteHoffman.RawZeroOneMatrixGoal) :
    ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal

theorem ActiveHall.FiniteHoffman.rawZeroOneMatrixGoal_of_rawExactEdgeColoringGoal
    (hRaw : ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal) :
    ActiveHall.FiniteHoffman.RawZeroOneMatrixGoal

theorem ActiveHall.FiniteHoffman.rawZeroOneMatrixGoal_iff_rawExactEdgeColoringGoal :
    ActiveHall.FiniteHoffman.RawZeroOneMatrixGoal ↔
      ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal

theorem ActiveHall.FiniteHoffman.rawExactEdgeColoringGoal_of_hallRealizationGoal
    (hHall : ActiveHall.HallRealizationGoal) :
    ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal

theorem ActiveHall.FiniteHoffman.rawZeroOneMatrixGoal_of_hallRealizationGoal
    (hHall : ActiveHall.HallRealizationGoal) :
    ActiveHall.FiniteHoffman.RawZeroOneMatrixGoal

theorem ActiveHall.FiniteHoffman.rawZeroOneMatrixGoal_iff_hallRealizationGoal :
    ActiveHall.FiniteHoffman.RawZeroOneMatrixGoal ↔
      ActiveHall.HallRealizationGoal

theorem ActiveHall.FiniteHoffman.rawZeroOneMatrixGoal_of_eraseLastHallCutsTokenLinearChoiceGoal
    (hToken : ActiveHall.EraseLastHallCutsTokenLinearChoiceGoal) :
    ActiveHall.FiniteHoffman.RawZeroOneMatrixGoal

theorem ActiveHall.FiniteHoffman.rawZeroOneMatrixGoal_iff_eraseLastHallCutsTokenLinearChoiceGoal :
    ActiveHall.FiniteHoffman.RawZeroOneMatrixGoal ↔
      ActiveHall.EraseLastHallCutsTokenLinearChoiceGoal
```

The pointwise `T <= 2` ActiveHall base cases and the `T = 3` singleton
selection adapters are also closed, including the token-load form:

```lean
ActiveHall.FiniteHoffman.rawZeroOneMatrix_zero
ActiveHall.FiniteHoffman.rawZeroOneMatrix_one
ActiveHall.FiniteHoffman.rawZeroOneMatrix_two
ActiveHall.FiniteHoffman.rawZeroOneMatrix_of_T_le_two
ActiveHall.EraseLastHallCutsTwoSingletonSelectionGoal
ActiveHall.EraseLastHallCutsTwoSingletonCutSlackSelectionGoal
ActiveHall.EraseLastHallCutsTwoSingletonTokenCutSlackSelectionGoal
ActiveHall.eraseLastHallCutsTwoSingletonCutSlackSelectionGoal_of_token
ActiveHall.hallRealization_three_of_singletonTokenCutSlackSelection
ActiveHall.hallRealization_of_T_le_three_of_singletonTokenCutSlackSelection
ActiveHall.FiniteHoffman.rawZeroOneMatrix_three_of_singletonTokenCutSlackSelection
ActiveHall.FiniteHoffman.rawZeroOneMatrix_of_T_le_three_of_singletonTokenCutSlackSelection
ActiveHall.hallRealization_succ_of_eraseLastHallCuts_and_lower_T_le_three
ActiveHall.hallRealization_four_of_eraseLastHallCuts_and_singletonTokenCutSlackSelection
ActiveHall.EraseLastHallCutsFourGoal
ActiveHall.hallRealization_four_of_eraseLastHallCutsFourGoal
ActiveHall.FiniteHoffman.rawZeroOneMatrix_four_of_eraseLastHallCutsFourGoal
ActiveHall.EraseLastHallCutsFourTokenCutSlackSelectionGoal
ActiveHall.eraseLastHallCutsFourGoal_of_tokenCutSlackSelection
ActiveHall.hallRealization_four_of_fourTokenCutSlackSelection
ActiveHall.FiniteHoffman.rawZeroOneMatrix_four_of_fourTokenCutSlackSelection
```

The base-tail cylinder layer now also proves the first structural positivity
fact needed by residue rounding: if a cylinder color is Hamiltonian and
`1 < m`, its active degree cannot be zero.

```lean
Concrete.BaseTail.Cylinder.iterate_step_activeDir_eq_of_colorDegree_zero
Concrete.BaseTail.IsCylinder.active_degree_pos
Concrete.BaseTail.IsCylinder.active_degree_dvd_modulus
Concrete.BaseTail.IsCylinder.modulus_le_active_degree
```

It also has the stronger active-block interface needed for the paper-style
controlled rounding proof.  If a cylinder construction supplies
`colorDegree c = (m - activeBlock c) * m^b` with `activeBlock c` a unit between
`0` and `m`, Lean now derives the corresponding unit, divisibility, lower
bound, and existing weak-cylinder facts:

```lean
Concrete.BaseTail.ActiveBlockData
Concrete.BaseTail.ActiveBlockData.activeBlock_isUnit
Concrete.BaseTail.ActiveBlockData.active_complement_coprime
Concrete.BaseTail.ActiveBlockData.active_complement_isUnit
Concrete.BaseTail.ActiveBlockData.active_degree_mod
Concrete.BaseTail.ActiveBlockData.active_degree_lower_bound
Concrete.BaseTail.ActiveBlockData.active_degree_upper_bound
Concrete.BaseTail.ActiveBlockData.sum_colorDegree_lower_bound
Concrete.BaseTail.ActiveBlockData.sum_active_complement_eq
Concrete.BaseTail.ActiveBlockData.sum_activeBlock_eq
Concrete.BaseTail.ActiveBlockData.isCylinder_of_activeBlockData
Concrete.BaseTail.exists_universalResidueSpec_compatible_primitive_of_activeBlockData
Concrete.BaseTail.exists_universalResidueSpec_compatible_primitive_of_successor_activeBlockData
Concrete.BaseTail.feasiblePrimitiveResidues_of_successor_activeBlockData_feasible_compatible
Concrete.BaseTail.primitiveActiveSymboling_of_successor_activeBlockData_feasible_compatible
```

The successor-small geometry core also has an explicit active-block proof
split in `RoundComposite/OddCore.lean`:

```lean
OddSuccessorBaseTailActiveBlockCylinderConstructionGoal
OddSuccessorBaseTailActiveBlockResidueRoundingGoal
OddSuccessorBaseTailActiveBlockPrimitiveLiftGoal
oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_activeBlockPieces
```

This means the remaining ActiveHall work is the finite combinatorics theorem
that supplies either `CompatibleZeroOneMatrixGoal` or the narrower
`RawZeroOneMatrixGoal`/`RawExactEdgeColoringGoal` or
`ExactEdgeColoringGoal` or `HallRealizationGoal` or
`EraseLastHallCutsTokenLinearChoiceGoal` or
`CompatibleZeroOneMatrixGoal`/`CompatibleDeWerraGoal`, not the one-hot
extraction or adapter plumbing.

## Remaining Lean Fields

For the preferred endpoint, the remaining fields are:

```lean
PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal
OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal
ActiveHall.FiniteHoffman.RawZeroOneMatrixGoal.{0, 0}
```

Equivalently, `ActiveHall.FiniteHoffman.CompatibleZeroOneMatrixGoal.{0, 0}` is
also sufficient.  `ActiveHall.HallRealizationGoal.{0, 0}` is now sufficient as
well, since it is Lean-equivalent to the raw zero-one matrix and exact
edge-colouring formulations.

The current final adapters are:

```lean
def RoundComposite.Concrete.OddModulusToriV4CompletionCoreRawMatrixGoal :
    Prop

def RoundComposite.Concrete.OddModulusToriV4CompletionCoreCompatibleMatrixGoal :
    Prop

theorem RoundComposite.Concrete
  .oddModulusToriAllDimensionsGoal_of_v4_seedProper_core_rawMatrix
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hCore : OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal)
    (hMat : ActiveHall.FiniteHoffman.RawZeroOneMatrixGoal.{0, 0}) :
    OddModulusToriAllDimensionsGoal

theorem RoundComposite.Concrete
  .oddModulusToriAllDimensionsGoal_of_v4_seedProper_core_compatibleMatrix
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hCore : OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal)
    (hMat : ActiveHall.FiniteHoffman.CompatibleZeroOneMatrixGoal.{0, 0}) :
    OddModulusToriAllDimensionsGoal

theorem RoundComposite.Concrete
  .oddModulusToriAllDimensionsGoal_of_v4_completionCoreRawMatrix
    (hCore : OddModulusToriV4CompletionCoreRawMatrixGoal) :
    OddModulusToriAllDimensionsGoal

theorem RoundComposite.Concrete
  .oddModulusToriAllDimensionsGoal_of_v4_completionCoreCompatibleMatrix
    (hCore : OddModulusToriV4CompletionCoreCompatibleMatrixGoal) :
    OddModulusToriAllDimensionsGoal
```

The older endpoint remains useful if a researcher proves a less reduced field:

```lean
OddSuccessorSmallModulusBaseTailGeometryFromHallGoal
ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal
ActiveHall.FiniteHoffman.CompatibleDeWerraGoal
ActiveHall.HallRealizationGoal
```

As a final-resort direct proof, it is also valid to prove one of the bundled
completion Props directly:

```lean
OddModulusToriV4CompletionCoreRawMatrixGoal
OddModulusToriV4CompletionCoreCompatibleMatrixGoal
OddModulusToriV4CompletionCoreHallGoal
```

This is intentionally a large theorem: it contains the q>=2 seed/proper-cut
closure, the successor-small geometry core, and the finite zero-one
edge-colouring content in one package.

Thus the only remaining q>=2 field is:

```lean
PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal
```

The full-support route remains available through:

```lean
PrefixCount.ordinaryQge2SignedFullSupportTrellisGoal_of_seedClosure
PrefixCount.ordinaryQge2IndicatorToFullSupportGoal_of_internalHalfSlack
```

but it is no longer the preferred endpoint because the closed return-tail orbit
wrapper can consume the proper-cut seed closure directly.

## Next Direct Lean Formalization Targets

The half-slack internal branch and the adapter layers are closed.  The next
direct Lean work should be one of the three theorem-content fields below.

1. q>=2 seed/proper-cut closure:

```lean
PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal
PrefixCount.OrdinaryQge2SignedMatrixGoal
```

This is the shortest high-modulus path.  The equivalent
`OrdinaryQge2SignedSeedClosureGoal` is also acceptable.  The matrix version is
the narrowest paper-facing theorem: it supplies the signed matrix for each
`OrdinaryQge2PlanData`, while the already-closed Lean estimates supply the cut
conditions.

2. finite zero-one edge-colouring theorem:

```lean
ActiveHall.FiniteHoffman.RawZeroOneMatrixGoal.{0, 0}
```

The existing raw exact copied-edge theorem is equivalent:

```lean
ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal.{0, 0}
ActiveHall.FiniteHoffman.ExactEdgeColoringGoal.{0, 0}
ActiveHall.HallRealizationGoal.{0, 0}
ActiveHall.EraseLastHallCutsTokenLinearChoiceGoal.{0, 0}
ActiveHall.EraseLastHallCutsProperTokenLinearChoiceGoal.{0, 0}
```

The compatible matrix theorem is also sufficient:

```lean
ActiveHall.FiniteHoffman.CompatibleZeroOneMatrixGoal.{0, 0}
```

The extraction from a one-hot matrix to the existing `RawExactEdgeColoringGoal`
is already proved.

3. successor-small base-tail geometry core:

```lean
OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal
OddCoreSmallModulusSlackPacketLiftAddGoal
```

This core target may assume the proper-prefix-unit packet condition directly.
`oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_core` converts the raw
successor packet hypotheses and `T = b + 1` to that condition using the already
closed packet arithmetic in `RoundComposite/BaseTailGeometry.lean`.  The
stronger `OddCoreSmallModulusSlackPacketLiftAddGoal` also suffices via
`oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_coreAdd`.

## Separate Module Targets

These should not be attempted inside the half-slack file.

### Finite Hoffman / Signed Trellis

Preferred target:

```lean
PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal
```

Recommended location:

```text
RoundComposite/FiniteHoffman/SignedTrellis.lean
```

The equivalent `OrdinaryQge2SignedSeedClosureGoal` is also sufficient.  The
full-support target remains available as an intermediate:

```lean
PrefixCount.ordinaryQge2SignedFullSupportTrellisGoal_of_seedClosure
```

Do not replace this by the false arbitrary-row
`Qge2SignedColumnPackingGoal`; the repository contains a counterexample.

### Finite Hoffman / Edge Coloring

Targets:

```lean
ActiveHall.FiniteHoffman.CompatibleZeroOneMatrixGoal
ActiveHall.FiniteHoffman.RawZeroOneMatrixGoal
ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal
ActiveHall.FiniteHoffman.ExactEdgeColoringGoal
ActiveHall.FiniteHoffman.CompatibleDeWerraGoal
```

Recommended location:

```text
RoundComposite/FiniteHoffman/EdgeColoring.lean
```

The module now proves:

```text
CompatibleZeroOneMatrixGoal -> CompatibleDeWerraGoal
CompatibleZeroOneMatrixGoal -> RawExactEdgeColoringGoal
RawZeroOneMatrixGoal -> RawExactEdgeColoringGoal
ExactEdgeColoringGoal -> RawExactEdgeColoringGoal
RawExactEdgeColoringGoal <-> ExactEdgeColoringGoal
```

The `T = 4` active-Hall branch has also been reduced one step further.  The
universal lower-symbol cut is automatic in all dimensions:

```lean
ActiveHall.CountMatrix.choiceLowHitCount_univ_le_cutSlack_image_castSucc
ActiveHall.EraseLastHallCutsProperTokenLinearChoiceGoal
ActiveHall.eraseLastHallCutsTokenLinearChoiceGoal_of_proper
ActiveHall.hallRealizationGoal_of_eraseLastHallCutsProperTokenLinearChoice
ActiveHall.hallRealizationGoal_iff_eraseLastHallCutsProperTokenLinearChoiceGoal
ActiveHall.FiniteHoffman.rawZeroOneMatrixGoal_of_eraseLastHallCutsProperTokenLinearChoiceGoal
ActiveHall.FiniteHoffman.rawZeroOneMatrixGoal_iff_eraseLastHallCutsProperTokenLinearChoiceGoal
```

Thus the general erase theorem may be targeted with only nonempty proper symbol
cuts `S ≠ Finset.univ`.  The four-symbol selection theorem can now be targeted
through:

```lean
ActiveHall.EraseLastHallCutsFourSmallTokenCutSlackSelectionGoal
ActiveHall.EraseLastHallCutsFourSingletonPairTokenCutSlackSelectionGoal
ActiveHall.eraseLastHallCutsFourSmallTokenCutSlackSelectionGoal_of_singletonPair
ActiveHall.eraseLastHallCutsFourTokenCutSlackSelectionGoal_of_small
ActiveHall.hallRealization_four_of_fourSmallTokenCutSlackSelection
ActiveHall.hallRealization_four_of_fourSingletonPairTokenCutSlackSelection
ActiveHall.FiniteHoffman.rawZeroOneMatrix_four_of_fourSmallTokenCutSlackSelection
ActiveHall.FiniteHoffman.rawZeroOneMatrix_four_of_fourSingletonPairTokenCutSlackSelection
```

Thus, for the `T = 4` erase step, the remaining token-selection proof only
needs nonempty proper symbol cuts with `S.card ≤ 2`; the case
`S = Finset.univ : Finset (Fin 3)` no longer has to be supplied by the
external theorem.  The `SmallToken` goal is now also split into explicit
singleton and pair symbol cuts, so the remaining proof can target only
`S = {σ}` and `S = {σ, τ}` with `σ ≠ τ`.

Any one of the theorem-content endpoints is enough if adapters are used:

```text
CompatibleDeWerraGoal -> RawExactEdgeColoringGoal -> ExactEdgeColoringGoal
ExactEdgeColoringGoal -> RawExactEdgeColoringGoal
```

### Successor Small Geometry

Target:

```lean
OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal
```

Recommended timing: after the finite Hall/edge-coloring API is stable.  This
is project-specific geometry glue rather than a standard finite-combinatorics
theorem.

The successor packet arithmetic sublayer is now closed independently in
`RoundComposite/BaseTailGeometry.lean`:

```lean
theorem Concrete.BaseTail.successorPacketLengthTwoOrThreeGoal :
    Concrete.BaseTail.SuccessorPacketLengthTwoOrThreeGoal

theorem Concrete.BaseTail.successorPacketProperPrefixUnitsGoal :
    Concrete.BaseTail.SuccessorPacketProperPrefixUnitsGoal
```

These prove that under the raw successor hypotheses `T = b + 1`, every packet
has length `2` or `3`, and every nonempty proper packet prefix has sum coprime
to `m`.  The remaining successor-small work is the geometric cylinder,
residue-rounding/Hall, and base-tail lift construction.

`RoundComposite/OddCore.lean` now exposes the reduced core target:

```lean
def OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal : Prop := ...

theorem oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_core
    (hCore : OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal) :
    OddSuccessorSmallModulusBaseTailGeometryFromHallGoal
```

So the remaining geometry theorem may assume the proper-prefix-unit condition
directly; the raw packet hypotheses are converted to that condition internally.

## Current Fixed Attempt Order

1. Completed: `RoundComposite/PrefixCountHalfSlack.lean`
   - `Qge2OrdinaryHalfSlackGoal`
   - level-set decomposition helpers
   - signed support half-penalty bound
   - `Qge2IndicatorCutsHalfSlackToSupportGoal`
   - wrapper to `OrdinaryQge2IndicatorToFullSupportGoal`

2. `RoundComposite/FiniteHoffman/SignedTrellis.lean`
   - `OrdinaryQge2SignedSeedProperCutClosureGoal`

3. `RoundComposite/FiniteHoffman/EdgeColoring.lean`
   - `RawZeroOneMatrixGoal.{0,0}` or `CompatibleZeroOneMatrixGoal.{0,0}`

4. Successor-small geometry glue
   - `OddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal`

Item 1 is complete.  The next q>=2 direct Lean target is item 2.

### Progress On Item 1

```lean
import RoundComposite.PrefixCountHalfSlack
```

has been added to `RoundComposite.lean`, and the new module
`RoundComposite/PrefixCountHalfSlack.lean` Lean-closes:

```lean
PrefixCount.exists_nat_shift_of_int_weight
PrefixCount.nat_eq_sum_upper_indicators
PrefixCount.int_weight_dot_eq_nat_upperLevels
PrefixCount.qge2OrdinaryHalfSlackGoal
PrefixCount.qge2SignedSupportHalfPenaltyGoal
PrefixCount.qge2IndicatorCutsHalfSlackToSupportGoal_of_signedSupportHalfPenalty
PrefixCount.qge2IndicatorCutsHalfSlackToSupportGoal
PrefixCount.ordinaryQge2IndicatorToFullSupportGoal_of_signedSupportHalfPenalty
PrefixCount.ordinaryQge2IndicatorToFullSupportGoal_of_internalHalfSlack
```

The sorted signed-column pattern proof is now internal.  It uses `Tuple.sort`
to arrange `u : Fin n -> Nat` in descending order, proves that upper level sets
are sorted prefixes, and feeds the explicit signed pattern columns to
`qge2SignedColumnSupport_ge_of_intColumn`.  The key closed-form bounds are:

```lean
PrefixCount.qge2SignedPatternPrefixOne_capacity
PrefixCount.qge2SignedPatternPrefixTwo_capacity_sub_half
```

The remaining q>=2 proof work is no longer the indicator/full-support bridge;
it is the separate seed/proper-cut closure theorem:

```lean
PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal
```

## Verification Gate

For any future Lean proof change, run:

```bash
lake build RoundComposite
git diff --check
grep -R -n -E '\b(sorry|admit|axiom|constant)\b' \
  RoundComposite Shared TorusD3Odd D5Odd D7Odd --include='*.lean'
```

Current unrelated dirty files to ignore unless explicitly requested:

```text
lake-manifest.json
scripts/d5_odd_paper_verify.py
Torus-Hamilton-Decomposition/
odd_tori_gpt55_pro_oneshot_bundle_20260504.tar.gz is ignored
```
