# Odd-Modulus Tori Current Goal v3.4

Date: 2026-05-04.

This supersedes `docs/ODD_TORI_CURRENT_GOAL_V3_3_20260504.md` as the clean
three-layer closure goal.  The final theorem is still:

```lean
theorem odd_modulus_tori_all_dimensions
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

Lean packages this as:

```lean
def RoundComposite.Concrete.OddModulusToriAllDimensionsGoal : Prop :=
  forall {d m : Nat}, 2 <= d -> Odd m -> 3 <= m ->
    Shared.CayleyHamiltonDecomposition d m
```

## 1. Closure Dispatcher

The first deliverable is already Lean-closed in
`RoundComposite/ConcreteEndpoints.lean`.

```lean
def RoundComposite.Concrete.OddSuccessorClosureGoal : Prop :=
  forall {b m : Nat},
    5 <= b ->
    Odd m -> 3 <= m ->
    StandardCayleySolved b m ->
    StandardCayleySolved (2 * b + 1) m

theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_357_and_successor
    (hSucc : OddSuccessorClosureGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

The dispatcher uses only:

```text
D2, D3, D5, D7 seeds
+ product closure
+ successor closure b -> 2*b + 1
```

It also handles `d = 9` as `3 * 3`, and all even dimensions by repeated
factorization through the D2 seed and product closure.

## 2. Successor Closure

The second deliverable is the successor theorem:

```lean
theorem odd_successor_closure
    {b m : Nat}
    (hb5 : 5 <= b)
    (hmodd : Odd m) (hm3 : 3 <= m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2*b + 1) m
```

Lean currently exposes this as a conditional closure goal:

```lean
def RoundComposite.Concrete.OddSuccessorClosureGoal : Prop := ...
```

and closes it from the high/small split:

```lean
theorem RoundComposite.Concrete
  .oddSuccessorClosureGoal_of_successorHigh_and_successorSmall
    (hHigh : OddSuccessorHighModulusPrefixCountGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddSuccessorClosureGoal
```

The intended branch split is:

```text
m >= 2*b + 1 : successor-high prefix-count branch
m <  2*b + 1 : successor-small base-tail Hall-slack branch with T = b + 1
```

## 3. Construction Blocks

The successor closure is reduced to two construction blocks.

### 3.1 High Modulus

```lean
def RoundComposite.Concrete.OddSuccessorHighModulusPrefixCountGoal : Prop :=
  forall {b m : Nat},
    5 <= b -> Odd m -> 2 * b + 1 <= m ->
      StandardCayleySolved (2 * b + 1) m
```

This is weaker than the older all-high-dimension branch because it asks only
for the successor output dimension.  Lean closes it from the currently
preferred prefix-count field plus the now-internal first-hit return-tail
theorem:

```lean
PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal
```

After the q>=2 proof-request response, Lean also exposes the smaller
full-support finite-Hoffman interface behind the ordinary trellis field:

```lean
def PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal : Prop := ...

def PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal : Prop := ...
def PrefixCount.OrdinaryQge2IndicatorToFullSupportGoal : Prop := ...

theorem PrefixCount
  .ordinaryQge2SignedTrellisHoffmanGoal_of_fullSupport
    (hFull : OrdinaryQge2SignedFullSupportTrellisGoal)
    (hLift : OrdinaryQge2IndicatorToFullSupportGoal) :
    OrdinaryQge2SignedTrellisHoffmanGoal

theorem PrefixCount
  .ordinaryQge2SignedSeedProperCutClosureGoal_of_signedTrellisHoffman
    (hHoffman : OrdinaryQge2SignedTrellisHoffmanGoal) :
    OrdinaryQge2SignedSeedProperCutClosureGoal
```

Equivalent stronger routes are still available through return-tail rank,
rank-equivalence, or cycle-coordinate goals.  They are no longer needed for the
current endpoint: Lean now closes the one-step hit-condition locality field,
the residual reindexing field, the exact signed cocycle-sum field, and the
unit-carry refinement internally:

```lean
def PrefixCountFirstHitReturnTailTriangularGoal : Prop := ...
def PrefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal : Prop := ...
def PrefixCountFirstHitReturnTailIncrementDependsOnTakeGoal : Prop := ...
def PrefixCountFirstHitReturnTailCocycleUnitGoal : Prop := ...
def PrefixCountFirstHitReturnTailCocycleSumGoal : Prop := ...
def PrefixCountFirstHitReturnLowResidualReindexGoal : Prop := ...

def PrefixCountFirstHitReturnTailTriangularCocycleBlocksGoal : Prop :=
  PrefixCountFirstHitReturnTailTriangularGoal ∧
  PrefixCountFirstHitReturnTailCocycleUnitGoal

def PrefixCountFirstHitReturnTailIncrementUnitBlocksGoal : Prop :=
  PrefixCountFirstHitReturnTailIncrementDependsOnTakeGoal ∧
  PrefixCountFirstHitReturnTailCocycleUnitGoal

def PrefixCountFirstHitReturnFiberHitConditionUnitBlocksGoal : Prop :=
  PrefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal ∧
  PrefixCountFirstHitReturnTailCocycleUnitGoal

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
  .prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_triangularCocycleBlocks
    (hBlocks : PrefixCountFirstHitReturnTailTriangularCocycleBlocksGoal) :
    PrefixCountFirstHitReturnTailMonodromyOrbitGoal

theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_incrementUnitBlocks
    (hBlocks : PrefixCountFirstHitReturnTailIncrementUnitBlocksGoal) :
    PrefixCountFirstHitReturnTailMonodromyOrbitGoal

theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_hitConditionUnitBlocks
    (hBlocks : PrefixCountFirstHitReturnFiberHitConditionUnitBlocksGoal) :
    PrefixCountFirstHitReturnTailMonodromyOrbitGoal
```

The shared theorem is:

```lean
theorem Shared.zmodVectorLowerTriangularUnitCycleCoordinate :
    Shared.ZModVectorLowerTriangularUnitCycleCoordinateGoal
```

Lean converts its rank-equivalence witness to `Shared.CycleCoordinate` inside
the wrapper.

The one-coordinate and skew-product unit-carry pieces for this route are now
closed in `Shared`:

```lean
Shared.zmod_add_single_cycle_of_unit
Shared.CycleCoordinate.zmodAddConstOfUnit
Shared.sectionReturn_skewProductMap_zmod_add_cycleCoordinate_of_unit
Shared.cycleCoordinate_of_skewProduct_zmod_additive_unit_carry
Shared.zmodVectorSnocEquiv
Shared.zmodVectorTake_snoc
Shared.zmodVectorTake_snoc_self
Shared.ZModVectorIncrementDependsOnTake
Shared.zmodVectorIncrementDependsOnTake_skewFiberIterate
Shared.zmod_rank_iterate_period
Shared.zmod_rank_orbit_cover_lt
Shared.skewFiberAdditiveCarry_eq_univ_sum_of_rank_step
Shared.single_cycle_of_skewProduct_zmod_additive_carry_of_rank_unit_sum
Shared.cycleCoordinate_of_skewProduct_zmod_additive_carry_of_rank_unit_sum
```

The closed generic lower-triangular proof note is recorded in
`docs/ZMOD_LOWER_TRIANGULAR_UNIT_PROOF_PLAN_20260504.md`.

### 3.2 Small Modulus

```lean
def RoundComposite.Concrete.OddSuccessorSmallModulusBaseTailGoal : Prop :=
  forall {b m : Nat},
    5 <= b ->
    Odd m -> 3 <= m ->
    m < 2 * b + 1 ->
    StandardCayleySolved b m ->
    StandardCayleySolved (2 * b + 1) m
```

The additive packet route is a sufficient sharper target:

```lean
def RoundComposite.Concrete
  .OddSuccessorSmallModulusSlackPacketLiftAddGoal : Prop := ...

theorem RoundComposite.Concrete
  .oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd
    (hSmallPacket : OddSuccessorSmallModulusSlackPacketLiftAddGoal) :
    OddSuccessorSmallModulusBaseTailGoal
```

Lean also exposes a geometry/combinatorics split for this small branch:

```lean
def RoundComposite.Concrete
  .OddSuccessorSmallModulusBaseTailGeometryFromHallGoal : Prop :=
  ActiveHall.HallRealizationGoal ->
    OddSuccessorSmallModulusSlackPacketLiftAddGoal

theorem RoundComposite.Concrete
  .oddSuccessorSmallModulusBaseTailGoal_of_baseTailGeometryFromHall
    (hGeom : OddSuccessorSmallModulusBaseTailGeometryFromHallGoal)
    (hHall : ActiveHall.HallRealizationGoal) :
    OddSuccessorSmallModulusBaseTailGoal
```

There is an analogous `...FromHoffmanGoal` wrapper using
`ActiveHall.HoffmanOrderedSDRGoal`.

After the ActiveHall ordered-SDR proof response, Lean also exposes a more
standard copied-edge finite Hoffman interface:

```lean
def RoundComposite.ActiveHall.FiniteHoffman.ExactEdgeColoringGoal : Prop := ...

theorem RoundComposite.ActiveHall
  .hallRealizationGoal_of_exactEdgeColoring
    (hEdge : ActiveHall.FiniteHoffman.ExactEdgeColoringGoal) :
    ActiveHall.HallRealizationGoal
```

So the ActiveHall subproblem may now be supplied either as
`HoffmanOrderedSDRGoal` or as the copied-edge
`FiniteHoffman.ExactEdgeColoringGoal`.

## Active Packets

The older orbit packet for completing the final theorem is still available:

```lean
def RoundComposite.Concrete.OddModulusToriV4ReturnTailOrbitBlocksGoal :
    Prop :=
  (PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal ∧
   PrefixCountFirstHitReturnTailMonodromyOrbitGoal) ∧
  OddSuccessorSmallModulusBaseTailGoal
```

Lean endpoint:

```lean
theorem RoundComposite.Concrete
  .oddModulusToriAllDimensionsGoal_of_v4_returnTailOrbit_blocks
    (hBlocks : OddModulusToriV4ReturnTailOrbitBlocksGoal) :
    OddModulusToriAllDimensionsGoal
```

The sharper q>=2 trellis packet endpoint is:

```lean
def RoundComposite.Concrete
  .OddModulusToriV4ReturnTailOrbitTrellisBlocksGoal : Prop :=
  (PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal ∧
   PrefixCountFirstHitReturnTailMonodromyOrbitGoal) ∧
  OddSuccessorSmallModulusBaseTailGoal

theorem RoundComposite.Concrete
  .oddModulusToriAllDimensionsGoal_of_v4_returnTailOrbitTrellis_blocks
    (hBlocks : OddModulusToriV4ReturnTailOrbitTrellisBlocksGoal) :
    OddModulusToriAllDimensionsGoal

theorem RoundComposite.Concrete
  .oddModulusToriAllDimensionsGoal_of_v4_returnTailOrbitTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hOrbit : PrefixCountFirstHitReturnTailMonodromyOrbitGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddModulusToriAllDimensionsGoal
```

The currently sharpest return-tail endpoint uses trellis for the q>=2 branch
and the Lean-closed return-tail cocycle chain.  The exact formula is signed:
the rank `k` total carry is `(-1)^(k+1) * (C.step c k - C.delta c)`, not the
unsigned row difference.  The sign is a unit, so the unit-carry reduction is
unchanged.

```lean
def RoundComposite.Concrete
  .OddModulusToriV4ReturnTailClosedTrellisBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal ∧
  OddSuccessorSmallModulusBaseTailGoal

theorem RoundComposite.Concrete
  .oddModulusToriAllDimensionsGoal_of_v4_returnTailClosedTrellis_blocks
    (hBlocks : OddModulusToriV4ReturnTailClosedTrellisBlocksGoal) :
    OddModulusToriAllDimensionsGoal
```

```lean
theorem RoundComposite.Concrete
  .oddModulusToriAllDimensionsGoal_of_v4_returnTailClosedTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddModulusToriAllDimensionsGoal
```

With the additive small branch:

```lean
theorem RoundComposite.Concrete
  .oddModulusToriAllDimensionsGoal_of_v4_returnTailClosedTrellisAdd
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal) :
    OddModulusToriAllDimensionsGoal
```

After the full-support q>=2 split, Lean also exposes the direct endpoint:

```lean
def RoundComposite.Concrete
  .OddModulusToriV4ReturnTailClosedFullSupportTrellisBlocksGoal : Prop :=
  (PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal ∧
   PrefixCount.OrdinaryQge2IndicatorToFullSupportGoal) ∧
  OddSuccessorSmallModulusBaseTailGoal

theorem RoundComposite.Concrete
  .oddModulusToriAllDimensionsGoal_of_v4_returnTailClosedFullSupportTrellis
    (hFull : PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal)
    (hLift : PrefixCount.OrdinaryQge2IndicatorToFullSupportGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddModulusToriAllDimensionsGoal
```

The small branch can also be supplied through the copied-edge finite Hoffman
interface:

```lean
def ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal : Prop := ...
def ActiveHall.FiniteHoffman.ExactEdgeColoringGoal : Prop := ...
def ActiveHall.FiniteHoffman.CompatibleDeWerraGoal : Prop := ...

theorem ActiveHall.FiniteHoffman.exactEdgeColoringGoal_of_raw
    (hRaw : ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal) :
    ActiveHall.FiniteHoffman.ExactEdgeColoringGoal

theorem ActiveHall.FiniteHoffman.rawExactEdgeColoringGoal_of_compatibleDeWerra
    (hDW : ActiveHall.FiniteHoffman.CompatibleDeWerraGoal) :
    ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal

def RoundComposite.Concrete
  .OddSuccessorSmallModulusBaseTailGeometryExactEdgeColoringGoal : Prop :=
  OddSuccessorSmallModulusBaseTailGeometryFromHallGoal ∧
  ActiveHall.FiniteHoffman.ExactEdgeColoringGoal

theorem RoundComposite.Concrete
  .oddModulusToriAllDimensionsGoal_of_v4_returnTailClosedFullSupportTrellisGeometryRawEdge
    (hFull : PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal)
    (hLift : PrefixCount.OrdinaryQge2IndicatorToFullSupportGoal)
    (hGeom : OddSuccessorSmallModulusBaseTailGeometryFromHallGoal)
    (hRaw : ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal) :
    OddModulusToriAllDimensionsGoal
```

The q>=2 indicator-to-full-support field is also split by the level-set
half-slack bridge:

```lean
def PrefixCount.Qge2IndicatorCutsHalfSlackToSupportGoal : Prop := ...
def PrefixCount.Qge2OrdinaryHalfSlackGoal : Prop := ...

theorem PrefixCount.ordinaryQge2IndicatorToFullSupportGoal_of_halfSlackBridge
    (hBridge : PrefixCount.Qge2IndicatorCutsHalfSlackToSupportGoal)
    (hHalf : PrefixCount.Qge2OrdinaryHalfSlackGoal) :
    PrefixCount.OrdinaryQge2IndicatorToFullSupportGoal
```

## Remaining Fields

The goal is not complete.  For the sharpest Lean-exposed split, the remaining
hard fields are:

```lean
PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal
PrefixCount.Qge2IndicatorCutsHalfSlackToSupportGoal
PrefixCount.Qge2OrdinaryHalfSlackGoal
OddSuccessorSmallModulusBaseTailGeometryFromHallGoal
ActiveHall.FiniteHoffman.CompatibleDeWerraGoal
```

Equivalently, the first three q>=2 fields may be replaced by the coarser pair
`PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal` and
`PrefixCount.OrdinaryQge2IndicatorToFullSupportGoal`, or by the single still
coarser field `PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal`.  The last two
fields may
be replaced by the single coarser field
`OddSuccessorSmallModulusBaseTailGoal`.  The raw ActiveHall field may also be
used in place of `ActiveHall.FiniteHoffman.CompatibleDeWerraGoal`, and
`ActiveHall.FiniteHoffman.ExactEdgeColoringGoal` is an even coarser sufficient
field.  Lean also exposes the separation endpoint
`PrefixCount.OrdinaryQge2SupportViolationGivesIndicatorCutGoal`, which implies
the indicator-to-full-support half.

The older `PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal` remains a
valid sufficient field, but it is now Lean-reduced from the trellis-Hoffman
form above.

The return-tail orbit, rank, rank-equivalence, cycle-coordinate, increment, and
triangular fields remain valid sufficient alternatives, but they are no longer
remaining fields for the preferred endpoint.  In older endpoint variants, the
one-step fiber field can be replaced by the stronger tail increment or
triangular fields:

```lean
PrefixCountFirstHitReturnTailIncrementDependsOnTakeGoal
PrefixCountFirstHitReturnTailTriangularGoal
```

or by the older orbit field:

```lean
PrefixCountFirstHitReturnTailMonodromyOrbitGoal
```

or, replacing the small-modulus line by the sufficient additive form:

```lean
OddSuccessorSmallModulusSlackPacketLiftAddGoal
```

## Verification Gate

Use:

```bash
lake build RoundComposite
git diff --check
grep -R -n -E '\b(sorry|admit|axiom|constant)\b' \
  RoundComposite Shared TorusD3Odd D5Odd D7Odd --include='*.lean'
```
