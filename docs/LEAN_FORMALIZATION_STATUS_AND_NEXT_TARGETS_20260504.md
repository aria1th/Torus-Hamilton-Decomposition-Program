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
  .oddModulusToriAllDimensionsGoal_of_v4_returnTailClosedFullSupportTrellisGeometryRawEdge
    (hFull : PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal)
    (hLift : PrefixCount.OrdinaryQge2IndicatorToFullSupportGoal)
    (hGeom : OddSuccessorSmallModulusBaseTailGeometryFromHallGoal)
    (hRaw : ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal.{0, 0}) :
    OddModulusToriAllDimensionsGoal
```

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

So `OrdinaryQge2IndicatorToFullSupportGoal` is no longer the direct target.

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
```

This means the remaining ActiveHall work is the finite combinatorics theorem
itself, not the adapter plumbing.

## Remaining Lean Fields

For the preferred endpoint, the remaining fields are:

```lean
PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal
PrefixCount.Qge2IndicatorCutsHalfSlackToSupportGoal
PrefixCount.Qge2OrdinaryHalfSlackGoal
OddSuccessorSmallModulusBaseTailGeometryFromHallGoal
ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal
```

`ActiveHall.FiniteHoffman.CompatibleDeWerraGoal` is also sufficient, since it
implies the raw copied-edge field.

## Next Direct Lean Formalization Targets

The next direct Lean work should be the half-slack internal branch.  This is
local, specialized, and does not require importing a general finite Hoffman
library.

### Target Module

Use a new parallel file:

```text
RoundComposite/PrefixCountHalfSlack.lean
```

Do not use:

```text
RoundComposite/PrefixCount/HalfSlack.lean
```

because `RoundComposite/PrefixCount.lean` is currently a file, so that path
cannot also be a directory without a larger module refactor.

Suggested import plan:

```lean
-- RoundComposite/PrefixCountHalfSlack.lean
import RoundComposite.PrefixCount

namespace RoundComposite
namespace PrefixCount
```

Then add:

```lean
import RoundComposite.PrefixCountHalfSlack
```

to `RoundComposite.lean` after `RoundComposite.PrefixCount`.

### Attempt 1: Ordinary Half-Size Slack

First target:

```lean
PrefixCount.Qge2OrdinaryHalfSlackGoal
```

Reason: this is arithmetic and `Finset` bookkeeping, with no support-function
or sorting argument.

Concrete helper targets:

```lean
theorem qge2ColumnCapacity_half_of_one
    {n : Nat} (hnEven : Even n) :
    qge2ColumnCapacity n (n / 2) 1 = ...

theorem qge2ColumnCapacity_half_of_two
    {n : Nat} (hnEven : Even n) :
    qge2ColumnCapacity n (n / 2) 2 = ...

theorem sum_eps_on_half_lower_bound
    {n r : Nat} {epsBit : Fin n -> Nat} {J : Finset (Fin n)}
    (hnEven : Even n)
    (heps : forall i : Fin n, epsBit i = 0 \/ epsBit i = 1)
    (hepsSum : (sum i : Fin n, epsBit i) = r)
    (hJ : J.card = n / 2) :
    ...
```

Then close:

```lean
theorem qge2OrdinaryRowTarget_halfLevel_le_capacity_sub_allColumns
    ... :
    (sum i in J, qge2OrdinaryRowTarget n r a epsBit i)
      <= (sum k : Fin (n - 1), qge2ColumnCapacity n J.card (c k))
          - ((n - 1 : Nat) : Int)
```

and package it as:

```lean
theorem qge2OrdinaryHalfSlackGoal :
    Qge2OrdinaryHalfSlackGoal
```

### Target 2: Level-Set Decomposition

Second target:

```lean
lemma exists_nat_shift_of_int_weight {n : Nat} (w : Fin n -> Int) :
    exists (lo : Int) (u : Fin n -> Nat) (D : Nat),
      (forall i, w i = lo + (u i : Int)) /\
      (forall i, u i <= D)
```

and:

```lean
lemma int_weight_dot_eq_nat_upperLevels {n : Nat}
    (R w : Fin n -> Int) (lo : Int) (u : Fin n -> Nat) (D : Nat)
    (hw : forall i, w i = lo + (u i : Int))
    (hD : forall i, u i <= D) :
    (sum i : Fin n, w i * R i)
      =
    lo * (sum i : Fin n, R i)
      + sum t in Finset.range D,
          sum i in qge2UpperLevel u t, R i
```

Reason: this is reusable for the support bridge and does not depend on the
specific signed-column witness.

### Target 3: Signed Support Half-Penalty Bound

Third target:

```lean
theorem qge2SignedColumnSupport_ge_levelCapacity_sub_halfPenalty
    {n c : Nat}
    (hnEven : Even n) (hn4 : 4 <= n)
    (hc : c = 1 \/ c = 2)
    (w : Fin n -> Int) (lo : Int) (u : Fin n -> Nat) (D : Nat)
    (hw : forall i, w i = lo + (u i : Int))
    (hD : forall i, u i <= D) :
    lo * (-(c : Int))
      + sum t in Finset.range D,
          (qge2ColumnCapacity n (qge2UpperLevel u t).card c
            - qge2HalfLevelPenalty n u t)
      <= qge2SignedColumnSupport n c w
```

Then sum over columns:

```lean
theorem qge2SignedColumnSupport_sum_ge_levelCapacity_sub_halfPenalty
    ... :
    ...
```

Reason: this is the only half-slack target that needs an explicit witness or
sorting argument for the local signed alphabet.

### Target 4: Indicator Cuts Plus Half-Slack

Final internal half-slack target:

```lean
theorem qge2IndicatorCutsHalfSlackToSupportGoal :
    Qge2IndicatorCutsHalfSlackToSupportGoal
```

Use the level-set decomposition, the ordinary/cut hypotheses at each level,
and the signed support lower bound.  Then close:

```lean
theorem ordinaryQge2IndicatorToFullSupportGoal :
    OrdinaryQge2IndicatorToFullSupportGoal :=
  ordinaryQge2IndicatorToFullSupportGoal_of_halfSlackBridge
    qge2IndicatorCutsHalfSlackToSupportGoal
    qge2OrdinaryHalfSlackGoal
```

Name choice may need an `_of_halfSlack` suffix if it conflicts with existing
declarations.

## Separate Module Targets

These should not be attempted inside the half-slack file.

### Finite Hoffman / Signed Trellis

Target:

```lean
PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal
```

Recommended location:

```text
RoundComposite/FiniteHoffman/SignedTrellis.lean
```

This requires a finite integral Hoffman/Rado-Edmonds style theorem.  It should
be imported into the main chain only after its API is stable.

### Finite Hoffman / Edge Coloring

Targets:

```lean
ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal
ActiveHall.FiniteHoffman.ExactEdgeColoringGoal
ActiveHall.FiniteHoffman.CompatibleDeWerraGoal
```

Recommended location:

```text
RoundComposite/FiniteHoffman/EdgeColoring.lean
```

Any one of these is enough if adapters are used:

```text
CompatibleDeWerraGoal -> RawExactEdgeColoringGoal -> ExactEdgeColoringGoal
```

### Successor Small Geometry

Target:

```lean
OddSuccessorSmallModulusBaseTailGeometryFromHallGoal
```

Recommended timing: after the finite Hall/edge-coloring API is stable.  This
is project-specific geometry glue rather than a standard finite-combinatorics
theorem.

## Current Fixed Attempt Order

1. `RoundComposite/PrefixCountHalfSlack.lean`
   - `Qge2OrdinaryHalfSlackGoal`
   - level-set decomposition helpers
   - signed support half-penalty bound
   - `Qge2IndicatorCutsHalfSlackToSupportGoal`
   - wrapper to `OrdinaryQge2IndicatorToFullSupportGoal`

2. `RoundComposite/FiniteHoffman/SignedTrellis.lean`
   - `OrdinaryQge2SignedFullSupportTrellisGoal`

3. `RoundComposite/FiniteHoffman/EdgeColoring.lean`
   - raw/exact/de Werra edge-colouring theorem

4. Successor-small geometry glue
   - `OddSuccessorSmallModulusBaseTailGeometryFromHallGoal`

Only item 1 is the immediate direct Lean formalization attempt fixed by this
audit.

### Progress On Item 1

Status after the first implementation pass:

```lean
import RoundComposite.PrefixCountHalfSlack
```

has been added to `RoundComposite.lean`, and the new module
`RoundComposite/PrefixCountHalfSlack.lean` now Lean-closes:

```lean
PrefixCount.exists_nat_shift_of_int_weight
PrefixCount.nat_eq_sum_upper_indicators
PrefixCount.int_weight_dot_eq_nat_upperLevels
PrefixCount.qge2OrdinaryHalfSlackGoal
```

It also isolates the remaining sorted-pattern support estimate as:

```lean
PrefixCount.Qge2SignedSupportHalfPenaltyGoal
```

and proves the conditional bridge:

```lean
PrefixCount.qge2IndicatorCutsHalfSlackToSupportGoal_of_signedSupportHalfPenalty
PrefixCount.ordinaryQge2IndicatorToFullSupportGoal_of_signedSupportHalfPenalty
```

Therefore the current remaining blocker for item 1 is exactly the signed
support half-penalty estimate, i.e. the sorted signed-column pattern proof that
should imply `Qge2SignedSupportHalfPenaltyGoal`.  Item 1 is not yet complete
until that estimate is proved internally and the unconditional theorem

```lean
PrefixCount.qge2IndicatorCutsHalfSlackToSupportGoal
```

is provided.

The immediate subgoal can now be stated more sharply:

```lean
theorem PrefixCount.qge2SignedSupportHalfPenaltyGoal :
    PrefixCount.Qge2SignedSupportHalfPenaltyGoal
```

The new file already contains the closed-form prefix-pattern bounds:

```lean
PrefixCount.qge2SignedPatternPrefixOne_capacity
PrefixCount.qge2SignedPatternPrefixTwo_capacity_sub_half
```

so the remaining Lean work is the permutation/sorting layer: use `Tuple.sort`
to arrange `u : Fin n -> Nat` in descending order, construct the corresponding
signed column pattern, prove that every upper level set is a sorted prefix, and
feed that explicit column to `qge2SignedColumnSupport_ge_of_intColumn`.

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
