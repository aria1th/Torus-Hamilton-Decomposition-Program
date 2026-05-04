# Odd-Modulus Tori Current Goal v3.3

Date: 2026-05-04.

This supersedes `docs/ODD_TORI_CURRENT_GOAL_V3_2_20260504.md` as the concise
active Lean goal statement.  The final theorem is unchanged.

## Final Theorem

```lean
theorem odd_modulus_tori_all_dimensions
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

Lean packages this target as:

```lean
def RoundComposite.Concrete.OddModulusToriAllDimensionsGoal : Prop :=
  forall {d m : Nat}, 2 <= d -> Odd m -> 3 <= m ->
    Shared.CayleyHamiltonDecomposition d m
```

The closed spine remains:

```text
D2/D3/D5/D7 seeds
+ product closure
+ successor closure b -> 2*b + 1
= all d >= 2 and all odd m >= 3
```

The dispatcher from `OddSuccessorClosureGoal` to the final theorem is
Lean-closed in `RoundComposite/ConcreteEndpoints.lean`.

## Current Preferred Packet

The current Lean-facing packet is now orbit-only on the high-modulus
first-hit tail return:

```lean
def RoundComposite.Concrete.OddCoreHighModulusReturnTailOrbitBlocksGoal :
    Prop :=
  PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal ∧
  PrefixCountFirstHitReturnTailMonodromyOrbitGoal

def RoundComposite.Concrete.OddModulusToriV4ReturnTailOrbitBlocksGoal :
    Prop :=
  OddCoreHighModulusReturnTailOrbitBlocksGoal ∧
  OddSuccessorSmallModulusBaseTailGoal
```

It closes the final target conditionally:

```lean
theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_v4_returnTailOrbit_blocks
    (hBlocks : OddModulusToriV4ReturnTailOrbitBlocksGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m

theorem RoundComposite.Concrete
  .oddModulusToriAllDimensionsGoal_of_v4_returnTailOrbit_blocks
    (hBlocks : OddModulusToriV4ReturnTailOrbitBlocksGoal) :
    OddModulusToriAllDimensionsGoal
```

## Why This Is Smaller Than v3.2

The v3.2 packet used:

```lean
PrefixCountFirstHitReturnTailMonodromyGoal
```

which asked for a full `Shared.IsSingleCycleMap`.  Lean now proves the
bijective part automatically:

```lean
theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnTailMonodromy_bijective :
    Function.Bijective (prefixCountFirstHitReturnTailMonodromy hd2 L c)
```

Therefore the remaining high-modulus monodromy field is only:

```lean
def PrefixCountFirstHitReturnTailMonodromyOrbitGoal : Prop :=
  forall {d m : Nat} [NeZero m] (hd2 : 2 <= d) {C : PrefixCount.Parts d},
    Odd d -> 5 <= d -> Odd m -> d <= m ->
    C.Admissible m ->
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) ->
    forall c : Fin d, forall tail1 tail2 : Fin (d - 2) -> ZMod m,
      exists n : Nat,
        (prefixCountFirstHitReturnTailMonodromy hd2 L c)^[n] tail1 =
          tail2
```

Lean closes:

```lean
theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnTailMonodromyGoal_of_orbit
    (hOrbit : PrefixCountFirstHitReturnTailMonodromyOrbitGoal) :
    PrefixCountFirstHitReturnTailMonodromyGoal
```

An alternate odometer/rank route is also available:

```lean
def PrefixCountFirstHitReturnTailRankGoal : Prop :=
  forall {d m : Nat} [NeZero m] (hd2 : 2 <= d) {C : PrefixCount.Parts d},
    Odd d -> 5 <= d -> Odd m -> d <= m ->
    C.Admissible m ->
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) ->
    forall c : Fin d,
      exists rank :
          ((Fin (d - 2) -> ZMod m) -> ZMod (m ^ (d - 2))),
        Function.Bijective rank /\
        forall tail : Fin (d - 2) -> ZMod m,
          rank (prefixCountFirstHitReturnTailMonodromy hd2 L c tail) =
            rank tail + 1

theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_rank
    (hRank : PrefixCountFirstHitReturnTailRankGoal) :
    PrefixCountFirstHitReturnTailMonodromyOrbitGoal
```

If the rank is naturally constructed as an equivalence, Lean also exposes:

```lean
def PrefixCountFirstHitReturnTailRankEquivGoal : Prop :=
  forall {d m : Nat} [NeZero m] (hd2 : 2 <= d) {C : PrefixCount.Parts d},
    Odd d -> 5 <= d -> Odd m -> d <= m ->
    C.Admissible m ->
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) ->
    forall c : Fin d,
      exists e :
          ((Fin (d - 2) -> ZMod m) ≃ ZMod (m ^ (d - 2))),
        forall tail : Fin (d - 2) -> ZMod m,
          e (prefixCountFirstHitReturnTailMonodromy hd2 L c tail) =
            e tail + 1

theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnTailRankGoal_of_rankEquiv
    (hEquiv : PrefixCountFirstHitReturnTailRankEquivGoal) :
    PrefixCountFirstHitReturnTailRankGoal
```

If the proof is naturally built as a forward cycle parameterization, Lean now
also exposes the `CycleCoordinate` route:

```lean
def PrefixCountFirstHitReturnTailCycleCoordinateGoal : Prop :=
  forall {d m : Nat} [NeZero m] (hd2 : 2 <= d) {C : PrefixCount.Parts d},
    Odd d -> 5 <= d -> Odd m -> d <= m ->
    C.Admissible m ->
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) ->
    forall c : Fin d,
      Shared.CycleCoordinate (m ^ (d - 2))
        (prefixCountFirstHitReturnTailMonodromy hd2 L c)

theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnTailRankEquivGoal_of_cycleCoordinate
    (hCycle : PrefixCountFirstHitReturnTailCycleCoordinateGoal) :
    PrefixCountFirstHitReturnTailRankEquivGoal
```

The generic tail-space equivalence is available as:

```lean
noncomputable def Shared.zmodVectorPowerEquiv (n m : Nat) [NeZero m] :
    (Fin n -> ZMod m) ≃ ZMod (m ^ n)
```

## Remaining External Fields

The goal is not complete.  The current preferred packet leaves exactly:

```lean
PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal
PrefixCountFirstHitReturnTailMonodromyOrbitGoal
OddSuccessorSmallModulusBaseTailGoal
```

The first field is the q>=2 proper-cut signed decomposition theorem.  The
second is the high-modulus first-hit tail orbit theorem.  The third is the
successor small-modulus base-tail branch.

For the second field, any of the stronger targets
`PrefixCountFirstHitReturnTailRankGoal`,
`PrefixCountFirstHitReturnTailRankEquivGoal`, or
`PrefixCountFirstHitReturnTailCycleCoordinateGoal` is sufficient.

## Verification Gate

Current checked gate:

```bash
lake build RoundComposite
git diff --check
grep -R -n -E '\b(sorry|admit|axiom|constant)\b' \
  RoundComposite Shared D5Odd D7Odd --include='*.lean'
```
