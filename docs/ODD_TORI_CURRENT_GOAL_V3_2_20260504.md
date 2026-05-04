# Odd-Modulus Tori Current Goal v3.2

Date: 2026-05-04.

This supersedes `docs/ODD_TORI_CURRENT_GOAL_V3_1_20260504.md` as the concise
active Lean goal statement.  The final theorem is unchanged.

## Final Theorem

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

The proof spine remains:

```text
D2/D3/D5/D7 seeds
+ product closure
+ successor closure b -> 2*b + 1
= all d >= 2 and all odd m >= 3
```

## Closed Spine

The seed/product/successor dispatcher is Lean-closed:

```lean
theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_357_and_successor
    (hSucc : OddSuccessorClosureGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

The successor branch dispatcher is also Lean-closed:

```lean
theorem RoundComposite.Concrete
  .oddSuccessorClosureGoal_of_high_and_successorSmall
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddSuccessorClosureGoal
```

## Current Preferred Packet

The current Lean-facing packet is:

```lean
def RoundComposite.Concrete.OddCoreHighModulusReturnTailMonodromyBlocksGoal :
    Prop :=
  PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal ∧
  PrefixCountFirstHitReturnTailMonodromyGoal

def RoundComposite.Concrete.OddModulusToriV4ReturnTailMonodromyBlocksGoal :
    Prop :=
  OddCoreHighModulusReturnTailMonodromyBlocksGoal ∧
  OddSuccessorSmallModulusBaseTailGoal
```

It closes the final target conditionally:

```lean
theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_v4_returnTailMonodromy_blocks
    (hBlocks : OddModulusToriV4ReturnTailMonodromyBlocksGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m

theorem RoundComposite.Concrete
  .oddModulusToriAllDimensionsGoal_of_v4_returnTailMonodromy_blocks
    (hBlocks : OddModulusToriV4ReturnTailMonodromyBlocksGoal) :
    OddModulusToriAllDimensionsGoal
```

## Why This Is Better Than v3.1

The previous minimal packet used:

```lean
PrefixCountRootFlatCanonicalScheduleCriterionGoal
```

as a high-modulus field.  Lean now exposes the first-hit schedule criterion
through a smaller tail-return target:

```lean
def PrefixCountFirstHitReturnTailMonodromyGoal : Prop :=
  forall {d m : Nat} [NeZero m] (hd2 : 2 <= d) {C : PrefixCount.Parts d},
    Odd d -> 5 <= d -> Odd m -> d <= m ->
    C.Admissible m ->
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) ->
    forall c : Fin d,
      Shared.IsSingleCycleMap
        (prefixCountFirstHitReturnTailMonodromy hd2 L c)
```

The bridge from this target to the old schedule criterion is Lean-closed:

```lean
theorem RoundComposite.Concrete
  .prefixCountFirstHitHeadTailSectionMonodromyGoal_of_returnTailMonodromy
    (hTail : PrefixCountFirstHitReturnTailMonodromyGoal) :
    PrefixCountFirstHitHeadTailSectionMonodromyGoal

theorem RoundComposite.Concrete
  .prefixCountFirstHitCanonicalReturnsSingleCycleGoal_of_returnTailMonodromy
    (hTail : PrefixCountFirstHitReturnTailMonodromyGoal) :
    PrefixCountFirstHitCanonicalReturnsSingleCycleGoal
```

The key definitional bridge is:

```lean
theorem RoundComposite.Concrete
  .prefixCountFirstHitSectionReturn_eq_returnTailMonodromy :
    Shared.sectionReturn
        (Shared.skewProductMap
          (prefixCountFirstHitReturnBaseStep C c)
          (prefixCountFirstHitReturnFiberStep hd2 L c))
        (0 : ZMod m) m =
      prefixCountFirstHitReturnTailMonodromy hd2 L c
```

So the high-modulus cyclicity proof can now focus on the concrete
`returnMap^[m]` tail projection instead of proving cyclicity directly for the
generic `Shared.sectionReturn` skew product.

## Remaining External Fields

The goal is not complete.  The current preferred packet leaves exactly these
fields:

```lean
PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal
PrefixCountFirstHitReturnTailMonodromyGoal
OddSuccessorSmallModulusBaseTailGoal
```

The first field is the q>=2 proper-cut signed decomposition theorem.  The
second is the high-modulus first-hit tail monodromy theorem.  The third is the
successor small-modulus base-tail branch.

## Verification Gate

Current checked gate:

```bash
lake build RoundComposite
git diff --check
grep -R -n -E '\b(sorry|admit|axiom|constant)\b' \
  RoundComposite Shared D5Odd D7Odd --include='*.lean'
```

