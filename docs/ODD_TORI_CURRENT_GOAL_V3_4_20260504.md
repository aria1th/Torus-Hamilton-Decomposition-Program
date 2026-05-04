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
preferred prefix-count fields:

```lean
PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal
PrefixCountFirstHitReturnTailMonodromyOrbitGoal
```

After the q>=2 proof-request response, Lean also exposes the smaller
ordinary-trellis interface:

```lean
def PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal : Prop := ...

theorem PrefixCount
  .ordinaryQge2SignedSeedProperCutClosureGoal_of_signedTrellisHoffman
    (hHoffman : OrdinaryQge2SignedTrellisHoffmanGoal) :
    OrdinaryQge2SignedSeedProperCutClosureGoal
```

Equivalent stronger routes are also available through return-tail rank,
rank-equivalence, or cycle-coordinate goals.

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

## Minimal Active Packet

The current minimal packet for completing the final theorem is:

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

With the additive small branch:

```lean
theorem RoundComposite.Concrete
  .oddModulusToriAllDimensionsGoal_of_v4_returnTailOrbitAdd
    (hQge2Proper : PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hOrbit : PrefixCountFirstHitReturnTailMonodromyOrbitGoal)
    (hSmall : OddSuccessorSmallModulusSlackPacketLiftAddGoal) :
    OddModulusToriAllDimensionsGoal
```

## Remaining Fields

The goal is not complete.  The remaining hard fields are:

```lean
PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal
PrefixCountFirstHitReturnTailMonodromyOrbitGoal
OddSuccessorSmallModulusBaseTailGoal
```

The older `PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal` remains a
valid sufficient field, but it is now Lean-reduced from the trellis-Hoffman
form above.

or, replacing the third line by the sufficient additive form:

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
