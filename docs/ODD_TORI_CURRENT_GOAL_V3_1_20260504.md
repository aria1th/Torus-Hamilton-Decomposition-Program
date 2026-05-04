# Odd-Modulus Tori Current Goal v3.1

Date: 2026-05-04.

This supersedes `docs/ODD_TORI_CURRENT_GOAL_V3_0_20260504.md` as the concise
active goal statement.  Older notes remain audit and design background.

## Final Theorem

Formalize the all-dimensional odd-modulus theorem:

```lean
theorem odd_modulus_tori_all_dimensions
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

The intended proof spine is:

```text
D2/D3/D5/D7 seeds
+ product closure
+ successor closure b -> 2*b + 1
= all d >= 2 and all odd m >= 3
```

## Goal 1: Closure Dispatcher

Use the solved dimensions `2`, `3`, `5`, and `7`, product closure, and the
successor closure interface:

```lean
def RoundComposite.Concrete.OddSuccessorClosureGoal : Prop :=
  forall {b m : Nat},
    5 <= b ->
    Odd m -> 3 <= m ->
    StandardCayleySolved b m ->
    StandardCayleySolved (2*b + 1) m
```

to derive the final theorem.

Lean status: closed.

```lean
theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_357_and_successor
    (hSucc : OddSuccessorClosureGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

Location: `RoundComposite/ConcreteEndpoints.lean`.

## Goal 2: Successor Closure

Close the successor theorem:

```lean
theorem odd_successor_closure
    {b m : Nat}
    (hb5 : 5 <= b)
    (hmodd : Odd m) (hm3 : 3 <= m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2*b + 1) m
```

The branch split is:

```text
m >= 2*b + 1: prefix-count high-modulus branch
m <  2*b + 1: successor base-tail Hall-slack branch
```

Lean status: the conditional branch dispatcher is closed.

```lean
theorem RoundComposite.Concrete
  .odd_successor_closure_of_high_and_successorSmall
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {b m : Nat}
    (hb5 : 5 <= b)
    (hmodd : Odd m) (hm3 : 3 <= m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2*b + 1) m
```

Location: `RoundComposite/OddCore.lean`.

## Goal 3: Construction Blocks

Close the two construction branches consumed by successor closure.

High-modulus branch:

```lean
def RoundComposite.Concrete.OddCoreHighModulusPrefixCountGoal : Prop :=
  forall {d m : Nat}, Odd d -> 5 <= d -> Odd m -> d <= m ->
    StandardCayleySolved d m
```

Successor small-modulus branch:

```lean
def RoundComposite.Concrete.OddSuccessorSmallModulusBaseTailGoal : Prop :=
  forall {b m : Nat},
    5 <= b ->
    Odd m -> 3 <= m ->
    m < 2*b + 1 ->
    StandardCayleySolved b m ->
    StandardCayleySolved (2*b + 1) m
```

The current preferred Lean packet that closes both branches is:

```lean
def RoundComposite.Concrete.OddModulusToriV4PreferredBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal
```

Lean status: the endpoint from this packet to the final theorem is closed.
The q=1 target-Hall field is no longer an assumption: Lean proves it as
`PrefixCount.ordinaryQeq1AuxTargetHallDataGoal`.

```lean
theorem RoundComposite.Concrete
  .odd_successor_small_modulus_base_tail_of_v4_preferred_blocks
    (hBlocks : OddModulusToriV4PreferredBlocksGoal)
    {b m : Nat}
    (hb5 : 5 <= b)
    (hmodd : Odd m) (hm3 : 3 <= m)
    (hmSmall : m < 2*b + 1)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2*b + 1) m

theorem RoundComposite.Concrete
  .odd_successor_closure_of_v4_preferred_blocks
    (hBlocks : OddModulusToriV4PreferredBlocksGoal)
    {b m : Nat}
    (hb5 : 5 <= b)
    (hmodd : Odd m) (hm3 : 3 <= m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2*b + 1) m

theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_v4_preferred_blocks
    (hBlocks : OddModulusToriV4PreferredBlocksGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

Location: `RoundComposite/OddCore.lean`.

## Remaining Lean Work

The active proof obligations are exactly the three fields of
`OddModulusToriV4PreferredBlocksGoal`:

1. `PrefixCount.OrdinaryQge2SignedSeedClosureGoal`
2. `PrefixCountRootFlatCanonicalReturnGoal`
3. `OddCoreSmallModulusSlackPacketLiftGoal`

For the first item, Lean now exposes the equivalent nontrivial-cut formulation
`PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal`.  The endpoint cuts
`J = empty` and `J = univ` are no longer external obligations:
`PrefixCount.ordinaryQge2SignedSeedClosureGoal_iff_properCutClosure` proves that
they are forced by the row/column sum hypotheses and the `qge2ColumnCapacity`
endpoint arithmetic.

The q=1 auxiliary `0/1` degree matrix existence is Lean-closed as
`PrefixCount.ordinaryQeq1AuxDegreeMatrixGoal`.  The universal theorem asking for
a special matching for every such degree matrix is too strong; Lean records this
as `PrefixCount.not_ordinaryQeq1DegreeSpecialMatchingGoal`, and the corresponding
block packet is Lean-proved impossible as
`RoundComposite.Concrete.not_oddModulusToriV4DegreeSpecialMatchingBlocksGoal`.

The repaired q=1 route is now Lean-closed.  For `r = 1`,
`PrefixCount.OrdinaryQeq1AuxTargetHallData.nonempty_of_auxMatrix_r_eq_one`
turns any auxiliary matrix into target-Hall data.  For `1 < r`,
`PrefixCount.OrdinaryQeq1AuxTargetHallData.nonempty_of_auxMatrix_one_lt_r`
uses the forced P-row matching
`PrefixCount.OrdinaryQeq1AuxMatrixData.exists_pRows_matching_with_forced_of_one_lt_r`,
then relabels columns via
`PrefixCount.OrdinaryQeq1AuxMatrixData.relabelColumns` so the matching image is
exactly the canonical high columns plus one low special column.  Combining these
branches with the uniform degree matrix construction gives
`PrefixCount.ordinaryQeq1AuxTargetHallDataGoal`.

When these three propositions are proved, the current conditional endpoint
immediately yields the final all-dimensional theorem.
