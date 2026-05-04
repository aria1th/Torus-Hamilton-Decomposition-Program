# Odd-Modulus Tori Current Goal v3.0

Date: 2026-05-04.

## Target Theorem

Formalize the all-dimensional odd-modulus closure theorem:

```lean
theorem odd_modulus_tori_all_dimensions
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

## Minimal Proof Spine

### 1. Closure Dispatcher

Generate every `d >= 2` from the solved dimensions `2`, `3`, `5`, `7`,
product closure, and the successor closure `b -> 2*b + 1`.

Lean interface:

```lean
def RoundComposite.Concrete.OddSuccessorClosureGoal : Prop :=
  forall {b m : Nat},
    5 <= b ->
    Odd m -> 3 <= m ->
    StandardCayleySolved b m ->
    StandardCayleySolved (2*b + 1) m
```

Dispatcher endpoint:

```lean
theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_357_and_successor
    (hSucc : OddSuccessorClosureGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

Status: Lean-closed in `RoundComposite/ConcreteEndpoints.lean`.

### 2. Successor Closure

Prove the uniform successor theorem:

```lean
theorem odd_successor_closure
    {b m : Nat}
    (hb5 : 5 <= b)
    (hmodd : Odd m) (hm3 : 3 <= m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2*b + 1) m
```

It is assembled from two construction branches:

```text
m >= 2*b + 1: OddCoreHighModulusPrefixCountGoal
m <  2*b + 1: OddSuccessorSmallModulusBaseTailGoal
```

Status: the conditional branch-split theorem is Lean-closed in
`RoundComposite/OddCore.lean`:

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

### 3. Construction Blocks

Close the two branch interfaces consumed by successor closure.

High-modulus count branch:

```lean
def RoundComposite.Concrete.OddCoreHighModulusPrefixCountGoal : Prop :=
  forall {d m : Nat}, Odd d -> 5 <= d -> Odd m -> d <= m ->
    StandardCayleySolved d m
```

Preferred Lean inputs for this branch:

```lean
PrefixCount.MarginTransportQge2CompatibleGoal
PrefixCount.MarginTransportQeq1CompatibleGoal
PrefixCountRootFlatCanonicalReturnGoal
```

Small-modulus successor branch:

```lean
def RoundComposite.Concrete.OddSuccessorSmallModulusBaseTailGoal : Prop :=
  forall {b m : Nat},
    5 <= b ->
    Odd m -> 3 <= m ->
    m < 2*b + 1 ->
    StandardCayleySolved b m ->
    StandardCayleySolved (2*b + 1) m
```

Lean reduces this branch to the broader slack-packet theorem:

```lean
def RoundComposite.Concrete.OddCoreSmallModulusSlackPacketLiftGoal : Prop
```

## Current Working Endpoint

The strongest current all-dimensional adapter is:

```lean
theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_qge2Compat_qeq1Compat_rootFlatCanonical_and_slackPacketLift
    (hQge2 : PrefixCount.MarginTransportQge2CompatibleGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1CompatibleGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

Thus the concrete Lean work is exactly:

1. prove the q>=2 compatible signed-transport constructor;
2. prove the q=1 compatible signed-transport constructor;
3. prove the prefix-count root-flat canonical return certificate;
4. prove the base-tail Hall-slack packet lift.

## Active Hall Current Boundary

The finite Active Hall realization has been reduced to one narrower selection
interface.  As of the latest Lean state, this is best viewed at the
choice-function level:

```lean
def RoundComposite.ActiveHall.EraseLastHallCutsGoal : Prop
def RoundComposite.ActiveHall.EraseLastHallCutsSelectionGoal : Prop
def RoundComposite.ActiveHall.EraseLastHallCutsChoiceGoal : Prop
def RoundComposite.ActiveHall.EraseLastHallCutsSlackChoiceGoal : Prop
def RoundComposite.ActiveHall.EraseLastHallCutsNontrivialSlackChoiceGoal : Prop
def RoundComposite.ActiveHall.EraseLastHallCutsLinearChoiceGoal : Prop
def RoundComposite.ActiveHall.EraseLastHallCutsTokenLinearChoiceGoal : Prop
def RoundComposite.ActiveHall.ColumnFillingUpgradeGoal : Prop

theorem RoundComposite.ActiveHall
  .hallRealizationGoal_of_columnFillingUpgrade
    (hUpgrade : ColumnFillingUpgradeGoal) :
    HallRealizationGoal

theorem RoundComposite.ActiveHall
  .columnFillingUpgradeGoal_of_hallRealization
    (hRealize : HallRealizationGoal) :
    ColumnFillingUpgradeGoal

theorem RoundComposite.ActiveHall
  .hallRealizationGoal_iff_columnFillingUpgradeGoal :
    HallRealizationGoal <-> ColumnFillingUpgradeGoal

theorem RoundComposite.ActiveHall
  .hallRealizationGoal_of_eraseLastHallCuts
    (hErase : EraseLastHallCutsGoal) :
    HallRealizationGoal

theorem RoundComposite.ActiveHall
  .symbolingWithResidues_of_feasible_and_eraseLastHallCuts
    (hErase : EraseLastHallCutsGoal)
    (hFeasible : FeasibleWithResidues I R) :
    SymbolingWithResidues I R

theorem RoundComposite.ActiveHall
  .eraseLastHallCutsGoal_of_choice
    (hChoice : EraseLastHallCutsChoiceGoal) :
    EraseLastHallCutsGoal

theorem RoundComposite.ActiveHall
  .eraseLastHallCutsChoiceGoal_of_slackChoice
    (hSlackChoice : EraseLastHallCutsSlackChoiceGoal) :
    EraseLastHallCutsChoiceGoal

theorem RoundComposite.ActiveHall
  .eraseLastHallCutsGoal_of_slackChoice
    (hSlackChoice : EraseLastHallCutsSlackChoiceGoal) :
    EraseLastHallCutsGoal

theorem RoundComposite.ActiveHall
  .eraseLastHallCutsSlackChoiceGoal_of_nontrivial
    (hNontriv : EraseLastHallCutsNontrivialSlackChoiceGoal) :
    EraseLastHallCutsSlackChoiceGoal

theorem RoundComposite.ActiveHall
  .eraseLastHallCutsGoal_of_nontrivialSlackChoice
    (hNontriv : EraseLastHallCutsNontrivialSlackChoiceGoal) :
    EraseLastHallCutsGoal

theorem RoundComposite.ActiveHall
  .eraseLastHallCutsNontrivialSlackChoiceGoal_of_linear
    (hLinear : EraseLastHallCutsLinearChoiceGoal) :
    EraseLastHallCutsNontrivialSlackChoiceGoal

theorem RoundComposite.ActiveHall
  .eraseLastHallCutsLinearChoiceGoal_of_tokenLinear
    (hToken : EraseLastHallCutsTokenLinearChoiceGoal) :
    EraseLastHallCutsLinearChoiceGoal

theorem RoundComposite.ActiveHall
  .eraseLastHallCutsTokenLinearChoiceGoal_of_hallRealization
    (hRealize : HallRealizationGoal) :
    EraseLastHallCutsTokenLinearChoiceGoal

theorem RoundComposite.ActiveHall
  .eraseLastHallCutsGoal_of_linearChoice
    (hLinear : EraseLastHallCutsLinearChoiceGoal) :
    EraseLastHallCutsGoal

theorem RoundComposite.ActiveHall
  .eraseLastHallCutsGoal_of_tokenLinearChoice
    (hToken : EraseLastHallCutsTokenLinearChoiceGoal) :
    EraseLastHallCutsGoal

theorem RoundComposite.ActiveHall
  .hallRealizationGoal_of_eraseLastHallCutsChoice
    (hChoice : EraseLastHallCutsChoiceGoal) :
    HallRealizationGoal

theorem RoundComposite.ActiveHall
  .hallRealizationGoal_of_eraseLastHallCutsSlackChoice
    (hSlackChoice : EraseLastHallCutsSlackChoiceGoal) :
    HallRealizationGoal

theorem RoundComposite.ActiveHall
  .hallRealizationGoal_of_eraseLastHallCutsNontrivialSlackChoice
    (hNontriv : EraseLastHallCutsNontrivialSlackChoiceGoal) :
    HallRealizationGoal

theorem RoundComposite.ActiveHall
  .hallRealizationGoal_of_eraseLastHallCutsLinearChoice
    (hLinear : EraseLastHallCutsLinearChoiceGoal) :
    HallRealizationGoal

theorem RoundComposite.ActiveHall
  .hallRealizationGoal_of_eraseLastHallCutsTokenLinearChoice
    (hToken : EraseLastHallCutsTokenLinearChoiceGoal) :
    HallRealizationGoal

theorem RoundComposite.ActiveHall
  .hallRealizationGoal_iff_eraseLastHallCutsTokenLinearChoiceGoal :
    HallRealizationGoal <-> EraseLastHallCutsTokenLinearChoiceGoal

theorem RoundComposite.ActiveHall
  .symbolingWithResidues_of_feasible_and_eraseLastHallCutsChoice
    (hChoice : EraseLastHallCutsChoiceGoal)
    (hFeasible : FeasibleWithResidues I R) :
    SymbolingWithResidues I R

theorem RoundComposite.ActiveHall
  .symbolingWithResidues_of_feasible_and_eraseLastHallCutsSlackChoice
    (hSlackChoice : EraseLastHallCutsSlackChoiceGoal)
    (hFeasible : FeasibleWithResidues I R) :
    SymbolingWithResidues I R

theorem RoundComposite.ActiveHall
  .symbolingWithResidues_of_feasible_and_eraseLastHallCutsNontrivialSlackChoice
    (hNontriv : EraseLastHallCutsNontrivialSlackChoiceGoal)
    (hFeasible : FeasibleWithResidues I R) :
    SymbolingWithResidues I R

theorem RoundComposite.ActiveHall
  .symbolingWithResidues_of_feasible_and_eraseLastHallCutsLinearChoice
    (hLinear : EraseLastHallCutsLinearChoiceGoal)
    (hFeasible : FeasibleWithResidues I R) :
    SymbolingWithResidues I R

theorem RoundComposite.ActiveHall
  .symbolingWithResidues_of_feasible_and_eraseLastHallCutsTokenLinearChoice
    (hToken : EraseLastHallCutsTokenLinearChoiceGoal)
    (hFeasible : FeasibleWithResidues I R) :
    SymbolingWithResidues I R
```

The choice-level form asks for a function `choice : X -> C` selecting one active
color at each vertex, with the prescribed last-column degrees, such that every
lower-symbol cut has enough existing Hall slack to absorb exactly the low-hit
loss introduced by erasing `choice`.  The preferred remaining interface is now
the slack form:

```lean
Incidence.choiceLowHitCount I choice U S
  <= M.cutSlack U (S.image Fin.castSucc)
```

The nontrivial-cut form is even narrower: the above inequality only has to be
checked for `U.Nonempty`, `U != Finset.univ`, and `S.Nonempty`.  The cases
`U = empty`, `U = univ`, and `S = empty` are Lean-closed because their
low-hit count is zero.

The current smallest interface is the linear form, using

```lean
Incidence.lowCutSet I U S
Incidence.choiceDegreeOn (Incidence.lowCutSet I U S) choice c
```

and requiring

```lean
sum c in U,
  Incidence.choiceDegreeOn (Incidence.lowCutSet I U S) choice c
<= M.cutSlack U (S.image Fin.castSucc)
```

for the same nontrivial cuts.

After the token-load bridge, an even cleaner equivalent target is the
token-linear form:

```lean
def EraseLastHallCutsTokenLinearChoiceGoal : Prop :=
  forall I M, M.HallCuts ->
    exists f : (Sigma fun c => Fin (M.val c (Fin.last T))) ≃ X,
      (forall q, q.1 ∈ I.active (f q)) ∧
        forall U S,
          U.Nonempty -> U != Finset.univ -> S.Nonempty ->
            Incidence.tokenLoadOn f (Incidence.lowCutSet I U S) U
              <= M.cutSlack U (S.image Fin.castSucc)
```

Here `f` places the last-column tokens directly into vertices.  The induced
choice is `fun x => (f.symm x).1`, so the prescribed degrees follow from the
token bijection, and the linear cut inequality follows from:

```lean
Incidence.tokenLoadOn_eq_sum_choiceDegreeOn
```

Thus the preferred remaining Active Hall request is now
`EraseLastHallCutsTokenLinearChoiceGoal`.

Closed support includes:

```lean
theorem RoundComposite.ActiveHall.hallRealization_zero
theorem RoundComposite.ActiveHall.hallRealization_one
theorem RoundComposite.ActiveHall.eraseLastHallCuts_zero
theorem RoundComposite.ActiveHall.eraseLastHallCutsChoice_zero
theorem RoundComposite.ActiveHall.eraseLastHallCutsSlackChoice_zero
theorem RoundComposite.ActiveHall.eraseLastHallCutsNontrivialSlackChoice_zero
theorem RoundComposite.ActiveHall.eraseLastHallCutsLinearChoice_zero
theorem RoundComposite.ActiveHall.eraseLastHallCutsTokenLinearChoice_zero
noncomputable def RoundComposite.ActiveHall.Symboling.extendLast
theorem RoundComposite.ActiveHall.Symboling.color_mem_active
theorem RoundComposite.ActiveHall.Symboling.count_eq_choiceDegree
theorem RoundComposite.ActiveHall.Symboling
  .extendLast_realizes_eraseLastCountMatrix
theorem RoundComposite.ActiveHall.Symboling
  .local_castSucc_cut_count_add_last_low_indicator_le_cap
theorem RoundComposite.ActiveHall.Symboling
  .cutMass_eq_sum_local_of_realizes
theorem RoundComposite.ActiveHall.Symboling
  .cutMass_image_castSucc_add_choiceLowHitCount_le_cutCap_of_realizes
def RoundComposite.ActiveHall.Incidence.eraseChoice
def RoundComposite.ActiveHall.CountMatrix.eraseLastCountMatrix
def RoundComposite.ActiveHall.CountMatrix.cutSlack
theorem RoundComposite.ActiveHall.CountMatrix.cutMass_add_le_iff_le_cutSlack
def RoundComposite.ActiveHall.Incidence.choiceDegreeOn
def RoundComposite.ActiveHall.Incidence.choiceHitCountOn
def RoundComposite.ActiveHall.Incidence.lowCutSet
def RoundComposite.ActiveHall.Incidence.choiceLowHitCount
theorem RoundComposite.ActiveHall.Incidence.choiceDegreeOn_le_card
theorem RoundComposite.ActiveHall.Incidence.choiceDegreeOn_mono_set
theorem RoundComposite.ActiveHall.Incidence.choiceDegreeOn_le_choiceDegree
theorem RoundComposite.ActiveHall.Incidence.choiceDegreeOn_univ
theorem RoundComposite.ActiveHall.Incidence.choiceHitCountOn_le_card
theorem RoundComposite.ActiveHall.Incidence.choiceHitCountOn_mono_set
theorem RoundComposite.ActiveHall.Incidence.choiceHitCountOn_mono_colors
theorem RoundComposite.ActiveHall.Incidence.choiceHitCountOn_le_choiceHitCount
theorem RoundComposite.ActiveHall.Incidence.choiceHitCountOn_univ
theorem RoundComposite.ActiveHall.Incidence.lowCutSet_mono_symbols
theorem RoundComposite.ActiveHall.Incidence.lowCutSet_mono_symbols_of_subset
theorem RoundComposite.ActiveHall.Incidence.lowCutSet_colors_empty
theorem RoundComposite.ActiveHall.Incidence.lowCutSet_colors_univ
theorem RoundComposite.ActiveHall.Incidence
  .choiceLowHitCount_eq_choiceHitCountOn_lowCutSet
theorem RoundComposite.ActiveHall.Incidence
  .sum_choiceDegreeOn_on
theorem RoundComposite.ActiveHall.Incidence
  .sum_choiceDegreeOn_on_le_card
theorem RoundComposite.ActiveHall.Incidence
  .sum_choiceDegreeOn_on_le_choiceHitCount
theorem RoundComposite.ActiveHall.Incidence
  .sum_choiceDegreeOn_on_le_sum_choiceDegree
theorem RoundComposite.ActiveHall.Incidence
  .sum_choiceDegreeOn_on_mono_set
theorem RoundComposite.ActiveHall.Incidence
  .sum_choiceDegreeOn_on_mono_colors
def RoundComposite.ActiveHall.Incidence.tokenLoadOn
theorem RoundComposite.ActiveHall.Incidence
  .tokenLoadOn_eq_choiceHitCountOn
theorem RoundComposite.ActiveHall.Incidence
  .tokenLoadOn_eq_sum_choiceDegreeOn
theorem RoundComposite.ActiveHall.Incidence
  .tokenLoadOn_le_card
theorem RoundComposite.ActiveHall.Incidence
  .tokenLoadOn_mono_set
theorem RoundComposite.ActiveHall.Incidence
  .tokenLoadOn_mono_colors
theorem RoundComposite.ActiveHall.Incidence
  .tokenLoadOn_set_empty
theorem RoundComposite.ActiveHall.Incidence
  .tokenLoadOn_colors_empty
theorem RoundComposite.ActiveHall.Incidence
  .tokenLoadOn_colors_univ
theorem RoundComposite.ActiveHall.Incidence
  .choiceLowHitCount_eq_sum_choiceDegreeOn_lowCutSet
theorem RoundComposite.ActiveHall.Incidence
  .choiceLowHitCount_symbols_empty
theorem RoundComposite.ActiveHall.Incidence
  .choiceLowHitCount_colors_empty
theorem RoundComposite.ActiveHall.Incidence
  .choiceLowHitCount_colors_univ
theorem RoundComposite.ActiveHall.Incidence
  .choiceLowHitCount_le_choiceHitCount
theorem RoundComposite.ActiveHall.CountMatrix.eraseLastCountMatrix_cutMass
theorem RoundComposite.ActiveHall.CountMatrix.cutMass_last_eq_choiceHitCount
theorem RoundComposite.ActiveHall.CountMatrix
  .cutMass_image_castSucc_insert_last_eq_eraseLast_add_choiceHitCount
theorem RoundComposite.ActiveHall.CountMatrix
  .eraseLastCountMatrix_hallCuts_of_cutCap_slack
theorem RoundComposite.ActiveHall.CountMatrix
  .eraseLastCountMatrix_hallCuts_of_cutSlack
theorem RoundComposite.ActiveHall.Incidence.sum_choiceDegree_on
theorem RoundComposite.ActiveHall.Incidence
  .eraseChoice_active_inter_card_add_indicator
theorem RoundComposite.ActiveHall.Incidence.cutCap_image_castSucc
theorem RoundComposite.ActiveHall.Incidence.cutCap_image_castSucc_insert_last
theorem RoundComposite.ActiveHall.Incidence
  .cutCap_image_castSucc_eq_eraseChoice_cutCap_add_choiceLowHitCount
theorem RoundComposite.ActiveHall.Incidence
  .exists_choiceDegree_bijective_token_matching
structure RoundComposite.ActiveHall.CountMatrix.ColumnFilling
theorem RoundComposite.ActiveHall.CountMatrix
  .exists_columnFilling_of_hallCuts
def RoundComposite.ActiveHall.Symboling.toColumnFilling
```

Remaining Active Hall proof obligation:

```lean
EraseLastHallCutsTokenLinearChoiceGoal
```

Equivalently, the remaining theorem is a degree-constrained active token
placement theorem with the cut condition

```lean
Incidence.tokenLoadOn f (Incidence.lowCutSet I U S) U
<= M.cutSlack U (S.image Fin.castSucc)
```

for every nonempty proper color cut `U` and nonempty lower-symbol cut `S`.

Plain Hall matching now gives the weaker `CountMatrix.ColumnFilling`: each
symbol column can be filled with active colors and the prescribed column
counts.  This does not enforce the row-Latin condition that, at each vertex,
the `T` chosen colors are all distinct.  This remaining strengthening is
isolated as:

```lean
ColumnFillingUpgradeGoal
```

It is Lean-equivalent to `HallRealizationGoal`, so the true abstract finite
combinatorics blocker is the Hoffman/capacitated upgrade from column-wise
fillings to genuine `Symboling`s.
