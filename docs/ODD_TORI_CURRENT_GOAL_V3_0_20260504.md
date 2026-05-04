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
  .hallRealizationGoal_of_eraseLastHallCutsChoice
    (hChoice : EraseLastHallCutsChoiceGoal) :
    HallRealizationGoal

theorem RoundComposite.ActiveHall
  .hallRealizationGoal_of_eraseLastHallCutsSlackChoice
    (hSlackChoice : EraseLastHallCutsSlackChoiceGoal) :
    HallRealizationGoal

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

Closed support includes:

```lean
theorem RoundComposite.ActiveHall.hallRealization_zero
theorem RoundComposite.ActiveHall.hallRealization_one
theorem RoundComposite.ActiveHall.eraseLastHallCuts_zero
theorem RoundComposite.ActiveHall.eraseLastHallCutsChoice_zero
theorem RoundComposite.ActiveHall.eraseLastHallCutsSlackChoice_zero
noncomputable def RoundComposite.ActiveHall.Symboling.extendLast
theorem RoundComposite.ActiveHall.Symboling
  .extendLast_realizes_eraseLastCountMatrix
def RoundComposite.ActiveHall.Incidence.eraseChoice
def RoundComposite.ActiveHall.CountMatrix.eraseLastCountMatrix
def RoundComposite.ActiveHall.CountMatrix.cutSlack
theorem RoundComposite.ActiveHall.CountMatrix.cutMass_add_le_iff_le_cutSlack
def RoundComposite.ActiveHall.Incidence.choiceLowHitCount
theorem RoundComposite.ActiveHall.Incidence
  .choiceLowHitCount_symbols_empty
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
```

Remaining Active Hall proof obligation:

```lean
EraseLastHallCutsSlackChoiceGoal
```

Equivalently, the remaining theorem is a degree-constrained active choice
theorem with the cut condition

```lean
Incidence.choiceLowHitCount I choice U S
  <= M.cutSlack U (S.image Fin.castSucc)
```

for every color cut `U` and lower-symbol cut `S`.
