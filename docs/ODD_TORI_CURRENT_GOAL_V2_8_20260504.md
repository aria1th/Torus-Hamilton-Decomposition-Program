# Odd-Modulus Tori Current Goal v2.8

Date: 2026-05-04.

This is the minimal active goal after the v4 manuscript absorption and the
Lean closure-dispatcher update.

## Final Theorem

Formalize:

```lean
theorem odd_modulus_tori_all_dimensions
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

## Deliverable 1: Closure Dispatcher

Use the solved base dimensions `2`, `3`, `5`, and `7`, product closure, and
successor closure to generate every dimension.

Lean interface:

```lean
def RoundComposite.Concrete.OddSuccessorClosureGoal : Prop :=
  forall {b m : Nat},
    5 <= b ->
    Odd m -> 3 <= m ->
    StandardCayleySolved b m ->
    StandardCayleySolved (2*b + 1) m
```

Lean dispatcher:

```lean
theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_357_and_successor
    (hSucc : OddSuccessorClosureGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

Status: Lean-closed in `RoundComposite/ConcreteEndpoints.lean`.

## Deliverable 2: Successor Closure

Prove:

```lean
theorem odd_successor_closure
    {b m : Nat}
    (hb5 : 5 <= b)
    (hmodd : Odd m) (hm3 : 3 <= m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2*b + 1) m
```

Proof split:

```text
m >= 2*b + 1: count branch
m <  2*b + 1: base-tail Hall-slack branch with T = b + 1
```

Status: open as a non-conditional Lean theorem.

Lean now also contains the conditional adapter:

```lean
theorem RoundComposite.Concrete
  .oddSuccessorClosureGoal_of_high_and_successorSmall
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddSuccessorClosureGoal
```

and the corresponding all-dimensional endpoint:

```lean
theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_high_and_successor_small
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

The same reduction is also exposed in theorem form as:

```lean
theorem RoundComposite.Concrete
  .odd_successor_closure_of_high_and_slackPacketLift
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {b m : Nat}
    (hb5 : 5 <= b)
    (hmodd : Odd m) (hm3 : 3 <= m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2*b + 1) m
```

## Deliverable 3: Construction Blocks

Close the construction theorems needed by successor closure.

### Count Branch

Lean endpoint:

```lean
OddCoreHighModulusPrefixCountGoal
```

Internal Lean targets:

```lean
PrefixCount.MarginTransportQge2CompatibleGoal
PrefixCount.MarginTransportQeq1CompatibleGoal
PrefixCountRootFlatCanonicalReturnGoal
```

### Successor Small Branch

Suggested narrow endpoint:

```lean
theorem odd_successor_small_modulus_base_tail
    {b m : Nat}
    (hb5 : 5 <= b)
    (hmodd : Odd m) (hm3 : 3 <= m)
    (hmSmall : m < 2*b + 1)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2*b + 1) m
```

Lean contains this narrow endpoint as an interface:

```lean
def RoundComposite.Concrete.OddSuccessorSmallModulusBaseTailGoal : Prop := ...
```

and proves it from the broader slack-packet lift:

```lean
theorem RoundComposite.Concrete
  .odd_successor_small_modulus_base_tail_of_slackPacketLift
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {b m : Nat}
    (hb5 : 5 <= b)
    (hmodd : Odd m) (hm3 : 3 <= m)
    (hmSmall : m < 2*b + 1)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2*b + 1) m
```

Reusable broader endpoint:

```lean
OddCoreSmallModulusSlackPacketLiftGoal
```

Internal Lean targets:

```text
root-flat canonical return
q>=2 signed transportation
q=1 matching correction
Active Hall realization
controlled residue rounding
base-tail lift
```

Status: open as construction formalization.

Closed support added for the successor arithmetic:

```lean
RoundComposite.successor_quadratic_lt_three_pow_pred
RoundComposite.successor_hall_slack
```

## Current Summary

The top-level dimension induction is now reduced to successor closure.  The
remaining mathematical work is to formalize the v4 count branch and the
base-tail Hall-slack successor branch.
