# Odd Tori Minimal Blocks Completion Audit

Date: 2026-05-04.

This audit records the current Lean state for the all-dimensional odd-modulus
goal after the v4 minimal-block refactor.

## Objective

The final target remains:

```lean
theorem odd_modulus_tori_all_dimensions
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

Lean now also names this final target as:

```lean
def RoundComposite.Concrete.OddModulusToriAllDimensionsGoal : Prop :=
  forall {d m : Nat}, 2 <= d -> Odd m -> 3 <= m ->
    Shared.CayleyHamiltonDecomposition d m
```

The intended proof spine is:

1. D2, D3, D5, D7 seed decompositions.
2. Product closure for composite dimensions.
3. Successor closure `b -> 2*b + 1`.
4. The high-modulus prefix-count branch for the successor.
5. The successor-specific small-modulus base-tail branch.

## Current Lean Endpoint

The current minimal conditional endpoint is:

```lean
def RoundComposite.Concrete.OddCoreHighModulusScheduleBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal ∧
  PrefixCountRootFlatCanonicalScheduleCriterionGoal

def RoundComposite.Concrete.OddModulusToriV4MinimalBlocksGoal : Prop :=
  OddCoreHighModulusScheduleBlocksGoal ∧
  OddSuccessorSmallModulusBaseTailGoal

theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_v4_minimal_blocks
    (hBlocks : OddModulusToriV4MinimalBlocksGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

For proof scripts that prefer the three arguments directly:

```lean
theorem RoundComposite.Concrete
  .oddSuccessorClosureGoal_of_v4_successorSchedule
    (hQge2Proper :
      PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hSchedule : PrefixCountRootFlatCanonicalScheduleCriterionGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddSuccessorClosureGoal

theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_v4_successorSchedule
    (hQge2Proper :
      PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hSchedule : PrefixCountRootFlatCanonicalScheduleCriterionGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

The same endpoint is also packaged as the named final target:

```lean
theorem RoundComposite.Concrete
  .oddModulusToriAllDimensionsGoal_of_v4_minimal_blocks
    (hBlocks : OddModulusToriV4MinimalBlocksGoal) :
    OddModulusToriAllDimensionsGoal
```

## Prompt-To-Artifact Checklist

| Requirement | Artifact | Status | Evidence |
|---|---|---:|---|
| D2 seed | `standard_cayley_odd_uniform_2` | Lean-closed | `RoundComposite/ConcreteEndpoints.lean` imports `Shared.D2Seed` |
| D3 seed | `standard_cayley_odd_uniform_3` | Lean-closed | `RoundComposite/ConcreteEndpoints.lean` imports `Shared.D3Seed` |
| D5 seed | `standard_cayley_odd_uniform_5` | Lean-closed | `RoundComposite/ConcreteEndpoints.lean` imports `D5Odd.Cayley` |
| D7 seed | `standard_cayley_odd_uniform_7` | Lean-closed | `RoundComposite/ConcreteEndpoints.lean` imports `D7Odd.Cayley` |
| Even/composite dimensions | product wrappers | Lean-closed | `odd_uniform_cayley_mul_of_standard`, `standard_cayley_odd_uniform_all_dimensions_of_odd_core` |
| Dispatcher from seeds + successor | `odd_modulus_tori_all_dimensions_of_357_and_successor` | Lean-closed | `RoundComposite/ConcreteEndpoints.lean` |
| Successor closure split | `oddSuccessorClosureGoal_of_high_and_successorSmall` | Lean-closed | `RoundComposite/OddCore.lean` |
| Successor closure from current three fields | `oddSuccessorClosureGoal_of_v4_successorSchedule` | Lean-closed conditional | Directly consumes the three remaining fields |
| q>=2 pure column-packing overreach | `PrefixCount.not_qge2SignedColumnPackingGoal` | Lean-closed negative | Shows the attempted arbitrary-row packing replacement is false |
| q>=2 column-packing block packet | `not_oddModulusToriV4ColumnPackingScheduleBlocksGoal` | Lean-closed negative | Prevents treating the false packet as an active endpoint |
| q>=2 small finite sanity check | `scripts/verify_qge2_proper_cut_small.py` | Script-checked | Verifies the arbitrary-row counterexample and exhaustively checks active ordinary-row data for `n=4` by default |
| High branch from current schedule fields | `oddCoreHighModulusPrefixCountGoal_of_v4_highSchedule_blocks` | Lean-closed | `RoundComposite/OddCore.lean` |
| q=1 auxiliary count branch | `PrefixCount.ordinaryQeq1AuxTargetHallDataGoal` | Lean-closed | Used by the high-branch adapter |
| q>=2 endpoint cut cleanup | `ordinaryQge2SignedSeedClosureGoal_iff_properCutClosure` | Lean-closed | Empty and full cuts are no longer external obligations |
| Root-flat certificate wrapper | `prefixCountRootFlatCanonicalReturnGoal_iff_scheduleCriterion` | Lean-closed | Schedule-facing field is enough |
| Successor small additive wrapper | `oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd` | Lean-closed | Instantiates `T = b + 1`, unit packets, and successor Hall slack |
| Current compact all-dimensional conditional theorem | `odd_modulus_tori_all_dimensions_of_v4_minimal_blocks` | Lean-closed conditional | Depends only on the three remaining fields below |
| Named final-goal wrapper | `oddModulusToriAllDimensionsGoal_of_v4_minimal_blocks` | Lean-closed conditional | Same endpoint, packaged as `OddModulusToriAllDimensionsGoal` |

## Remaining External Fields

The goal is not complete.  In the current minimal packet, the remaining proof
obligations are exactly:

```lean
PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal
PrefixCountRootFlatCanonicalScheduleCriterionGoal
OddSuccessorSmallModulusBaseTailGoal
```

These are not assumptions hidden behind `sorry`; they are explicit fields in
the conditional theorem statement.

## Field 1: q>=2 Proper-Cut Signed Closure

The current first field is the nonempty proper-cut integral decomposition
theorem:

```lean
PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal
```

Mathematically this is a finite signed-column Hoffman/Rado-Edmonds style
decomposition with entries in `{±1, ±2}`.  It is isolated from the torus
geometry.  The overly broad arbitrary-row packing theorem
`PrefixCount.Qge2SignedColumnPackingGoal` is false; Lean records this as
`PrefixCount.not_qge2SignedColumnPackingGoal`.

## Field 2: Root-Flat Canonical Schedule Criterion

The remaining schedule-facing statement is:

```lean
PrefixCountRootFlatCanonicalScheduleCriterionGoal
```

For every admissible prefix-count certificate and layer-permutation count
decomposition, it asks for a `Shared.RootFlatSchedule` with:

```lean
S.step = prefixCountRootStep d m
S.rowLatin
S.layerBijective
S.returnsSingleCycle
```

The generic root-flat lift from those properties to Hamilton decompositions is
already Lean-closed in `Shared/RootFlat.lean` and `RoundComposite/OddCore.lean`.

## Field 3: Successor Small-Modulus Branch

The minimal field is:

```lean
OddSuccessorSmallModulusBaseTailGoal
```

The certificate-facing variant is:

```lean
OddSuccessorSmallModulusSlackPacketLiftAddGoal
```

Lean proves:

```lean
oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd
```

so a proof of the additive packet-lift theorem for `T = b + 1` is sufficient.
The arithmetic side, including `m^b > m*(2*b+1)*((2*b+1)-b)`, is already
Lean-closed as `successor_hall_slack`.

## Active-Hall Status

The abstract finite symboling theorem is isolated in:

```lean
RoundComposite.ActiveHall.HallRealizationGoal
```

Lean already records equivalent or sufficient formulations:

```lean
HoffmanOrderedSDRGoal
ColumnFillingUpgradeGoal
EraseLastHallCutsGoal
EraseLastHallCutsChoiceGoal
EraseLastHallCutsSlackChoiceGoal
EraseLastHallCutsNontrivialSlackChoiceGoal
EraseLastHallCutsLinearChoiceGoal
EraseLastHallCutsTokenLinearChoiceGoal
```

and the bridges from these goals to `SymbolingWithResidues` are Lean-closed.
The named `iff` wrappers make any one of the erase-last formulations enough to
recover `HallRealizationGoal`.
This does not yet prove `OddSuccessorSmallModulusBaseTailGoal`; it is the
abstract combinatorial realization layer expected to be used inside that branch.

## Verification

The current checked gate is:

```bash
lake build RoundComposite
```

It completed successfully after the minimal-block refactor.

## Verdict

The global theorem is not complete.  The dispatcher, seed/product closure, and
conditional successor split are Lean-closed.  The remaining work is concentrated
in three explicit mathematical fields, with the strongest current endpoint being
`odd_modulus_tori_all_dimensions_of_v4_minimal_blocks`.
