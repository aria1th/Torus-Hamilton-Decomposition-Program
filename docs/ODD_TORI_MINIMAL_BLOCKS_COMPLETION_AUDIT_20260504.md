# Odd Tori Current Blocks Completion Audit

Date: 2026-05-04.

This audit records the current Lean state for the all-dimensional odd-modulus
goal after the v3.3 return-tail refactor.  The file name is historical; the
current endpoint is the return-tail orbit packet recorded in
`docs/ODD_TORI_CURRENT_GOAL_V3_3_20260504.md`.

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

The current preferred conditional endpoint is:

```lean
def RoundComposite.Concrete.OddCoreHighModulusReturnTailOrbitBlocksGoal :
    Prop :=
  PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal ∧
  PrefixCountFirstHitReturnTailMonodromyOrbitGoal

def RoundComposite.Concrete.OddModulusToriV4ReturnTailOrbitBlocksGoal :
    Prop :=
  OddCoreHighModulusReturnTailOrbitBlocksGoal ∧
  OddSuccessorSmallModulusBaseTailGoal

theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_v4_returnTailOrbit_blocks
    (hBlocks : OddModulusToriV4ReturnTailOrbitBlocksGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

For proof scripts that prefer the three arguments directly:

```lean
theorem RoundComposite.Concrete
  .oddSuccessorClosureGoal_of_v4_returnTailOrbit
    (hQge2Proper :
      PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hOrbit : PrefixCountFirstHitReturnTailMonodromyOrbitGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddSuccessorClosureGoal

theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_v4_returnTailOrbit
    (hQge2Proper :
      PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hOrbit : PrefixCountFirstHitReturnTailMonodromyOrbitGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

The same endpoint is also packaged as the named final target:

```lean
theorem RoundComposite.Concrete
  .oddModulusToriAllDimensionsGoal_of_v4_returnTailOrbit_blocks
    (hBlocks : OddModulusToriV4ReturnTailOrbitBlocksGoal) :
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
| Successor closure from current three fields | `oddSuccessorClosureGoal_of_v4_returnTailOrbit` | Lean-closed conditional | Directly consumes the three remaining fields |
| q>=2 pure column-packing overreach | `PrefixCount.not_qge2SignedColumnPackingGoal` | Lean-closed negative | Shows the attempted arbitrary-row packing replacement is false |
| q>=2 column-packing block packet | `not_oddModulusToriV4ColumnPackingScheduleBlocksGoal` | Lean-closed negative | Prevents treating the false packet as an active endpoint |
| q>=2 small finite sanity check | `scripts/verify_qge2_proper_cut_small.py` | Script-checked | Verifies the arbitrary-row counterexample and exhaustively checks active ordinary-row data for `n=4` by default |
| High branch from current return-tail fields | `oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailOrbit_blocks` | Lean-closed | `RoundComposite/OddCore.lean` |
| q=1 auxiliary count branch | `PrefixCount.ordinaryQeq1AuxTargetHallDataGoal` | Lean-closed | Used by the high-branch adapter |
| q>=2 endpoint cut cleanup | `ordinaryQge2SignedSeedClosureGoal_iff_properCutClosure` | Lean-closed | Empty and full cuts are no longer external obligations |
| q>=2 proper-cut direct wrappers | `ordinaryQge2SignedMatrixGoal_of_properCutClosure`, `ordinaryQge2SignedCoreGoal_of_properCutClosure` | Lean-closed | Routes the first remaining field directly into the q>=2 matrix/core branch |
| First-hit schedule construction | first-hit schedule, row-Latin, layer-bijective, and head-tail return bridges | Lean-closed | `RoundComposite/OddCore.lean` |
| First-hit head cycle coordinate | `prefixCountFirstHitReturnBaseStep_cycleCoordinate` | Lean-closed | `C.prim_zero` gives a coordinate for the head map |
| Tail monodromy bijectivity | `prefixCountFirstHitReturnTailMonodromy_bijective` | Lean-closed | Leaves only orbit/transitivity for the tail map |
| Tail orbit from rank | `prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_rank` | Lean-closed conditional | A bijective odometer rank is enough |
| Tail rank from equivalence | `prefixCountFirstHitReturnTailRankGoal_of_rankEquiv` | Lean-closed conditional | An explicit equivalence odometer is enough |
| Tail rank equivalence from cycle coordinate | `prefixCountFirstHitReturnTailRankEquivGoal_of_cycleCoordinate` | Lean-closed conditional | A forward `Shared.CycleCoordinate` is enough |
| Tail cycle coordinate from monodromy | `prefixCountFirstHitReturnTailCycleCoordinateGoal_of_monodromy` | Lean-closed conditional | On the finite tail vector space, a single-cycle monodromy also yields a `CycleCoordinate` |
| Shared rank cycle criterion | `Shared.single_cycle_of_zmod_rank`, `Shared.single_cycle_of_zmod_rank_equiv` | Lean-closed | Generic `ZMod N` rank increment cycle lemma |
| Unit additive cycle coordinate | `Shared.CycleCoordinate.zmodAddConstOfCoprime` | Lean-closed | Gives a coordinate-level base case for `x ↦ x + a` when `gcd(a,m)=1` |
| Section-return additive cycle coordinate | `Shared.sectionReturn_skewProductMap_zmod_add_cycleCoordinate_of_coprime` | Lean-closed | Converts a computed unit total carry into a `CycleCoordinate` for the section return |
| Full skew-product cycle coordinate | `Shared.cycleCoordinate_of_skewProduct_base_orbit_monodromy`, `Shared.cycleCoordinate_of_skewProduct_zmod_additive_carry` | Lean-closed conditional | Turns the base-cover plus section-monodromy/carry proof into a coordinate for the full skew product |
| Successor small additive wrapper | `oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd` | Lean-closed | Instantiates `T = b + 1`, unit packets, and successor Hall slack |
| Active-Hall feasible-symboling bridge | `symbolingWithResidues_iff_feasible_of_realization` | Lean-closed conditional | Under `HallRealizationGoal`, residue-feasible count matrices are equivalent to actual symbolings |
| Current compact all-dimensional conditional theorem | `odd_modulus_tori_all_dimensions_of_v4_returnTailOrbit_blocks` | Lean-closed conditional | Depends only on the three remaining fields below |
| Named final-goal wrapper | `oddModulusToriAllDimensionsGoal_of_v4_returnTailOrbit_blocks` | Lean-closed conditional | Same endpoint, packaged as `OddModulusToriAllDimensionsGoal` |

## Remaining External Fields

The goal is not complete.  In the current preferred packet, the remaining proof
obligations are exactly:

```lean
PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal
PrefixCountFirstHitReturnTailMonodromyOrbitGoal
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

## Field 2: First-Hit Return-Tail Orbit

The remaining high-modulus monodromy statement is:

```lean
PrefixCountFirstHitReturnTailMonodromyOrbitGoal
```

For every admissible prefix-count certificate, layer-permutation count
decomposition, and color, it asks that the first-hit return-tail monodromy on

```lean
Fin (d - 2) -> ZMod m
```

is orbit-transitive.  Lean already proves the schedule construction, row-Latin
property, layer bijectivity, the root-flat/head-tail return bridges, and
bijectivity of this tail map.  Therefore the remaining field can be closed
directly by orbit-transitivity, or by either odometer sufficient target:

```lean
PrefixCountFirstHitReturnTailRankGoal
PrefixCountFirstHitReturnTailRankEquivGoal
PrefixCountFirstHitReturnTailCycleCoordinateGoal
```

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
git diff --check
grep -R -n -E '\b(sorry|admit|axiom|constant)\b' \
  RoundComposite Shared D5Odd D7Odd --include='*.lean'
```

It completed successfully after the v3.3 return-tail refactor.  The grep is
expected to exit with status 1 and no output when no forbidden token is found.

## Verdict

The global theorem is not complete.  The dispatcher, seed/product closure, and
conditional successor split are Lean-closed.  The remaining work is concentrated
in three explicit mathematical fields, with the strongest current endpoint being
`odd_modulus_tori_all_dimensions_of_v4_returnTailOrbit_blocks`.
