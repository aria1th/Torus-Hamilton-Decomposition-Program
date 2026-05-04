# Odd Tori Current Blocks Completion Audit

Date: 2026-05-04.

This audit records the current Lean state for the all-dimensional odd-modulus
goal after the v3.4 closure-goal reset.  The file name is historical; the
current endpoint is the return-tail triangular/trellis packet recorded in
`docs/ODD_TORI_CURRENT_GOAL_V3_4_20260504.md`.

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

The current sharp preferred conditional endpoint is:

```lean
theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_v4_returnTailHitConditionTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hHit : PrefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

For proof scripts that prefer the three arguments directly:

```lean
theorem RoundComposite.Concrete
  .oddSuccessorClosureGoal_of_v4_returnTailHitConditionTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hHit : PrefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddSuccessorClosureGoal

theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_v4_returnTailHitConditionTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hHit : PrefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

The same endpoint is also packaged as the named final target:

```lean
theorem RoundComposite.Concrete
  .oddModulusToriAllDimensionsGoal_of_v4_returnTailHitConditionTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hHit : PrefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
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
| Successor-only high split | `OddSuccessorHighModulusPrefixCountGoal`, `oddSuccessorClosureGoal_of_successorHigh_and_successorSmall` | Lean-closed conditional | Final closure only needs high-modulus construction for outputs `2*b+1 >= 11` |
| Successor closure from current three fields | `oddSuccessorClosureGoal_of_v4_returnTailOrbit` | Lean-closed conditional | Directly consumes the three remaining fields |
| q>=2 pure column-packing overreach | `PrefixCount.not_qge2SignedColumnPackingGoal` | Lean-closed negative | Shows the attempted arbitrary-row packing replacement is false |
| q>=2 column-packing block packet | `not_oddModulusToriV4ColumnPackingScheduleBlocksGoal` | Lean-closed negative | Prevents treating the false packet as an active endpoint |
| q>=2 small finite sanity check | `scripts/verify_qge2_proper_cut_small.py --max-n 6` | Script-checked | Verifies the arbitrary-row counterexample and exhaustively checks active ordinary-row data for `n=4,6` |
| High branch from current return-tail fields | `oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailOrbit_blocks` | Lean-closed | `RoundComposite/OddCore.lean` |
| q=1 auxiliary count branch | `PrefixCount.ordinaryQeq1AuxTargetHallDataGoal` | Lean-closed | Used by the high-branch adapter |
| q>=2 endpoint cut cleanup | `ordinaryQge2SignedSeedClosureGoal_iff_properCutClosure` | Lean-closed | Empty and full cuts are no longer external obligations |
| q>=2 proper-cut direct wrappers | `ordinaryQge2SignedMatrixGoal_of_properCutClosure`, `ordinaryQge2SignedCoreGoal_of_properCutClosure` | Lean-closed | Routes the first remaining field directly into the q>=2 matrix/core branch |
| q>=2 trellis-Hoffman wrapper | `OrdinaryQge2SignedTrellisHoffmanGoal`, `ordinaryQge2SignedSeedProperCutClosureGoal_of_signedTrellisHoffman` | Lean-closed conditional | Shrinks the q>=2 external field to the ordinary signed-trellis HEG theorem suggested by GPT-5.5 Pro |
| First-hit schedule construction | first-hit schedule, row-Latin, layer-bijective, and head-tail return bridges | Lean-closed | `RoundComposite/OddCore.lean` |
| First-hit head cycle coordinate | `prefixCountFirstHitReturnBaseStep_cycleCoordinate` | Lean-closed | `C.prim_zero` gives a coordinate for the head map |
| First-hit positive hit case split | `prefixCountLambdaRho_val_eq_pos_iff`, `prefixCountFirstHitReturnFiberStep_apply_cases` | Lean-closed | Rewrites a tail-coordinate fiber carry into the three explicit positive-hit cases |
| Tail monodromy bijectivity | `prefixCountFirstHitReturnTailMonodromy_bijective` | Lean-closed | Leaves only orbit/transitivity for the tail map |
| Tail orbit from rank | `prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_rank` | Lean-closed conditional | A bijective odometer rank is enough |
| Tail rank from equivalence | `prefixCountFirstHitReturnTailRankGoal_of_rankEquiv` | Lean-closed conditional | An explicit equivalence odometer is enough |
| Tail rank equivalence from cycle coordinate | `prefixCountFirstHitReturnTailRankEquivGoal_of_cycleCoordinate` | Lean-closed conditional | A forward `Shared.CycleCoordinate` is enough |
| Tail cycle coordinate from monodromy | `prefixCountFirstHitReturnTailCycleCoordinateGoal_of_monodromy` | Lean-closed conditional | On the finite tail vector space, a single-cycle monodromy also yields a `CycleCoordinate` |
| Tail formulation equivalences | `prefixCountFirstHitReturnTailMonodromyGoal_iff_orbitGoal`, `..._iff_rankGoal`, `..._iff_rankEquivGoal`, `..._iff_cycleCoordinateGoal` | Lean-closed | The external tail request can be supplied in whichever of these four forms is easiest |
| Generic increment-dependency preservation | `Shared.ZModVectorIncrementDependsOnTake`, `Shared.zmodVectorIncrementDependsOnTake_skewFiberIterate` | Lean-closed | If every fiber step has lower-prefix-dependent increments, every skew fiber iterate has the same property |
| Tail hit-condition/unit split | `PrefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal`, `PrefixCountFirstHitReturnTailCocycleUnitGoal`, `prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_hitConditionUnitBlocks` | Lean-closed conditional | One-step hit-condition dependency gives fiber increment dependency, which is preserved by `skewFiberIterate`; with unit total carries and the generic odometer theorem, it closes the tail orbit |
| Tail increment/unit split | `PrefixCountFirstHitReturnTailIncrementDependsOnTakeGoal`, `PrefixCountFirstHitReturnTailCocycleUnitGoal`, `prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_incrementUnitBlocks` | Lean-closed conditional | Stronger than the hit-condition packet; kept as a sufficient route |
| Tail triangular/unit split | `PrefixCountFirstHitReturnTailTriangularGoal`, `PrefixCountFirstHitReturnTailCocycleUnitGoal`, `prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_triangularCocycleBlocks` | Lean-closed conditional | Stronger than the increment dependency packet; kept as an equivalent sufficient route |
| Shared rank cycle criterion | `Shared.single_cycle_of_zmod_rank`, `Shared.single_cycle_of_zmod_rank_equiv` | Lean-closed | Generic `ZMod N` rank increment cycle lemma |
| Unit additive cycle coordinate | `Shared.zmod_add_single_cycle_of_unit`, `Shared.CycleCoordinate.zmodAddConstOfUnit`, plus the older coprime variants | Lean-closed | Gives a coordinate-level base case for `x ↦ x + a` directly from `IsUnit a : ZMod m`, avoiding a Nat/coprime conversion |
| Section-return additive cycle coordinate | `Shared.sectionReturn_skewProductMap_zmod_add_cycleCoordinate_of_unit`, plus the older coprime variant | Lean-closed | Converts a computed unit total carry into a `CycleCoordinate` for the section return |
| Full skew-product unit-carry coordinate | `Shared.single_cycle_of_skewProduct_zmod_additive_unit_carry`, `Shared.cycleCoordinate_of_skewProduct_zmod_additive_unit_carry` | Lean-closed conditional | Turns the base-cover plus a `ZMod m` unit total carry proof into a single-cycle or coordinate proof for the full skew product |
| Lower-triangular vector split | `Shared.zmodVectorSnocEquiv`, `Shared.zmodVectorTake_snoc`, `Shared.zmodVectorTake_snoc_self` | Lean-closed | Provides the last-coordinate split needed for the induction proof of the generic lower-triangular odometer theorem |
| Ranked base orbit helpers | `Shared.zmod_rank_iterate_period`, `Shared.zmod_rank_orbit_cover_lt` | Lean-closed | A rank map incrementing by `1` over `ZMod N` returns after `N` steps and covers every base point within one period |
| Ranked base carry-sum helpers | `Shared.skewFiberAdditiveCarry_eq_sum_range`, `Shared.skewFiberAdditiveCarry_eq_univ_sum_of_rank_step`, `Shared.single_cycle_of_skewProduct_zmod_additive_carry_of_rank_unit_sum`, `Shared.cycleCoordinate_of_skewProduct_zmod_additive_carry_of_rank_unit_sum` | Lean-closed conditional | One full ranked base cycle accumulates the finite carry sum; if that sum is a unit, the additive skew product is a single cycle or has a `CycleCoordinate` |
| Generic lower-triangular unit theorem | `Shared.zmodVectorLowerTriangularUnitCycleCoordinate` | Lean-closed | Inductively splits `Fin r -> ZMod m` by `snoc` and applies the ranked-base unit-carry skew-product coordinate theorem |
| Successor small additive wrapper | `oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd` | Lean-closed | Instantiates `T = b + 1`, unit packets, and successor Hall slack |
| Return-tail additive endpoints | `odd_modulus_tori_all_dimensions_of_v4_returnTailOrbitAdd`, `odd_modulus_tori_all_dimensions_of_v4_returnTailCycleCoordinateAdd` | Lean-closed conditional | Final theorem wrappers that consume `OddSuccessorSmallModulusSlackPacketLiftAddGoal` directly |
| Successor-small Hall/geometry split | `OddSuccessorSmallModulusBaseTailGeometryFromHallGoal`, `OddSuccessorSmallModulusBaseTailGeometryFromHoffmanGoal` | Lean-closed conditional | Lets the small branch be supplied as base-tail geometry assuming `ActiveHall.HallRealizationGoal` or `HoffmanOrderedSDRGoal` |
| Active-Hall feasible-symboling bridge | `symbolingWithResidues_iff_feasible_of_realization` | Lean-closed conditional | Under `HallRealizationGoal`, residue-feasible count matrices are equivalent to actual symbolings |
| Active-Hall selection symboling bridge | `symbolingWithResidues_of_feasible_and_eraseLastHallCutsSelection`, `symbolingWithResidues_iff_feasible_of_eraseLastHallCutsSelection` | Lean-closed conditional | Lets a selection-form erase-last theorem consume feasible residue data directly |
| Active-Hall erase-last residue iff family | `symbolingWithResidues_iff_feasible_of_eraseLastHallCuts`, `...Choice`, `...SlackChoice`, `...NontrivialSlackChoice`, `...LinearChoice`, `...TokenLinearChoice` | Lean-closed conditional | Any erase-last formulation equivalent to `HallRealizationGoal` can now consume feasible residue data directly |
| Active-Hall selection-token equivalence | `eraseLastHallCutsTokenLinearChoiceGoal_of_selection`, `eraseLastHallCutsSelectionGoal_iff_tokenLinearChoiceGoal` | Lean-closed conditional | A selection-form erase-last proof now directly satisfies the token-linear request |
| Current compact all-dimensional conditional theorem | `odd_modulus_tori_all_dimensions_of_v4_returnTailHitConditionTrellis`, `oddModulusToriAllDimensionsGoal_of_v4_returnTailHitConditionTrellis` | Lean-closed conditional | Depends on trellis-Hoffman q>=2, one-step hit-condition/unit-carry fields, and successor-small field |
| Trellis compact all-dimensional conditional theorem | `odd_modulus_tori_all_dimensions_of_v4_returnTailOrbitTrellis`, `oddModulusToriAllDimensionsGoal_of_v4_returnTailOrbitTrellis` | Lean-closed conditional | Direct three-argument endpoint depending on the smaller trellis-Hoffman q>=2 field, tail orbit, and successor-small field |
| Successor-high compact final theorem | `oddModulusToriAllDimensionsGoal_of_successorHighSmall_blocks`, `...Add_blocks` | Lean-closed conditional | Allows a direct successor-high theorem plus small branch to close the final target |
| Named final-goal wrapper | `oddModulusToriAllDimensionsGoal_of_v4_returnTailHitConditionTrellis` | Lean-closed conditional | Same endpoint, packaged as `OddModulusToriAllDimensionsGoal` |

## Remaining External Fields

The goal is not complete.  In the current preferred packet, the remaining proof
obligations are exactly:

```lean
PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal
PrefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal
PrefixCountFirstHitReturnTailCocycleUnitGoal
OddSuccessorSmallModulusBaseTailGoal
```

These are not assumptions hidden behind `sorry`; they are explicit fields in
the conditional theorem statement.

The older `PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal` remains a
valid sufficient field, but Lean now reduces it from the trellis-Hoffman field.

## Field 1: q>=2 Ordinary Signed-Trellis Hoffman Closure

The current first preferred field is the ordinary signed-trellis HEG theorem:

```lean
PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal
```

Mathematically this is a finite signed-column Hoffman/Rado-Edmonds style
decomposition with entries in `{±1, ±2}`.  It is isolated from the torus
geometry and implies the nonempty proper-cut integral decomposition theorem:

```lean
PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal
```

The overly broad arbitrary-row packing theorem
`PrefixCount.Qge2SignedColumnPackingGoal` is false; Lean records this as
`PrefixCount.not_qge2SignedColumnPackingGoal`.

Latest finite sanity check:

```text
$ python3 scripts/verify_qge2_proper_cut_small.py --max-n 6
arbitrary-row counterexample verified: n=4, c=(1,1,1), R=(-6,-5,2,6)
ordinary proper-cut exhaustive check passed: n=4, checked=168, skipped=0
ordinary proper-cut exhaustive check passed: n=6, checked=10560, skipped=0
```

## Fields 2-3: First-Hit Return-Fiber Increment And Unit Carry

The preferred remaining high-modulus monodromy fields are:

```lean
PrefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal
PrefixCountFirstHitReturnTailCocycleUnitGoal
```

For every admissible prefix-count certificate, layer-permutation count
decomposition, and color, these ask that the first-hit return-tail monodromy on

```lean
Fin (d - 2) -> ZMod m
```

has one-step fiber hit condition depending only on the lower prefix and
that every rank cocycle has unit total carry.  Lean already proves that this
one-step dependency is preserved by `Shared.skewFiberIterate`, then implies
lower-triangular form and closes the tail orbit through the generic odometer
theorem.  Therefore the older orbit field can now be closed from:

```lean
PrefixCountFirstHitReturnFiberHitConditionUnitBlocksGoal
```

The response in
`docs/GPT55_PRO_RETURN_TAIL_ORBIT_RESPONSE_20260504.md` recommends this route.
Lean packages it as:

```lean
prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_hitConditionUnitBlocks
```

The older sufficient alternatives remain valid:

```lean
PrefixCountFirstHitReturnTailTriangularGoal
PrefixCountFirstHitReturnTailIncrementDependsOnTakeGoal
PrefixCountFirstHitReturnTailMonodromyOrbitGoal
PrefixCountFirstHitReturnTailRankGoal
PrefixCountFirstHitReturnTailRankEquivGoal
PrefixCountFirstHitReturnTailCycleCoordinateGoal
```

## Field 4: Successor Small-Modulus Branch

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

Lean also exposes a split form:

```lean
OddSuccessorSmallModulusBaseTailGeometryFromHallGoal
OddSuccessorSmallModulusBaseTailGeometryFromHoffmanGoal
```

The first asks for the base-tail/cylinder geometry assuming
`ActiveHall.HallRealizationGoal`; the second asks for the same assuming
`ActiveHall.HoffmanOrderedSDRGoal`.

The response in
`docs/GPT55_PRO_SUCCESSOR_SMALL_BASE_TAIL_RESPONSE_20260504.md` recommends
keeping the hard work in this exact split: pure cylinder expansion, active
symboling using Hall once, and pure base-tail lift.  It also warns not to
generalize the packet theorem away from `T = b + 1` unless packet-prefix sums
are strengthened.

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
EraseLastHallCutsSelectionGoal
EraseLastHallCutsChoiceGoal
EraseLastHallCutsSlackChoiceGoal
EraseLastHallCutsNontrivialSlackChoiceGoal
EraseLastHallCutsLinearChoiceGoal
EraseLastHallCutsTokenLinearChoiceGoal
```

and the bridges from these goals to `SymbolingWithResidues` are Lean-closed.
The named `iff` wrappers, including
`hallRealizationGoal_iff_eraseLastHallCutsSelectionGoal`, make any one of the
erase-last formulations enough to recover `HallRealizationGoal`.  The residue
level iff wrappers
`symbolingWithResidues_iff_feasible_of_eraseLastHallCuts*` also let any
erase-last formulation consume `FeasibleWithResidues` data directly.  In
particular, `eraseLastHallCutsSelectionGoal_iff_tokenLinearChoiceGoal` records
that the selection form and token-linear form are equivalent.
This does not yet prove `OddSuccessorSmallModulusBaseTailGoal`; it is the
abstract combinatorial realization layer expected to be used inside that branch.

## Verification

The current checked gate is:

```bash
lake build RoundComposite
git diff --check
grep -R -n -E '\b(sorry|admit|axiom|constant)\b' \
  RoundComposite Shared TorusD3Odd D5Odd D7Odd --include='*.lean'
```

It completed successfully after the v3.4 goal reset.  The grep is
expected to exit with status 1 and no output when no forbidden token is found.

## Active External Requests

The GPT-5.5 Pro background requests for the remaining hard fields are:

| Field | Request Doc | Response Id | Latest Status |
|---|---|---|---|
| q>=2 proper-cut signed closure | `docs/GPT55_PRO_QGE2_PROPER_CUT_REQUEST_20260504.md`, `docs/GPT55_PRO_QGE2_PROPER_CUT_RESPONSE_20260504.md` | `resp_0ef429ec8c8f7dbf0069f8a065ffe081a18ca122b1ee9e4a7b` | `completed` |
| first-hit return-fiber hit-condition/unit | `docs/GPT55_PRO_RETURN_TAIL_ORBIT_REQUEST_20260504.md`, `docs/GPT55_PRO_RETURN_TAIL_ORBIT_RESPONSE_20260504.md` | `resp_027f823c07feb7000069f8a28fa85481a188b9e57ef6926c33` | `completed`; generic lower-triangular theorem and skewFiberIterate preservation now Lean-closed |
| successor-small base-tail branch | `docs/GPT55_PRO_SUCCESSOR_SMALL_BASE_TAIL_REQUEST_20260504.md`, `docs/GPT55_PRO_SUCCESSOR_SMALL_BASE_TAIL_RESPONSE_20260504.md` | `resp_06781d5a17f099250069f8a2de229081919ddf1d65046d89c9` | `completed` |

## Verdict

The global theorem is not complete.  The dispatcher, seed/product closure, and
conditional successor split are Lean-closed.  The remaining work is concentrated
in four explicit mathematical fields, with the strongest current endpoint being
`odd_modulus_tori_all_dimensions_of_v4_returnTailHitConditionTrellis`.
