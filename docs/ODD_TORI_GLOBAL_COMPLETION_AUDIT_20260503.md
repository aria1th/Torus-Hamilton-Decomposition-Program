# Odd-Modulus Global Theorem Completion Audit

Date: 2026-05-03.

This audit tracks the current state of the target

```lean
theorem odd_modulus_tori_all_dimensions
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

The theorem is not complete yet.  The current Lean work fixes the proof spine
and closes the D2/D3 seeds, the all-dimensional wrapper, and the
seed-semigroup base arithmetic.

## Success Criteria

The active goal is achieved only when the repository contains a non-conditional
Lean theorem of the following shape, with no branch hypotheses:

```lean
theorem odd_modulus_tori_all_dimensions
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

The proof must use the D2/product wrapper for even dimensions, reduce the hard
part to the odd-dimensional core, close the small odd dimensions
`3,5,7,9,11`, and handle all odd `d >= 13` by the two uniform branches
`m >= d` and `m < d`.  The proof spine must not use the `d < 29` finite
boundary table as an input theorem or Lean dependency.

## Prompt-to-Artifact Checklist

| Requirement | Current artifact | Evidence | Status |
|---|---|---|---|
| Final theorem should cover every `d >= 2`, odd `m >= 3` | `RoundComposite.Concrete.odd_modulus_tori_all_dimensions_of_high_slack_and_small_packet_lift` | Lean-checked in `RoundComposite/OddCore.lean` | Conditional skeleton |
| Proof spine should not depend on the `d < 29` finite boundary table | `docs/ODD_TORI_GLOBAL_FORMALIZATION_GOAL_20260503.md` and `RoundComposite/OddCore.lean` | Dispatcher uses branch interfaces, not the table | Satisfied at skeleton level |
| D2 seed for even-dimensional wrapper | `Shared/D2Seed.lean`; `standard_cayley_odd_uniform_2` | `lake env lean Shared/D2Seed.lean`; imported in `ConcreteEndpoints` | Closed |
| D3 seed for odd core | `Shared/D3Seed.lean`; `standard_cayley_odd_uniform_3` | `lake env lean Shared/D3Seed.lean`; `lake build Shared.D3Seed` | Closed |
| All-dimensional wrapper from odd core | `standard_cayley_odd_uniform_all_dimensions_of_odd_core` and aliases | `lake env lean RoundComposite/ConcreteEndpoints.lean` | Closed |
| Odd-dimensional core dispatcher | `odd_modulus_tori_odd_dimension_core_of_refined_branches` | `lake env lean RoundComposite/OddCore.lean` | Conditional skeleton |
| Small odd dimension `d = 3` | `standard_cayley_odd_uniform_3` | Used directly by `OddCore.lean` | Closed |
| Small odd dimensions `d = 5,7` | Existing D5/D7 endpoints in `ConcreteEndpoints` | Used directly by `OddCore.lean` | Closed |
| Small odd dimension `d = 9` | `standard_cayley_odd_uniform_9_of_3` | Derived from `D3 * D3` in `OddCore.lean` | Closed |
| Small odd dimension `d = 11` | `standard_cayley_odd_uniform_11_of_high_and_d5_base_tail` | Splits into prefix-count for `m >= 11` and D5-base tail lift for `m < 11` | Conditional |
| General odd `d >= 13`, `m >= d` | `OddCoreHighModulusPrefixCount` | Interface only | Open |
| High-modulus branch decomposition | `PrefixCountLayerRealizationGoal`; `PrefixCountGeometricCriterionGoal`; `oddCoreHighModulusPrefixCountGoal_of_prefixCount`; `oddCoreHighModulusPrefixCountGoal_of_parts_and_geometry`; `oddCoreHighModulusPrefixCountGoal_of_transports_and_geometry` | Lean-checked in `RoundComposite/OddCore.lean` | Conditional adapter |
| Dense matrix layer realization | `PrefixCount.MatrixBalanced`; `PrefixCount.BalancedMatrixLayerRealizationGoal`; `PrefixCount.balancedMatrixLayerRealization_zero`; `PrefixCount.matrixBalanced_exists_positive_perm`; `PrefixCount.peelLayer_balanced`; `PrefixCount.balancedMatrixLayerRealizationGoal`; `PrefixCount.matrixLayerRealizationGoal`; `prefixCountLayerRealizationGoal` | Lean-checked in `RoundComposite/PrefixCount.lean` and `RoundComposite/OddCore.lean` | Closed |
| Margin-facing transport split | `PrefixCount.MarginTransportQge2Goal`; `PrefixCount.MarginTransportQeq1Goal`; `PrefixCount.transportQge2Goal_of_margin`; `PrefixCount.transportQeq1Goal_of_margin`; `PrefixCount.admissiblePartsCountBranchGoal_of_margin`; `oddCoreHighModulusPrefixCountGoal_of_margins_and_geometry`; `odd_modulus_tori_all_dimensions_of_margins_geometry_and_small_packet_lift` | Lean-checked in `RoundComposite/PrefixCount.lean` and `RoundComposite/OddCore.lean` | Conditional adapter |
| Q>=2 transport nonnegativity split | `PrefixCount.signedVal_ge_neg_two`; `PrefixCount.SignedMarginMatrix.eps_ge_neg_two`; `PrefixCount.SignedMarginMatrix.sigma_sum_eq_zero`; `PrefixCount.MarginPlan.sigma_sum_eq`; `PrefixCount.MarginPlan.sigma_sum_eq_zero_of_zero_sum`; `PrefixCount.Qge2PlanBounds`; `PrefixCount.Qge2PlanBounds.step_nonneg`; `PrefixCount.MarginTransportQge2PlanGoal`; `PrefixCount.marginTransportQge2Goal_of_plan`; `oddCoreHighModulusPrefixCountGoal_of_qge2Plan_qeq1Margin_and_geometry`; `odd_modulus_tori_all_dimensions_of_qge2Plan_qeq1Margin_geometry_and_small_packet_lift` | Lean-checked in `RoundComposite/PrefixCount.lean` and `RoundComposite/OddCore.lean` | Conditional adapter |
| Q>=2 plan/matrix split | `PrefixCount.MarginPlanQge2Goal`; `PrefixCount.SignedMarginMatrixForQge2PlanGoal`; `PrefixCount.marginTransportQge2PlanGoal_of_plan_and_matrix`; `oddCoreHighModulusPrefixCountGoal_of_qge2PlanParts_qeq1PlusFamily_and_geometry`; `odd_modulus_tori_all_dimensions_of_qge2PlanParts_qeq1PlusFamily_geometry_and_small_packet_lift` | Lean-checked in `RoundComposite/PrefixCount.lean` and `RoundComposite/OddCore.lean` | Conditional adapter |
| Q=1 transport compatibility split | `PrefixCount.StepNonnegCompatibility`; `PrefixCount.StepNonnegCompatibility.step_nonneg`; `PrefixCount.MarginTransportQeq1CompatibleGoal`; `PrefixCount.marginTransportQeq1Goal_of_compatible`; `oddCoreHighModulusPrefixCountGoal_of_qge2Plan_qeq1Compat_and_geometry`; `odd_modulus_tori_all_dimensions_of_qge2Plan_qeq1Compat_geometry_and_small_packet_lift` | Lean-checked in `RoundComposite/PrefixCount.lean` and `RoundComposite/OddCore.lean` | Conditional adapter |
| Q=1 matched `±1` matrix split | `PrefixCount.PMOneBase`; `PrefixCount.PMOneBase.PlusOneMatching`; `PrefixCount.PMOneBase.upgrade_signed`; `PrefixCount.PMOneBase.upgrade_col_sum_zero`; `PrefixCount.MatchedPMOneMatrix`; `PrefixCount.MatchedPMOneMatrix.toSignedMarginMatrix`; `PrefixCount.MatchedPMOneMatrix.stepNonnegCompatibility`; `PrefixCount.MarginTransportQeq1MatchedPMOneGoal`; `PrefixCount.marginTransportQeq1CompatibleGoal_of_matchedPMOne`; `oddCoreHighModulusPrefixCountGoal_of_qge2Plan_qeq1MatchedPMOne_and_geometry`; `odd_modulus_tori_all_dimensions_of_qge2Plan_qeq1MatchedPMOne_geometry_and_small_packet_lift` | Lean-checked in `RoundComposite/PrefixCount.lean` and `RoundComposite/OddCore.lean` | Conditional adapter |
| Q=1 plus-set-family split | `PrefixCount.PMOneBase.sum_if_mem_one_neg_one`; `PrefixCount.PMOneBase.sum_if_mem_one_neg_one_eq_neg_one_of_card_half`; `PrefixCount.PMOneBase.exists_finset_card_eq_and_mem`; `PrefixCount.PMOneBase.PlusFamily`; `PrefixCount.PMOneBase.PlusFamily.nonempty`; `PrefixCount.PMOneBase.PlusFamily.toBase`; `PrefixCount.PMOneBase.PlusFamily.toMatching`; `PrefixCount.MarginTransportQeq1PlusFamilyGoal`; `PrefixCount.marginTransportQeq1MatchedPMOneGoal_of_plusFamily`; `oddCoreHighModulusPrefixCountGoal_of_qge2Plan_qeq1PlusFamily_and_geometry`; `odd_modulus_tori_all_dimensions_of_qge2Plan_qeq1PlusFamily_geometry_and_small_packet_lift` | Lean-checked in `RoundComposite/PrefixCount.lean` and `RoundComposite/OddCore.lean` | Conditional adapter |
| Root-flat geometric split | `PrefixCountRootState`; `PrefixCountRootFlatReturnGoal`; `PrefixCountRootFlatCayleyLiftGoal`; `RootFlatCayleyStepCompatible`; `PrefixCountRootFlatEquivLiftGoal`; `standardCayleySolved_of_rootFlatLayeredEquiv`; `prefixCountRootFlatCayleyLiftGoal_of_equiv`; `prefixCountGeometricCriterionGoal_of_rootFlat`; `oddCoreHighModulusPrefixCountGoal_of_qge2PlanParts_qeq1PlusFamily_and_rootFlatEquiv`; `odd_modulus_tori_all_dimensions_of_qge2PlanParts_qeq1PlusFamily_rootFlatEquiv_and_small_packet_lift` | Lean-checked in `RoundComposite/OddCore.lean` | Conditional adapter |
| General odd `d >= 13`, `m < d` | `OddCoreSmallModulusLiftOfBase` | Interface only | Open |
| Prefix-count signed foundation | `Parts`; `Parts.toMatrix`; `Parts.sum_cols_split`; `MatrixAdmissible`; `Parts.Admissible.toMatrixAdmissible`; `LayerPermCounts`; `LayerPermCounts.row_sum`; `LayerPermCounts.col_sum`; `SignedPrefixCounts`; `SignedPrefixCounts.toParts_admissible`; `QuotientTransport`; `QuotientTransport.toSigned_admissible`; `TransportQge2Goal`; `TransportQeq1Goal`; `admissiblePartsCountBranchGoal_of_transports`; `MarginPlan`; `SignedMarginMatrix`; `MarginPlan.toTransport`; `quotient_remainder_count_branch`; `signedVal_coprime_of_odd`; `pred_mod_pos_of_odd` | Lean-checked in `RoundComposite/PrefixCount.lean` | Closed foundation |
| Packet-based adapter for the small branch | `OddCoreSmallModulusOfUnitPacketsGoal`; `oddCoreSmallModulusOfBaseGoal_of_unitPackets` | Lean-checked in `RoundComposite/OddCore.lean` | Closed adapter |
| Hall-slack packet-lift endpoint for D11-small and general small branch | `OddCoreSmallModulusSlackPacketLiftGoal`; `odd_modulus_tori_all_dimensions_of_high_slack_and_small_packet_lift` | Lean-checked in `RoundComposite/OddCore.lean` | Conditional skeleton |
| Active-Hall symboling foundation for small branch | `ActiveHall.Incidence`; `ActiveHall.Incidence.colorDegree`; `ActiveHall.CountMatrix`; `ActiveHall.Symboling`; `ActiveHall.Symboling.count`; `ActiveHall.Symboling.count_row_sum`; `ActiveHall.Symboling.count_col_sum`; `ActiveHall.Symboling.toCountMatrix`; `ActiveHall.Symboling.Realizes` | Lean-checked in `RoundComposite/ActiveHall.lean`; imported by `RoundComposite.lean` | Closed foundation |
| Uniform small-base Hall-slack arithmetic witness | `seed_semigroup_base_available_with_hall_slack`; `oddCoreSmallBaseSlackWitnessGoal_of_seed_semigroup` | Lean-checked in `RoundComposite/SeedSemigroup.lean` and `RoundComposite/OddCore.lean` | Closed |
| Seed/product base availability with `2*b < d <= 3*b` | `seed_semigroup_base_available` | Lean-checked in `RoundComposite/SeedSemigroup.lean` | Closed |
| Convert `2*b < d <= 3*b` to `b` blocks of size `2` or `3` | `twoThreeBlockParts_spec` | Lean-checked in `RoundComposite/SeedSemigroup.lean` | Closed |
| Fill each `2`/`3` block with positive unit residues summing to `m` | `unitCarryPacket_spec`; `twoThreeBlockParts_unitCarryPacket_spec` | Lean-checked in `RoundComposite/SeedSemigroup.lean` | Closed |
| Aggregate the unit packets for the whole base-tail input | `unitCarryPackets_spec` | Lean-checked in `RoundComposite/SeedSemigroup.lean` | Closed |
| Package solved seed base plus unit packet data | `SmallBaseUnitPacketWitness`; `smallBaseUnitPacketWitness`; `smallBaseUnitPacketWitness_solvedBase` | Lean-checked in `RoundComposite/SeedSemigroup.lean` | Closed |
| Convert seed-semigroup base to solved base using D2/D3 | `standard_cayley_odd_uniform_of_seed_semigroup` | Lean-checked in `RoundComposite/SeedSemigroup.lean` | Closed |
| Keep `d < 29` table as audit/regression only | `docs/ODD_TORI_D_LT_29_BOUNDARY_WITNESSES_20260503.md` | Documentation explicitly marks it non-spine | Satisfied |

## Direct Evidence

The current conditional final dispatcher is:

```lean
theorem RoundComposite.Concrete.odd_modulus_tori_all_dimensions_of_main_lemmas
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hD11Small : D11SmallModulusFromD5BaseGoal)
    (hSmallLift : OddCoreSmallModulusOfBaseGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

This is intentionally conditional.  It verifies the dispatcher and reduction
architecture, not the final theorem.

The manuscript-facing active-goal dispatcher is:

```lean
theorem RoundComposite.Concrete.odd_modulus_tori_all_dimensions_of_high_slack_and_small_packet_lift
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

This shows that the D11-small branch and the general small branch can be
treated by one Hall-slack packet-level base-tail theorem.  The separate
small-base slack arithmetic witness for the general `d >= 13` small branch is
already closed in Lean.

The main new Lean files contain no `sorry`, `admit`, or explicit `axiom`:

```text
grep -RIn "sorry\|axiom\|admit" \
  RoundComposite/OddCore.lean \
  RoundComposite/SeedSemigroup.lean \
  RoundComposite/PrefixCount.lean \
  Shared/D2Seed.lean \
  Shared/D3Seed.lean \
  RoundComposite/ConcreteEndpoints.lean
```

The command currently returns no matches.

The current core Lean files also do not reference the finite boundary audit
table:

```text
grep -RIn "D_LT_29\|BOUNDARY\|169\|ODD_TORI_D_LT_29" \
  RoundComposite/OddCore.lean \
  RoundComposite/SeedSemigroup.lean \
  RoundComposite/PrefixCount.lean \
  RoundComposite/ConcreteEndpoints.lean \
  Shared/D2Seed.lean \
  Shared/D3Seed.lean
```

The command currently returns no matches.

## Verification Commands

Latest relevant checks:

```text
lake env lean Shared/D2Seed.lean
lake env lean Shared/D3Seed.lean
lake build Shared.D3Seed
lake env lean RoundComposite/ConcreteEndpoints.lean
lake env lean RoundComposite/SeedSemigroup.lean
lake build RoundComposite.PrefixCount
lake env lean RoundComposite/OddCore.lean
lake build RoundComposite.OddCore
git diff --check
```

`lake build RoundComposite.OddCore` succeeds.  It emits many pre-existing D5
lint warnings, but no errors in the new `RoundComposite` files.

These green checks do not prove the final theorem.  They only prove that the
current dispatcher, seed adapters, seed-semigroup arithmetic, and documented
interfaces elaborate without errors.

## Remaining Proof Blocks

The older refined dispatcher exposes these mathematical/Lean blocks:

1. `hHigh`:
   the prefix-count theorem
   ```lean
   OddCoreHighModulusPrefixCountGoal
   ```
   covering odd `d >= 5`, odd `m >= 3`, and `d <= m`.

2. `hD11Small`:
   the D11 small-modulus base-tail lift from the D5 seed:
   ```lean
   D11SmallModulusFromD5BaseGoal
   ```

3. `hSmallLift`:
   the general base-tail Hall-slack theorem:
   ```lean
   OddCoreSmallModulusOfBaseGoal
   ```
   It may equivalently be supplied through the packet-level interface:
   ```lean
   OddCoreSmallModulusOfUnitPacketsGoal
   ```
   because `oddCoreSmallModulusOfBaseGoal_of_unitPackets` is Lean-checked.

This older view is useful but slightly too coarse for the v2 manuscript: the
small branch should expose the Hall-slack inequalities rather than hiding them
inside a packet-only lift assumption.

The preferred manuscript-facing version is now:

1. `hHigh`:
   ```lean
   OddCoreHighModulusPrefixCountGoal
   ```

2. `hSmallPacket`:
   ```lean
   OddCoreSmallModulusSlackPacketLiftGoal
   ```

The slack packet-lift goal derives the D11 small branch with a Lean-closed
`b = 5` slack calculation.  The general small branch consumes the already
closed `OddCoreSmallBaseSlackWitnessGoal`.

Once the three refined branch goals are formalized, or equivalently once
`hHigh` and `hSmallPacket` are formalized, the current dispatcher yields the
target all-dimensional odd-modulus theorem without using the finite boundary
table.

The high branch is now further split at Lean level.  The theorem
`oddCoreHighModulusPrefixCountGoal_of_prefixCount` proves
`OddCoreHighModulusPrefixCountGoal` from:

```lean
PrefixCount.AdmissiblePartsCountBranchGoal
PrefixCountLayerRealizationGoal
PrefixCountGeometricCriterionGoal
```

So the remaining high-modulus work is no longer a single opaque block: it is
admissible parts construction, dense matrix layer decomposition,
layer-permutation realization, and the geometric prefix-count Hamilton
criterion.  The layer-realization interface is itself reduced to
`PrefixCount.MatrixLayerRealizationGoal`, and then to
`PrefixCount.BalancedMatrixLayerRealizationGoal`, a pure
permutation-decomposition statement for dense row/column count matrices with
no primitive prefix-count hypotheses.  This layer-decomposition statement is
now Lean-closed by `PrefixCount.balancedMatrixLayerRealizationGoal`, using
Hall's theorem to extract a positive permutation and induction to peel one
permutation layer at a time.

Consequently, the high-modulus public goal is now reduced to:

```lean
PrefixCount.TransportQge2Goal
PrefixCount.TransportQeq1Goal
PrefixCountGeometricCriterionGoal
```

The all-dimensional conditional endpoint has also been exposed directly in
that form:

```lean
theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_transports_geometry_and_small_packet_lift
```

It requires the two transport goals, the geometric prefix-count criterion, and
the small-modulus Hall-slack packet lift.

The transport goals are further decomposed by
`PrefixCount.admissiblePartsCountBranchGoal_of_margin`.  Thus a lower-level
high-branch path now asks for:

```lean
PrefixCount.MarginTransportQge2Goal
PrefixCount.MarginTransportQeq1Goal
PrefixCountGeometricCriterionGoal
```

The global endpoint in that shape is
`odd_modulus_tori_all_dimensions_of_margins_geometry_and_small_packet_lift`.

For the `q >= 2` branch, nonnegativity has been split out further.  Since every
signed correction entry is at least `-2`, `Qge2PlanBounds.step_nonneg` proves
the per-cell condition from the row bound `2 <= q - tau i`.  The current
lowest-level high-modulus endpoint therefore asks for:

```lean
PrefixCount.MarginTransportQge2PlanGoal
PrefixCount.MarginTransportQeq1Goal
PrefixCountGeometricCriterionGoal
```

and the global endpoint in that shape is
`odd_modulus_tori_all_dimensions_of_qge2Plan_qeq1Margin_geometry_and_small_packet_lift`.

For the `q = 1` branch, `StepNonnegCompatibility.step_nonneg` now isolates the
exact row-local restrictions needed for nonnegativity:

```text
q - tau = 0  -> eps >= 0
q - tau = 1  -> eps >= -1
q - tau >= 2 -> automatic from eps >= -2
```

The corresponding global endpoint is
`odd_modulus_tori_all_dimensions_of_qge2Plan_qeq1Compat_geometry_and_small_packet_lift`.

The q=1 branch has also been reduced to the matched `±1` certificate shape:

```text
PMOneBase:             entries are ±1 and every column sums to -1
PlusOneMatching:       one explicit +1 is chosen in each column
matched upgrade:       chosen +1 entries become +2, so column sums become 0
zero-row compatibility: rows with q - tau = 0 have no negative base entries
```

The corresponding global endpoint is
`odd_modulus_tori_all_dimensions_of_qge2Plan_qeq1MatchedPMOne_geometry_and_small_packet_lift`.

Finally, the matched `±1` base can now be generated from plus-set families:

```text
plus k has cardinality (d-1)/2 -> the ±1 column sum is -1, since d is odd
mate k in plus k                -> the matched entry is +1 before upgrade
injective mate                  -> the matching certificate is explicit
```

Lean also proves `PMOneBase.PlusFamily.nonempty`, so this certificate layer is
not empty.  The still-open q=1 work is to choose plus sets and row margins whose
upgraded row sums match `P.sigma` and satisfy the zero-row restriction.

The corresponding global endpoint is
`odd_modulus_tori_all_dimensions_of_qge2Plan_qeq1PlusFamily_geometry_and_small_packet_lift`.

For q>=2, the bundled margin transport goal has been split into a row-margin
plan goal and a signed matrix realization goal.  The corresponding global
endpoint is
`odd_modulus_tori_all_dimensions_of_qge2PlanParts_qeq1PlusFamily_geometry_and_small_packet_lift`.

The geometric criterion has also been split into root-flat return construction
and an equivalence-level root-flat-to-Cayley coordinate lift.  Lean proves that
the equivalence plus one-step compatibility yields the Cayley endpoint.  The
corresponding global endpoint is
`odd_modulus_tori_all_dimensions_of_qge2PlanParts_qeq1PlusFamily_rootFlatEquiv_and_small_packet_lift`.

## Verdict

Not complete.  The proof spine is now Lean-checked and the finite-boundary
table has been removed from the intended proof path, but the final theorem is
still conditional on the high-modulus prefix-count branch and the Hall-slack
packet-lift branch.
