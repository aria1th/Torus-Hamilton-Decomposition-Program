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
| General odd `d >= 13`, `m < d` | `OddCoreSmallModulusLiftOfBase` | Interface only | Open |
| Prefix-count signed foundation | `Parts`; `SignedPrefixCounts`; `SignedPrefixCounts.toParts_admissible`; `QuotientTransport`; `QuotientTransport.toSigned_admissible`; `MarginPlan`; `SignedMarginMatrix`; `MarginPlan.toTransport`; `signedVal_coprime_of_odd`; `pred_mod_pos_of_odd` | Lean-checked in `RoundComposite/PrefixCount.lean` | Closed foundation |
| Packet-based adapter for the small branch | `OddCoreSmallModulusOfUnitPacketsGoal`; `oddCoreSmallModulusOfBaseGoal_of_unitPackets` | Lean-checked in `RoundComposite/OddCore.lean` | Closed adapter |
| Hall-slack packet-lift endpoint for D11-small and general small branch | `OddCoreSmallModulusSlackPacketLiftGoal`; `odd_modulus_tori_all_dimensions_of_high_slack_and_small_packet_lift` | Lean-checked in `RoundComposite/OddCore.lean` | Conditional skeleton |
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

## Verdict

Not complete.  The proof spine is now Lean-checked and the finite-boundary
table has been removed from the intended proof path, but the final theorem is
still conditional on the high-modulus prefix-count branch and the Hall-slack
packet-lift branch.
