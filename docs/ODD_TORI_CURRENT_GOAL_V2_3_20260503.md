# Odd-Modulus Tori Current Goal v2.3

Date: 2026-05-03.

This is the current working goal after the `d < 29` boundary review, the
D2/product-wrapper review, the q=1 plus-family split, the root-flat geometry
split, and the first Active-Hall residue-symboling interface.

It supersedes `docs/ODD_TORI_CURRENT_GOAL_V2_2_20260503.md` as the concise
goal reference.

## Final Target

Prove the all-dimensional odd-modulus theorem:

```lean
theorem odd_modulus_tori_all_dimensions
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

Equivalently, every standard directed torus
`Cay((ZMod m)^d, {e_0, ..., e_{d-1}})` has a directed Hamilton decomposition
when `2 <= d`, `Odd m`, and `3 <= m`.

## Main Strategic Reset

The `d < 29` finite boundary table is not a theorem-level input in the current
proof spine.  It remains audit/regression evidence only.

The proof should not single out `(d,m) = (13,3)`.  That pair, and the rest of
the former finite boundary list, are meant to be absorbed by the uniform
small-modulus Hall-slack packet-lift theorem.

The revised proof spine is:

```text
D2 seed and product wrapper
+ odd-dimensional core seeds D3, D5, D7
+ D9 as D3 * D3
+ D11 from high-prefix-count for m >= 11 and D5-base packet lift for m < 11
+ high-modulus prefix-count theorem for odd d >= 5, m >= d
+ small-modulus Hall-slack packet lift for odd d >= 11, m < d
```

## Current Lean Endpoint

The public all-dimensional theorem is reduced to two manuscript-level theorem
families:

```lean
OddCoreHighModulusPrefixCountGoal
OddCoreSmallModulusSlackPacketLiftGoal
```

The current preferred lowest-level Lean endpoint is:

```lean
theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_qge2PlanParts_qeq1PlusFamily_rootFlatCanonical_and_small_packet_lift
    (hQge2Plan : PrefixCount.MarginPlanQge2Goal)
    (hQge2Matrix : PrefixCount.SignedMarginMatrixForQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

The older compatibility endpoint is still available:

```lean
theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_qge2PlanParts_qeq1PlusFamily_rootFlatEquiv_and_small_packet_lift
    (hQge2Plan : PrefixCount.MarginPlanQge2Goal)
    (hQge2Matrix : PrefixCount.SignedMarginMatrixForQge2PlanGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hReturn : PrefixCountRootFlatReturnGoal)
    (hEquiv : PrefixCountRootFlatEquivLiftGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

So the active Lean goal is now to remove the five preferred assumptions:
q>=2 row margin plans, q>=2 signed matrix realization, q=1 plus-family
margins, canonical root-flat return construction, and the small-modulus
Hall-slack packet lift.

## Remaining Blocks

1. `PrefixCount.MarginPlanQge2Goal`

   Construct q>=2 row-margin plans with `Qge2PlanBounds`, giving the rowwise
   lower bound `2 <= q - tau i`.

2. `PrefixCount.SignedMarginMatrixForQge2PlanGoal`

   Realize the q>=2 signed correction matrix for each margin plan.  The
   existing Lean adapter then gets nonnegativity from the universal bound
   `eps >= -2`.

3. `PrefixCount.MarginTransportQeq1PlusFamilyGoal`

   Close the high-modulus q=1 boundary through plus-family certificates.  The
   local target is now a family of plus sets of size `(d-1)/2`, with injective
   mates inside the plus sets, so that the matched `±1` matrix upgrades to the
   required nonnegative correction.

4. `PrefixCountRootFlatCanonicalReturnGoal`

   Prove the root-flat return part of the prefix-count geometric theorem with
   the canonical root step exposed:
   admissible prefix counts and layer permutations give a root-flat certificate
   with row Latin, layer bijectivity, single-cycle color returns, and
   `cert.schedule.step = prefixCountRootStep d m`.  Lean now proves the Cayley
   lift from this canonical-step certificate through
   `prefixCountRootLayerEquiv`, `prefixCountRootLayerEquiv_step`,
   `standardCayleySolved_of_rootFlatLayered_standardStep`, and
   `prefixCountGeometricCriterionGoal_of_rootFlatCanonical`.

5. `OddCoreSmallModulusSlackPacketLiftGoal`

   Prove the uniform small-modulus base-tail lift from a solved base, unit
   packets, and Hall-slack inequalities.  The arithmetic witnesses are
   Lean-closed; the remaining content is the construction and proof of the
   lift.

Legacy note: `PrefixCountRootFlatReturnGoal` and
`PrefixCountRootFlatEquivLiftGoal` remain as older compatibility interfaces.
They are no longer the preferred target because the arbitrary-`D` equivalence
formulation is stronger than the actual geometric need.

## Small Branch Internal Split

The small branch is now being factored through an Active-Hall layer:

```lean
ActiveHall.FeasibleWithResidues
ActiveHall.SymbolingWithResidues
ActiveHall.HallRealizationGoal
ActiveHall.symbolingWithResidues_of_feasible_and_realization
ActiveHall.feasibleWithResidues_of_symbolingWithResidues
```

This isolates two different tasks:

1. Build a feasible count matrix with the required residues and Hall cuts from
   the Hall-slack packet data.

2. Prove the Hall/Hoffman realization theorem turning such a count matrix into
   an active symboling.

After those are available, the packet-lift proof still needs the final
translation from active symboling residues to unit carries and then to the
base-tail Hamilton lift.

## Closed Support

Already Lean-checked support includes:

- D2 seed and all-dimensional product wrapper.
- D3 seed, D5 seed, D7 seed, and D9 as `D3 * D3`.
- Seed-semigroup base availability for odd `d >= 13`.
- Unit packet construction and Hall-slack arithmetic witnesses.
- D11-specific `b = 5` Hall-slack arithmetic adapter.
- Dense matrix layer realization for balanced count matrices.
- Prefix-count quotient/remainder interfaces and margin-facing adapters.
- Q>=2 nonnegativity adapter.
- Q=1 compatibility, matched `±1`, and plus-family adapters.
- Root-flat split of the prefix-count geometric criterion, including the
  equivalence-to-Cayley lift adapter, the successor-indexed canonical root-step
  Cayley lift, the `d`-indexed canonical root-step wrapper, and the preferred
  canonical-return geometric adapter.
- Active-Hall symboling foundation: incidence data, symbolings, count
  matrices, residue specifications, row/column count lemmas, Hall cuts, and
  the feasible-residue to symboling adapter conditional on Hall realization,
  plus the converse sanity adapter from symbolings back to feasible residue
  count matrices.

## Non-Goals

- Do not prove the final theorem by importing the `d < 29` finite boundary
  table.
- Do not treat `(13,3)` as a special certificate target unless the uniform
  small-modulus packet-lift theorem fails.
- Do not include Route E or even-modulus work in the active goal.
- Do not reopen D7 as a construction target; use the existing D7 odd endpoint
  as a seed.

## One-Sentence Goal

Close all `d >= 2` and odd `m >= 3` by proving the high-modulus prefix-count
construction and the small-modulus Hall-slack packet-lift construction after
D2/product and odd-seed reductions, with the high branch currently split into
q>=2 margin plans, q>=2 signed matrices, q=1 plus-family margins, and a
canonical-step root-flat return certificate, and with the small branch now
split through Active-Hall feasible residues plus Hall realization.
