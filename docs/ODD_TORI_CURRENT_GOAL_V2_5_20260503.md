# Odd-Modulus Tori Current Goal v2.5

Date: 2026-05-03.

This note records the current goal after the `d < 29` boundary review, the D2
all-dimensional wrapper correction, the D3/D5/D7 seed audit, the D9 product
seed, the high-prefix-count split, the q=1 compatibility split and
plus-family obstruction audit, the canonical root-flat lift, and the first
Active-Hall slack interface.

It supersedes `docs/ODD_TORI_CURRENT_GOAL_V2_4_20260503.md` as the concise
active-goal reference.

## Final Target

Formalize the all-dimensional odd-modulus theorem:

```lean
theorem odd_modulus_tori_all_dimensions
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

Equivalently, every standard directed Cayley torus
`Cay((ZMod m)^d, {e_0, ..., e_{d-1}})` has a directed Hamilton decomposition
for every `2 <= d`, odd `m`, and `3 <= m`.

The target is all dimensions, not only odd dimensions.  The even-dimensional
part is handled by the D2 seed and product wrapper.  The hard construction is
the odd-dimensional core.

## Main Reset

The `d < 29` finite boundary table is not a theorem-level input.  It remains
useful as audit, regression, and search evidence, but the final proof spine
should not import it.

In particular, `(d, m) = (13, 3)` is not a distinguished endpoint.  The earlier
apparent gap disappears from the theorem spine once D2 and D3 are available as
seed/product bases and the uniform small-modulus Hall-slack packet lift is
proved.  The same applies to the other former finite-boundary pairs.

The proof spine is now:

```text
D2 seed and product wrapper
+ odd-dimensional seeds D3, D5, D7
+ D9 as D3 * D3
+ D11 from high-prefix-count for m >= 11 and D5-base packet lift for m < 11
+ high-modulus prefix-count theorem for odd d >= 5, m >= d
+ small-modulus Hall-slack packet lift for odd d >= 11, m < d
```

For odd `d >= 13` and `m < d`, the small branch chooses a solved
seed-semigroup base `b`, generated from D2 and D3, and uses the already
Lean-closed arithmetic witnesses

```text
d - b > b
m^b > m*d*(d-b)
```

together with unit-packet data.  The remaining non-arithmetic content is the
uniform base-tail/Hall-slack lift theorem.

## Current Lean Endpoints

The manuscript-facing conditional endpoint is:

```lean
theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_high_slack_and_small_packet_lift
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

The preferred lowest-level endpoint currently exposes four remaining
assumptions:

```lean
theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_qge2Compat_qeq1Compat_rootFlatCanonical_and_small_packet_lift
    (hQge2 : PrefixCount.MarginTransportQge2CompatibleGoal)
    (hQeq1 : PrefixCount.MarginTransportQeq1CompatibleGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

Thus the active goal is to remove exactly these four preferred assumptions.

The older q>=2 endpoints involving global `Qge2PlanBounds` or arbitrary
`SignedMarginMatrixForQge2PlanGoal` are retained as compatibility adapters,
not as the preferred target.  Lean records the obstruction to the global
`Qge2PlanBounds` formulation in `Qge2PlanBounds.not_for_q_two_r_one`: for
`q = 2, r = 1`, the required global bounds are incompatible with the natural
`tau_sum = q - r` value.  The safe q>=2 target is therefore
`MarginTransportQge2CompatibleGoal`, or equivalently the direct
`MarginTransportQge2Goal`.

Correction after the q=1 obstruction audit: the older
`MarginTransportQeq1PlusFamilyGoal` endpoint is no longer a preferred target.
Lean proves `PrefixCount.not_marginTransportQeq1PlusFamilyGoal`, by
instantiating the `q = 1, r = 1, d = m = 5` boundary.  The plus-family layer
remains useful as a diagnostic and partial certificate layer, but it cannot be
the global q=1 theorem family.

## Remaining Blocks

1. `PrefixCount.MarginTransportQge2CompatibleGoal`

   Construct the q>=2 row-margin plan, signed correction matrix, and exact
   low-delta compatibility proof together.  The Lean side already records the
   signed-row necessary bounds and the adapter from step nonnegativity to
   compatibility.  The remaining proof should be a feasible transport
   construction, not the too-strong global `Qge2PlanBounds` statement.

2. `PrefixCount.MarginTransportQeq1CompatibleGoal`

   Close the q=1 high-modulus boundary through a compatible margin plan and
   signed correction matrix.  This replaces the over-specific plus-family
   target.

   Lean records why the old plus-family target cannot be the final q=1 goal:
   `PrefixCount.not_marginTransportQeq1PlusFamilyGoal`, and locally
   `PlusFamily.not_all_upgraded_row_sum_zero`.  A pure plus-family upgrade
   cannot make every upgraded row sum vanish when `d` is odd and `5 <= d`,
   because at least one row is outside the mate image and would force
   `2 * card = d - 2`.  In fact the global plus-family goal itself is
   inconsistent at `d = m = 5`, `q = r = 1`.

   The q=1 branch therefore needs either a direct compatible signed transport
   construction or a richer certificate interface than pure plus-family
   upgrade.

   The local form is also Lean-recorded: `PlusFamily.rowMateSet_card_le_one`,
   `PlusFamily.rowMateSet_card_eq_one_of_mate`,
   `PlusFamily.rowMateSet_card_eq_zero_of_not_mate`,
   `PlusFamily.upgraded_row_sum_of_not_mate`, and
   `PlusFamily.upgraded_row_sum_ne_zero_of_not_mate`.

3. `PrefixCountRootFlatCanonicalReturnGoal`

   Build the canonical root-flat prefix-count certificate.  The Cayley lift
   from a canonical-step certificate is already Lean-closed; what remains is
   the certificate itself: row Latin, layer bijectivity, single-cycle color
   returns, and
   `cert.schedule.step = prefixCountRootStep d m`.

4. `OddCoreSmallModulusSlackPacketLiftGoal`

   Prove the uniform small-modulus base-tail theorem from a solved base, unit
   packets, and Hall-slack inequalities.  The current Lean split goes through
   Active-Hall: construct feasible residue count matrices with Hall cuts,
   prove the Hall/Hoffman realization theorem, then translate active
   symbolings into unit carries and the base-tail Hamilton lift.

## Already Lean-Closed Support

- D2 seed and all-dimensional product wrapper.
- D3 seed, D5 seed, D7 seed, and D9 as `D3 * D3`.
- Seed-semigroup base availability for odd `d >= 13`.
- Unit-packet construction and Hall-slack arithmetic witnesses, including the
  D11 `b = 5` adapter.
- Dense matrix layer realization for balanced count matrices.
- Prefix-count quotient/remainder interfaces and margin-facing adapters.
- Q>=2 nonnegativity adapter, signed-row necessary bounds, and the explicit
  obstruction to global `Qge2PlanBounds`.
- Q=1 range arithmetic, compatibility, matched `+/-1`, plus-family adapters,
  row-plus-set formulas, row-mate-set formulas, upgraded row sums, and
  matched upgraded row sums, plus the no-all-zero upgraded-row obstruction for
  odd `d >= 5`, its row-local non-mate form, and the global
  `not_marginTransportQeq1PlusFamilyGoal` obstruction.
- Root-flat equivalence and canonical-step Cayley lifts.
- Active-Hall foundation: feasible residues, symbolings with residues,
  Hall-realization interface, color-degree double counting, full-set cut
  cap/mass and equality reductions, empty/full cut reductions, nontrivial
  Hall-cut reduction, cut cap/mass monotonicity, residue compatibility from
  feasible matrices, and the sanity converse from symbolings back to feasible
  residue count matrices.

## Non-Goals

- Do not prove the final theorem by importing the `d < 29` finite boundary
  table.
- Do not treat `(13, 3)` as a special certificate target unless the uniform
  small-modulus packet-lift theorem genuinely fails.
- Do not include Route E or even-modulus work in the active goal.
- Do not reopen D7 as a construction target; use the existing D7 odd endpoint
  as a seed.

## Success Criterion

The goal is complete only when the repository contains the non-conditional
Lean theorem

```lean
theorem odd_modulus_tori_all_dimensions
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

with no branch assumptions.  Until then, the current endpoint should be read
as a checked reduction to the four preferred theorem families above.

## One-Sentence Goal

Close all `d >= 2` and odd `m >= 3` by proving the high-modulus prefix-count
construction and the small-modulus Hall-slack packet-lift construction after
D2/product and odd-seed reductions, without using the `d < 29` finite boundary
table as a theorem-level input.
