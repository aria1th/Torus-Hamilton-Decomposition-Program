# Odd-Modulus Tori Current Goal v2.4

Date: 2026-05-03.

This is the current goal after the D2/product-wrapper review, the
`d < 29` boundary review, the q=1 plus-family split, the canonical root-flat
lift, and the first Active-Hall residue-symboling split.

It supersedes `docs/ODD_TORI_CURRENT_GOAL_V2_3_20260503.md` as the concise
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
part is handled by the D2 seed and product wrapper; the difficult construction
is the odd-dimensional core.

## Main Strategic Reset

The `d < 29` finite boundary table is no longer a theorem-level input.  It
should remain only as audit, regression, and search evidence.

The proof should not isolate `(d, m) = (13, 3)` as a special endpoint.  That
pair and the rest of the former finite boundary list are intended to be
absorbed by the uniform small-modulus Hall-slack packet-lift theorem.

The proof spine is now:

```text
D2 seed and product wrapper
+ odd-dimensional core seeds D3, D5, D7
+ D9 as D3 * D3
+ D11 from high-prefix-count for m >= 11 and D5-base packet lift for m < 11
+ high-modulus prefix-count theorem for odd d >= 5, m >= d
+ small-modulus Hall-slack packet lift for odd d >= 11, m < d
```

For odd `d >= 13` and `m < d`, the small branch uses a solved seed-semigroup
base `b`, generated from D2 and D3, together with the closed arithmetic
witnesses

```text
d - b > b
m^b > m*d*(d-b)
```

and unit packet data.

## Current Lean Endpoint

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

The preferred lowest-level Lean endpoint currently exposes four remaining
assumptions:

```lean
theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_qge2Margin_qeq1PlusFamily_rootFlatCanonical_and_small_packet_lift
    (hQge2 : PrefixCount.MarginTransportQge2Goal)
    (hQeq1 : PrefixCount.MarginTransportQeq1PlusFamilyGoal)
    (hReturn : PrefixCountRootFlatCanonicalReturnGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

So the active goal is to remove exactly these four preferred assumptions.

The older endpoint
`odd_modulus_tori_all_dimensions_of_qge2PlanParts_qeq1PlusFamily_rootFlatCanonical_and_small_packet_lift`
is retained as a compatibility adapter, but it is no longer preferred.  Its
split assumption `SignedMarginMatrixForQge2PlanGoal` asks for a signed matrix
for every `MarginPlan` satisfying only `Qge2PlanBounds`.  That is too broad
unless the plan interface is strengthened with matrix-feasibility constraints
such as zero-column sum and signed row bounds.  The safe q>=2 target is
therefore `MarginTransportQge2Goal`, which constructs the margin plan, signed
matrix, and per-cell nonnegativity together.

The intermediate `MarginTransportQge2PlanGoal` is also a compatibility layer
rather than the preferred target: its global `Qge2PlanBounds` condition is too
strong for cases such as `q = 2, r = 1`, where `tau_sum = q-r = 1` but
`2 <= q - tau i` would force every `tau i <= 0`.

## Remaining Blocks

1. `PrefixCount.MarginTransportQge2Goal`

   Construct q>=2 row-margin plans, signed correction matrices, and the
   per-cell nonnegativity proof directly.  The Lean side now records the
   necessary row bounds
   `SignedMarginMatrix.neg_two_mul_le_row_sum` and
   `SignedMarginMatrix.row_sum_le_two_mul`; any further split must ensure
   those bounds and the exceptional low-delta cases are part of the plan-side
   feasibility data.

2. `PrefixCount.MarginTransportQeq1PlusFamilyGoal`

   Close the high-modulus q=1 boundary.  The remaining content is the
   coordinated choice of row margins and plus sets of size `(d-1)/2`, with
   injective mates inside the plus sets.  Plus-family nonemptiness alone is
   not enough; the choices must satisfy the margin transport constraints.

3. `PrefixCountRootFlatCanonicalReturnGoal`

   Build the canonical root-flat prefix-count certificate.  The Cayley lift
   from a canonical-step certificate is already Lean-closed; what remains is
   the certificate itself: row Latin, layer bijectivity, single-cycle color
   returns, and
   `cert.schedule.step = prefixCountRootStep d m`.

4. `OddCoreSmallModulusSlackPacketLiftGoal`

   Prove the uniform base-tail lift from a solved base, unit packets, and
   Hall-slack inequalities.  The current split goes through Active-Hall:
   construct feasible residue count matrices with Hall cuts, prove the
   Hall/Hoffman realization theorem, then translate the active symboling
   residues into unit carries and the base-tail Hamilton lift.

## Already Lean-Closed Support

- D2 seed and all-dimensional product wrapper.
- D3 seed, D5 seed, D7 seed, and D9 as `D3 * D3`.
- Seed-semigroup base availability for odd `d >= 13`.
- Unit packet construction and Hall-slack arithmetic witnesses, including the
  D11 `b = 5` adapter.
- Dense matrix layer realization for balanced count matrices.
- Prefix-count quotient/remainder interfaces and margin-facing adapters.
- Q>=2 nonnegativity adapter and signed-row necessary bounds.
- Q=1 range arithmetic, compatibility, matched `+/-1`, and plus-family
  adapters.
- Root-flat equivalence and canonical-step Cayley lifts.
- Active-Hall foundation: feasible residues, symbolings with residues,
  Hall-realization interface, and the sanity converse from symbolings back to
  feasible residue count matrices.

## Non-Goals

- Do not prove the final theorem by importing the `d < 29` finite boundary
  table.
- Do not treat `(13, 3)` as a special certificate target unless the uniform
  small-modulus packet-lift theorem genuinely fails.
- Do not include Route E or even-modulus work in the active goal.
- Do not reopen D7 as a construction target; use the existing D7 odd endpoint
  as a seed.

## One-Sentence Goal

Close all `d >= 2` and odd `m >= 3` by proving the high-modulus prefix-count
construction and the small-modulus Hall-slack packet-lift construction after
D2/product and odd-seed reductions, without using the `d < 29` finite boundary
table as a theorem-level input.
