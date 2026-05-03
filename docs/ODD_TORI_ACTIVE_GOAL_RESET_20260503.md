# Odd-Modulus Tori Active Goal Reset

Date: 2026-05-03.

This note records the current target after the D2 review and the
`prefix_count_odd_tori_overhauled_v2_submission_bundle (1).zip` absorption.
It supersedes the older finite-boundary framing.

Correction after the first reset: the manuscript-facing small branch must
explicitly expose the Hall-slack hypotheses `d - b > b` and
`m^b > m*d*(d-b)`.  Packet data alone is a useful strong interface, but it is
not the exact v2 proof spine.

## Final Target

Formalize the all-dimensional odd-modulus theorem:

```lean
theorem odd_modulus_tori_all_dimensions
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

Equivalently, for every `d >= 2` and every odd `m >= 3`, prove a directed
Hamilton decomposition of the standard directed Cayley torus
`Cay((ZMod m)^d, {e_0, ..., e_{d-1}})`.

The `d < 29` finite boundary table is no longer a main proof input.  It should
remain an audit and regression artifact only.

## Proof Spine

The intended proof has three levels.

1. All-dimensional wrapper.

   Use the D2 seed and product lift to reduce every even dimension to a
   smaller dimension.  Thus the hard construction is the odd-dimensional core.

2. Odd-dimensional core.

   Close the small odd dimensions by seeds and products:

   - `d = 3`: D3 seed.
   - `d = 5`: existing D5 odd seed.
   - `d = 7`: existing D7 odd seed.
   - `d = 9`: product `D3 * D3`.
   - `d = 11`: high-modulus prefix-count for `m >= 11`, and small-modulus
     base-tail lift from the solved D5 base for `m < 11`.

3. Uniform odd dimensions `d >= 13`.

   Split by modulus size:

   - if `m >= d`, use the high-modulus prefix-count construction;
   - if `m < d`, choose a solved seed-semigroup base `b` generated from D2 and
     D3 with `2*b < d <= 3*b`, then apply the base-tail unit-packet lift.

The seed-semigroup and packet arithmetic is already Lean-checked.  The
remaining small-modulus content should be proved as a construction theorem,
with the Hall-slack arithmetic exposed separately, not as a
dimension-by-dimension finite boundary table.

## Current Lean Boundary

The manuscript-facing conditional endpoint is now:

```lean
theorem RoundComposite.Concrete.odd_modulus_tori_all_dimensions_of_high_slack_and_small_packet_lift
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hSmallPacket : OddCoreSmallModulusSlackPacketLiftGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

So the active goal is now two remaining theorem families.  The small-base
Hall-slack arithmetic witness is already Lean-closed.

## Remaining Theorem 1: High Modulus

```lean
def RoundComposite.Concrete.OddCoreHighModulusPrefixCountGoal : Prop :=
  ∀ {d m : Nat}, Odd d → 5 <= d → Odd m → d <= m →
    StandardCayleySolved d m
```

This is the prefix-count/count-matrix branch.  It should cover all odd
dimensions `d >= 5` when the odd modulus satisfies `m >= d`.  In the final
dispatch it supplies:

- `d = 11, m >= 11`;
- all odd `d >= 13, m >= d`;
- it may also cover D5 and D7 redundantly, although the seeds already close
  those dimensions.

## Closed Arithmetic: Small-Base Hall-Slack Witness

```lean
def RoundComposite.Concrete.OddCoreSmallBaseSlackWitnessGoal : Prop :=
  ∀ {d m : Nat},
    Odd d → 13 <= d →
    Odd m → 3 <= m → m < d →
    ∃ w : SmallBaseUnitPacketWitness d m,
      d - w.b > w.b ∧
      m ^ w.b > m * d * (d - w.b)
```

This is the uniform arithmetic part of the small branch.  The witness already
contains the solved seed-semigroup base `b`, the unit-packet list, and the
packet facts.  This theorem adds the Hall-slack inequalities needed by the v2
base-tail proof.

Lean now proves this goal by `seed_semigroup_base_available_with_hall_slack`
and `oddCoreSmallBaseSlackWitnessGoal_of_seed_semigroup`.

## Remaining Theorem 2: Small Modulus Hall-Slack Packet Lift

```lean
def RoundComposite.Concrete.OddCoreSmallModulusSlackPacketLiftGoal : Prop :=
  ∀ {d m b : Nat},
    Odd d → 11 <= d →
    Odd m → 3 <= m → m < d →
    StandardCayleySolved b m →
    (packets : List (List Nat)) →
    packets.length = b →
    (packets.map List.length).sum = d →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    d - b > b →
    m ^ b > m * d * (d - b) →
    StandardCayleySolved d m
```

This is the unified base-tail theorem.  It simultaneously supplies:

- the D11 small branch, by taking `b = 5` and the generated packet list for
  `(d,b) = (11,5)`.  The D11 Hall-slack arithmetic is already closed in Lean;
- the general odd `d >= 13, m < d` branch, by taking the seed-semigroup base
  `b` supplied by the closed `OddCoreSmallBaseSlackWitnessGoal`.

This is now the preferred Lean-facing form of the small branch.  The older
interfaces

```lean
D11SmallModulusFromD5BaseGoal
OddCoreSmallModulusOfBaseGoal
OddCoreSmallModulusOfUnitPacketsGoal
```

remain useful local views, but they are derivable from the unified packet-lift
goal only when their missing slack hypotheses are supplied.  In the current
manuscript-facing dispatcher, the D11 goal is derived directly from the
slack-packet lift, while the general small branch bypasses the older
`OddCoreSmallModulusOfBaseGoal` interface and consumes
the closed `OddCoreSmallBaseSlackWitnessGoal`.  The stronger packet-only endpoint
`odd_modulus_tori_all_dimensions_of_high_and_small_packet_lift` is retained as
a convenience, but the Hall-slack endpoint above is the accurate v2 target.

## Already Closed in Lean

- D2 seed and all-dimensional product wrapper.
- D3 seed adapter.
- Existing D5 and D7 odd endpoints.
- D9 as `D3 * D3`.
- Seed-semigroup base availability for odd `d >= 13`.
- Decomposition of `2*b < d <= 3*b` into `b` blocks of sizes `2` and `3`.
- Unit packet construction for each size-`2` or size-`3` block.
- Aggregated packet witness and adapters from packet data to the older
  base-tail interface.
- Uniform seed-semigroup base availability with Hall slack:
  `seed_semigroup_base_available_with_hall_slack`.
- `OddCoreSmallBaseSlackWitnessGoal`, derived from that arithmetic theorem.
- D11-specific Hall-slack arithmetic for `b = 5`, exposed through the adapter
  from `OddCoreSmallModulusSlackPacketLiftGoal` to
  `D11SmallModulusFromD5BaseGoal`.
- Prefix-count foundation module `RoundComposite/PrefixCount.lean`, including
  `Parts`, `SignedPrefixCounts`, `signedVal_coprime_of_odd`,
  `SignedPrefixCounts.toParts_admissible`, `one_le_div_pred_of_le`, and
  `pred_mod_pos_of_odd`.
- The first dense-matrix bridge for prefix-count parts:
  `Parts.toMatrix`, `Parts.toMatrix_colZero`, `Parts.toMatrix_colDelta`, and
  `Parts.toMatrix_colStep`.
- Dense matrix admissibility bridge:
  `MatrixAdmissible`, `Parts.sum_cols_split`, and
  `Parts.Admissible.toMatrixAdmissible`.
- Layer-count realization interface:
  `LayerPermCounts`, `LayerPermCounts.row_sum`, `LayerPermCounts.col_sum`,
  and `LayerPermCounts.toMatrixAdmissible`.
- `QuotientTransport` and `QuotientTransport.toSigned_admissible`, giving the
  algebraic bridge from quotient/remainder transportation data to admissible
  prefix-count data.
- `MarginPlan`, `SignedMarginMatrix`, and `MarginPlan.toTransport`, splitting
  the remaining high-modulus signed-transport construction into row-margin
  arithmetic, signed correction matrix construction, and per-cell
  nonnegativity.
- Quotient/remainder branch arithmetic for the count branch, including
  `quotient_remainder_count_branch`, `quotient_one_or_ge_two_of_le`, and the
  `q = 1` upper-bound helper `quotient_eq_one_upper_bound`.

## Revised Goal in One Sentence

Prove all `d >= 2`, odd `m >= 3` by D2/product reduction to the odd core,
then close the odd core with the high-modulus prefix-count theorem and the
Hall-slack base-tail unit-packet lift theorem; keep the `d < 29` table only as
audit evidence.
