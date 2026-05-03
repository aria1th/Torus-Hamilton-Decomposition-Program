# Odd-Modulus Tori Active Goal Reset

Date: 2026-05-03.

This note records the current target after the D2 review and the
`prefix_count_odd_tori_overhauled_v2_submission_bundle (1).zip` absorption.
It supersedes the older finite-boundary framing.

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
not as a dimension-by-dimension finite boundary table.

## Current Lean Boundary

The most compressed conditional endpoint is now:

```lean
theorem RoundComposite.Concrete.odd_modulus_tori_all_dimensions_of_high_and_small_packet_lift
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hSmallPacket : OddCoreSmallModulusUnitPacketLiftGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

So the active goal can be stated as two remaining theorem families.

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

## Remaining Theorem 2: Small Modulus Unit-Packet Lift

```lean
def RoundComposite.Concrete.OddCoreSmallModulusUnitPacketLiftGoal : Prop :=
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
    StandardCayleySolved d m
```

This is the unified base-tail theorem.  It simultaneously supplies:

- the D11 small branch, by taking `b = 5` and the generated packet list for
  `(d,b) = (11,5)`;
- the general odd `d >= 13, m < d` branch, by taking the seed-semigroup base
  `b` with `2*b < d <= 3*b` and the generated unit-packet list.

This is now the preferred Lean-facing form of the small branch.  The older
interfaces

```lean
D11SmallModulusFromD5BaseGoal
OddCoreSmallModulusOfBaseGoal
OddCoreSmallModulusOfUnitPacketsGoal
```

remain useful local views, but they are derivable from the unified packet-lift
goal where needed.

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

## Revised Goal in One Sentence

Prove all `d >= 2`, odd `m >= 3` by D2/product reduction to the odd core,
then close the odd core with the high-modulus prefix-count theorem and one
unified small-modulus base-tail unit-packet lift theorem; keep the `d < 29`
table only as audit evidence.
