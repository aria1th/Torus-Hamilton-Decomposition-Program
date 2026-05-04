# GPT-5.5 Pro Successor-Small Geometry-From-Hall Request

Date: 2026-05-04.

Purpose: ask for a Lean-facing proof plan for the remaining successor-small
geometry theorem
`RoundComposite.Concrete.OddSuccessorSmallModulusBaseTailGeometryFromHallGoal`.

Model settings requested by the user:

```text
model: gpt-5.5-pro
reasoning effort: xhigh
max_output_tokens: 100000
mode: background
```

Response id:

```text
response_id = resp_01731cacc08aae120069f8eb3bbeec819d8a723b1647b82643
initial_status = queued
initial_submit_date = 2026-05-04
latest_poll_status = in_progress
latest_poll_date = 2026-05-04
final_status = pending
final_poll_date = pending
response_doc = docs/GPT55_PRO_SUCCESSOR_SMALL_GEOMETRY_FROM_HALL_RESPONSE_20260504.md
```

## Files To Read

1. `RoundComposite/OddCore.lean`
2. `RoundComposite/ActiveHall.lean`
3. `docs/GPT55_PRO_SUCCESSOR_SMALL_BASE_TAIL_RESPONSE_20260504.md`
4. `docs/ODD_TORI_CURRENT_GOAL_V3_4_20260504.md`
5. `/data/angel/repos/etc/prefix_count_odd_tori_overhauled_v7.tex`

## Current Lean Target

The target is:

```lean
def RoundComposite.Concrete.OddSuccessorSmallModulusBaseTailGeometryFromHallGoal
    : Prop :=
  ActiveHall.HallRealizationGoal.{0, 0} ->
    OddSuccessorSmallModulusSlackPacketLiftAddGoal
```

where

```lean
def RoundComposite.Concrete.OddSuccessorSmallModulusSlackPacketLiftAddGoal
    : Prop :=
  ∀ {b m T : Nat},
    5 <= b ->
    Odd m -> 3 <= m -> m < b + T ->
    StandardCayleySolved b m ->
    (packets : List (List Nat)) ->
    packets.length = b ->
    (packets.map List.length).sum = b + T ->
    (∀ packet, packet ∈ packets -> packet.sum = m) ->
    (∀ packet, packet ∈ packets ->
      ∀ a, a ∈ packet -> 0 < a ∧ a < m ∧ Nat.Coprime a m) ->
    T = b + 1 ->
    m ^ b > m * (b + T) * T ->
    StandardCayleySolved (b + T) m
```

This theorem is consumed by the most split final endpoint:

```lean
theorem RoundComposite.Concrete
  .oddModulusToriAllDimensionsGoal_of_v4_returnTailClosedFullSupportTrellisGeometryRawEdge
    (hFull : PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal)
    (hLift : PrefixCount.OrdinaryQge2IndicatorToFullSupportGoal)
    (hGeom : OddSuccessorSmallModulusBaseTailGeometryFromHallGoal)
    (hRaw : ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal) :
    OddModulusToriAllDimensionsGoal
```

## Already Lean-Closed Arithmetic

Do not spend effort on these arithmetic facts; Lean already has them:

```lean
theorem RoundComposite.successor_hall_slack
    {b m : Nat} (hb5 : 5 <= b) (hm3 : 3 <= m) :
    m ^ b > m * (2 * b + 1) * ((2 * b + 1) - b)

theorem RoundComposite.unitCarryPackets_spec
    ... :
    packets.length = b ∧
    (packets.map List.length).sum = d ∧
    (∀ packet, packet ∈ packets -> packet.sum = m ∧
      ∀ a, a ∈ packet -> 0 < a ∧ a < m ∧ Nat.Coprime a m)
```

## Desired Proof Split

The previous GPT response suggested the following internal split.  Please now
make this precise enough for Lean, avoiding `axiom`, `constant`, or `sorry` in
the final repository.

```lean
structure UnitSlackPackets (b m T : Nat) (packets : List (List Nat)) : Prop :=
  (packets_length :
    packets.length = b)
  (total_parts :
    (packets.map List.length).sum = b + T)
  (packet_sum :
    ∀ packet, packet ∈ packets -> packet.sum = m)
  (entry_unit :
    ∀ packet, packet ∈ packets ->
      ∀ a, a ∈ packet -> 0 < a ∧ a < m ∧ Nat.Coprime a m)

namespace BaseTail

-- Define these using existing StandardCayleySolved / CayleyHamilton structures.
def Cylinder :
  Nat -> Nat -> Nat -> List (List Nat) -> Type := ...

def IsCylinder :
  {b m T : Nat} -> {packets : List (List Nat)} ->
    Cylinder b m T packets -> Prop := ...

def ActiveSymboling :
  {b m T : Nat} -> {packets : List (List Nat)} ->
    Cylinder b m T packets -> Type := ...

def IsActiveSymboling :
  {b m T : Nat} -> {packets : List (List Nat)}
    {C : Cylinder b m T packets} ->
    ActiveSymboling C -> Prop := ...

end BaseTail
```

The desired theorem chain is:

```lean
theorem cylinderBaseExpansion_of_standardCayleySolved_packets :
  ∀ {b m T : Nat} {packets : List (List Nat)},
    1 <= b ->
    0 < m ->
    1 <= T ->
    StandardCayleySolved b m ->
    UnitSlackPackets b m T packets ->
    ∃ C : BaseTail.Cylinder b m T packets,
      BaseTail.IsCylinder C

theorem activeSymbolingWithResidues_of_cylinder :
  ActiveHall.HallRealizationGoal ->
  ∀ {b m T : Nat} {packets : List (List Nat)}
    {C : BaseTail.Cylinder b m T packets},
    5 <= b ->
    Odd m ->
    3 <= m ->
    m < b + T ->
    T = b + 1 ->
    UnitSlackPackets b m T packets ->
    BaseTail.IsCylinder C ->
    m ^ b > m * (b + T) * T ->
    ∃ A : BaseTail.ActiveSymboling C,
      BaseTail.IsActiveSymboling A

theorem standardCayleySolved_of_baseTailActive :
  ∀ {b m T : Nat} {packets : List (List Nat)}
    {C : BaseTail.Cylinder b m T packets}
    {A : BaseTail.ActiveSymboling C},
    1 <= b ->
    Odd m ->
    3 <= m ->
    1 <= T ->
    UnitSlackPackets b m T packets ->
    BaseTail.IsCylinder C ->
    BaseTail.IsActiveSymboling A ->
    StandardCayleySolved (b + T) m
```

## Prompt

Please give a Lean-facing proof plan for
`OddSuccessorSmallModulusBaseTailGeometryFromHallGoal`.

The answer should:

1. define the minimal `BaseTail.Cylinder` and `ActiveSymboling` data structures
   in terms of existing repository objects;
2. state the exact auxiliary Lean theorems needed to construct the cylinder,
   realize active symbols using `ActiveHall.HallRealizationGoal`, and lift to
   `StandardCayleySolved (b+T) m`;
3. explain how packet sums and unit entries become tail carry units;
4. explain how the Hall slack inequality is used only in the active-symboling
   cut verification;
5. identify whether the successor restriction `T = b+1` is sufficient to avoid
   any additional proper-prefix-unit assumptions on packets.

Prefer concrete theorem statements and proof skeletons over prose.  If the
target is too large to close directly, propose the smallest next Lean
interfaces that would materially reduce it.
