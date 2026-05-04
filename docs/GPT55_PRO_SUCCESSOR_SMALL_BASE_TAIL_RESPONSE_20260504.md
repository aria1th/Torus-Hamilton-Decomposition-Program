# GPT-5.5 Pro Successor-Small Base-Tail Response

Date: 2026-05-04.

Response id: `resp_06781d5a17f099250069f8a2de229081919ddf1d65046d89c9`.

Status: `completed`.

---

Below is the Lean-facing cut I would use.  The main point is to isolate the hard geometry from the Hall realization.  **The only place Active Hall should be used is the active-symboling theorem.**

```lean
namespace RoundComposite.Concrete

structure UnitSlackPackets (b m T : Nat) (packets : List (List Nat)) : Prop where
  packets_length :
    packets.length = b
  total_parts :
    (packets.map List.length).sum = b + T
  packet_sum :
    ∀ packet, packet ∈ packets -> packet.sum = m
  entry_unit :
    ∀ packet, packet ∈ packets ->
      ∀ a, a ∈ packet -> 0 < a ∧ a < m ∧ Nat.Coprime a m

namespace BaseTail

/-- Fill this with the actual cylinder data:
base cycles on `(ZMod m)^(b+1)`, packet-position colors,
active incidences/tokens, residue maps, etc. -/
constant Cylinder :
  Nat -> Nat -> Nat -> List (List Nat) -> Type

/-- Pure cylinder validity, no active symbols yet. -/
constant IsCylinder :
  {b m T : Nat} -> {packets : List (List Nat)} ->
    Cylinder b m T packets -> Prop

/-- An assignment of active symbols to the active incidences of a cylinder. -/
constant ActiveSymboling :
  {b m T : Nat} -> {packets : List (List Nat)} ->
    Cylinder b m T packets -> Type

/-- Valid active symboling: allowed symbols, residue-compatible counts,
and per-color unit prefix-count residues. -/
constant IsActiveSymboling :
  {b m T : Nat} -> {packets : List (List Nat)}
    {C : Cylinder b m T packets} ->
    ActiveSymboling C -> Prop

end BaseTail
```

Use these three theorem goals.

```lean
/-- Pure geometry: expand a solved `b`-torus using packet cylinders. -/
axiom cylinderBaseExpansion_of_standardCayleySolved_packets :
  ∀ {b m T : Nat} {packets : List (List Nat)},
    1 ≤ b ->
    0 < m ->
    1 ≤ T ->
    StandardCayleySolved b m ->
    UnitSlackPackets b m T packets ->
    ∃ C : BaseTail.Cylinder b m T packets,
      BaseTail.IsCylinder C

/-- Pure finite combinatorics plus Active Hall.
This is the only theorem that should use `ActiveHall.HallRealizationGoal`. -/
axiom activeSymbolingWithResidues_of_cylinder :
  ActiveHall.HallRealizationGoal ->
  ∀ {b m T : Nat} {packets : List (List Nat)}
    {C : BaseTail.Cylinder b m T packets},
    5 ≤ b ->
    Odd m ->
    3 ≤ m ->
    m < b + T ->
    T = b + 1 ->
    UnitSlackPackets b m T packets ->
    BaseTail.IsCylinder C ->
    m ^ b > m * (b + T) * T ->
    ∃ A : BaseTail.ActiveSymboling C,
      BaseTail.IsActiveSymboling A

/-- Pure geometry/base-tail lift: a valid cylinder plus valid active symboling
gives a standard Hamilton decomposition in dimension `b+T`. -/
axiom standardCayleySolved_of_baseTailActive :
  ∀ {b m T : Nat} {packets : List (List Nat)}
    {C : BaseTail.Cylinder b m T packets}
    {A : BaseTail.ActiveSymboling C},
    1 ≤ b ->
    Odd m ->
    3 ≤ m ->
    1 ≤ T ->
    UnitSlackPackets b m T packets ->
    BaseTail.IsCylinder C ->
    BaseTail.IsActiveSymboling A ->
    StandardCayleySolved (b + T) m
```

Then the requested target is just the wrapper:

```lean
theorem oddSuccessorSmallModulusSlackPacketLiftAddGoal_of_baseTailPieces
    (hHall : ActiveHall.HallRealizationGoal) :
    OddSuccessorSmallModulusSlackPacketLiftAddGoal := by
  intro b m T hb5 hodd hm3 hsmall hsol
  intro packets hplen htotal hsum hunit hT hslack
  subst T

  let hp : UnitSlackPackets b m (b + 1) packets :=
    ⟨hplen, htotal, hsum, hunit⟩

  have hb1 : 1 ≤ b := by omega
  have hmpos : 0 < m := by omega
  have hTpos : 1 ≤ b + 1 := by omega

  rcases
    cylinderBaseExpansion_of_standardCayleySolved_packets
      hb1 hmpos hTpos hsol hp
    with ⟨C, hC⟩

  rcases
    activeSymbolingWithResidues_of_cylinder hHall
      hb5 hodd hm3 hsmall rfl hp hC hslack
    with ⟨A, hA⟩

  exact
    standardCayleySolved_of_baseTailActive
      hb1 hodd hm3 hTpos hp hC hA
```

Dependency graph:

```text
OddSuccessorSmallModulusSlackPacketLiftAddGoal
│
├─ cylinderBaseExpansion_of_standardCayleySolved_packets   [pure geometry]
│  ├─ StandardCayleySolved b m
│  └─ UnitSlackPackets b m T packets
│
├─ activeSymbolingWithResidues_of_cylinder                 [finite combinatorics]
│  ├─ BaseTail.IsCylinder C
│  ├─ small modulus hypotheses: m < b+T, T=b+1
│  ├─ Hall slack: m^b > m*(b+T)*T
│  └─ ActiveHall.HallRealizationGoal   ← only use of Active Hall
│
└─ standardCayleySolved_of_baseTailActive                  [pure geometry]
   ├─ BaseTail.IsCylinder C
   └─ BaseTail.IsActiveSymboling A
```

Proof outlines:

1. **Cylinder expansion.**
   - Extract a standard `b`-dimensional Hamilton decomposition from `StandardCayleySolved b m`.
   - Index new colors by packet positions  
     `Σ j : Fin packets.length, Fin ((packets.get j).length)`.
   - Use `(packets.map List.length).sum = b+T` to relabel those positions by `Fin (b+T)`.
   - For packet part `p`, use `Nat.Coprime p m` to get that multiplication by `p` is a permutation of `ZMod m`.
   - Copy each base Hamilton factor into the extra base coordinate cylinder.
   - Use `packet.sum = m` to show the packet intervals tile the extra base coordinate and close cyclically.
   - Produce `BaseTail.Cylinder` and prove `BaseTail.IsCylinder`.

2. **Active symboling with residues.**
   - From a valid cylinder, define the finite token system of active incidences.
   - Define allowed active symbols `{0, Δ, 2, ..., T-1}`; Lean-friendly representation can simply be `Fin T`, with `0` and `1` reserved for `0` and `Δ`.
   - Define residue demands so that every color word satisfies the unit prefix-count conditions.
   - Prove the Hall cut inequalities using the supplied slack  
     `m^b > m * (b+T) * T`.
   - Invoke `ActiveHall.HallRealizationGoal` here.
   - Convert the Hall choice into `BaseTail.ActiveSymboling C`.
   - Prove `BaseTail.IsActiveSymboling A`, including per-color unit prefix-count residues.

3. **Base-tail lift.**
   - Given `C` and `A`, define the full words/cycles in dimension `b+T`.
   - Prove closure modulo `m`.
   - Prove Hamiltonicity by splitting prefix counts into base coordinates and tail/active coordinates.  The base part is controlled by the cylinder; the tail part is controlled by the unit prefix-count residue condition.
   - Prove edge-disjointness/edge-cover:
     - passive/base edges from the cylinder decomposition,
     - active/tail edges from the active symboling and residue counts.
   - Package the resulting word/edge decomposition as `StandardCayleySolved (b+T) m`.

Warning/interface issue: the successor hypothesis `T = b+1` is useful.  If you try to generalize the primitive theorem to arbitrary `T`, the raw packet hypotheses may be too weak if your active/cylinder proof needs **proper packet-prefix sums** to be units.  For successor packets this follows automatically because total length `2*b+1` forces packet lengths to be `2` except one `3`.  Without `T=b+1`, e.g. for `m=15`, the packet `[1,2,4,8]` has unit entries summing to `15`, but prefix sum `1+2=3` is not coprime to `15`.  So either keep `T=b+1` in the active theorem, as above, or strengthen the packet predicate for arbitrary `T`.
