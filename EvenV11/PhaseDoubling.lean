import EvenV11.AffineSeparation

namespace EvenV11
namespace PhaseDoubling

abbrev PhaseSection (h M : Nat) := ZMod h × ZMod M

def phaseProjection {h M : Nat} (x : PhaseSection h M) : ZMod h :=
  x.1

def PhaseLine {h M : Nat} (k : ZMod h) : Set (PhaseSection h M) :=
  ProjectionFiber phaseProjection k

abbrev PhaseLinePoint {h M : Nat} (k : ZMod h) :=
  {x : PhaseSection h M // x ∈ PhaseLine k}

def phaseLinePointEquiv {h M : Nat} (k : ZMod h) :
    ZMod M ≃ PhaseLinePoint (h := h) (M := M) k where
  toFun u := ⟨(k, u), rfl⟩
  invFun x := x.1.2
  left_inv u := rfl
  right_inv x := by
    apply Subtype.ext
    cases x with
    | mk x hx =>
        cases x with
        | mk k0 u =>
            change (k, u) = (k0, u)
            change k0 = k at hx
            rw [hx]

theorem phaseLinePointEquiv_bijective {h M : Nat} (k : ZMod h) :
    Function.Bijective (phaseLinePointEquiv (h := h) (M := M) k) :=
  (phaseLinePointEquiv k).bijective

theorem phaseLinePoint_card_zmod {h M : Nat} [NeZero M] (k : ZMod h) :
    @Fintype.card (@PhaseLinePoint h M k)
      (Fintype.ofEquiv (ZMod M) (@phaseLinePointEquiv h M k)) =
        Fintype.card (ZMod M) :=
  Fintype.ofEquiv_card (@phaseLinePointEquiv h M k)

theorem phaseLinePoint_card {h M : Nat} [NeZero M] (k : ZMod h) :
    @Fintype.card (@PhaseLinePoint h M k)
      (Fintype.ofEquiv (ZMod M) (@phaseLinePointEquiv h M k)) = M := by
  rw [phaseLinePoint_card_zmod k]
  exact ZMod.card M

def phaseLineInitialSlot {h M n : Nat} [NeZero M]
    (k : ZMod h) (hn : n ≤ M) : Fin n → PhaseLinePoint (h := h) (M := M) k :=
  fun i => phaseLinePointEquiv k
    ((ZMod.finEquiv M) (Fin.castLE hn i))

theorem phaseLineInitialSlot_injective {h M n : Nat} [NeZero M]
    (k : ZMod h) (hn : n ≤ M) :
    Function.Injective (phaseLineInitialSlot k hn) := by
  intro i j hij
  have hz := (@phaseLinePointEquiv h M k).injective hij
  have hfin := (ZMod.finEquiv M).injective hz
  exact Fin.castLE_inj.mp hfin

theorem phaseLineConstantOn {h M : Nat} (k : ZMod h) :
    ProjectionConstantOn phaseProjection (PhaseLine (h := h) (M := M) k) k :=
  projectionFiberConstantOn phaseProjection k

theorem phaseLineDisjointFromLine {h M : Nat} {k j : ZMod h}
    (hkj : k ≠ j) :
    SetsDisjoint (PhaseLine (h := h) (M := M) k)
      (PhaseLine (h := h) (M := M) j) :=
  setsDisjointOfConstantProjectionNe phaseProjection
    (PhaseLine (h := h) (M := M) k)
    (PhaseLine (h := h) (M := M) j) k j
    (phaseLineConstantOn k) (phaseLineConstantOn j) hkj

def PhaseProtectedStrips (h M : Nat) : Set (PhaseSection h M) :=
  (PhaseLine (h := h) (M := M) (-1 : ZMod h) ∪
    PhaseLine (h := h) (M := M) (0 : ZMod h)) ∪
      PhaseLine (h := h) (M := M) (1 : ZMod h)

theorem phaseTwo_ne_zero {h : Nat} [NeZero h] (hh : 2 < h) :
    (2 : ZMod h) ≠ 0 := by
  intro hzero
  have hdvd : h ∣ 2 := (ZMod.natCast_eq_zero_iff 2 h).mp hzero
  exact (Nat.not_dvd_of_pos_of_lt (by decide) hh) hdvd

theorem phaseTwo_ne_one {h : Nat} [NeZero h] (hh : 1 < h) :
    (2 : ZMod h) ≠ 1 := by
  intro heq
  have hzero : ((1 : Nat) : ZMod h) = 0 := by
    calc
      ((1 : Nat) : ZMod h) = (2 : ZMod h) - 1 := by norm_num
      _ = 0 := by rw [heq]; simp
  have hdvd : h ∣ 1 := (ZMod.natCast_eq_zero_iff 1 h).mp hzero
  exact (Nat.not_dvd_of_pos_of_lt (by decide) hh) hdvd

theorem phaseTwo_ne_negOne {h : Nat} [NeZero h] (hh : 3 < h) :
    (2 : ZMod h) ≠ -1 := by
  intro heq
  have hzero : ((3 : Nat) : ZMod h) = 0 := by
    calc
      ((3 : Nat) : ZMod h) = (2 : ZMod h) + 1 := by norm_num
      _ = 0 := by rw [heq]; simp
  have hdvd : h ∣ 3 := (ZMod.natCast_eq_zero_iff 3 h).mp hzero
  exact (Nat.not_dvd_of_pos_of_lt (by decide) hh) hdvd

theorem phaseReserveLineDisjointFromProtectedStrips
    {h M : Nat} [NeZero h] (hh : 3 < h) :
    SetsDisjoint (PhaseLine (h := h) (M := M) (2 : ZMod h))
      (PhaseProtectedStrips h M) := by
  intro x hxLine hxUnion
  rcases hxUnion with hxNegOrZero | hxOne
  · rcases hxNegOrZero with hxNeg | hxZero
    · exact phaseTwo_ne_negOne hh (by
        have h2 :=
          phaseLineConstantOn (h := h) (M := M) (2 : ZMod h) x hxLine
        have hn :=
          phaseLineConstantOn (h := h) (M := M) (-1 : ZMod h) x hxNeg
        exact h2.symm.trans hn)
    · exact phaseTwo_ne_zero (Nat.lt_trans (by decide : 2 < 3) hh) (by
        have h2 :=
          phaseLineConstantOn (h := h) (M := M) (2 : ZMod h) x hxLine
        have h0 :=
          phaseLineConstantOn (h := h) (M := M) (0 : ZMod h) x hxZero
        exact h2.symm.trans h0)
  · exact phaseTwo_ne_one (Nat.lt_trans (by decide : 1 < 3) hh) (by
      have h2 :=
        phaseLineConstantOn (h := h) (M := M) (2 : ZMod h) x hxLine
      have h1 :=
        phaseLineConstantOn (h := h) (M := M) (1 : ZMod h) x hxOne
      exact h2.symm.trans h1)

theorem phaseProtectedStripsAvoids
    {h M : Nat} {k : ZMod h}
    (hkNeg : k ≠ -1) (hkZero : k ≠ 0) (hkOne : k ≠ 1) :
    ProjectionAvoids (@phaseProjection h M) (PhaseProtectedStrips h M) k := by
  intro x hxProtected hxk
  rcases hxProtected with hxNegOrZero | hxOne
  · rcases hxNegOrZero with hxNeg | hxZero
    · exact hkNeg (hxk.symm.trans
        (phaseLineConstantOn (h := h) (M := M) (-1 : ZMod h) x hxNeg))
    · exact hkZero (hxk.symm.trans
        (phaseLineConstantOn (h := h) (M := M) (0 : ZMod h) x hxZero))
  · exact hkOne (hxk.symm.trans
      (phaseLineConstantOn (h := h) (M := M) (1 : ZMod h) x hxOne))

theorem phaseProtectedStripsAvoidsReservePhase
    {h M : Nat} [NeZero h] (hh : 3 < h) :
    ProjectionAvoids (@phaseProjection h M)
      (PhaseProtectedStrips h M) (2 : ZMod h) :=
  phaseProtectedStripsAvoids
    (phaseTwo_ne_negOne hh)
    (phaseTwo_ne_zero (Nat.lt_trans (by decide : 2 < 3) hh))
    (phaseTwo_ne_one (Nat.lt_trans (by decide : 1 < 3) hh))

theorem phaseReserveLineProjectionSeparatedFromProtectedStrips
    {h M : Nat} [NeZero h] (hh : 3 < h) :
    ProjectionImagesDisjoint (@phaseProjection h M)
      (@PhaseLine h M (2 : ZMod h)) (PhaseProtectedStrips h M) :=
  projectionImagesDisjointOfConstantProjectionAvoids
    (@phaseProjection h M) (@PhaseLine h M (2 : ZMod h))
    (PhaseProtectedStrips h M) (2 : ZMod h)
    (phaseLineConstantOn (h := h) (M := M) (2 : ZMod h))
    (phaseProtectedStripsAvoidsReservePhase hh)

theorem phaseSetCardCoprimePow (m a : Nat) [NeZero m] :
    Nat.Coprime (m - 1) (m ^ a) := by
  have hm1 : 1 ≤ m :=
    Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne m))
  have hcop : Nat.Coprime (m - 1) m :=
    (Nat.coprime_self_sub_left hm1).2 (by simp)
  exact hcop.pow_right a

theorem fourPowReserveCapacityShifted (n : Nat) :
    2 * (n + 2) + 3 ≤ 4 ^ (n + 2) := by
  induction n with
  | zero =>
      norm_num
  | succ n ih =>
      calc
        2 * (n.succ + 2) + 3 ≤ 4 * (2 * (n + 2) + 3) := by
          omega
        _ ≤ 4 * 4 ^ (n + 2) := Nat.mul_le_mul_left 4 ih
        _ = 4 ^ ((n + 2).succ) := (@Nat.pow_succ' 4 (n + 2)).symm
        _ = 4 ^ (n.succ + 2) := by
          congr 1

theorem fourPowReserveCapacity (a : Nat) (ha : 2 ≤ a) :
    2 * a + 3 ≤ 4 ^ a := by
  rcases Nat.exists_eq_add_of_le ha with ⟨n, rfl⟩
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    using fourPowReserveCapacityShifted n

theorem phaseReserveCapacity (a m : Nat) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    2 * a + 3 ≤ m ^ a :=
  le_trans (fourPowReserveCapacity a ha) (Nat.pow_le_pow_left hm a)

theorem phaseReserveLineCapacity
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    2 * a + 3 ≤ @Fintype.card
      (@PhaseLinePoint h (m ^ a) (2 : ZMod h))
      (Fintype.ofEquiv (ZMod (m ^ a))
        (@phaseLinePointEquiv h (m ^ a) (2 : ZMod h))) := by
  rw [phaseLinePoint_card (h := h) (M := m ^ a) (2 : ZMod h)]
  exact phaseReserveCapacity a m ha hm

def phaseReserveLineSlot
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    Fin (2 * a + 3) → PhaseLinePoint (h := h) (M := m ^ a) (2 : ZMod h) :=
  phaseLineInitialSlot (h := h) (M := m ^ a)
    (2 : ZMod h) (phaseReserveCapacity a m ha hm)

theorem phaseReserveLineSlot_injective
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    Function.Injective (phaseReserveLineSlot h a m ha hm) :=
  phaseLineInitialSlot_injective (h := h) (M := m ^ a)
    (2 : ZMod h) (phaseReserveCapacity a m ha hm)

theorem phaseReserveLineSlot_phase
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    (i : Fin (2 * a + 3)) :
    phaseProjection (phaseReserveLineSlot h a m ha hm i).1 = (2 : ZMod h) :=
  (phaseReserveLineSlot h a m ha hm i).2

theorem phaseReserveLineSlot_not_mem_protectedStrips
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (i : Fin (2 * a + 3)) :
    (phaseReserveLineSlot h a m ha hm i).1 ∉
      PhaseProtectedStrips h (m ^ a) := by
  intro hxProtected
  exact phaseReserveLineDisjointFromProtectedStrips (M := m ^ a) hh
    (phaseReserveLineSlot h a m ha hm i).1
    (phaseReserveLineSlot h a m ha hm i).2
    hxProtected

def phaseReserveLineSlotList
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    List (PhaseLinePoint (h := h) (M := m ^ a) (2 : ZMod h)) :=
  (List.finRange (2 * a + 3)).map (phaseReserveLineSlot h a m ha hm)

theorem phaseReserveLineSlotList_length
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    (phaseReserveLineSlotList h a m ha hm).length = 2 * a + 3 := by
  rw [phaseReserveLineSlotList, List.length_map, List.length_finRange]

theorem phaseReserveLineSlotList_nodup
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    (phaseReserveLineSlotList h a m ha hm).Nodup :=
  List.Nodup.map
    (phaseReserveLineSlot_injective h a m ha hm)
    (List.nodup_finRange (2 * a + 3))

theorem phaseReserveLineSlotList_phase
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {x : PhaseLinePoint (h := h) (M := m ^ a) (2 : ZMod h)}
    (hx : x ∈ phaseReserveLineSlotList h a m ha hm) :
    phaseProjection x.1 = (2 : ZMod h) := by
  rcases (List.mem_map.mp hx) with ⟨i, hi, rfl⟩
  exact phaseReserveLineSlot_phase h a m ha hm i

theorem phaseReserveLineSlotList_not_mem_protectedStrips
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {x : PhaseLinePoint (h := h) (M := m ^ a) (2 : ZMod h)}
    (hx : x ∈ phaseReserveLineSlotList h a m ha hm) :
    x.1 ∉ PhaseProtectedStrips h (m ^ a) := by
  rcases (List.mem_map.mp hx) with ⟨i, hi, rfl⟩
  exact phaseReserveLineSlot_not_mem_protectedStrips h a m hh ha hm i

def phaseReserveLineSlotPointList
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    List (PhaseSection h (m ^ a)) :=
  (phaseReserveLineSlotList h a m ha hm).map Subtype.val

theorem phaseReserveLineSlotPointList_length
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    (phaseReserveLineSlotPointList h a m ha hm).length = 2 * a + 3 := by
  rw [phaseReserveLineSlotPointList, List.length_map,
    phaseReserveLineSlotList_length]

theorem phaseReserveLineSlotPointList_nodup
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    (phaseReserveLineSlotPointList h a m ha hm).Nodup :=
  List.Nodup.map
    (fun _ _ hxy => Subtype.ext hxy)
    (phaseReserveLineSlotList_nodup h a m ha hm)

theorem phaseReserveLineSlotPointList_phase
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {x : PhaseSection h (m ^ a)}
    (hx : x ∈ phaseReserveLineSlotPointList h a m ha hm) :
    phaseProjection x = (2 : ZMod h) := by
  rcases (List.mem_map.mp hx) with ⟨slot, hslot, rfl⟩
  exact phaseReserveLineSlotList_phase h a m ha hm hslot

theorem phaseReserveLineSlotPointList_not_mem_protectedStrips
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {x : PhaseSection h (m ^ a)}
    (hx : x ∈ phaseReserveLineSlotPointList h a m ha hm) :
    x ∉ PhaseProtectedStrips h (m ^ a) := by
  rcases (List.mem_map.mp hx) with ⟨slot, hslot, rfl⟩
  exact phaseReserveLineSlotList_not_mem_protectedStrips
    h a m hh ha hm hslot

def phaseReserveLineSlotPointSet
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    Set (PhaseSection h (m ^ a)) :=
  {x | x ∈ phaseReserveLineSlotPointList h a m ha hm}

theorem phaseReserveLineSlotPointSet_mem
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    (x : PhaseSection h (m ^ a)) :
    x ∈ phaseReserveLineSlotPointSet h a m ha hm ↔
      x ∈ phaseReserveLineSlotPointList h a m ha hm :=
  Iff.rfl

theorem phaseReserveLineSlotPointSet_subsetReserveLine
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    phaseReserveLineSlotPointSet h a m ha hm ⊆
      PhaseLine (h := h) (M := m ^ a) (2 : ZMod h) := by
  intro x hx
  exact phaseReserveLineSlotPointList_phase h a m ha hm hx

theorem phaseReserveLineSlotPointSet_constantProjection
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    ProjectionConstantOn (@phaseProjection h (m ^ a))
      (phaseReserveLineSlotPointSet h a m ha hm) (2 : ZMod h) :=
  phaseReserveLineSlotPointSet_subsetReserveLine h a m ha hm

theorem phaseReserveLineSlotPointSet_disjointFromProtectedStrips
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    SetsDisjoint (phaseReserveLineSlotPointSet h a m ha hm)
      (PhaseProtectedStrips h (m ^ a)) := by
  intro x hxSet hxProtected
  exact phaseReserveLineSlotPointList_not_mem_protectedStrips
    h a m hh ha hm hxSet hxProtected

theorem phaseReserveLineSlotPointSet_mem_iff_exists_slot
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    (x : PhaseSection h (m ^ a)) :
    x ∈ phaseReserveLineSlotPointSet h a m ha hm ↔
      ∃ i : Fin (2 * a + 3),
        (phaseReserveLineSlot h a m ha hm i).1 = x := by
  constructor
  · intro hx
    rcases (List.mem_map.mp hx) with ⟨slot, hslot, hval⟩
    rcases (List.mem_map.mp hslot) with ⟨i, hi, hslotEq⟩
    refine ⟨i, ?_⟩
    rw [hslotEq]
    exact hval
  · intro hx
    rcases hx with ⟨i, rfl⟩
    exact List.mem_map.mpr
      ⟨phaseReserveLineSlot h a m ha hm i,
        List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩,
        rfl⟩

theorem phaseReserveLineSlotPointSet_slot_unique
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {i j : Fin (2 * a + 3)}
    (hij :
      (phaseReserveLineSlot h a m ha hm i).1 =
        (phaseReserveLineSlot h a m ha hm j).1) :
    i = j :=
  phaseReserveLineSlot_injective h a m ha hm (Subtype.ext hij)

theorem phaseReserveLineSlotPointSet_exists_unique_slot
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {x : PhaseSection h (m ^ a)}
    (hx : x ∈ phaseReserveLineSlotPointSet h a m ha hm) :
    ∃! i : Fin (2 * a + 3),
      (phaseReserveLineSlot h a m ha hm i).1 = x := by
  rcases (phaseReserveLineSlotPointSet_mem_iff_exists_slot
      h a m ha hm x).mp hx with ⟨i, hi⟩
  refine ⟨i, hi, ?_⟩
  intro j hj
  exact phaseReserveLineSlotPointSet_slot_unique
    h a m ha hm (hj.trans hi.symm)

end PhaseDoubling

export PhaseDoubling
  (PhaseSection phaseProjection PhaseLine PhaseLinePoint
   phaseLinePointEquiv phaseLinePointEquiv_bijective
   phaseLinePoint_card_zmod phaseLinePoint_card
   phaseLineInitialSlot phaseLineInitialSlot_injective
   phaseLineConstantOn phaseLineDisjointFromLine PhaseProtectedStrips
   phaseTwo_ne_zero phaseTwo_ne_one phaseTwo_ne_negOne
   phaseReserveLineDisjointFromProtectedStrips
   phaseProtectedStripsAvoids phaseProtectedStripsAvoidsReservePhase
   phaseReserveLineProjectionSeparatedFromProtectedStrips
   phaseSetCardCoprimePow fourPowReserveCapacityShifted
   fourPowReserveCapacity phaseReserveCapacity phaseReserveLineCapacity
   phaseReserveLineSlot phaseReserveLineSlot_injective
   phaseReserveLineSlot_phase phaseReserveLineSlot_not_mem_protectedStrips
   phaseReserveLineSlotList phaseReserveLineSlotList_length
   phaseReserveLineSlotList_nodup phaseReserveLineSlotList_phase
   phaseReserveLineSlotList_not_mem_protectedStrips
   phaseReserveLineSlotPointList phaseReserveLineSlotPointList_length
   phaseReserveLineSlotPointList_nodup
   phaseReserveLineSlotPointList_phase
   phaseReserveLineSlotPointList_not_mem_protectedStrips
   phaseReserveLineSlotPointSet phaseReserveLineSlotPointSet_mem
   phaseReserveLineSlotPointSet_subsetReserveLine
   phaseReserveLineSlotPointSet_constantProjection
   phaseReserveLineSlotPointSet_disjointFromProtectedStrips
   phaseReserveLineSlotPointSet_mem_iff_exists_slot
   phaseReserveLineSlotPointSet_slot_unique
   phaseReserveLineSlotPointSet_exists_unique_slot)

end EvenV11
