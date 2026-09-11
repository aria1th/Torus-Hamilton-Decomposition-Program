-- STATUS: main-path
import TorusEven.Entry.Seed.NumericRows
import TorusEven.Collar.ComponentPairs

namespace TorusEven.Entry.Seed

open Collar Incidence

variable (p : ℕ) (hp : 2 ≤ p) {m : ℕ} (heven : Even m)

def component (j : Fin 3) : (Fin 4 ⊕ Shell.Color p) → Component (support p hp heven j) :=
  componentOf (support p hp heven j)

variable [NeZero m] (hm : 4 ≤ m)
include hm

theorem same_component_nat {j : Fin 3} {x y : Fin 4 ⊕ Shell.Color p} (h w : ℕ)
    (hh : h < 4) (hw : w < 4)
    (hx : x ∈ supportNat p hp j h w) (hy : y ∈ supportNat p hp j h w) :
    component p hp heven j x = component p hp heven j y := by
  have he := support_natCast hm heven p hp j h w (hh.trans_le hm) (hw.trans_le hm)
  exact same_component (support p hp heven j) (he.symm ▸ hx) (he.symm ▸ hy)

theorem support_nonempty (j : Fin 3) (hw : ZMod m × ZMod m) :
    (support p hp heven j hw).Nonempty := by
  rw [← Finset.card_pos, card_support p hp heven hm]
  fin_cases j <;> simp

omit [NeZero m] in
theorem coherent_xy (hp4 : 4 ≤ p) (j : Fin 3) (hj : j = 0 ∨ j = 1) (h : ZMod m) :
    Coherent (fun w => support p hp heven j (h, w)) := by
  rcases hj with rfl | rfl
  · apply coherent_of_map_subset (fun w => Shell.aUsers p h.val \ Shell.selected p hp h w)
      (fun w => support p hp heven 0 (h, w)) Sum.inr
    · intro w c hc
      rw [mem_support_right]
      simpa only [← Shell.direction_zero p hp h w, Finset.mem_filter,
        Finset.mem_univ, true_and] using hc
    · exact Shell.complement_coherent p hp hm hp4 h
  · apply coherent_of_map_subset (Shell.selected p hp h)
      (fun w => support p hp heven 1 (h, w)) Sum.inr
    · intro w c hc
      rw [mem_support_right]
      simpa only [← Shell.direction_one p hp h w, Finset.mem_filter,
        Finset.mem_univ, true_and] using hc
    · exact Shell.selected_coherent p hp hm hp4 h

theorem same_height_xy (hp4 : 4 ≤ p) (j : Fin 3) (hj : j = 0 ∨ j = 1)
    (h : ZMod m) {w v : ZMod m} {x y : Fin 4 ⊕ Shell.Color p}
    (hx : x ∈ support p hp heven j (h, w)) (hy : y ∈ support p hp heven j (h, v)) :
    component p hp heven j x = component p hp heven j y := by
  have hc := coherent_same_component (fun w => support p hp heven j (h, w))
    (fun w => support_nonempty p hp heven hm j (h, w))
    (coherent_xy p hp heven hm hp4 j hj h) hx hy
  exact component_map (fun w => (h, w)) id (fun _ _ hx => hx) hc

omit heven [NeZero m] in
theorem endpoint_uses_xy (j : Fin 3) (hj : j = 0 ∨ j = 1)
    (h : ZMod m) (i : Fin (Shell.pairCount p h.val)) (b : Bool) :
    ∃ w, Shell.direction p hp h w (Shell.endpoint p hp h.val (i, b)) = j := by
  have ha := (Shell.pairs p hp h.val).mem_endpoint (i, b)
  have he (w : ZMod m) : Shell.endpoint p hp h.val (i, b) ∈ Shell.selected p hp h w ↔
      b = if w = Shell.event i then true else false :=
    (Shell.pairs p hp h.val).endpoint_mem_row Shell.event _
      (Shell.fillers_disjoint p hp h.val) false w i b
  have h20 : (2 : ZMod m) ≠ 0 := by
    simpa using cast_ne_zero (m := m) (n := 2) (by omega) (by omega)
  have h21 : (2 : ZMod m) ≠ 1 := by
    have h10 := cast_ne_zero (m := m) (n := 1) (by omega) (by omega)
    intro h
    apply h10
    linear_combination h
  have hbase : (2 : ZMod m) ≠ Shell.event i := by
    unfold Shell.event
    split_ifs <;> assumption
  change Shell.endpoint p hp h.val (i, b) ∈ Shell.aUsers p h.val at ha
  rcases hj with rfl | rfl <;> cases b
  · refine ⟨Shell.event i, ?_⟩
    simp [Shell.direction, ha, he]
  · refine ⟨2, ?_⟩
    simp [Shell.direction, ha, he, hbase]
  · refine ⟨2, ?_⟩
    simp [Shell.direction, ha, he, hbase]
  · refine ⟨Shell.event i, ?_⟩
    simp [Shell.direction, ha, he]

theorem auxiliary_pair_xy (hp4 : 4 ≤ p) (j : Fin 3) (hj : j = 0 ∨ j = 1)
    (h : ZMod m) (i : Fin (Shell.pairCount p h.val)) :
    component p hp heven j (.inr (Shell.endpoint p hp h.val (i, false))) =
      component p hp heven j (.inr (Shell.endpoint p hp h.val (i, true))) := by
  obtain ⟨w, hw⟩ := endpoint_uses_xy p hp hm j hj h i false
  obtain ⟨v, hv⟩ := endpoint_uses_xy p hp hm j hj h i true
  exact same_height_xy p hp heven hm hp4 j hj h
    ((mem_support_right p hp heven j (h, w) _).mpr hw)
    ((mem_support_right p hp heven j (h, v) _).mpr hv)

theorem auxiliary_w (c : Shell.Color p) :
    component p hp heven 2 (.inr c) = component p hp heven 2 (.inr ⟨0, by omega⟩) := by
  by_cases hc : c.val < p
  · apply same_component_nat p hp heven hm 2 0 (by decide) (by decide)
    all_goals simp [Shell.directionNat, Shell.mem_aUsers, Shell.aUser]; omega
  · by_cases hc0 : c.val = p
    · trans component p hp heven 2 (.inr ⟨1, by omega⟩)
      · apply same_component_nat p hp heven hm 0 0 (by decide) (by decide)
        all_goals simp [Shell.directionNat, Shell.mem_aUsers, Shell.aUser]; omega
      · apply same_component_nat p hp heven hm 2 0 (by decide) (by decide)
        all_goals simp [Shell.directionNat, Shell.mem_aUsers, Shell.aUser]; omega
    · apply same_component_nat p hp heven hm 1 0 (by decide) (by decide)
      all_goals simp [Shell.directionNat, Shell.mem_aUsers, Shell.aUser] <;> omega

end TorusEven.Entry.Seed
