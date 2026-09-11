-- STATUS: main-path
import TorusEven.Entry.Seed.Components

namespace TorusEven.Entry.Seed

open Collar Incidence

variable (p : ℕ) (hp : 2 ≤ p)

private theorem b_one_not_selected (h w : ℕ) (hh : h = 2 ∨ h = 0 ∧ w = 2) :
    (⟨p + 1, by omega⟩ : Shell.Color p) ∉ Shell.selectedNat p hp h w := by
  rw [Shell.mem_selectedNat]
  rintro (⟨i, hi, he⟩ | ⟨i, hi, he⟩)
  · rcases hh with rfl | ⟨rfl, rfl⟩ <;>
      norm_num only [Shell.pairCount, Shell.fillerIndex, if_true, if_false] at hi he <;>
        (try split_ifs at hi he) <;> omega
  · rcases hh with rfl | ⟨rfl, rfl⟩ <;>
      norm_num only [Shell.pairCount, Shell.endpointIndex, if_true, if_false] at hi he <;>
        split_ifs at hi he <;> omega

private theorem b_one_x (h w : ℕ) (hh : h = 2 ∨ h = 0 ∧ w = 2) :
    Shell.directionNat p hp h w ⟨p + 1, by omega⟩ = 0 := by
  have ha : (⟨p + 1, by omega⟩ : Shell.Color p) ∈ Shell.aUsers p h := by
    rcases hh with rfl | ⟨rfl, rfl⟩ <;> simp [Shell.mem_aUsers, Shell.aUser]
  simp only [Shell.directionNat, if_pos ha, if_neg (b_one_not_selected p hp h w hh)]

private theorem b_zero_y (h : ℕ) (hh : h = 2 ∨ h = 3) :
    Shell.directionNat p hp h 2 ⟨p, by omega⟩ = 1 := by
  have ha : (⟨p, by omega⟩ : Shell.Color p) ∈ Shell.aUsers p h := by
    rcases hh with rfl | rfl <;> simp [Shell.mem_aUsers, Shell.aUser]
  have hs : (⟨p, by omega⟩ : Shell.Color p) ∈ Shell.selectedNat p hp h 2 := by
    rw [Shell.mem_selectedNat]
    rcases hh with rfl | rfl
    · by_cases he : p % 2 = 0
      · apply Or.inl
        refine ⟨0, ?_, ?_⟩
        · norm_num [Shell.pairCount, he]; omega
        · simp [Shell.fillerIndex]
      · apply Or.inr
        refine ⟨0, ?_, ?_⟩
        · norm_num [Shell.pairCount, he]; omega
        · simp [Shell.endpointIndex, he]
    · apply Or.inl
      refine ⟨0, ?_, ?_⟩
      · norm_num [Shell.pairCount]; omega
      · simp [Shell.fillerIndex]
  simp only [Shell.directionNat, if_pos ha, if_pos hs]

variable {m : ℕ} [NeZero m] (heven : Even m) (hm : 4 ≤ m)
include hm

theorem same_height_nat_xy (hp4 : 4 ≤ p) (j : Fin 3) (hj : j = 0 ∨ j = 1)
    (h w v : ℕ) (hh : h < 4) (hw : w < 4) (hv : v < 4)
    {x y : Fin 4 ⊕ Shell.Color p}
    (hx : x ∈ supportNat p hp j h w) (hy : y ∈ supportNat p hp j h v) :
    component p hp heven j x = component p hp heven j y := by
  apply same_height_xy p hp heven hm hp4 j hj (h : ZMod m)
    (w := (w : ZMod m)) (v := (v : ZMod m))
  · rwa [support_natCast hm heven p hp j h w (hh.trans_le hm) (hw.trans_le hm)]
  · rwa [support_natCast hm heven p hp j h v (hh.trans_le hm) (hv.trans_le hm)]

theorem core_zero_three_xy (hp4 : 4 ≤ p) (j : Fin 3) (hj : j = 0 ∨ j = 1) :
    component p hp heven j (.inl 0) = component p hp heven j (.inl 3) := by
  rcases hj with rfl | rfl
  · apply same_height_nat_xy p hp heven hm hp4 0 (Or.inl rfl) 1 0 3
      (by decide) (by decide) (by decide)
    all_goals rw [mem_supportNat_left]; decide
  · apply same_height_nat_xy p hp heven hm hp4 1 (Or.inr rfl) 1 2 1
      (by decide) (by decide) (by decide)
    all_goals rw [mem_supportNat_left]; decide

theorem core_one_two_x :
    component p hp heven 0 (.inl 1) = component p hp heven 0 (.inl 2) := by
  trans component p hp heven 0 (.inr ⟨p + 1, by omega⟩)
  · apply same_component_nat p hp heven hm 2 0 (by decide) (by decide)
    · rw [mem_supportNat_left]; decide
    · exact (mem_supportNat_right p hp 0 2 0 _).mpr (b_one_x p hp 2 0 (Or.inl rfl))
  · apply same_component_nat p hp heven hm 0 2 (by decide) (by decide)
    · exact (mem_supportNat_right p hp 0 0 2 _).mpr (b_one_x p hp 0 2 (Or.inr ⟨rfl, rfl⟩))
    · rw [mem_supportNat_left]; decide

theorem core_one_two_y (hp4 : 4 ≤ p) :
    component p hp heven 1 (.inl 1) = component p hp heven 1 (.inl 2) := by
  trans component p hp heven 1 (.inr ⟨p, by omega⟩)
  · apply same_component_nat p hp heven hm 3 2 (by decide) (by decide)
    · rw [mem_supportNat_left]; decide
    · exact (mem_supportNat_right p hp 1 3 2 _).mpr (b_zero_y p hp 3 (Or.inr rfl))
  · trans component p hp heven 1 (.inl 0)
    · apply same_height_nat_xy p hp heven hm hp4 1 (Or.inr rfl) 2 2 0
        (by decide) (by decide) (by decide)
      · exact (mem_supportNat_right p hp 1 2 2 _).mpr (b_zero_y p hp 2 (Or.inl rfl))
      · rw [mem_supportNat_left]; decide
    · apply same_height_nat_xy p hp heven hm hp4 1 (Or.inr rfl) 1 2 0
        (by decide) (by decide) (by decide)
      all_goals rw [mem_supportNat_left]; decide

theorem core_w (q : Fin 4) :
    component p hp heven 2 (.inl q) = component p hp heven 2 (.inr ⟨0, by omega⟩) := by
  fin_cases q
  · trans component p hp heven 2 (.inr ⟨1, by omega⟩)
    · apply same_component_nat p hp heven hm 0 0 (by decide) (by decide)
      · rw [mem_supportNat_left]; decide
      · simp [Shell.directionNat, Shell.mem_aUsers, Shell.aUser]; omega
    · exact auxiliary_w p hp heven hm _
  · apply same_component_nat p hp heven hm 1 0 (by decide) (by decide)
    · rw [mem_supportNat_left]; decide
    · simp [Shell.directionNat, Shell.mem_aUsers, Shell.aUser]
  · apply same_component_nat p hp heven hm 2 0 (by decide) (by decide)
    · rw [mem_supportNat_left]; decide
    · simp [Shell.directionNat, Shell.mem_aUsers, Shell.aUser]; omega
  · apply same_component_nat p hp heven hm 2 1 (by decide) (by decide)
    · rw [mem_supportNat_left]; decide
    · simp [Shell.directionNat, Shell.mem_aUsers, Shell.aUser]; omega

theorem w_connected (x y : Fin 4 ⊕ Shell.Color p) :
    component p hp heven 2 x = component p hp heven 2 y := by
  have h (x : Fin 4 ⊕ Shell.Color p) : component p hp heven 2 x =
      component p hp heven 2 (.inr ⟨0, by omega⟩) := by
    cases x with
    | inl q => exact core_w p hp heven hm q
    | inr c => exact auxiliary_w p hp heven hm c
  exact (h x).trans (h y).symm

end TorusEven.Entry.Seed
