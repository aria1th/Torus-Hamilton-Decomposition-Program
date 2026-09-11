-- STATUS: main-path
import TorusEven.Entry.NearCore
import TorusEven.Entry.LayerSums
import TorusEven.Collar.Circuits

namespace TorusEven.Entry.NearCore

open Collar Surgery

variable {m : ℕ} [NeZero m] (hm : 4 ≤ m)

theorem base_hamilton_zero : Shared.IsSingleCycleMap (baseStep (m := m) 0) := by
  apply lift_singleCycle _ height_singleCycle _ 0
  have hs : (∑ h : ZMod m, wVoltage 0 h) = 1 := by simp [wVoltage]
  rw [hs]
  exact isUnit_one

include hm

theorem base_hamilton_one : Shared.IsSingleCycleMap (baseStep (m := m) 1) := by
  apply lift_singleCycle _ height_singleCycle _ 0
  have h10 : (1 : ZMod m) ≠ 0 := by
    simpa using cast_ne_zero (m := m) (n := 1) (by omega) (by omega)
  have hs : (∑ h : ZMod m, wVoltage 1 h) = 1 := by
    have he (h : ZMod m) : wVoltage 1 h = if h = 1 then 1 else 0 := by
      by_cases h0 : h = 0
      · subst h; simp [wVoltage, Ne.symm h10]
      · simp [wVoltage, h0]
    simp [he]
  rw [hs]
  exact isUnit_one

theorem yVoltage_sum (c : Fin 3) (hc : c = 0 ∨ c = 1) :
    (∑ p : ZMod m × ZMod m, yVoltage c p) = -1 := by
  have h10 : (1 : ZMod m) ≠ 0 := by
    simpa using cast_ne_zero (m := m) (n := 1) (by omega) (by omega)
  have h20 : (2 : ZMod m) ≠ 0 := by
    simpa using cast_ne_zero (m := m) (n := 2) (by omega) (by omega)
  have h21 : (2 : ZMod m) ≠ 1 := by intro h; apply h10; linear_combination h
  have hrow (h : ZMod m) : (∑ w : ZMod m, yVoltage c (h, w)) =
      if c = 0 then (if h = 1 then -2 else if h = 2 then 1 else 0)
      else if h = 2 then -1 else 0 := by
    by_cases h0 : h = 0
    · subst h
      rcases hc with rfl | rfl <;>
        simp [yVoltage, nearRow, Equiv.swap_apply_def, Ne.symm h10, Ne.symm h20]
    · by_cases h1 : h = 1
      · subst h
        rcases hc with rfl | rfl
        · have hf (w : ZMod m) : yVoltage 0 (1, w) =
              if w = 0 then 0 else if w = 1 then 0 else 1 := by
            by_cases hw0 : w = 0 <;> by_cases hw1 : w = 1 <;>
              simp_all [yVoltage, nearRow, rotate, Equiv.swap_apply_def]
          simp only [hf, Fin.isValue, if_true]
          rw [sum_zmod_two_exceptions 0 1 0 0 1 (Ne.symm h10)]
          ring
        · have hf (w : ZMod m) : yVoltage 1 (1, w) = 0 := by
            by_cases hw : w = 0 ∨ w = 1 <;>
              simp [yVoltage, nearRow, h10, hw, rotate]
          simp [hf, Ne.symm h21]
      · by_cases h2 : h = 2
        · subst h
          rcases hc with rfl | rfl
          · have hf (w : ZMod m) : yVoltage 0 (2, w) = if w = 0 then 1 else 0 := by
              by_cases hw : w = 0 <;>
                simp [yVoltage, nearRow, h20, h21, hw]
            simp [hf, h21]
          · have hf (w : ZMod m) : yVoltage 1 (2, w) = if w = 0 then 0 else 1 := by
              by_cases hw : w = 0 <;>
                simp [yVoltage, nearRow, h20, h21, hw]
            simp only [hf, Fin.isValue, Fin.reduceEq, if_false, if_true]
            rw [sum_zmod_if_eq]
            ring
        · rcases hc with rfl | rfl <;> simp [yVoltage, nearRow, h0, h1, h2]
  rw [Fintype.sum_prod_type]
  simp only [hrow]
  rcases hc with rfl | rfl
  · simp only [Fin.isValue, if_true]
    have he (h : ZMod m) :
        (if h = 1 then (-2 : ZMod m) else if h = 2 then 1 else 0) =
          (if h = 1 then -2 else 0) + if h = 2 then 1 else 0 := by
      by_cases h1 : h = 1
      · subst h; simp [Ne.symm h21]
      · simp [h1]
    simp only [he, Finset.sum_add_distrib]
    simp
    ring
  · simp

theorem hamilton (c : Fin 3) (hc : c = 0 ∨ c = 1) :
    Shared.IsSingleCycleMap ((factorization (m := m)).step c) := by
  have hb : Shared.IsSingleCycleMap (baseStep (m := m) c) := by
    rcases hc with rfl | rfl
    · exact base_hamilton_zero
    · exact base_hamilton_one hm
  have hy : IsUnit (∑ p : ZMod m × ZMod m, yVoltage c p) := by
    rw [yVoltage_sum hm c hc]
    exact isUnit_one.neg
  have hl := lift_singleCycle (baseStep c) hb (yVoltage c) 0 hy
  have hs : Function.Semiconj (chart (m := m)) (lift (baseStep c) (yVoltage c)) (step c) := by
    intro p
    exact (step_chart c p).symm
  refine ⟨(step c).bijective, ?_⟩
  intro x y
  obtain ⟨n, hn⟩ := hl.2 (chart.symm x) (chart.symm y)
  exact ⟨n, by simpa using (hs.iterate_right n (chart.symm x)).symm.trans (congrArg chart hn)⟩

end TorusEven.Entry.NearCore
