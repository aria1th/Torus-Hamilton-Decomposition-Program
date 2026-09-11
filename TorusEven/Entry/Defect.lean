-- STATUS: main-path
import TorusEven.Entry.NearCircuits

namespace TorusEven.Entry.NearCore

open Collar Surgery

variable {m : ℕ} [NeZero m] (hm : 4 ≤ m) (heven : Even m)

def baseDefect (p : ZMod m × ZMod m) : ZMod 2 :=
  parityMap heven p.2 - (p.1.val - 2 : ℕ)

def defect (v : Point m) : ZMod 2 := baseDefect heven (height v, v 2)

include hm

theorem baseDefect_step (p : ZMod m × ZMod m) :
    baseDefect heven (baseStep 2 p) = baseDefect heven p := by
  rcases p with ⟨h, w⟩
  have hv1 : (1 : ZMod m).val = 1 := ZMod.val_one'' (by omega)
  have h10 : (1 : ZMod m) ≠ 0 := by
    simpa using cast_ne_zero (m := m) (n := 1) (by omega) (by omega)
  change parityMap heven (w + wVoltage 2 h) - ((h + 1).val - 2 : ℕ) =
    parityMap heven w - (h.val - 2 : ℕ)
  by_cases h0 : h = 0
  · subst h
    simp [wVoltage, hv1]
  · by_cases h1 : h = 1
    · subst h
      have hv2 : ((1 : ZMod m) + 1).val = 2 := by
        rw [ZMod.val_add, hv1, Nat.mod_eq_of_lt (by omega)]
      simp [wVoltage, h10, hv1, hv2]
    · have hv : 2 ≤ h.val := by
        have hv0 := (ZMod.val_eq_zero h).not.mpr h0
        have hv1' := (ZMod.val_eq_one (by omega : 1 < m) h).not.mpr h1
        omega
      simp only [wVoltage, if_neg h0, if_neg h1, Fin.isValue, if_true, map_add, map_one]
      by_cases hwrap : h.val + 1 = m
      · have hnext : (h + 1).val = 0 := by
          rw [ZMod.val_add, hv1, hwrap, Nat.mod_self]
        have hsum : (h.val - 2) + 3 = m := by omega
        have hcast := congrArg (fun n : ℕ => (n : ZMod 2)) hsum
        have hm0 : (m : ZMod 2) = 0 := ZMod.natCast_eq_zero_iff_even.mpr heven
        simp only [Nat.cast_add, hm0] at hcast
        change ((h.val - 2 : ℕ) : ZMod 2) + (3 : ZMod 2) = 0 at hcast
        rw [hnext]
        rw [show (3 : ZMod 2) = 1 by decide] at hcast
        simp only [Nat.zero_sub, Nat.cast_zero, sub_zero]
        linear_combination hcast
      · have hnext : (h + 1).val = h.val + 1 := by
          apply (ZMod.val_add_of_lt (by rw [hv1]; have := h.val_lt; omega)).trans
          rw [hv1]
        rw [hnext, show h.val + 1 - 2 = (h.val - 2) + 1 by omega, Nat.cast_add]
        simp

theorem baseDefect_eq_of_mem {p q : ZMod m × ZMod m}
    (h : q ∈ orbitSet (baseStep 2) p) : baseDefect heven q = baseDefect heven p := by
  obtain ⟨n, rfl⟩ := h
  induction n with
  | zero => rfl
  | succ n ih =>
    change baseDefect heven ((baseStep 2)^[n + 1] p) = baseDefect heven p
    rw [Function.iterate_succ_apply', baseDefect_step hm, ih]

omit [NeZero m] in
theorem baseDefect_section (w : ZMod m) : baseDefect heven (1, w) = parityMap heven w := by
  simp [baseDefect, ZMod.val_one'' (by omega : m ≠ 1)]

theorem base_orbit_defect_iff (p q : ZMod m × ZMod m) :
    q ∈ orbitSet (baseStep 2) p ↔ baseDefect heven q = baseDefect heven p := by
  constructor
  · exact baseDefect_eq_of_mem hm heven
  · intro h
    have hsame {a : ZMod m × ZMod m} (hp : a ∈ orbitSet (baseStep 2) p)
        (hq : a ∈ orbitSet (baseStep 2) q) : q ∈ orbitSet (baseStep 2) p := by
      have hq' := mem_orbitSet_symm (baseStep 2).injective hq
      rwa [orbitSet_eq_of_mem (baseStep 2).injective hp] at hq'
    rcases base_two_representative hm heven p with hp | hp <;>
      rcases base_two_representative hm heven q with hq | hq
    · exact hsame hp hq
    · have he := (baseDefect_eq_of_mem hm heven hp).trans
        (h.symm.trans (baseDefect_eq_of_mem hm heven hq).symm)
      simp [baseDefect_section hm] at he
    · have he := (baseDefect_eq_of_mem hm heven hp).trans
        (h.symm.trans (baseDefect_eq_of_mem hm heven hq).symm)
      simp [baseDefect_section hm] at he
    · exact hsame hp hq

theorem orbit_defect_iff (u v : Point m) :
    v ∈ orbitSet (step 2) u ↔ defect heven v = defect heven u := by
  have h := (chart_orbit_iff hm heven 2 (chart.symm u) (chart.symm v)).trans
    (base_orbit_defect_iff hm heven _ _)
  simpa only [Equiv.apply_symm_apply] using h

end TorusEven.Entry.NearCore
