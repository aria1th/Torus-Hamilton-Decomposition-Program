-- STATUS: main-path
import TorusEven.Entry.NearCircuits

namespace TorusEven.Entry

open Collar Surgery

variable {m : ℕ}

def xChart : ((ZMod m × ZMod m) × ZMod m) ≃ Point m where
  toFun p := ![p.2, p.1.1 - p.1.2 - p.2, p.1.2]
  invFun v := ((height v, v 2), v 0)
  left_inv p := by
    rcases p with ⟨⟨h, w⟩, x⟩
    dsimp [height]
    congr 2
    ring
  right_inv v := by
    funext j
    fin_cases j <;> simp [height]

@[simp] theorem height_xChart (p : (ZMod m × ZMod m) × ZMod m) :
    height (xChart p) = p.1.1 := by
  simp [height, xChart]

theorem xChart_eq_chart (p : (ZMod m × ZMod m) × ZMod m) :
    xChart p = NearCore.chart (p.1, p.1.1 - p.1.2 - p.2) := by
  funext j
  fin_cases j <;> simp [xChart, NearCore.chart]

def anchorColor : Fin 4 → Fin 3 := ![0, 1, 2, 2]

def replacementSupport (m : ℕ) : Set (Point m) :=
  {v | terminalRow v ≠ nearRow (height v) (v 2)}

instance : DecidablePred (· ∈ replacementSupport m) :=
  fun v => inferInstanceAs (Decidable (terminalRow v ≠ nearRow (height v) (v 2)))

variable [NeZero m] (hm : 4 ≤ m) (heven : Even m)

include hm

omit [NeZero m] in
theorem anchor_outside (q : Fin 4) : anchor q ∉ replacementSupport m := by
  exact fun h => h (anchor_agreement hm q)

omit [NeZero m] in
theorem anchor_direction (q : Fin 4) :
    (NearCore.factorization (m := m)).direction (anchorColor q) (anchor q) = 0 := by
  have h10 : (1 : ZMod m) ≠ 0 := by
    simpa using cast_ne_zero (m := m) (n := 1) (by omega) (by omega)
  have h20 : (2 : ZMod m) ≠ 0 := by
    simpa using cast_ne_zero (m := m) (n := 2) (by omega) (by omega)
  have h30 : (3 : ZMod m) ≠ 0 := by
    simpa using cast_ne_zero (m := m) (n := 3) (by omega) (by omega)
  have h21 : (2 : ZMod m) ≠ 1 := by intro h; apply h10; linear_combination h
  have h31 : (3 : ZMod m) ≠ 1 := by intro h; apply h20; linear_combination h
  fin_cases q <;>
    simp [NearCore.factorization, anchor, anchorColor, height, nearRow, rotate,
      Equiv.swap_apply_def, h10, h20, h30, h21, h31,
      show (1 : ZMod m) + 1 = 2 by ring, show -(2 : ZMod m) + 3 = 1 by ring]

def anchorLabel (q : Fin 4) : (NearCore.factorization (m := m)).CircuitLabel :=
  ⟨anchorColor q, circuitOf (NearCore.step (anchorColor q)) (anchor q)⟩

include heven

theorem xChart_consistent : CircuitConsistent (NearCore.factorization (m := m)) xChart where
  direction c p s t := by
    change nearRow (height (xChart (p, s))) p.2 c = nearRow (height (xChart (p, t))) p.2 c
    simp only [height_xChart]
  circuit c p s t := by
    rw [xChart_eq_chart, xChart_eq_chart]
    exact (NearCore.consistent hm heven).circuit c p _ _

theorem anchor_two_distinct :
    anchor 3 ∉ orbitSet (NearCore.step (m := m) 2) (anchor 2) := by
  intro h
  have hb := (NearCore.chart_orbit_iff hm heven 2
    (NearCore.chart.symm (anchor 2)) (NearCore.chart.symm (anchor 3))).mp (by simpa using h)
  have hb' : (1, 3) ∈ orbitSet (NearCore.baseStep (m := m) 2) (0, 0) := by
    simpa [NearCore.chart, anchor, height, show -(2 : ZMod m) + 3 = 1 by ring] using hb
  have h01 : (1, 0) ∈ orbitSet (NearCore.baseStep (m := m) 2) (0, 0) :=
    ⟨1, by simp [NearCore.baseStep, lift, NearCore.wVoltage]⟩
  rw [← orbitSet_eq_of_mem (NearCore.baseStep 2).injective h01,
    NearCore.base_two_section_orbit hm, negTwo_orbit_iff heven] at hb'
  have hthree : parityMap heven (3 : ZMod m) = 1 := by
    change parityMap heven ((3 : ℕ) : ZMod m) = 1
    rw [map_natCast]
    rfl
  simp only [hthree, map_zero] at hb'
  exact one_ne_zero hb'

theorem anchorLabel_injective : Function.Injective (anchorLabel (m := m)) := by
  have hsep : anchorLabel (m := m) 2 ≠ anchorLabel 3 := by
    intro h
    have he : circuitOf (NearCore.step (m := m) 2) (anchor 2) =
        circuitOf (NearCore.step 2) (anchor 3) := by
      exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
    exact anchor_two_distinct hm heven ((circuitOf_eq _ _ _).mp he)
  intro a b hab
  have hc := congrArg Sigma.fst hab
  change anchorColor a = anchorColor b at hc
  fin_cases a <;> fin_cases b <;> simp_all [anchorColor]

noncomputable def anchorEquiv : Fin 4 ≃ (NearCore.factorization (m := m)).CircuitLabel :=
  Equiv.ofBijective anchorLabel ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨anchorLabel_injective hm heven, by simp [NearCore.circuitLabel_card hm heven]⟩)

omit heven in
theorem anchorLabel_mem (q : Fin 4) :
    anchorLabel q ∈ (NearCore.factorization (m := m)).supportAt 0 (anchor q) := by
  exact (MultitorusFactorization.mem_supportAt _ _ _ _).mpr ⟨anchor_direction hm q, rfl⟩

end TorusEven.Entry
