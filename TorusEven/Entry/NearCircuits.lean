-- STATUS: main-path
import TorusEven.Entry.NearHamilton
import TorusEven.Entry.HeightReturn
import TorusEven.Entry.EvenTranslation
import TorusEven.Entry.SingleVoltage
import TorusEven.Collar.CircuitBlocks

namespace TorusEven.Entry.NearCore

open Collar Surgery

variable {m : ℕ} [NeZero m] (hm : 4 ≤ m) (heven : Even m)

include hm

theorem wVoltage_two_sum : (∑ h : ZMod m, wVoltage 2 h) = -2 := by
  have h10 : (1 : ZMod m) ≠ 0 := by
    simpa using cast_ne_zero (m := m) (n := 1) (by omega) (by omega)
  simpa [wVoltage] using sum_zmod_two_exceptions (0 : ZMod m) 1 0 0 1 (Ne.symm h10)

theorem base_two_section_orbit (h x y : ZMod m) :
    (h, y) ∈ orbitSet (baseStep 2) (h, x) ↔
      y ∈ orbitSet (Equiv.addRight (-2 : ZMod m)) x := by
  simpa only [wVoltage_two_sum hm] using heightLift_section_orbit (wVoltage 2) h x y

omit [NeZero m] in
theorem yVoltage_two (p : ZMod m × ZMod m) :
    yVoltage 2 p = if p = (1, 0) ∨ p = (1, 1) then 1 else 0 := by
  rcases p with ⟨h, w⟩
  have h10 : (1 : ZMod m) ≠ 0 := by
    simpa using cast_ne_zero (m := m) (n := 1) (by omega) (by omega)
  by_cases h0 : h = 0
  · subst h
    simp [yVoltage, nearRow, Ne.symm h10]
  · by_cases h1 : h = 1
    · subst h
      by_cases hw : w = 0 ∨ w = 1 <;>
        simp [yVoltage, nearRow, h10, hw, rotate]
    · by_cases hw : h = 2 ∧ w = 0
      · simp only [yVoltage, nearRow, if_neg h0, if_neg h1, if_pos hw]
        simp [Prod.mk.injEq, h1, Equiv.swap_apply_def]
      · simp [yVoltage, nearRow, h0, h1, hw, Prod.mk.injEq]

include heven

theorem base_two_representative (p : ZMod m × ZMod m) :
    (1, 0) ∈ orbitSet (baseStep 2) p ∨ (1, 1) ∈ orbitSet (baseStep 2) p := by
  obtain ⟨⟨h, w⟩, hsec, horb⟩ := heightLift_meets (wVoltage 2) 1 p
  change h = 1 at hsec
  subst h
  rw [← orbitSet_eq_of_mem (baseStep 2).injective horb]
  simpa only [base_two_section_orbit hm] using negTwo_representative heven w

theorem base_two_distinct :
    (1, 1) ∉ orbitSet (baseStep (m := m) 2) (1, 0) := by
  rw [base_two_section_orbit hm]
  exact negTwo_distinct heven

theorem yVoltage_two_single : SingleVoltage (baseStep (m := m) 2) (yVoltage 2) :=
  singleVoltage_of_pair _ _ (1, 0) (1, 1) (base_two_distinct hm heven)
    (base_two_representative hm heven) (yVoltage_two hm)

theorem base_two_circuitCount : circuitCount (baseStep (m := m) 2) = 2 := by
  change circuitCount (lift (Equiv.addRight 1) (wVoltage 2)) = 2
  rw [heightLift_circuitCount, wVoltage_two_sum hm]
  exact negTwo_circuitCount heven

theorem unit (c : Fin 3) : UnitCarry (baseStep (m := m) c) (yVoltage c) := by
  fin_cases c
  · apply unitCarry_of_singleCycle (baseStep (m := m) 0) (yVoltage 0) base_hamilton_zero
    change IsUnit (∑ p : ZMod m × ZMod m, yVoltage 0 p)
    rw [yVoltage_sum hm 0 (Or.inl rfl)]
    exact isUnit_one.neg
  · apply unitCarry_of_singleCycle (baseStep (m := m) 1) (yVoltage 1) (base_hamilton_one hm)
    change IsUnit (∑ p : ZMod m × ZMod m, yVoltage 1 p)
    rw [yVoltage_sum hm 1 (Or.inr rfl)]
    exact isUnit_one.neg
  · exact (yVoltage_two_single hm heven).unit _ _

theorem chart_orbit_iff (c : Fin 3) (p q : (ZMod m × ZMod m) × ZMod m) :
    chart q ∈ orbitSet (step c) (chart p) ↔ q.1 ∈ orbitSet (baseStep c) p.1 :=
  (orbit_equiv_iff _ _ chart (fun x => (step_chart c x).symm) p q).trans
    (lift_orbit_iff _ _ (unit hm heven c) p q)

theorem consistent : CircuitConsistent (factorization (m := m)) chart where
  direction c p s t := by
    change nearRow (height (chart (p, s))) p.2 c = nearRow (height (chart (p, t))) p.2 c
    simp only [height_chart]
  circuit c p s t := (circuitOf_eq _ _ _).mpr
    ((chart_orbit_iff hm heven c (p, s) (p, t)).mpr (self_mem_orbitSet _ p))

theorem circuitCount_two : circuitCount ((factorization (m := m)).step 2) = 2 := by
  have he := circuitCount_congr (lift (baseStep 2) (yVoltage 2)) (step (m := m) 2)
    chart (fun x => (step_chart 2 x).symm)
  rw [lift_circuitCount _ _ (unit hm heven 2)] at he
  exact he.symm.trans (base_two_circuitCount hm heven)

theorem circuitCount (c : Fin 3) : Surgery.circuitCount ((factorization (m := m)).step c) =
    if c = 2 then 2 else 1 := by
  fin_cases c
  · exact circuitCount_one_of_singleCycle _ (hamilton hm 0 (Or.inl rfl))
  · exact circuitCount_one_of_singleCycle _ (hamilton hm 1 (Or.inr rfl))
  · exact circuitCount_two hm heven

theorem circuitLabel_card : Fintype.card (factorization (m := m)).CircuitLabel = 4 := by
  classical
  rw [← Nat.card_eq_fintype_card]
  change Nat.card (Σ c : Fin 3, Circuit ((factorization (m := m)).step c)) = 4
  rw [Nat.card_sigma]
  change (∑ c : Fin 3, Surgery.circuitCount ((factorization (m := m)).step c)) = 4
  simp [circuitCount hm heven, Fin.sum_univ_succ]

end TorusEven.Entry.NearCore
