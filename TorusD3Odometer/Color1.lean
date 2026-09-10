import TorusD3Even.Color1
import Mathlib.Tactic

namespace TorusD3Odometer

instance factFiveOfFactNine [Fact (9 < m)] : Fact (5 < m) := by
  have hm9 : 9 < m := Fact.out
  exact ⟨by omega⟩

instance factSevenOfFactNine [Fact (9 < m)] : Fact (7 < m) := by
  have hm9 : 9 < m := Fact.out
  exact ⟨by omega⟩

abbrev laneMap1CaseI (m : ℕ) [Fact (5 < m)] := TorusD3Even.T1CaseI (m := m)

abbrev laneMap1CaseII (m : ℕ) [Fact (9 < m)] (hm : m % 6 = 4) :=
  TorusD3Even.T1CaseII (m := m) hm

def laneMap1 (m : ℕ) [Fact (9 < m)] : Fin m → Fin m :=
  if hm4 : m % 6 = 4 then
    laneMap1CaseII (m := m) hm4
  else
    laneMap1CaseI (m := m)

theorem mod_six_eq_zero_or_two_or_four_of_even (hm : Even m) :
    m % 6 = 0 ∨ m % 6 = 2 ∨ m % 6 = 4 := by
  rcases hm with ⟨k, rfl⟩
  have hparity : ((2 * k) % 6) % 2 = 0 := by
    rw [Nat.mod_mod_of_dvd (2 * k) (by decide : 2 ∣ 6)]
    simp
  have hlt : (2 * k) % 6 < 6 := Nat.mod_lt _ (by decide)
  interval_cases h : (2 * k) % 6 <;>
    simp [two_mul] at h ⊢ <;> omega

theorem cycleOn_laneMap1_caseI_mod_two [Fact (5 < m)] [Fact (7 < m)] (hm : m % 6 = 2) :
    TorusD4.CycleOn m (laneMap1CaseI (m := m)) ⟨0, by
      have hm5 : 5 < m := Fact.out
      omega⟩ := by
  simpa [laneMap1CaseI] using TorusD3Even.cycleOn_T1CaseIModTwo (m := m) hm

theorem cycleOn_laneMap1_caseI_mod_zero [Fact (5 < m)] (hm : m % 6 = 0) :
    TorusD4.CycleOn m (laneMap1CaseI (m := m)) ⟨0, by
      have hm5 : 5 < m := Fact.out
      omega⟩ := by
  simpa [laneMap1CaseI] using TorusD3Even.cycleOn_T1CaseIModZero (m := m) hm

theorem cycleOn_laneMap1_caseII_mod_four [Fact (9 < m)] (hm : m % 6 = 4) :
    TorusD4.CycleOn m (laneMap1CaseII (m := m) hm) ⟨0, by
      have hm9 : 9 < m := Fact.out
      omega⟩ := by
  simpa [laneMap1CaseII] using TorusD3Even.cycleOn_T1CaseIIModFour (m := m) hm

theorem cycleOn_laneMap1 [Fact (9 < m)] (hmEven : Even m) :
    TorusD4.CycleOn m (laneMap1 (m := m)) ⟨0, by
      have hm9 : 9 < m := Fact.out
      omega⟩ := by
  rcases mod_six_eq_zero_or_two_or_four_of_even (m := m) hmEven with hm0 | hm2 | hm4
  · have hne4 : m % 6 ≠ 4 := by omega
    simpa [laneMap1, hm0, hne4] using cycleOn_laneMap1_caseI_mod_zero (m := m) hm0
  · have hne4 : m % 6 ≠ 4 := by omega
    simpa [laneMap1, hm2, hne4] using cycleOn_laneMap1_caseI_mod_two (m := m) hm2
  · simpa [laneMap1, hm4] using cycleOn_laneMap1_caseII_mod_four (m := m) hm4

end TorusD3Odometer
