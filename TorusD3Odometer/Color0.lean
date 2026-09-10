import TorusD3Even.Color0
import Mathlib.Tactic

namespace TorusD3Odometer

instance factFourOfFactNine [Fact (9 < m)] : Fact (4 < m) := by
  have hm9 : 9 < m := Fact.out
  exact ⟨by omega⟩

abbrev laneMap0CaseI (m : ℕ) [Fact (4 < m)] := TorusD3Even.T0CaseI (m := m)

private theorem mod_six_eq_four_of_mod_twelve_eq_ten (hm : m % 12 = 10) :
    m % 6 = 4 := by
  omega

private theorem mod_six_eq_four_of_mod_twelve_eq_four (hm : m % 12 = 4) :
    m % 6 = 4 := by
  omega

def laneMap0 (m : ℕ) [Fact (9 < m)] : Fin m → Fin m :=
  if hm4 : m % 6 = 4 then
    TorusD3Even.T0CaseII (m := m) hm4
  else
    laneMap0CaseI (m := m)

theorem mod_twelve_even_residues_of_even (hm : Even m) :
    m % 12 = 0 ∨ m % 12 = 2 ∨ m % 12 = 4 ∨ m % 12 = 6 ∨ m % 12 = 8 ∨ m % 12 = 10 := by
  rcases hm with ⟨k, rfl⟩
  have hparity : ((2 * k) % 12) % 2 = 0 := by
    rw [Nat.mod_mod_of_dvd (2 * k) (by decide : 2 ∣ 12)]
    simp
  have hlt : (2 * k) % 12 < 12 := Nat.mod_lt _ (by decide)
  interval_cases h : (2 * k) % 12 <;>
    simp [two_mul] at h ⊢ <;> omega

abbrev laneMap0CaseII_modTen (m : ℕ) [Fact (9 < m)] (hm : m % 12 = 10) :=
  TorusD3Even.T0CaseII (m := m) (mod_six_eq_four_of_mod_twelve_eq_ten (m := m) hm)

abbrev laneMap0CaseII_modFour (m : ℕ) [Fact (9 < m)] (hm : m % 12 = 4) :=
  TorusD3Even.T0CaseII (m := m) (mod_six_eq_four_of_mod_twelve_eq_four (m := m) hm)

theorem cycleOn_laneMap0_caseI_mod_zeroTwo [Fact (4 < m)] (hm : m % 6 = 0 ∨ m % 6 = 2) :
    TorusD4.CycleOn m (laneMap0CaseI (m := m)) ⟨0, by
      have hm4 : 4 < m := Fact.out
      omega⟩ := by
  simpa [laneMap0CaseI] using TorusD3Even.cycleOn_T0CaseIModZeroTwo (m := m) hm

theorem cycleOn_laneMap0_caseII_mod_ten [Fact (9 < m)] (hm : m % 12 = 10) :
    TorusD4.CycleOn m (laneMap0CaseII_modTen (m := m) hm) ⟨0, by omega⟩ := by
  simpa [laneMap0CaseII_modTen] using TorusD3Even.cycleOn_T0CaseIIModTen (m := m) hm

theorem cycleOn_laneMap0_caseII_mod_four [Fact (9 < m)] (hm : m % 12 = 4) :
    TorusD4.CycleOn m (laneMap0CaseII_modFour (m := m) hm) ⟨0, by omega⟩ := by
  simpa [laneMap0CaseII_modFour] using TorusD3Even.cycleOn_T0CaseIIModFour (m := m) hm

theorem cycleOn_laneMap0 [Fact (9 < m)] (hmEven : Even m) :
    TorusD4.CycleOn m (laneMap0 (m := m)) ⟨0, by
      have hm9 : 9 < m := Fact.out
      omega⟩ := by
  rcases mod_twelve_even_residues_of_even (m := m) hmEven with
    hm0 | hm2 | hm4 | hm6 | hm8 | hm10
  · have hmCaseI : m % 6 = 0 ∨ m % 6 = 2 := by
      left
      omega
    have hne4 : m % 6 ≠ 4 := by omega
    simpa [laneMap0, hm0, hmCaseI, hne4] using cycleOn_laneMap0_caseI_mod_zeroTwo (m := m) hmCaseI
  · have hmCaseI : m % 6 = 0 ∨ m % 6 = 2 := by
      right
      omega
    have hne4 : m % 6 ≠ 4 := by omega
    simpa [laneMap0, hm2, hmCaseI, hne4] using cycleOn_laneMap0_caseI_mod_zeroTwo (m := m) hmCaseI
  · have hm4' : m % 6 = 4 := mod_six_eq_four_of_mod_twelve_eq_four (m := m) hm4
    simpa [laneMap0, hm4', hm4] using cycleOn_laneMap0_caseII_mod_four (m := m) hm4
  · have hmCaseI : m % 6 = 0 ∨ m % 6 = 2 := by
      left
      omega
    have hne4 : m % 6 ≠ 4 := by omega
    simpa [laneMap0, hm6, hmCaseI, hne4] using cycleOn_laneMap0_caseI_mod_zeroTwo (m := m) hmCaseI
  · have hmCaseI : m % 6 = 0 ∨ m % 6 = 2 := by
      right
      omega
    have hne4 : m % 6 ≠ 4 := by omega
    simpa [laneMap0, hm8, hmCaseI, hne4] using cycleOn_laneMap0_caseI_mod_zeroTwo (m := m) hmCaseI
  · have hm4' : m % 6 = 4 := mod_six_eq_four_of_mod_twelve_eq_ten (m := m) hm10
    simpa [laneMap0, hm4', hm10] using cycleOn_laneMap0_caseII_mod_ten (m := m) hm10

end TorusD3Odometer
