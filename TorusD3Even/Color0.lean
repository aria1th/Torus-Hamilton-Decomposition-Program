import TorusD3Even.Splice
import Mathlib.Tactic

namespace TorusD3Even

local instance instFactZeroLtFour : Fact (0 < 4) := ⟨by decide⟩

def T0CaseI [Fact (4 < m)] (x : Fin m) : Fin m :=
  let hm4 : 4 < m := Fact.out
  if hx0 : x.1 = 0 then
    ⟨m - 2, by omega⟩
  else if hxm4 : x.1 = m - 4 then
    ⟨m - 1, by omega⟩
  else if hxm3 : x.1 = m - 3 then
    ⟨2, by omega⟩
  else if hxm2 : x.1 = m - 2 then
    ⟨1, by omega⟩
  else if hxm1 : x.1 = m - 1 then
    ⟨0, by omega⟩
  else
    ⟨x.1 + 2, by omega⟩

theorem mod_two_eq_zero_of_mod_six_zero_or_two (hm : m % 6 = 0 ∨ m % 6 = 2) :
    m % 2 = 0 := by
  rcases hm with hm | hm <;> omega

theorem eq_six_mul_of_mod_six_eq_zero (hm : m % 6 = 0) :
    ∃ q, m = 6 * q := by
  refine ⟨m / 6, ?_⟩
  have hdiv := Nat.mod_add_div m 6
  omega

theorem eq_six_mul_add_two_of_mod_six_eq_two (hm : m % 6 = 2) :
    ∃ q, m = 6 * q + 2 := by
  refine ⟨m / 6, ?_⟩
  have hdiv := Nat.mod_add_div m 6
  omega

def lenT0CaseIModZeroTwo (m : ℕ) : Fin 4 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => (m - 4) / 2
  | ⟨2, _⟩ => (m - 6) / 2
  | _ => 0

def pointT0CaseIModZeroTwoZero [Fact (4 < m)] :
    Fin (lenT0CaseIModZeroTwo m 0 + 1) → Fin m := fun s =>
  if hs0 : s.1 = 0 then
    ⟨0, by
      have hm4 : 4 < m := Fact.out
      omega⟩
  else
    ⟨m - 2, by
      have hm4 : 4 < m := Fact.out
      omega⟩

def pointT0CaseIModZeroTwoOne [Fact (4 < m)] :
    Fin (lenT0CaseIModZeroTwo m 1 + 1) → Fin m := fun s =>
  ⟨1 + 2 * s.1, by
    have hm4 : 4 < m := Fact.out
    have hsLe : s.1 ≤ (m - 4) / 2 := Nat.lt_succ_iff.mp s.2
    have hmul : 2 * s.1 ≤ 2 * ((m - 4) / 2) := Nat.mul_le_mul_left 2 hsLe
    have hdiv : 2 * ((m - 4) / 2) ≤ m - 4 := Nat.mul_div_le (m - 4) 2
    omega⟩

def pointT0CaseIModZeroTwoTwo [Fact (4 < m)] :
    Fin (lenT0CaseIModZeroTwo m 2 + 1) → Fin m := fun s =>
  ⟨2 + 2 * s.1, by
    have hm4 : 4 < m := Fact.out
    have hsLe : s.1 ≤ (m - 6) / 2 := Nat.lt_succ_iff.mp s.2
    have hmul : 2 * s.1 ≤ 2 * ((m - 6) / 2) := Nat.mul_le_mul_left 2 hsLe
    have hdiv : 2 * ((m - 6) / 2) ≤ m - 6 := Nat.mul_div_le (m - 6) 2
    omega⟩

def pointT0CaseIModZeroTwoThree [Fact (4 < m)] :
    Fin (lenT0CaseIModZeroTwo m 3 + 1) → Fin m := fun _ =>
  ⟨m - 1, by
    have hm4 : 4 < m := Fact.out
    omega⟩

def pointT0CaseIModZeroTwo [Fact (4 < m)] (j : Fin 4) :
    Fin (lenT0CaseIModZeroTwo m j + 1) → Fin m :=
  match j with
  | ⟨0, _⟩ => pointT0CaseIModZeroTwoZero (m := m)
  | ⟨1, _⟩ => pointT0CaseIModZeroTwoOne (m := m)
  | ⟨2, _⟩ => pointT0CaseIModZeroTwoTwo (m := m)
  | ⟨_ + 3, _⟩ => pointT0CaseIModZeroTwoThree (m := m)

def pointT0CaseIModZeroTwoSigma [Fact (4 < m)] :
    SplicePoint (lenT0CaseIModZeroTwo m) → Fin m
  | ⟨j, s⟩ => pointT0CaseIModZeroTwo (m := m) j s

theorem card_splicePoint_lenT0CaseIModZeroTwo [Fact (4 < m)] (hm : m % 6 = 0 ∨ m % 6 = 2) :
    Fintype.card (SplicePoint (lenT0CaseIModZeroTwo m)) = m := by
  have hcard :
      Fintype.card (SplicePoint (lenT0CaseIModZeroTwo m))
        = ∑ j : Fin 4, (lenT0CaseIModZeroTwo m j + 1) := by
    simpa [SplicePoint] using
      (Fintype.card_sigma (α := fun j : Fin 4 => Fin (lenT0CaseIModZeroTwo m j + 1)))
  rcases hm with hm | hm
  · rcases eq_six_mul_of_mod_six_eq_zero (m := m) hm with ⟨q, rfl⟩
    have hq : 1 ≤ q := by
      have hm4 : 4 < 6 * q := Fact.out
      omega
    have h0 : lenT0CaseIModZeroTwo (6 * q) 0 = 1 := by
      simp [lenT0CaseIModZeroTwo]
    have h1 : lenT0CaseIModZeroTwo (6 * q) 1 = 3 * q - 2 := by
      change (6 * q - 4) / 2 = 3 * q - 2
      omega
    have h2 : lenT0CaseIModZeroTwo (6 * q) 2 = 3 * q - 3 := by
      change (6 * q - 6) / 2 = 3 * q - 3
      omega
    have h3 : lenT0CaseIModZeroTwo (6 * q) 3 = 0 := by
      simp [lenT0CaseIModZeroTwo]
    rw [hcard, Fin.sum_univ_four, h0, h1, h2, h3]
    omega
  · rcases eq_six_mul_add_two_of_mod_six_eq_two (m := m) hm with ⟨q, rfl⟩
    have hq : 1 ≤ q := by
      have hm4 : 4 < 6 * q + 2 := Fact.out
      omega
    have h0 : lenT0CaseIModZeroTwo (6 * q + 2) 0 = 1 := by
      simp [lenT0CaseIModZeroTwo]
    have h1 : lenT0CaseIModZeroTwo (6 * q + 2) 1 = 3 * q - 1 := by
      change (6 * q + 2 - 4) / 2 = 3 * q - 1
      omega
    have h2 : lenT0CaseIModZeroTwo (6 * q + 2) 2 = 3 * q - 2 := by
      change (6 * q + 2 - 6) / 2 = 3 * q - 2
      omega
    have h3 : lenT0CaseIModZeroTwo (6 * q + 2) 3 = 0 := by
      simp [lenT0CaseIModZeroTwo]
    rw [hcard, Fin.sum_univ_four, h0, h1, h2, h3]
    omega

theorem T0CaseI_eq_m_sub_two_of_val_eq_zero [Fact (4 < m)] {x : Fin m} (hx : x.1 = 0) :
    (T0CaseI (m := m) x).1 = m - 2 := by
  simp [T0CaseI, hx]

theorem T0CaseI_eq_m_sub_one_of_val_eq_m_sub_four [Fact (4 < m)] {x : Fin m}
    (hx : x.1 = m - 4) :
    (T0CaseI (m := m) x).1 = m - 1 := by
  have hm4 : 4 < m := Fact.out
  have hm40 : m - 4 ≠ 0 := by omega
  simpa [T0CaseI, hx, hm40]

theorem T0CaseI_eq_two_of_val_eq_m_sub_three [Fact (4 < m)] {x : Fin m}
    (hx : x.1 = m - 3) :
    (T0CaseI (m := m) x).1 = 2 := by
  have hm4 : 4 < m := Fact.out
  have hm30 : m - 3 ≠ 0 := by omega
  have hm34 : m - 3 ≠ m - 4 := by omega
  simpa [T0CaseI, hx, hm30, hm34]

theorem T0CaseI_eq_one_of_val_eq_m_sub_two [Fact (4 < m)] {x : Fin m}
    (hx : x.1 = m - 2) :
    (T0CaseI (m := m) x).1 = 1 := by
  have hm4 : 4 < m := Fact.out
  have hm20 : m - 2 ≠ 0 := by omega
  have hm24 : m - 2 ≠ m - 4 := by omega
  have hm23 : m - 2 ≠ m - 3 := by omega
  simpa [T0CaseI, hx, hm20, hm24, hm23]

theorem T0CaseI_eq_zero_of_val_eq_m_sub_one [Fact (4 < m)] {x : Fin m}
    (hx : x.1 = m - 1) :
    (T0CaseI (m := m) x).1 = 0 := by
  have hm4 : 4 < m := Fact.out
  have hm10 : m - 1 ≠ 0 := by omega
  have hm14 : m - 1 ≠ m - 4 := by omega
  have hm13 : m - 1 ≠ m - 3 := by omega
  have hm12 : m - 1 ≠ m - 2 := by omega
  simpa [T0CaseI, hx, hm10, hm14, hm13, hm12]

theorem T0CaseI_eq_add_two_of_ne_special [Fact (4 < m)] {x : Fin m}
    (hx0 : x.1 ≠ 0) (hxm4 : x.1 ≠ m - 4) (hxm3 : x.1 ≠ m - 3)
    (hxm2 : x.1 ≠ m - 2) (hxm1 : x.1 ≠ m - 1) :
    (T0CaseI (m := m) x).1 = x.1 + 2 := by
  simp [T0CaseI, hx0, hxm4, hxm3, hxm2, hxm1]

theorem pointT0CaseIModZeroTwoZero_val [Fact (4 < m)]
    (s : Fin (lenT0CaseIModZeroTwo m 0 + 1)) :
    (pointT0CaseIModZeroTwoZero (m := m) s).1 = if s.1 = 0 then 0 else m - 2 := by
  by_cases hs0 : s.1 = 0
  · simp [pointT0CaseIModZeroTwoZero, hs0]
  · simp [pointT0CaseIModZeroTwoZero, hs0]

private theorem pointT0CaseIModZeroTwoZero_val_of_eq_zero [Fact (4 < m)]
    {s : Fin (lenT0CaseIModZeroTwo m 0 + 1)} (hs0 : s.1 = 0) :
    (pointT0CaseIModZeroTwoZero (m := m) s).1 = 0 := by
  rw [pointT0CaseIModZeroTwoZero_val (m := m) (s := s)]
  simp [hs0]

private theorem pointT0CaseIModZeroTwoZero_val_of_ne_zero [Fact (4 < m)]
    {s : Fin (lenT0CaseIModZeroTwo m 0 + 1)} (hs0 : s.1 ≠ 0) :
    (pointT0CaseIModZeroTwoZero (m := m) s).1 = m - 2 := by
  rw [pointT0CaseIModZeroTwoZero_val (m := m) (s := s)]
  simp [hs0]

theorem pointT0CaseIModZeroTwoOne_val [Fact (4 < m)]
    (s : Fin (lenT0CaseIModZeroTwo m 1 + 1)) :
    (pointT0CaseIModZeroTwoOne (m := m) s).1 = 1 + 2 * s.1 := by
  rfl

theorem pointT0CaseIModZeroTwoTwo_val [Fact (4 < m)]
    (s : Fin (lenT0CaseIModZeroTwo m 2 + 1)) :
    (pointT0CaseIModZeroTwoTwo (m := m) s).1 = 2 + 2 * s.1 := by
  rfl

theorem pointT0CaseIModZeroTwoThree_val [Fact (4 < m)]
    (s : Fin (lenT0CaseIModZeroTwo m 3 + 1)) :
    (pointT0CaseIModZeroTwoThree (m := m) s).1 = m - 1 := by
  cases s
  rfl

theorem pointT0CaseIModZeroTwo_zero_zero_val [Fact (4 < m)] :
    (pointT0CaseIModZeroTwo (m := m) 0 0).1 = 0 := by
  simpa [pointT0CaseIModZeroTwo] using
    (pointT0CaseIModZeroTwoZero_val (m := m) (s := (0 : Fin (lenT0CaseIModZeroTwo m 0 + 1))))

theorem pointT0CaseIModZeroTwo_one_zero_val [Fact (4 < m)] :
    (pointT0CaseIModZeroTwo (m := m) 1 0).1 = 1 := by
  simp [pointT0CaseIModZeroTwo, pointT0CaseIModZeroTwoOne_val]

theorem pointT0CaseIModZeroTwo_two_zero_val [Fact (4 < m)] :
    (pointT0CaseIModZeroTwo (m := m) 2 0).1 = 2 := by
  simp [pointT0CaseIModZeroTwo, pointT0CaseIModZeroTwoTwo_val]

theorem pointT0CaseIModZeroTwo_three_zero_val [Fact (4 < m)] :
    (pointT0CaseIModZeroTwo (m := m) 3 0).1 = m - 1 := by
  simp [pointT0CaseIModZeroTwo, pointT0CaseIModZeroTwoThree_val]

theorem pointT0CaseIModZeroTwo_last_zero_val [Fact (4 < m)] :
    (pointT0CaseIModZeroTwo (m := m) 0 ⟨lenT0CaseIModZeroTwo m 0, Nat.lt_succ_self _⟩).1 = m - 2 := by
  let s : Fin (lenT0CaseIModZeroTwo m 0 + 1) := ⟨lenT0CaseIModZeroTwo m 0, Nat.lt_succ_self _⟩
  change (pointT0CaseIModZeroTwoZero (m := m) s).1 = m - 2
  rw [pointT0CaseIModZeroTwoZero_val (m := m) (s := s)]
  have hs0 : s.1 ≠ 0 := by simp [s, lenT0CaseIModZeroTwo]
  simp [hs0]

theorem pointT0CaseIModZeroTwo_last_one_val [Fact (4 < m)] (hm : m % 6 = 0 ∨ m % 6 = 2) :
    (pointT0CaseIModZeroTwo (m := m) 1 ⟨lenT0CaseIModZeroTwo m 1, Nat.lt_succ_self _⟩).1 = m - 3 := by
  let s : Fin (lenT0CaseIModZeroTwo m 1 + 1) := ⟨lenT0CaseIModZeroTwo m 1, Nat.lt_succ_self _⟩
  rcases hm with hm | hm
  · rcases eq_six_mul_of_mod_six_eq_zero (m := m) hm with ⟨q, rfl⟩
    have hq : 1 ≤ q := by
      have hm4 : 4 < 6 * q := Fact.out
      omega
    change (pointT0CaseIModZeroTwoOne (m := 6 * q) s).1 = 6 * q - 3
    rw [pointT0CaseIModZeroTwoOne_val (m := 6 * q) (s := s)]
    change 1 + 2 * ((6 * q - 4) / 2) = 6 * q - 3
    omega
  · rcases eq_six_mul_add_two_of_mod_six_eq_two (m := m) hm with ⟨q, rfl⟩
    have hq : 1 ≤ q := by
      have hm4 : 4 < 6 * q + 2 := Fact.out
      omega
    change (pointT0CaseIModZeroTwoOne (m := 6 * q + 2) s).1 = 6 * q + 2 - 3
    rw [pointT0CaseIModZeroTwoOne_val (m := 6 * q + 2) (s := s)]
    change 1 + 2 * ((6 * q + 2 - 4) / 2) = 6 * q + 2 - 3
    omega

theorem pointT0CaseIModZeroTwo_last_two_val [Fact (4 < m)] (hm : m % 6 = 0 ∨ m % 6 = 2) :
    (pointT0CaseIModZeroTwo (m := m) 2 ⟨lenT0CaseIModZeroTwo m 2, Nat.lt_succ_self _⟩).1 = m - 4 := by
  let s : Fin (lenT0CaseIModZeroTwo m 2 + 1) := ⟨lenT0CaseIModZeroTwo m 2, Nat.lt_succ_self _⟩
  rcases hm with hm | hm
  · rcases eq_six_mul_of_mod_six_eq_zero (m := m) hm with ⟨q, rfl⟩
    have hq : 1 ≤ q := by
      have hm4 : 4 < 6 * q := Fact.out
      omega
    change (pointT0CaseIModZeroTwoTwo (m := 6 * q) s).1 = 6 * q - 4
    rw [pointT0CaseIModZeroTwoTwo_val (m := 6 * q) (s := s)]
    change 2 + 2 * ((6 * q - 6) / 2) = 6 * q - 4
    omega
  · rcases eq_six_mul_add_two_of_mod_six_eq_two (m := m) hm with ⟨q, rfl⟩
    have hq : 1 ≤ q := by
      have hm4 : 4 < 6 * q + 2 := Fact.out
      omega
    change (pointT0CaseIModZeroTwoTwo (m := 6 * q + 2) s).1 = 6 * q + 2 - 4
    rw [pointT0CaseIModZeroTwoTwo_val (m := 6 * q + 2) (s := s)]
    change 2 + 2 * ((6 * q + 2 - 6) / 2) = 6 * q + 2 - 4
    omega

private theorem pointT0CaseIModZeroTwoZero_injective [Fact (4 < m)] :
    Function.Injective (pointT0CaseIModZeroTwoZero (m := m)) := by
  intro s t h
  fin_cases s <;> fin_cases t
  · rfl
  · exfalso
    have hv := congrArg Fin.val h
    have hm4 : 4 < m := Fact.out
    have : (0 : ℕ) = m - 2 := by
      simpa [pointT0CaseIModZeroTwoZero, lenT0CaseIModZeroTwo] using hv
    omega
  · exfalso
    have hv := congrArg Fin.val h
    have hm4 : 4 < m := Fact.out
    have : m - 2 = (0 : ℕ) := by
      simpa [pointT0CaseIModZeroTwoZero, lenT0CaseIModZeroTwo] using hv
    omega
  · rfl

private theorem pointT0CaseIModZeroTwoOne_injective [Fact (4 < m)] :
    Function.Injective (pointT0CaseIModZeroTwoOne (m := m)) := by
  intro s t h
  apply Fin.ext
  have hv := congrArg Fin.val h
  have : 1 + 2 * s.1 = 1 + 2 * t.1 := by
    simpa [pointT0CaseIModZeroTwoOne_val] using hv
  omega

private theorem pointT0CaseIModZeroTwoTwo_injective [Fact (4 < m)] :
    Function.Injective (pointT0CaseIModZeroTwoTwo (m := m)) := by
  intro s t h
  apply Fin.ext
  have hv := congrArg Fin.val h
  have : 2 + 2 * s.1 = 2 + 2 * t.1 := by
    simpa [pointT0CaseIModZeroTwoTwo_val] using hv
  omega

private theorem pointT0CaseIModZeroTwoThree_injective [Fact (4 < m)] :
    Function.Injective (pointT0CaseIModZeroTwoThree (m := m)) := by
  intro s t _
  fin_cases s <;> fin_cases t <;> rfl

private theorem pointT0CaseIModZeroTwoZero_One_disjoint [Fact (4 < m)]
    (hm : m % 6 = 0 ∨ m % 6 = 2) :
    ∀ s t, pointT0CaseIModZeroTwoZero (m := m) s ≠ pointT0CaseIModZeroTwoOne (m := m) t := by
  intro s t h
  have hv := congrArg Fin.val h
  by_cases hs0 : s.1 = 0
  · have : (0 : ℕ) = 1 + 2 * t.1 := by
      simpa [pointT0CaseIModZeroTwoZero_val, pointT0CaseIModZeroTwoOne_val, hs0] using hv
    omega
  · have hmeven : m % 2 = 0 := mod_two_eq_zero_of_mod_six_zero_or_two (m := m) hm
    have : m - 2 = 1 + 2 * t.1 := by
      simpa [pointT0CaseIModZeroTwoZero_val, pointT0CaseIModZeroTwoOne_val, hs0] using hv
    omega

private theorem pointT0CaseIModZeroTwoZero_Two_disjoint [Fact (4 < m)] :
    ∀ s t, pointT0CaseIModZeroTwoZero (m := m) s ≠ pointT0CaseIModZeroTwoTwo (m := m) t := by
  intro s t h
  have hv := congrArg Fin.val h
  by_cases hs0 : s.1 = 0
  · have : (0 : ℕ) = 2 + 2 * t.1 := by
      rw [pointT0CaseIModZeroTwoZero_val_of_eq_zero (m := m) hs0,
        pointT0CaseIModZeroTwoTwo_val (m := m)] at hv
      exact hv
    omega
  · have htLe : t.1 ≤ (m - 6) / 2 := Nat.lt_succ_iff.mp t.2
    have hdiv : 2 * ((m - 6) / 2) ≤ m - 6 := Nat.mul_div_le (m - 6) 2
    have hm4 : 4 < m := Fact.out
    have : m - 2 = 2 + 2 * t.1 := by
      rw [pointT0CaseIModZeroTwoZero_val_of_ne_zero (m := m) hs0,
        pointT0CaseIModZeroTwoTwo_val (m := m)] at hv
      exact hv
    omega

private theorem pointT0CaseIModZeroTwoZero_Three_disjoint [Fact (4 < m)] :
    ∀ s t, pointT0CaseIModZeroTwoZero (m := m) s ≠ pointT0CaseIModZeroTwoThree (m := m) t := by
  intro s t h
  have hv := congrArg Fin.val h
  have hm4 : 4 < m := Fact.out
  by_cases hs0 : s.1 = 0
  · have : (0 : ℕ) = m - 1 := by
      rw [pointT0CaseIModZeroTwoZero_val_of_eq_zero (m := m) hs0,
        pointT0CaseIModZeroTwoThree_val (m := m)] at hv
      exact hv
    omega
  · have : m - 2 = m - 1 := by
      rw [pointT0CaseIModZeroTwoZero_val_of_ne_zero (m := m) hs0,
        pointT0CaseIModZeroTwoThree_val (m := m)] at hv
      exact hv
    omega

private theorem pointT0CaseIModZeroTwoOne_Two_disjoint [Fact (4 < m)] :
    ∀ s t, pointT0CaseIModZeroTwoOne (m := m) s ≠ pointT0CaseIModZeroTwoTwo (m := m) t := by
  intro s t h
  have hv := congrArg Fin.val h
  have : 1 + 2 * s.1 = 2 + 2 * t.1 := by
    simpa [pointT0CaseIModZeroTwoOne_val, pointT0CaseIModZeroTwoTwo_val] using hv
  omega

private theorem pointT0CaseIModZeroTwoOne_Three_disjoint [Fact (4 < m)]
    (hm : m % 6 = 0 ∨ m % 6 = 2) :
    ∀ s t, pointT0CaseIModZeroTwoOne (m := m) s ≠ pointT0CaseIModZeroTwoThree (m := m) t := by
  intro s t h
  have hv := congrArg Fin.val h
  have hm4 : 4 < m := Fact.out
  have hsLe : s.1 ≤ (m - 4) / 2 := Nat.lt_succ_iff.mp s.2
  have hmeven : m % 2 = 0 := mod_two_eq_zero_of_mod_six_zero_or_two (m := m) hm
  have hdiv := Nat.mod_add_div m 2
  have : 1 + 2 * s.1 = m - 1 := by
    rw [pointT0CaseIModZeroTwoOne_val (m := m), pointT0CaseIModZeroTwoThree_val (m := m)] at hv
    exact hv
  omega

private theorem pointT0CaseIModZeroTwoTwo_Three_disjoint [Fact (4 < m)]
    (hm : m % 6 = 0 ∨ m % 6 = 2) :
    ∀ s t, pointT0CaseIModZeroTwoTwo (m := m) s ≠ pointT0CaseIModZeroTwoThree (m := m) t := by
  intro s t h
  have hv := congrArg Fin.val h
  have hm4 : 4 < m := Fact.out
  have hmeven : m % 2 = 0 := mod_two_eq_zero_of_mod_six_zero_or_two (m := m) hm
  have hdiv := Nat.mod_add_div m 2
  have : 2 + 2 * s.1 = m - 1 := by
    rw [pointT0CaseIModZeroTwoTwo_val (m := m), pointT0CaseIModZeroTwoThree_val (m := m)] at hv
    exact hv
  omega

theorem pointT0CaseIModZeroTwoSigma_injective [Fact (4 < m)] (hm : m % 6 = 0 ∨ m % 6 = 2) :
    Function.Injective (pointT0CaseIModZeroTwoSigma (m := m)) := by
  intro p p' h
  rcases p with ⟨j, s⟩
  rcases p' with ⟨j', s'⟩
  fin_cases j <;> fin_cases j'
  · have hs : s = s' := pointT0CaseIModZeroTwoZero_injective (m := m) h
    subst hs
    rfl
  · exfalso
    exact pointT0CaseIModZeroTwoZero_One_disjoint (m := m) hm s s' h
  · exfalso
    exact pointT0CaseIModZeroTwoZero_Two_disjoint (m := m) s s' h
  · exfalso
    exact pointT0CaseIModZeroTwoZero_Three_disjoint (m := m) s s' h
  · exfalso
    exact pointT0CaseIModZeroTwoZero_One_disjoint (m := m) hm s' s h.symm
  · have hs : s = s' := pointT0CaseIModZeroTwoOne_injective (m := m) h
    subst hs
    rfl
  · exfalso
    exact pointT0CaseIModZeroTwoOne_Two_disjoint (m := m) s s' h
  · exfalso
    exact pointT0CaseIModZeroTwoOne_Three_disjoint (m := m) hm s s' h
  · exfalso
    exact pointT0CaseIModZeroTwoZero_Two_disjoint (m := m) s' s h.symm
  · exfalso
    exact pointT0CaseIModZeroTwoOne_Two_disjoint (m := m) s' s h.symm
  · have hs : s = s' := pointT0CaseIModZeroTwoTwo_injective (m := m) h
    subst hs
    rfl
  · exfalso
    exact pointT0CaseIModZeroTwoTwo_Three_disjoint (m := m) hm s s' h
  · exfalso
    exact pointT0CaseIModZeroTwoZero_Three_disjoint (m := m) s' s h.symm
  · exfalso
    exact pointT0CaseIModZeroTwoOne_Three_disjoint (m := m) hm s' s h.symm
  · exfalso
    exact pointT0CaseIModZeroTwoTwo_Three_disjoint (m := m) hm s' s h.symm
  · have hs : s = s' := pointT0CaseIModZeroTwoThree_injective (m := m) h
    subst hs
    rfl

noncomputable def spliceEquivT0CaseIModZeroTwo [Fact (4 < m)] (hm : m % 6 = 0 ∨ m % 6 = 2) :
    SplicePoint (lenT0CaseIModZeroTwo m) ≃ Fin m := by
  let f := pointT0CaseIModZeroTwoSigma (m := m)
  have hinj : Function.Injective f := pointT0CaseIModZeroTwoSigma_injective (m := m) hm
  have hcard : Fintype.card (SplicePoint (lenT0CaseIModZeroTwo m)) = Fintype.card (Fin m) := by
    simpa using card_splicePoint_lenT0CaseIModZeroTwo (m := m) hm
  exact Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩)

@[simp] theorem spliceEquivT0CaseIModZeroTwo_apply [Fact (4 < m)] (hm : m % 6 = 0 ∨ m % 6 = 2)
    (p : SplicePoint (lenT0CaseIModZeroTwo m)) :
    spliceEquivT0CaseIModZeroTwo (m := m) hm p = pointT0CaseIModZeroTwoSigma (m := m) p := by
  rfl

private theorem pointT0CaseIModZeroTwoZero_step [Fact (4 < m)] (hm : m % 6 = 0 ∨ m % 6 = 2)
    (s : Fin (lenT0CaseIModZeroTwo m 0 + 1)) (hs : s.1 + 1 < lenT0CaseIModZeroTwo m 0 + 1) :
    T0CaseI (m := m) (pointT0CaseIModZeroTwo (m := m) 0 s) =
      pointT0CaseIModZeroTwo (m := m) 0 ⟨s.1 + 1, hs⟩ := by
  have hs0 : s.1 = 0 := by
    simp [lenT0CaseIModZeroTwo] at hs
    omega
  have hsEq : s = 0 := Fin.ext hs0
  subst hsEq
  apply Fin.ext
  change (T0CaseI (m := m) (pointT0CaseIModZeroTwo (m := m) 0 0)).1 =
    (pointT0CaseIModZeroTwo (m := m) 0 ⟨1, hs⟩).1
  have hsrc : (pointT0CaseIModZeroTwo (m := m) 0 0).1 = 0 :=
    pointT0CaseIModZeroTwo_zero_zero_val (m := m)
  have hdst : (pointT0CaseIModZeroTwo (m := m) 0 ⟨1, hs⟩).1 = m - 2 := by
    have h1 : (⟨1, hs⟩ : Fin (lenT0CaseIModZeroTwo m 0 + 1)) =
        ⟨lenT0CaseIModZeroTwo m 0, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      simp [lenT0CaseIModZeroTwo]
    rw [h1]
    exact pointT0CaseIModZeroTwo_last_zero_val (m := m)
  rw [T0CaseI_eq_m_sub_two_of_val_eq_zero (m := m) hsrc, hdst]

private theorem pointT0CaseIModZeroTwoOne_step [Fact (4 < m)] (hm : m % 6 = 0 ∨ m % 6 = 2)
    (s : Fin (lenT0CaseIModZeroTwo m 1 + 1)) (hs : s.1 + 1 < lenT0CaseIModZeroTwo m 1 + 1) :
    T0CaseI (m := m) (pointT0CaseIModZeroTwo (m := m) 1 s) =
      pointT0CaseIModZeroTwo (m := m) 1 ⟨s.1 + 1, hs⟩ := by
  have hmeven : m % 2 = 0 := mod_two_eq_zero_of_mod_six_zero_or_two (m := m) hm
  have hcur : (pointT0CaseIModZeroTwo (m := m) 1 s).1 = 1 + 2 * s.1 := by
    simpa [pointT0CaseIModZeroTwo] using pointT0CaseIModZeroTwoOne_val (m := m) (s := s)
  have hx0 : (pointT0CaseIModZeroTwo (m := m) 1 s).1 ≠ 0 := by
    rw [hcur]
    omega
  have hxm4 : (pointT0CaseIModZeroTwo (m := m) 1 s).1 ≠ m - 4 := by
    rw [hcur]
    have hsLt : s.1 < (m - 4) / 2 := by
      simp [lenT0CaseIModZeroTwo] at hs
      omega
    have hdiv := Nat.mod_add_div m 2
    omega
  have hxm3 : (pointT0CaseIModZeroTwo (m := m) 1 s).1 ≠ m - 3 := by
    rw [hcur]
    have hsLt : s.1 < (m - 4) / 2 := by
      simp [lenT0CaseIModZeroTwo] at hs
      omega
    have hdiv := Nat.mod_add_div m 2
    omega
  have hxm2 : (pointT0CaseIModZeroTwo (m := m) 1 s).1 ≠ m - 2 := by
    rw [hcur]
    omega
  have hxm1 : (pointT0CaseIModZeroTwo (m := m) 1 s).1 ≠ m - 1 := by
    rw [hcur]
    have hsLt : s.1 < (m - 4) / 2 := by
      simp [lenT0CaseIModZeroTwo] at hs
      omega
    have hdiv := Nat.mod_add_div m 2
    omega
  apply Fin.ext
  change (T0CaseI (m := m) (pointT0CaseIModZeroTwo (m := m) 1 s)).1 =
    (pointT0CaseIModZeroTwo (m := m) 1 ⟨s.1 + 1, hs⟩).1
  rw [T0CaseI_eq_add_two_of_ne_special (m := m) hx0 hxm4 hxm3 hxm2 hxm1]
  rw [hcur]
  have hnext : (pointT0CaseIModZeroTwo (m := m) 1 ⟨s.1 + 1, hs⟩).1 = 1 + 2 * (s.1 + 1) := by
    simpa [pointT0CaseIModZeroTwo] using
      pointT0CaseIModZeroTwoOne_val (m := m) (s := ⟨s.1 + 1, hs⟩)
  rw [hnext]
  omega

private theorem pointT0CaseIModZeroTwoTwo_step [Fact (4 < m)] (hm : m % 6 = 0 ∨ m % 6 = 2)
    (s : Fin (lenT0CaseIModZeroTwo m 2 + 1)) (hs : s.1 + 1 < lenT0CaseIModZeroTwo m 2 + 1) :
    T0CaseI (m := m) (pointT0CaseIModZeroTwo (m := m) 2 s) =
      pointT0CaseIModZeroTwo (m := m) 2 ⟨s.1 + 1, hs⟩ := by
  have hmeven : m % 2 = 0 := mod_two_eq_zero_of_mod_six_zero_or_two (m := m) hm
  have hcur : (pointT0CaseIModZeroTwo (m := m) 2 s).1 = 2 + 2 * s.1 := by
    simpa [pointT0CaseIModZeroTwo] using pointT0CaseIModZeroTwoTwo_val (m := m) (s := s)
  have hx0 : (pointT0CaseIModZeroTwo (m := m) 2 s).1 ≠ 0 := by
    rw [hcur]
    omega
  have hxm4 : (pointT0CaseIModZeroTwo (m := m) 2 s).1 ≠ m - 4 := by
    rw [hcur]
    have hsLt : s.1 < (m - 6) / 2 := by
      simp [lenT0CaseIModZeroTwo] at hs
      omega
    have hdiv := Nat.mod_add_div m 2
    omega
  have hxm3 : (pointT0CaseIModZeroTwo (m := m) 2 s).1 ≠ m - 3 := by
    rw [hcur]
    omega
  have hxm2 : (pointT0CaseIModZeroTwo (m := m) 2 s).1 ≠ m - 2 := by
    rw [hcur]
    have hsLe : s.1 ≤ (m - 6) / 2 := Nat.lt_succ_iff.mp s.2
    have hdiv := Nat.mod_add_div m 2
    omega
  have hxm1 : (pointT0CaseIModZeroTwo (m := m) 2 s).1 ≠ m - 1 := by
    rw [hcur]
    omega
  apply Fin.ext
  change (T0CaseI (m := m) (pointT0CaseIModZeroTwo (m := m) 2 s)).1 =
    (pointT0CaseIModZeroTwo (m := m) 2 ⟨s.1 + 1, hs⟩).1
  rw [T0CaseI_eq_add_two_of_ne_special (m := m) hx0 hxm4 hxm3 hxm2 hxm1]
  rw [hcur]
  have hnext : (pointT0CaseIModZeroTwo (m := m) 2 ⟨s.1 + 1, hs⟩).1 = 2 + 2 * (s.1 + 1) := by
    simpa [pointT0CaseIModZeroTwo] using
      pointT0CaseIModZeroTwoTwo_val (m := m) (s := ⟨s.1 + 1, hs⟩)
  rw [hnext]
  omega

theorem pointT0CaseIModZeroTwo_step [Fact (4 < m)] (hm : m % 6 = 0 ∨ m % 6 = 2) {j : Fin 4}
    (s : Fin (lenT0CaseIModZeroTwo m j + 1)) (hs : s.1 + 1 < lenT0CaseIModZeroTwo m j + 1) :
    T0CaseI (m := m) (pointT0CaseIModZeroTwo (m := m) j s) =
      pointT0CaseIModZeroTwo (m := m) j ⟨s.1 + 1, hs⟩ := by
  fin_cases j
  · simpa using pointT0CaseIModZeroTwoZero_step (m := m) hm s hs
  · simpa using pointT0CaseIModZeroTwoOne_step (m := m) hm s hs
  · simpa using pointT0CaseIModZeroTwoTwo_step (m := m) hm s hs
  · simp [lenT0CaseIModZeroTwo] at hs

theorem pointT0CaseIModZeroTwo_wrap [Fact (4 < m)] (hm : m % 6 = 0 ∨ m % 6 = 2) :
    ∀ j : Fin 4,
      T0CaseI (m := m)
        (pointT0CaseIModZeroTwo (m := m) j ⟨lenT0CaseIModZeroTwo m j, Nat.lt_succ_self _⟩) =
      pointT0CaseIModZeroTwo (m := m) (nextBlock j) 0 := by
  intro j
  fin_cases j
  · apply Fin.ext
    change
      (T0CaseI (m := m)
        (pointT0CaseIModZeroTwo (m := m) 0 ⟨lenT0CaseIModZeroTwo m 0, Nat.lt_succ_self _⟩)).1 =
      (pointT0CaseIModZeroTwo (m := m) (nextBlock 0) 0).1
    have hsrc :
        (pointT0CaseIModZeroTwo (m := m) 0 ⟨lenT0CaseIModZeroTwo m 0, Nat.lt_succ_self _⟩).1 = m - 2 :=
      pointT0CaseIModZeroTwo_last_zero_val (m := m)
    have hdst : (pointT0CaseIModZeroTwo (m := m) (nextBlock 0) 0).1 = 1 := by
      simpa [nextBlock] using pointT0CaseIModZeroTwo_one_zero_val (m := m)
    rw [T0CaseI_eq_one_of_val_eq_m_sub_two (m := m) hsrc, hdst]
  · apply Fin.ext
    change
      (T0CaseI (m := m)
        (pointT0CaseIModZeroTwo (m := m) 1 ⟨lenT0CaseIModZeroTwo m 1, Nat.lt_succ_self _⟩)).1 =
      (pointT0CaseIModZeroTwo (m := m) (nextBlock 1) 0).1
    have hsrc :
        (pointT0CaseIModZeroTwo (m := m) 1 ⟨lenT0CaseIModZeroTwo m 1, Nat.lt_succ_self _⟩).1 = m - 3 :=
      pointT0CaseIModZeroTwo_last_one_val (m := m) hm
    have hdst : (pointT0CaseIModZeroTwo (m := m) (nextBlock 1) 0).1 = 2 := by
      simpa [nextBlock] using pointT0CaseIModZeroTwo_two_zero_val (m := m)
    rw [T0CaseI_eq_two_of_val_eq_m_sub_three (m := m) hsrc, hdst]
  · apply Fin.ext
    change
      (T0CaseI (m := m)
        (pointT0CaseIModZeroTwo (m := m) 2 ⟨lenT0CaseIModZeroTwo m 2, Nat.lt_succ_self _⟩)).1 =
      (pointT0CaseIModZeroTwo (m := m) (nextBlock 2) 0).1
    have hsrc :
        (pointT0CaseIModZeroTwo (m := m) 2 ⟨lenT0CaseIModZeroTwo m 2, Nat.lt_succ_self _⟩).1 = m - 4 :=
      pointT0CaseIModZeroTwo_last_two_val (m := m) hm
    have hdst : (pointT0CaseIModZeroTwo (m := m) (nextBlock 2) 0).1 = m - 1 := by
      simpa [nextBlock] using pointT0CaseIModZeroTwo_three_zero_val (m := m)
    rw [T0CaseI_eq_m_sub_one_of_val_eq_m_sub_four (m := m) hsrc, hdst]
  · apply Fin.ext
    change
      (T0CaseI (m := m)
        (pointT0CaseIModZeroTwo (m := m) 3 ⟨lenT0CaseIModZeroTwo m 3, Nat.lt_succ_self _⟩)).1 =
      (pointT0CaseIModZeroTwo (m := m) (nextBlock 3) 0).1
    have hsrc :
        (pointT0CaseIModZeroTwo (m := m) 3 ⟨lenT0CaseIModZeroTwo m 3, Nat.lt_succ_self _⟩).1 = m - 1 := by
      simpa [lenT0CaseIModZeroTwo, pointT0CaseIModZeroTwo, pointT0CaseIModZeroTwoThree_val]
    have hdst : (pointT0CaseIModZeroTwo (m := m) (nextBlock 3) 0).1 = 0 := by
      simpa [nextBlock] using pointT0CaseIModZeroTwo_zero_zero_val (m := m)
    rw [T0CaseI_eq_zero_of_val_eq_m_sub_one (m := m) hsrc, hdst]

theorem cycleOn_T0CaseIModZeroTwo [Fact (4 < m)] (hm : m % 6 = 0 ∨ m % 6 = 2) :
    TorusD4.CycleOn m (T0CaseI (m := m)) ⟨0, by
      have hm4 : 4 < m := Fact.out
      omega⟩ := by
  have hcycle :=
    cycleOn_of_spliceBlocks
      (len := lenT0CaseIModZeroTwo m)
      (e := spliceEquivT0CaseIModZeroTwo (m := m) hm)
      (T := T0CaseI (m := m))
      (hstep := by
        intro j s hs
        simpa using pointT0CaseIModZeroTwo_step (m := m) hm (j := j) s hs)
      (hwrap := by
        intro j
        simpa using pointT0CaseIModZeroTwo_wrap (m := m) hm j)
  simpa [spliceStart, spliceEquivT0CaseIModZeroTwo, pointT0CaseIModZeroTwoSigma,
    pointT0CaseIModZeroTwo, lenT0CaseIModZeroTwo] using hcycle

def T0CaseII (_hm : m % 6 = 4) [Fact (9 < m)] (x : Fin m) : Fin m :=
  let hm9 : 9 < m := Fact.out
  if hx0 : x.1 = 0 then
    ⟨m - 2, by omega⟩
  else if hx1 : x.1 = 1 then
    ⟨4, by omega⟩
  else if hx2 : x.1 = 2 then
    ⟨6, by omega⟩
  else if hxm6 : x.1 = m - 6 then
    ⟨3, by omega⟩
  else if hxm5 : x.1 = m - 5 then
    ⟨m - 1, by omega⟩
  else if hxm4 : x.1 = m - 4 then
    ⟨0, by omega⟩
  else if hxm3 : x.1 = m - 3 then
    ⟨2, by omega⟩
  else if hxm2 : x.1 = m - 2 then
    ⟨5, by omega⟩
  else if hxm1 : x.1 = m - 1 then
    ⟨1, by omega⟩
  else
    ⟨x.1 + 4, by omega⟩

theorem eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (hm : m % 12 = 10) :
    ∃ q, m = 12 * q + 10 := by
  refine ⟨m / 12, ?_⟩
  have hdiv := Nat.mod_add_div m 12
  omega

def qCaseIIModTen (m : ℕ) : ℕ := (m - 10) / 12

private theorem qCaseIIModTen_eq (q : ℕ) :
    qCaseIIModTen (12 * q + 10) = q := by
  unfold qCaseIIModTen
  omega

def lenT0CaseIIModTen (m : ℕ) : Fin 4 → ℕ
  | ⟨0, _⟩ => 3 * qCaseIIModTen m + 4
  | ⟨1, _⟩ => 3 * qCaseIIModTen m
  | ⟨2, _⟩ => 3 * qCaseIIModTen m + 1
  | _ => 3 * qCaseIIModTen m + 1

private def pointT0CaseIIModTenZeroLeft [Fact (9 < m)] : Fin 2 → Fin m := by
  intro s
  by_cases hs0 : s.1 = 0
  · exact ⟨0, by
      have hm9 : 9 < m := Fact.out
      omega⟩
  · exact ⟨m - 2, by
      have hm9 : 9 < m := Fact.out
      omega⟩

private def pointT0CaseIIModTenZeroRight [Fact (9 < m)] :
    Fin (3 * qCaseIIModTen m + 2 + 1) → Fin m := by
  have hm9 : 9 < m := Fact.out
  have hdiv : 12 * qCaseIIModTen m ≤ m - 10 := by
    unfold qCaseIIModTen
    exact Nat.mul_div_le (m - 10) 12
  refine affineThenTailPoint m 5 4 (3 * qCaseIIModTen m + 2) 1 ?_ ?_
  · omega
  · omega

private def pointT0CaseIIModTenOne [Fact (9 < m)] :
    Fin (lenT0CaseIIModTen m 1 + 1) → Fin m := by
  have hm9 : 9 < m := Fact.out
  have hdiv : 12 * qCaseIIModTen m ≤ m - 10 := by
    unfold qCaseIIModTen
    exact Nat.mul_div_le (m - 10) 12
  exact affinePoint m 4 4 (3 * qCaseIIModTen m) (by omega)

private def pointT0CaseIIModTenTwo [Fact (9 < m)] :
    Fin (lenT0CaseIIModTen m 2 + 1) → Fin m := by
  have hm9 : 9 < m := Fact.out
  have hdiv : 12 * qCaseIIModTen m ≤ m - 10 := by
    unfold qCaseIIModTen
    exact Nat.mul_div_le (m - 10) 12
  exact affinePoint m 3 4 (3 * qCaseIIModTen m + 1) (by omega)

private def pointT0CaseIIModTenThree [Fact (9 < m)] :
    Fin (lenT0CaseIIModTen m 3 + 1) → Fin m := by
  have hm9 : 9 < m := Fact.out
  have hdiv : 12 * qCaseIIModTen m ≤ m - 10 := by
    unfold qCaseIIModTen
    exact Nat.mul_div_le (m - 10) 12
  exact affinePoint m 2 4 (3 * qCaseIIModTen m + 1) (by omega)

private def pointT0CaseIIModTenZero [Fact (9 < m)] :
    Fin (lenT0CaseIIModTen m 0 + 1) → Fin m := by
  have hlen : 1 + (3 * qCaseIIModTen m + 2) + 2 = lenT0CaseIIModTen m 0 + 1 := by
    simp [lenT0CaseIIModTen]
    omega
  exact castFinFun hlen
    (appendPoint (n := 1) (k := 3 * qCaseIIModTen m + 2)
      (pointT0CaseIIModTenZeroLeft (m := m))
      (pointT0CaseIIModTenZeroRight (m := m)))

def pointT0CaseIIModTen [Fact (9 < m)] (j : Fin 4) :
    Fin (lenT0CaseIIModTen m j + 1) → Fin m :=
  match j with
  | ⟨0, _⟩ => pointT0CaseIIModTenZero (m := m)
  | ⟨1, _⟩ => pointT0CaseIIModTenOne (m := m)
  | ⟨2, _⟩ => pointT0CaseIIModTenTwo (m := m)
  | ⟨_ + 3, _⟩ => pointT0CaseIIModTenThree (m := m)

def pointT0CaseIIModTenSigma [Fact (9 < m)] :
    SplicePoint (lenT0CaseIIModTen m) → Fin m
  | ⟨j, s⟩ => pointT0CaseIIModTen (m := m) j s

private theorem lenT0CaseIIModTen_zero_eq (q : ℕ) :
    lenT0CaseIIModTen (12 * q + 10) 0 = 3 * q + 4 := by
  simp [lenT0CaseIIModTen, qCaseIIModTen_eq]

private theorem lenT0CaseIIModTen_one_eq (q : ℕ) :
    lenT0CaseIIModTen (12 * q + 10) 1 = 3 * q := by
  simp [lenT0CaseIIModTen, qCaseIIModTen_eq]

private theorem lenT0CaseIIModTen_two_eq (q : ℕ) :
    lenT0CaseIIModTen (12 * q + 10) 2 = 3 * q + 1 := by
  simp [lenT0CaseIIModTen, qCaseIIModTen_eq]

private theorem lenT0CaseIIModTen_three_eq (q : ℕ) :
    lenT0CaseIIModTen (12 * q + 10) 3 = 3 * q + 1 := by
  simp [lenT0CaseIIModTen, qCaseIIModTen_eq]

theorem card_splicePoint_lenT0CaseIIModTen [Fact (9 < m)] (hm : m % 12 = 10) :
    Fintype.card (SplicePoint (lenT0CaseIIModTen m)) = m := by
  rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, rfl⟩
  have hcard :
      Fintype.card (SplicePoint (lenT0CaseIIModTen (12 * q + 10)))
        = ∑ j : Fin 4, (lenT0CaseIIModTen (12 * q + 10) j + 1) := by
    simpa [SplicePoint] using
      (Fintype.card_sigma (α := fun j : Fin 4 => Fin (lenT0CaseIIModTen (12 * q + 10) j + 1)))
  rw [hcard, Fin.sum_univ_four,
    lenT0CaseIIModTen_zero_eq (q := q),
    lenT0CaseIIModTen_one_eq (q := q),
    lenT0CaseIIModTen_two_eq (q := q),
    lenT0CaseIIModTen_three_eq (q := q)]
  omega

theorem T0CaseII_eq_m_sub_two_of_val_eq_zero [Fact (9 < m)] (hm : m % 6 = 4) {x : Fin m}
    (hx : x.1 = 0) :
    (T0CaseII (m := m) hm x).1 = m - 2 := by
  simp [T0CaseII, hx]

theorem T0CaseII_eq_four_of_val_eq_one [Fact (9 < m)] (hm : m % 6 = 4) {x : Fin m}
    (hx : x.1 = 1) :
    (T0CaseII (m := m) hm x).1 = 4 := by
  have hm9 : 9 < m := Fact.out
  have h10 : (1 : ℕ) ≠ 0 := by omega
  simpa [T0CaseII, hx, h10]

theorem T0CaseII_eq_six_of_val_eq_two [Fact (9 < m)] (hm : m % 6 = 4) {x : Fin m}
    (hx : x.1 = 2) :
    (T0CaseII (m := m) hm x).1 = 6 := by
  have hm9 : 9 < m := Fact.out
  have h20 : (2 : ℕ) ≠ 0 := by omega
  have h21 : (2 : ℕ) ≠ 1 := by omega
  simpa [T0CaseII, hx, h20, h21]

theorem T0CaseII_eq_three_of_val_eq_m_sub_six [Fact (9 < m)] (hm : m % 6 = 4) {x : Fin m}
    (hx : x.1 = m - 6) :
    (T0CaseII (m := m) hm x).1 = 3 := by
  have hm9 : 9 < m := Fact.out
  have h0 : m - 6 ≠ 0 := by omega
  have h1 : m - 6 ≠ 1 := by omega
  have h2 : m - 6 ≠ 2 := by omega
  simpa [T0CaseII, hx, h0, h1, h2]

theorem T0CaseII_eq_m_sub_one_of_val_eq_m_sub_five [Fact (9 < m)] (hm : m % 6 = 4)
    {x : Fin m} (hx : x.1 = m - 5) :
    (T0CaseII (m := m) hm x).1 = m - 1 := by
  have hm9 : 9 < m := Fact.out
  have h0 : m - 5 ≠ 0 := by omega
  have h1 : m - 5 ≠ 1 := by omega
  have h2 : m - 5 ≠ 2 := by omega
  have h6 : m - 5 ≠ m - 6 := by omega
  simpa [T0CaseII, hx, h0, h1, h2, h6]

theorem T0CaseII_eq_zero_of_val_eq_m_sub_four [Fact (9 < m)] (hm : m % 6 = 4)
    {x : Fin m} (hx : x.1 = m - 4) :
    (T0CaseII (m := m) hm x).1 = 0 := by
  have hm9 : 9 < m := Fact.out
  have h0 : m - 4 ≠ 0 := by omega
  have h1 : m - 4 ≠ 1 := by omega
  have h2 : m - 4 ≠ 2 := by omega
  have h6 : m - 4 ≠ m - 6 := by omega
  have h5 : m - 4 ≠ m - 5 := by omega
  simpa [T0CaseII, hx, h0, h1, h2, h6, h5]

theorem T0CaseII_eq_two_of_val_eq_m_sub_three [Fact (9 < m)] (hm : m % 6 = 4)
    {x : Fin m} (hx : x.1 = m - 3) :
    (T0CaseII (m := m) hm x).1 = 2 := by
  have hm9 : 9 < m := Fact.out
  have h0 : m - 3 ≠ 0 := by omega
  have h1 : m - 3 ≠ 1 := by omega
  have h2 : m - 3 ≠ 2 := by omega
  have h6 : m - 3 ≠ m - 6 := by omega
  have h5 : m - 3 ≠ m - 5 := by omega
  have h4 : m - 3 ≠ m - 4 := by omega
  simpa [T0CaseII, hx, h0, h1, h2, h6, h5, h4]

theorem T0CaseII_eq_five_of_val_eq_m_sub_two [Fact (9 < m)] (hm : m % 6 = 4)
    {x : Fin m} (hx : x.1 = m - 2) :
    (T0CaseII (m := m) hm x).1 = 5 := by
  have hm9 : 9 < m := Fact.out
  have h0 : m - 2 ≠ 0 := by omega
  have h1 : m - 2 ≠ 1 := by omega
  have h2 : m - 2 ≠ 2 := by omega
  have h6 : m - 2 ≠ m - 6 := by omega
  have h5 : m - 2 ≠ m - 5 := by omega
  have h4 : m - 2 ≠ m - 4 := by omega
  have h3 : m - 2 ≠ m - 3 := by omega
  simpa [T0CaseII, hx, h0, h1, h2, h6, h5, h4, h3]

theorem T0CaseII_eq_one_of_val_eq_m_sub_one [Fact (9 < m)] (hm : m % 6 = 4)
    {x : Fin m} (hx : x.1 = m - 1) :
    (T0CaseII (m := m) hm x).1 = 1 := by
  have hm9 : 9 < m := Fact.out
  have h0 : m - 1 ≠ 0 := by omega
  have h1 : m - 1 ≠ 1 := by omega
  have h2 : m - 1 ≠ 2 := by omega
  have h6 : m - 1 ≠ m - 6 := by omega
  have h5 : m - 1 ≠ m - 5 := by omega
  have h4 : m - 1 ≠ m - 4 := by omega
  have h3 : m - 1 ≠ m - 3 := by omega
  have h2' : m - 1 ≠ m - 2 := by omega
  simpa [T0CaseII, hx, h0, h1, h2, h6, h5, h4, h3, h2']

theorem T0CaseII_eq_add_four_of_ne_special [Fact (9 < m)] (hm : m % 6 = 4) {x : Fin m}
    (hx0 : x.1 ≠ 0) (hx1 : x.1 ≠ 1) (hx2 : x.1 ≠ 2)
    (hxm6 : x.1 ≠ m - 6) (hxm5 : x.1 ≠ m - 5) (hxm4 : x.1 ≠ m - 4)
    (hxm3 : x.1 ≠ m - 3) (hxm2 : x.1 ≠ m - 2) (hxm1 : x.1 ≠ m - 1) :
    (T0CaseII (m := m) hm x).1 = x.1 + 4 := by
  simp [T0CaseII, hx0, hx1, hx2, hxm6, hxm5, hxm4, hxm3, hxm2, hxm1]

theorem pointT0CaseIIModTenZeroLeft_val [Fact (9 < m)] (s : Fin 2) :
    (pointT0CaseIIModTenZeroLeft (m := m) s).1 = if s.1 = 0 then 0 else m - 2 := by
  fin_cases s
  · simp [pointT0CaseIIModTenZeroLeft]
  · simp [pointT0CaseIIModTenZeroLeft]

theorem pointT0CaseIIModTenZeroRight_val [Fact (9 < m)]
    (s : Fin (3 * qCaseIIModTen m + 2 + 1)) :
    (pointT0CaseIIModTenZeroRight (m := m) s).1 =
      if s.1 = 3 * qCaseIIModTen m + 2 then 1 else 5 + 4 * s.1 := by
  simpa [pointT0CaseIIModTenZeroRight] using
    (affineThenTailPoint_val
      (m := m) (a := 5) (d := 4) (k := 3 * qCaseIIModTen m + 2) (tail := 1) (s := s))

theorem pointT0CaseIIModTenOne_val [Fact (9 < m)]
    (s : Fin (lenT0CaseIIModTen m 1 + 1)) :
    (pointT0CaseIIModTenOne (m := m) s).1 = 4 + 4 * s.1 := by
  simpa [pointT0CaseIIModTenOne, lenT0CaseIIModTen] using
    (affinePoint_val (m := m) (a := 4) (d := 4) (n := 3 * qCaseIIModTen m) (s := s))

theorem pointT0CaseIIModTenTwo_val [Fact (9 < m)]
    (s : Fin (lenT0CaseIIModTen m 2 + 1)) :
    (pointT0CaseIIModTenTwo (m := m) s).1 = 3 + 4 * s.1 := by
  simpa [pointT0CaseIIModTenTwo, lenT0CaseIIModTen] using
    (affinePoint_val (m := m) (a := 3) (d := 4) (n := 3 * qCaseIIModTen m + 1) (s := s))

theorem pointT0CaseIIModTenThree_val [Fact (9 < m)]
    (s : Fin (lenT0CaseIIModTen m 3 + 1)) :
    (pointT0CaseIIModTenThree (m := m) s).1 = 2 + 4 * s.1 := by
  simpa [pointT0CaseIIModTenThree, lenT0CaseIIModTen] using
    (affinePoint_val (m := m) (a := 2) (d := 4) (n := 3 * qCaseIIModTen m + 1) (s := s))

private theorem pointT0CaseIIModTenZeroLeft_injective [Fact (9 < m)] :
    Function.Injective (pointT0CaseIIModTenZeroLeft (m := m)) := by
  intro s t h
  fin_cases s <;> fin_cases t
  · rfl
  · exfalso
    have hm9 : 9 < m := Fact.out
    have hv := congrArg Fin.val h
    have h0 : (pointT0CaseIIModTenZeroLeft (m := m) 0).1 = 0 := by
      simp [pointT0CaseIIModTenZeroLeft]
    have h1 : (pointT0CaseIIModTenZeroLeft (m := m) 1).1 = m - 2 := by
      simp [pointT0CaseIIModTenZeroLeft]
    have : (0 : ℕ) = m - 2 := by
      simpa [h0, h1] using hv
    omega
  · exfalso
    have hm9 : 9 < m := Fact.out
    have hv := congrArg Fin.val h
    have h0 : (pointT0CaseIIModTenZeroLeft (m := m) 0).1 = 0 := by
      simp [pointT0CaseIIModTenZeroLeft]
    have h1 : (pointT0CaseIIModTenZeroLeft (m := m) 1).1 = m - 2 := by
      simp [pointT0CaseIIModTenZeroLeft]
    have : m - 2 = (0 : ℕ) := by
      simpa [h0, h1] using hv
    omega
  · rfl

private theorem pointT0CaseIIModTenZeroRight_injective [Fact (9 < m)] :
    Function.Injective (pointT0CaseIIModTenZeroRight (m := m)) := by
  intro s t h
  have hv := congrArg Fin.val h
  by_cases hsLast : s.1 = 3 * qCaseIIModTen m + 2
  · by_cases htLast : t.1 = 3 * qCaseIIModTen m + 2
    · exact Fin.ext (by omega)
    · have : (1 : ℕ) = 5 + 4 * t.1 := by
        simpa [pointT0CaseIIModTenZeroRight_val, hsLast, htLast] using hv
      omega
  · by_cases htLast : t.1 = 3 * qCaseIIModTen m + 2
    · have : 5 + 4 * s.1 = (1 : ℕ) := by
        simpa [pointT0CaseIIModTenZeroRight_val, hsLast, htLast] using hv
      omega
    · apply Fin.ext
      have : 5 + 4 * s.1 = 5 + 4 * t.1 := by
        simpa [pointT0CaseIIModTenZeroRight_val, hsLast, htLast] using hv
      omega

private theorem pointT0CaseIIModTenOne_injective [Fact (9 < m)] :
    Function.Injective (pointT0CaseIIModTenOne (m := m)) := by
  simpa [pointT0CaseIIModTenOne, lenT0CaseIIModTen] using
    (affinePoint_injective (m := m) (a := 4) (d := 4) (n := 3 * qCaseIIModTen m) (by omega))

private theorem pointT0CaseIIModTenTwo_injective [Fact (9 < m)] :
    Function.Injective (pointT0CaseIIModTenTwo (m := m)) := by
  simpa [pointT0CaseIIModTenTwo, lenT0CaseIIModTen] using
    (affinePoint_injective (m := m) (a := 3) (d := 4) (n := 3 * qCaseIIModTen m + 1) (by omega))

private theorem pointT0CaseIIModTenThree_injective [Fact (9 < m)] :
    Function.Injective (pointT0CaseIIModTenThree (m := m)) := by
  simpa [pointT0CaseIIModTenThree, lenT0CaseIIModTen] using
    (affinePoint_injective (m := m) (a := 2) (d := 4) (n := 3 * qCaseIIModTen m + 1) (by omega))

private theorem pointT0CaseIIModTenZero_disjoint [Fact (9 < m)] (hm : m % 12 = 10) :
    ∀ s t,
      pointT0CaseIIModTenZeroLeft (m := m) s ≠ pointT0CaseIIModTenZeroRight (m := m) t := by
  intro s t h
  have hv := congrArg Fin.val h
  fin_cases s
  · by_cases htLast : t.1 = 3 * qCaseIIModTen m + 2
    · have : (0 : ℕ) = 1 := by
        simpa [pointT0CaseIIModTenZeroLeft_val, pointT0CaseIIModTenZeroRight_val, htLast] using hv
      omega
    · have : (0 : ℕ) = 5 + 4 * t.1 := by
        simpa [pointT0CaseIIModTenZeroLeft_val, pointT0CaseIIModTenZeroRight_val, htLast] using hv
      omega
  · by_cases htLast : t.1 = 3 * qCaseIIModTen m + 2
    · have : m - 2 = (1 : ℕ) := by
        simpa [pointT0CaseIIModTenZeroLeft_val, pointT0CaseIIModTenZeroRight_val, htLast] using hv
      omega
    · have hmq : 12 * qCaseIIModTen m = m - 10 := by
        rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, rfl⟩
        simp [qCaseIIModTen_eq]
      have : m - 2 = 5 + 4 * t.1 := by
        simpa [pointT0CaseIIModTenZeroLeft_val, pointT0CaseIIModTenZeroRight_val, htLast] using hv
      omega

private theorem pointT0CaseIIModTenZero_injective [Fact (9 < m)] (hm : m % 12 = 10) :
    Function.Injective (pointT0CaseIIModTenZero (m := m)) := by
  have hlen : 1 + (3 * qCaseIIModTen m + 2) + 2 = lenT0CaseIIModTen m 0 + 1 := by
    simp [lenT0CaseIIModTen]
    omega
  simpa [pointT0CaseIIModTenZero, hlen] using
    (castFinFun_injective hlen
      (appendPoint_injective
        (f := pointT0CaseIIModTenZeroLeft (m := m))
        (g := pointT0CaseIIModTenZeroRight (m := m))
        (pointT0CaseIIModTenZeroLeft_injective (m := m))
        (pointT0CaseIIModTenZeroRight_injective (m := m))
        (pointT0CaseIIModTenZero_disjoint (m := m) hm)))

private theorem pointT0CaseIIModTenZero_apply_left [Fact (9 < m)] {i : ℕ}
    (hi : i < 2) (hmem : i < lenT0CaseIIModTen m 0 + 1) :
    pointT0CaseIIModTenZero (m := m) ⟨i, hmem⟩ =
      pointT0CaseIIModTenZeroLeft (m := m) ⟨i, hi⟩ := by
  have hlen : 1 + (3 * qCaseIIModTen m + 2) + 2 = lenT0CaseIIModTen m 0 + 1 := by
    simp [lenT0CaseIIModTen]
    omega
  have hmem' : i < 1 + (3 * qCaseIIModTen m + 2) + 2 := by
    simpa [hlen] using hmem
  simpa [pointT0CaseIIModTenZero, hlen] using
    (appendPoint_apply_left
      (n := 1) (k := 3 * qCaseIIModTen m + 2)
      (f := pointT0CaseIIModTenZeroLeft (m := m))
      (g := pointT0CaseIIModTenZeroRight (m := m))
      (i := i) hi hmem')

private theorem pointT0CaseIIModTenZero_apply_right [Fact (9 < m)] {i : ℕ}
    (hi : ¬ i < 2) (hmem : i < lenT0CaseIIModTen m 0 + 1) :
    pointT0CaseIIModTenZero (m := m) ⟨i, hmem⟩ =
      pointT0CaseIIModTenZeroRight (m := m)
        ⟨i - (1 + 1), by
          have hlen : 1 + (3 * qCaseIIModTen m + 2) + 2 = lenT0CaseIIModTen m 0 + 1 := by
            simp [lenT0CaseIIModTen]
            omega
          have hmem' : i < 1 + (3 * qCaseIIModTen m + 2) + 2 := by
            simpa [hlen] using hmem
          omega⟩ := by
  have hlen : 1 + (3 * qCaseIIModTen m + 2) + 2 = lenT0CaseIIModTen m 0 + 1 := by
    simp [lenT0CaseIIModTen]
    omega
  have hmem' : i < 1 + (3 * qCaseIIModTen m + 2) + 2 := by
    simpa [hlen] using hmem
  simpa [pointT0CaseIIModTenZero, hlen] using
    (appendPoint_apply_right
      (n := 1) (k := 3 * qCaseIIModTen m + 2)
      (f := pointT0CaseIIModTenZeroLeft (m := m))
      (g := pointT0CaseIIModTenZeroRight (m := m))
      (i := i) hi hmem')

private theorem twelve_mul_qCaseIIModTen_eq (hm : m % 12 = 10) :
    12 * qCaseIIModTen m = m - 10 := by
  rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, rfl⟩
  simp [qCaseIIModTen_eq]

private theorem pointT0CaseIIModTenZero_val_left [Fact (9 < m)]
    (s : Fin (lenT0CaseIIModTen m 0 + 1)) (hs : s.1 < 2) :
    (pointT0CaseIIModTenZero (m := m) s).1 = if s.1 = 0 then 0 else m - 2 := by
  rw [pointT0CaseIIModTenZero_apply_left (m := m) (i := s.1) hs s.2]
  simpa using pointT0CaseIIModTenZeroLeft_val (m := m) (s := ⟨s.1, hs⟩)

private theorem pointT0CaseIIModTenZero_val_right [Fact (9 < m)]
    (s : Fin (lenT0CaseIIModTen m 0 + 1)) (hs : ¬ s.1 < 2) :
    (pointT0CaseIIModTenZero (m := m) s).1 =
      if s.1 - (1 + 1) = 3 * qCaseIIModTen m + 2 then 1 else 5 + 4 * (s.1 - (1 + 1)) := by
  rw [pointT0CaseIIModTenZero_apply_right (m := m) (i := s.1) hs s.2]
  simpa using
    pointT0CaseIIModTenZeroRight_val (m := m)
      (s := ⟨s.1 - (1 + 1), by
        have hlen : 1 + (3 * qCaseIIModTen m + 2) + 2 = lenT0CaseIIModTen m 0 + 1 := by
          simp [lenT0CaseIIModTen]
          omega
        have hmem' : s.1 < 1 + (3 * qCaseIIModTen m + 2) + 2 := by
          simpa [hlen] using s.2
        omega⟩)

theorem pointT0CaseIIModTen_zero_zero_val [Fact (9 < m)] :
    (pointT0CaseIIModTen (m := m) 0 0).1 = 0 := by
  simpa [pointT0CaseIIModTen] using
    (pointT0CaseIIModTenZero_val_left (m := m)
      (s := (0 : Fin (lenT0CaseIIModTen m 0 + 1))) (by simp))

theorem pointT0CaseIIModTen_zero_one_val [Fact (9 < m)] :
    (pointT0CaseIIModTen (m := m) 0 1).1 = m - 2 := by
  let s : Fin (lenT0CaseIIModTen m 0 + 1) := ⟨1, by
    simp [lenT0CaseIIModTen]⟩
  have hs : s.1 < 2 := by simp [s]
  change (pointT0CaseIIModTenZero (m := m) s).1 = m - 2
  rw [pointT0CaseIIModTenZero_val_left (m := m) (s := s) hs]
  simp [s]

theorem pointT0CaseIIModTen_one_zero_val [Fact (9 < m)] :
    (pointT0CaseIIModTen (m := m) 1 0).1 = 4 := by
  simp [pointT0CaseIIModTen, pointT0CaseIIModTenOne_val]

theorem pointT0CaseIIModTen_two_zero_val [Fact (9 < m)] :
    (pointT0CaseIIModTen (m := m) 2 0).1 = 3 := by
  simp [pointT0CaseIIModTen, pointT0CaseIIModTenTwo_val]

theorem pointT0CaseIIModTen_three_zero_val [Fact (9 < m)] :
    (pointT0CaseIIModTen (m := m) 3 0).1 = 2 := by
  simp [pointT0CaseIIModTen, pointT0CaseIIModTenThree_val]

theorem pointT0CaseIIModTen_first_right_zero_val [Fact (9 < m)] :
    let s : Fin (lenT0CaseIIModTen m 0 + 1) := ⟨2, by
      simp [lenT0CaseIIModTen]⟩
    (pointT0CaseIIModTen (m := m) 0 s).1 = 5 := by
  let s : Fin (lenT0CaseIIModTen m 0 + 1) := ⟨2, by
    simp [lenT0CaseIIModTen]⟩
  have hsNotLeft : ¬ s.1 < 2 := by simp [s]
  have hsNotLast : s.1 - (1 + 1) ≠ 3 * qCaseIIModTen m + 2 := by
    simp [s]
  change (pointT0CaseIIModTenZero (m := m) s).1 = 5
  rw [pointT0CaseIIModTenZero_val_right (m := m) (s := s) hsNotLeft, if_neg hsNotLast]
  simp [s]

theorem pointT0CaseIIModTen_prelast_zero_val [Fact (9 < m)] (hm : m % 12 = 10) :
    let s : Fin (lenT0CaseIIModTen m 0 + 1) := ⟨lenT0CaseIIModTen m 0 - 1, by
      simp [lenT0CaseIIModTen]⟩
    (pointT0CaseIIModTen (m := m) 0 s).1 = m - 1 := by
  let s : Fin (lenT0CaseIIModTen m 0 + 1) := ⟨lenT0CaseIIModTen m 0 - 1, by
    simp [lenT0CaseIIModTen]⟩
  have hsNotLeft : ¬ s.1 < 2 := by
    simp [s, lenT0CaseIIModTen]
  have hsNotLast : s.1 - (1 + 1) ≠ 3 * qCaseIIModTen m + 2 := by
    simp [s, lenT0CaseIIModTen]
  change (pointT0CaseIIModTenZero (m := m) s).1 = m - 1
  rw [pointT0CaseIIModTenZero_val_right (m := m) (s := s) hsNotLeft, if_neg hsNotLast]
  have hmq := twelve_mul_qCaseIIModTen_eq (m := m) hm
  simp [s, lenT0CaseIIModTen] at *
  omega

theorem pointT0CaseIIModTen_last_zero_val [Fact (9 < m)] :
    (pointT0CaseIIModTen (m := m) 0 ⟨lenT0CaseIIModTen m 0, Nat.lt_succ_self _⟩).1 = 1 := by
  let s : Fin (lenT0CaseIIModTen m 0 + 1) := ⟨lenT0CaseIIModTen m 0, Nat.lt_succ_self _⟩
  have hsNotLeft : ¬ s.1 < 2 := by
    simp [s, lenT0CaseIIModTen]
  have hsLast : s.1 - (1 + 1) = 3 * qCaseIIModTen m + 2 := by
    simp [s, lenT0CaseIIModTen]
  change (pointT0CaseIIModTenZero (m := m) s).1 = 1
  rw [pointT0CaseIIModTenZero_val_right (m := m) (s := s) hsNotLeft, if_pos hsLast]

theorem pointT0CaseIIModTen_last_one_val [Fact (9 < m)] (hm : m % 12 = 10) :
    (pointT0CaseIIModTen (m := m) 1 ⟨lenT0CaseIIModTen m 1, Nat.lt_succ_self _⟩).1 = m - 6 := by
  let s : Fin (lenT0CaseIIModTen m 1 + 1) := ⟨lenT0CaseIIModTen m 1, Nat.lt_succ_self _⟩
  change (pointT0CaseIIModTenOne (m := m) s).1 = m - 6
  rw [pointT0CaseIIModTenOne_val (m := m) (s := s)]
  have hmq := twelve_mul_qCaseIIModTen_eq (m := m) hm
  simp [s, lenT0CaseIIModTen] at *
  omega

theorem pointT0CaseIIModTen_last_two_val [Fact (9 < m)] (hm : m % 12 = 10) :
    (pointT0CaseIIModTen (m := m) 2 ⟨lenT0CaseIIModTen m 2, Nat.lt_succ_self _⟩).1 = m - 3 := by
  let s : Fin (lenT0CaseIIModTen m 2 + 1) := ⟨lenT0CaseIIModTen m 2, Nat.lt_succ_self _⟩
  change (pointT0CaseIIModTenTwo (m := m) s).1 = m - 3
  rw [pointT0CaseIIModTenTwo_val (m := m) (s := s)]
  have hmq := twelve_mul_qCaseIIModTen_eq (m := m) hm
  simp [s, lenT0CaseIIModTen] at *
  omega

theorem pointT0CaseIIModTen_last_three_val [Fact (9 < m)] (hm : m % 12 = 10) :
    (pointT0CaseIIModTen (m := m) 3 ⟨lenT0CaseIIModTen m 3, Nat.lt_succ_self _⟩).1 = m - 4 := by
  let s : Fin (lenT0CaseIIModTen m 3 + 1) := ⟨lenT0CaseIIModTen m 3, Nat.lt_succ_self _⟩
  change (pointT0CaseIIModTenThree (m := m) s).1 = m - 4
  rw [pointT0CaseIIModTenThree_val (m := m) (s := s)]
  have hmq := twelve_mul_qCaseIIModTen_eq (m := m) hm
  simp [s, lenT0CaseIIModTen] at *
  omega

private theorem pointT0CaseIIModTenZero_One_disjoint [Fact (9 < m)] (hm : m % 12 = 10) :
    ∀ s t, pointT0CaseIIModTen (m := m) 0 s ≠ pointT0CaseIIModTen (m := m) 1 t := by
  intro s t h
  have hv := congrArg Fin.val h
  have hv' : (pointT0CaseIIModTenZero (m := m) s).1 = (pointT0CaseIIModTenOne (m := m) t).1 := by
    simpa [pointT0CaseIIModTen] using hv
  have hmq := twelve_mul_qCaseIIModTen_eq (m := m) hm
  by_cases hs : s.1 < 2
  · rw [pointT0CaseIIModTenZero_val_left (m := m) (s := s) hs,
      pointT0CaseIIModTenOne_val (m := m) (s := t)] at hv'
    by_cases hs0 : s.1 = 0
    · have : (0 : ℕ) = 4 + 4 * t.1 := by simpa [hs0] using hv'
      omega
    · have : m - 2 = 4 + 4 * t.1 := by simpa [hs0] using hv'
      have htLe : t.1 ≤ 3 * qCaseIIModTen m := by
        simpa [lenT0CaseIIModTen] using Nat.le_of_lt_succ t.2
      omega
  · rw [pointT0CaseIIModTenZero_val_right (m := m) (s := s) hs,
      pointT0CaseIIModTenOne_val (m := m) (s := t)] at hv'
    by_cases hsLast : s.1 - (1 + 1) = 3 * qCaseIIModTen m + 2
    · have : (1 : ℕ) = 4 + 4 * t.1 := by simpa [hsLast] using hv'
      omega
    · have : 5 + 4 * (s.1 - (1 + 1)) = 4 + 4 * t.1 := by simpa [hsLast] using hv'
      omega

private theorem pointT0CaseIIModTenZero_Two_disjoint [Fact (9 < m)] :
    ∀ s t, pointT0CaseIIModTen (m := m) 0 s ≠ pointT0CaseIIModTen (m := m) 2 t := by
  intro s t h
  have hv := congrArg Fin.val h
  have hv' : (pointT0CaseIIModTenZero (m := m) s).1 = (pointT0CaseIIModTenTwo (m := m) t).1 := by
    simpa [pointT0CaseIIModTen] using hv
  by_cases hs : s.1 < 2
  · rw [pointT0CaseIIModTenZero_val_left (m := m) (s := s) hs,
      pointT0CaseIIModTenTwo_val (m := m) (s := t)] at hv'
    by_cases hs0 : s.1 = 0
    · have : (0 : ℕ) = 3 + 4 * t.1 := by simpa [hs0] using hv'
      omega
    · have : m - 2 = 3 + 4 * t.1 := by simpa [hs0] using hv'
      have hm10 : 10 ≤ m := by
        have hm9 : 9 < m := Fact.out
        omega
      have htLe : t.1 ≤ 3 * qCaseIIModTen m + 1 := by
        simpa [lenT0CaseIIModTen] using Nat.le_of_lt_succ t.2
      have hdiv : 12 * qCaseIIModTen m ≤ m - 10 := by
        unfold qCaseIIModTen
        exact Nat.mul_div_le (m - 10) 12
      have hupper4 : 4 * t.1 ≤ 12 * qCaseIIModTen m + 4 := by
        omega
      have hupper12 : 12 * qCaseIIModTen m + 7 ≤ m - 3 := by
        calc
          12 * qCaseIIModTen m + 7 ≤ m - 10 + 7 := Nat.add_le_add_right hdiv 7
          _ = m - 3 := by omega
      have hupper : 3 + 4 * t.1 ≤ m - 3 := by
        calc
          3 + 4 * t.1 ≤ 3 + (12 * qCaseIIModTen m + 4) := by omega
          _ = 12 * qCaseIIModTen m + 7 := by omega
          _ ≤ m - 3 := hupper12
      omega
  · rw [pointT0CaseIIModTenZero_val_right (m := m) (s := s) hs,
      pointT0CaseIIModTenTwo_val (m := m) (s := t)] at hv'
    by_cases hsLast : s.1 - (1 + 1) = 3 * qCaseIIModTen m + 2
    · have : (1 : ℕ) = 3 + 4 * t.1 := by simpa [hsLast] using hv'
      omega
    · have : 5 + 4 * (s.1 - (1 + 1)) = 3 + 4 * t.1 := by simpa [hsLast] using hv'
      omega

private theorem pointT0CaseIIModTenZero_Three_disjoint [Fact (9 < m)] :
    ∀ s t, pointT0CaseIIModTen (m := m) 0 s ≠ pointT0CaseIIModTen (m := m) 3 t := by
  intro s t h
  have hv := congrArg Fin.val h
  have hv' :
      (pointT0CaseIIModTenZero (m := m) s).1 = (pointT0CaseIIModTenThree (m := m) t).1 := by
    simpa [pointT0CaseIIModTen] using hv
  by_cases hs : s.1 < 2
  · rw [pointT0CaseIIModTenZero_val_left (m := m) (s := s) hs,
      pointT0CaseIIModTenThree_val (m := m) (s := t)] at hv'
    by_cases hs0 : s.1 = 0
    · have : (0 : ℕ) = 2 + 4 * t.1 := by simpa [hs0] using hv'
      omega
    · have : m - 2 = 2 + 4 * t.1 := by simpa [hs0] using hv'
      have hm10 : 10 ≤ m := by
        have hm9 : 9 < m := Fact.out
        omega
      have htLe : t.1 ≤ 3 * qCaseIIModTen m + 1 := by
        simpa [lenT0CaseIIModTen] using Nat.le_of_lt_succ t.2
      have hdiv : 12 * qCaseIIModTen m ≤ m - 10 := by
        unfold qCaseIIModTen
        exact Nat.mul_div_le (m - 10) 12
      have hupper4 : 4 * t.1 ≤ 12 * qCaseIIModTen m + 4 := by
        omega
      have hupper12 : 12 * qCaseIIModTen m + 6 ≤ m - 4 := by
        calc
          12 * qCaseIIModTen m + 6 ≤ m - 10 + 6 := Nat.add_le_add_right hdiv 6
          _ = m - 4 := by omega
      have hupper : 2 + 4 * t.1 ≤ m - 4 := by
        calc
          2 + 4 * t.1 ≤ 2 + (12 * qCaseIIModTen m + 4) := by omega
          _ = 12 * qCaseIIModTen m + 6 := by omega
          _ ≤ m - 4 := hupper12
      omega
  · rw [pointT0CaseIIModTenZero_val_right (m := m) (s := s) hs,
      pointT0CaseIIModTenThree_val (m := m) (s := t)] at hv'
    by_cases hsLast : s.1 - (1 + 1) = 3 * qCaseIIModTen m + 2
    · have : (1 : ℕ) = 2 + 4 * t.1 := by simpa [hsLast] using hv'
      omega
    · have : 5 + 4 * (s.1 - (1 + 1)) = 2 + 4 * t.1 := by simpa [hsLast] using hv'
      omega

private theorem pointT0CaseIIModTenOne_Two_disjoint [Fact (9 < m)] :
    ∀ s t, pointT0CaseIIModTen (m := m) 1 s ≠ pointT0CaseIIModTen (m := m) 2 t := by
  intro s t h
  have hv := congrArg Fin.val h
  have hv' : (pointT0CaseIIModTenOne (m := m) s).1 = (pointT0CaseIIModTenTwo (m := m) t).1 := by
    simpa [pointT0CaseIIModTen] using hv
  have : 4 + 4 * s.1 = 3 + 4 * t.1 := by
    simpa [pointT0CaseIIModTenOne_val, pointT0CaseIIModTenTwo_val] using hv'
  omega

private theorem pointT0CaseIIModTenOne_Three_disjoint [Fact (9 < m)] :
    ∀ s t, pointT0CaseIIModTen (m := m) 1 s ≠ pointT0CaseIIModTen (m := m) 3 t := by
  intro s t h
  have hv := congrArg Fin.val h
  have hv' :
      (pointT0CaseIIModTenOne (m := m) s).1 = (pointT0CaseIIModTenThree (m := m) t).1 := by
    simpa [pointT0CaseIIModTen] using hv
  have : 4 + 4 * s.1 = 2 + 4 * t.1 := by
    simpa [pointT0CaseIIModTenOne_val, pointT0CaseIIModTenThree_val] using hv'
  omega

private theorem pointT0CaseIIModTenTwo_Three_disjoint [Fact (9 < m)] :
    ∀ s t, pointT0CaseIIModTen (m := m) 2 s ≠ pointT0CaseIIModTen (m := m) 3 t := by
  intro s t h
  have hv := congrArg Fin.val h
  have hv' :
      (pointT0CaseIIModTenTwo (m := m) s).1 = (pointT0CaseIIModTenThree (m := m) t).1 := by
    simpa [pointT0CaseIIModTen] using hv
  have : 3 + 4 * s.1 = 2 + 4 * t.1 := by
    simpa [pointT0CaseIIModTenTwo_val, pointT0CaseIIModTenThree_val] using hv'
  omega

theorem pointT0CaseIIModTenSigma_injective [Fact (9 < m)] (hm : m % 12 = 10) :
    Function.Injective (pointT0CaseIIModTenSigma (m := m)) := by
  intro p p' h
  rcases p with ⟨j, s⟩
  rcases p' with ⟨j', s'⟩
  fin_cases j <;> fin_cases j'
  · have hs : s = s' := pointT0CaseIIModTenZero_injective (m := m) hm h
    subst hs
    rfl
  · exfalso
    exact pointT0CaseIIModTenZero_One_disjoint (m := m) hm s s' h
  · exfalso
    exact pointT0CaseIIModTenZero_Two_disjoint (m := m) s s' h
  · exfalso
    exact pointT0CaseIIModTenZero_Three_disjoint (m := m) s s' h
  · exfalso
    exact pointT0CaseIIModTenZero_One_disjoint (m := m) hm s' s h.symm
  · have hs : s = s' := pointT0CaseIIModTenOne_injective (m := m) h
    subst hs
    rfl
  · exfalso
    exact pointT0CaseIIModTenOne_Two_disjoint (m := m) s s' h
  · exfalso
    exact pointT0CaseIIModTenOne_Three_disjoint (m := m) s s' h
  · exfalso
    exact pointT0CaseIIModTenZero_Two_disjoint (m := m) s' s h.symm
  · exfalso
    exact pointT0CaseIIModTenOne_Two_disjoint (m := m) s' s h.symm
  · have hs : s = s' := pointT0CaseIIModTenTwo_injective (m := m) h
    subst hs
    rfl
  · exfalso
    exact pointT0CaseIIModTenTwo_Three_disjoint (m := m) s s' h
  · exfalso
    exact pointT0CaseIIModTenZero_Three_disjoint (m := m) s' s h.symm
  · exfalso
    exact pointT0CaseIIModTenOne_Three_disjoint (m := m) s' s h.symm
  · exfalso
    exact pointT0CaseIIModTenTwo_Three_disjoint (m := m) s' s h.symm
  · have hs : s = s' := pointT0CaseIIModTenThree_injective (m := m) h
    subst hs
    rfl

noncomputable def spliceEquivT0CaseIIModTen [Fact (9 < m)] (hm : m % 12 = 10) :
    SplicePoint (lenT0CaseIIModTen m) ≃ Fin m := by
  let f := pointT0CaseIIModTenSigma (m := m)
  have hinj : Function.Injective f := pointT0CaseIIModTenSigma_injective (m := m) hm
  have hcard : Fintype.card (SplicePoint (lenT0CaseIIModTen m)) = Fintype.card (Fin m) := by
    simpa using card_splicePoint_lenT0CaseIIModTen (m := m) hm
  exact Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩)

@[simp] theorem spliceEquivT0CaseIIModTen_apply [Fact (9 < m)] (hm : m % 12 = 10)
    (p : SplicePoint (lenT0CaseIIModTen m)) :
    spliceEquivT0CaseIIModTen (m := m) hm p = pointT0CaseIIModTenSigma (m := m) p := by
  rfl

private theorem mod_six_eq_four_of_mod_twelve_eq_ten (hm : m % 12 = 10) :
    m % 6 = 4 := by
  omega

private theorem pointT0CaseIIModTenOne_step [Fact (9 < m)] (hm : m % 12 = 10)
    (s : Fin (lenT0CaseIIModTen m 1 + 1)) (hs : s.1 + 1 < lenT0CaseIIModTen m 1 + 1) :
    T0CaseII (m := m) (mod_six_eq_four_of_mod_twelve_eq_ten (m := m) hm)
      (pointT0CaseIIModTen (m := m) 1 s) =
      pointT0CaseIIModTen (m := m) 1 ⟨s.1 + 1, hs⟩ := by
  have hm6 : m % 6 = 4 := mod_six_eq_four_of_mod_twelve_eq_ten (m := m) hm
  have hmq : 12 * qCaseIIModTen m = m - 10 := twelve_mul_qCaseIIModTen_eq (m := m) hm
  have hsLt : s.1 < 3 * qCaseIIModTen m := by
    simpa [lenT0CaseIIModTen] using hs
  have hcur : (pointT0CaseIIModTen (m := m) 1 s).1 = 4 + 4 * s.1 := by
    simpa [pointT0CaseIIModTen] using pointT0CaseIIModTenOne_val (m := m) (s := s)
  have hx0 : (pointT0CaseIIModTen (m := m) 1 s).1 ≠ 0 := by
    rw [hcur]
    omega
  have hx1 : (pointT0CaseIIModTen (m := m) 1 s).1 ≠ 1 := by
    rw [hcur]
    omega
  have hx2 : (pointT0CaseIIModTen (m := m) 1 s).1 ≠ 2 := by
    rw [hcur]
    omega
  have hxm6 : (pointT0CaseIIModTen (m := m) 1 s).1 ≠ m - 6 := by
    rw [hcur]
    omega
  have hxm5 : (pointT0CaseIIModTen (m := m) 1 s).1 ≠ m - 5 := by
    rw [hcur]
    omega
  have hxm4 : (pointT0CaseIIModTen (m := m) 1 s).1 ≠ m - 4 := by
    rw [hcur]
    omega
  have hxm3 : (pointT0CaseIIModTen (m := m) 1 s).1 ≠ m - 3 := by
    rw [hcur]
    omega
  have hxm2 : (pointT0CaseIIModTen (m := m) 1 s).1 ≠ m - 2 := by
    rw [hcur]
    omega
  have hxm1 : (pointT0CaseIIModTen (m := m) 1 s).1 ≠ m - 1 := by
    rw [hcur]
    omega
  apply Fin.ext
  change
    (T0CaseII (m := m) hm6 (pointT0CaseIIModTen (m := m) 1 s)).1 =
      (pointT0CaseIIModTen (m := m) 1 ⟨s.1 + 1, hs⟩).1
  rw [T0CaseII_eq_add_four_of_ne_special (m := m) hm6 hx0 hx1 hx2 hxm6 hxm5 hxm4 hxm3 hxm2 hxm1]
  rw [hcur]
  have hnext : (pointT0CaseIIModTen (m := m) 1 ⟨s.1 + 1, hs⟩).1 = 4 + 4 * (s.1 + 1) := by
    simpa [pointT0CaseIIModTen] using
      pointT0CaseIIModTenOne_val (m := m) (s := ⟨s.1 + 1, hs⟩)
  rw [hnext]
  omega

private theorem pointT0CaseIIModTenTwo_step [Fact (9 < m)] (hm : m % 12 = 10)
    (s : Fin (lenT0CaseIIModTen m 2 + 1)) (hs : s.1 + 1 < lenT0CaseIIModTen m 2 + 1) :
    T0CaseII (m := m) (mod_six_eq_four_of_mod_twelve_eq_ten (m := m) hm)
      (pointT0CaseIIModTen (m := m) 2 s) =
      pointT0CaseIIModTen (m := m) 2 ⟨s.1 + 1, hs⟩ := by
  have hm6 : m % 6 = 4 := mod_six_eq_four_of_mod_twelve_eq_ten (m := m) hm
  have hmq : 12 * qCaseIIModTen m = m - 10 := twelve_mul_qCaseIIModTen_eq (m := m) hm
  have hsLt : s.1 < 3 * qCaseIIModTen m + 1 := by
    simpa [lenT0CaseIIModTen] using hs
  have hcur : (pointT0CaseIIModTen (m := m) 2 s).1 = 3 + 4 * s.1 := by
    simpa [pointT0CaseIIModTen] using pointT0CaseIIModTenTwo_val (m := m) (s := s)
  have hx0 : (pointT0CaseIIModTen (m := m) 2 s).1 ≠ 0 := by
    rw [hcur]
    omega
  have hx1 : (pointT0CaseIIModTen (m := m) 2 s).1 ≠ 1 := by
    rw [hcur]
    omega
  have hx2 : (pointT0CaseIIModTen (m := m) 2 s).1 ≠ 2 := by
    rw [hcur]
    omega
  have hxm6 : (pointT0CaseIIModTen (m := m) 2 s).1 ≠ m - 6 := by
    rw [hcur]
    omega
  have hxm5 : (pointT0CaseIIModTen (m := m) 2 s).1 ≠ m - 5 := by
    rw [hcur]
    omega
  have hxm4 : (pointT0CaseIIModTen (m := m) 2 s).1 ≠ m - 4 := by
    rw [hcur]
    omega
  have hxm3 : (pointT0CaseIIModTen (m := m) 2 s).1 ≠ m - 3 := by
    rw [hcur]
    omega
  have hxm2 : (pointT0CaseIIModTen (m := m) 2 s).1 ≠ m - 2 := by
    rw [hcur]
    omega
  have hxm1 : (pointT0CaseIIModTen (m := m) 2 s).1 ≠ m - 1 := by
    rw [hcur]
    omega
  apply Fin.ext
  change
    (T0CaseII (m := m) hm6 (pointT0CaseIIModTen (m := m) 2 s)).1 =
      (pointT0CaseIIModTen (m := m) 2 ⟨s.1 + 1, hs⟩).1
  rw [T0CaseII_eq_add_four_of_ne_special (m := m) hm6 hx0 hx1 hx2 hxm6 hxm5 hxm4 hxm3 hxm2 hxm1]
  rw [hcur]
  have hnext : (pointT0CaseIIModTen (m := m) 2 ⟨s.1 + 1, hs⟩).1 = 3 + 4 * (s.1 + 1) := by
    simpa [pointT0CaseIIModTen] using
      pointT0CaseIIModTenTwo_val (m := m) (s := ⟨s.1 + 1, hs⟩)
  rw [hnext]
  omega

private theorem pointT0CaseIIModTenThree_step [Fact (9 < m)] (hm : m % 12 = 10)
    (s : Fin (lenT0CaseIIModTen m 3 + 1)) (hs : s.1 + 1 < lenT0CaseIIModTen m 3 + 1) :
    T0CaseII (m := m) (mod_six_eq_four_of_mod_twelve_eq_ten (m := m) hm)
      (pointT0CaseIIModTen (m := m) 3 s) =
      pointT0CaseIIModTen (m := m) 3 ⟨s.1 + 1, hs⟩ := by
  have hm6 : m % 6 = 4 := mod_six_eq_four_of_mod_twelve_eq_ten (m := m) hm
  have hmq : 12 * qCaseIIModTen m = m - 10 := twelve_mul_qCaseIIModTen_eq (m := m) hm
  by_cases hs0 : s.1 = 0
  · apply Fin.ext
    change
      (T0CaseII (m := m) hm6 (pointT0CaseIIModTen (m := m) 3 s)).1 =
        (pointT0CaseIIModTen (m := m) 3 ⟨s.1 + 1, hs⟩).1
    have hsEq : s = 0 := Fin.ext hs0
    subst hsEq
    have hsrc : (pointT0CaseIIModTen (m := m) 3 0).1 = 2 :=
      pointT0CaseIIModTen_three_zero_val (m := m)
    have hlen : 1 < lenT0CaseIIModTen m 3 + 1 := by
      simp [lenT0CaseIIModTen]
    have h1 :
        (⟨0 + 1, hs⟩ : Fin (lenT0CaseIIModTen m 3 + 1)) =
          ⟨1, hlen⟩ := by
      apply Fin.ext
      simp
    have hdst : (pointT0CaseIIModTen (m := m) 3 ⟨0 + 1, hs⟩).1 = 6 := by
      rw [h1]
      change (pointT0CaseIIModTenThree (m := m) ⟨1, hlen⟩).1 = 6
      rw [pointT0CaseIIModTenThree_val (m := m) (s := ⟨1, hlen⟩)]
      norm_num
    rw [T0CaseII_eq_six_of_val_eq_two (m := m) hm6 hsrc]
    change 6 = (pointT0CaseIIModTen (m := m) 3 ⟨0 + 1, hs⟩).1
    rw [hdst]
  · have hsPos : 0 < s.1 := Nat.pos_of_ne_zero hs0
    have hsLt : s.1 < 3 * qCaseIIModTen m + 1 := by
      simpa [lenT0CaseIIModTen] using hs
    have hcur : (pointT0CaseIIModTen (m := m) 3 s).1 = 2 + 4 * s.1 := by
      simpa [pointT0CaseIIModTen] using pointT0CaseIIModTenThree_val (m := m) (s := s)
    have hx0 : (pointT0CaseIIModTen (m := m) 3 s).1 ≠ 0 := by
      rw [hcur]
      omega
    have hx1 : (pointT0CaseIIModTen (m := m) 3 s).1 ≠ 1 := by
      rw [hcur]
      omega
    have hx2 : (pointT0CaseIIModTen (m := m) 3 s).1 ≠ 2 := by
      rw [hcur]
      omega
    have hxm6 : (pointT0CaseIIModTen (m := m) 3 s).1 ≠ m - 6 := by
      rw [hcur]
      omega
    have hxm5 : (pointT0CaseIIModTen (m := m) 3 s).1 ≠ m - 5 := by
      rw [hcur]
      omega
    have hxm4 : (pointT0CaseIIModTen (m := m) 3 s).1 ≠ m - 4 := by
      rw [hcur]
      omega
    have hxm3 : (pointT0CaseIIModTen (m := m) 3 s).1 ≠ m - 3 := by
      rw [hcur]
      omega
    have hxm2 : (pointT0CaseIIModTen (m := m) 3 s).1 ≠ m - 2 := by
      rw [hcur]
      omega
    have hxm1 : (pointT0CaseIIModTen (m := m) 3 s).1 ≠ m - 1 := by
      rw [hcur]
      omega
    apply Fin.ext
    change
      (T0CaseII (m := m) hm6 (pointT0CaseIIModTen (m := m) 3 s)).1 =
        (pointT0CaseIIModTen (m := m) 3 ⟨s.1 + 1, hs⟩).1
    rw [T0CaseII_eq_add_four_of_ne_special (m := m) hm6 hx0 hx1 hx2 hxm6 hxm5 hxm4 hxm3 hxm2 hxm1]
    rw [hcur]
    have hnext : (pointT0CaseIIModTen (m := m) 3 ⟨s.1 + 1, hs⟩).1 = 2 + 4 * (s.1 + 1) := by
      simpa [pointT0CaseIIModTen] using
        pointT0CaseIIModTenThree_val (m := m) (s := ⟨s.1 + 1, hs⟩)
    rw [hnext]
    omega

private theorem pointT0CaseIIModTenZero_step [Fact (9 < m)] (hm : m % 12 = 10)
    (s : Fin (lenT0CaseIIModTen m 0 + 1)) (hs : s.1 + 1 < lenT0CaseIIModTen m 0 + 1) :
    T0CaseII (m := m) (mod_six_eq_four_of_mod_twelve_eq_ten (m := m) hm)
      (pointT0CaseIIModTen (m := m) 0 s) =
      pointT0CaseIIModTen (m := m) 0 ⟨s.1 + 1, hs⟩ := by
  have hm6 : m % 6 = 4 := mod_six_eq_four_of_mod_twelve_eq_ten (m := m) hm
  have hmq : 12 * qCaseIIModTen m = m - 10 := twelve_mul_qCaseIIModTen_eq (m := m) hm
  change T0CaseII (m := m) hm6 (pointT0CaseIIModTenZero (m := m) s) =
    pointT0CaseIIModTenZero (m := m) ⟨s.1 + 1, hs⟩
  by_cases hsLeft : s.1 < 2
  · have hsCases : s.1 = 0 ∨ s.1 = 1 := by
      omega
    cases hsCases with
    | inl hs0 =>
        have hsrc : (pointT0CaseIIModTenZero (m := m) s).1 = 0 := by
          rw [pointT0CaseIIModTenZero_val_left (m := m) (s := s) hsLeft]
          simp [hs0]
        have hsNextLeft : s.1 + 1 < 2 := by
          omega
        have hdst : (pointT0CaseIIModTenZero (m := m) ⟨s.1 + 1, hs⟩).1 = m - 2 := by
          rw [pointT0CaseIIModTenZero_val_left (m := m) (s := ⟨s.1 + 1, hs⟩) hsNextLeft]
          simp [hs0]
        apply Fin.ext
        change
          (T0CaseII (m := m) hm6 (pointT0CaseIIModTenZero (m := m) s)).1 =
            (pointT0CaseIIModTenZero (m := m) ⟨s.1 + 1, hs⟩).1
        rw [T0CaseII_eq_m_sub_two_of_val_eq_zero (m := m) hm6 hsrc, hdst]
    | inr hs1 =>
        have hsrc : (pointT0CaseIIModTenZero (m := m) s).1 = m - 2 := by
          rw [pointT0CaseIIModTenZero_val_left (m := m) (s := s) hsLeft]
          simp [hs1]
        have hsNextNotLeft : ¬ s.1 + 1 < 2 := by
          omega
        have hdst : (pointT0CaseIIModTenZero (m := m) ⟨s.1 + 1, hs⟩).1 = 5 := by
          rw [pointT0CaseIIModTenZero_val_right (m := m) (s := ⟨s.1 + 1, hs⟩) hsNextNotLeft]
          have hoff : (s.1 + 1) - (1 + 1) = 0 := by
            omega
          have hneq : (0 : ℕ) ≠ 3 * qCaseIIModTen m + 2 := by
            omega
          simp [hoff, hneq]
        apply Fin.ext
        change
          (T0CaseII (m := m) hm6 (pointT0CaseIIModTenZero (m := m) s)).1 =
            (pointT0CaseIIModTenZero (m := m) ⟨s.1 + 1, hs⟩).1
        rw [T0CaseII_eq_five_of_val_eq_m_sub_two (m := m) hm6 hsrc, hdst]
  · have hsNotLeft : ¬ s.1 < 2 := hsLeft
    by_cases hsm5 : s.1 - (1 + 1) = 3 * qCaseIIModTen m
    · have hsNotLast : s.1 - (1 + 1) ≠ 3 * qCaseIIModTen m + 2 := by
        omega
      have hcur : (pointT0CaseIIModTenZero (m := m) s).1 = 5 + 4 * (s.1 - (1 + 1)) := by
        rw [pointT0CaseIIModTenZero_val_right (m := m) (s := s) hsNotLeft, if_neg hsNotLast]
      have hsrc : (pointT0CaseIIModTenZero (m := m) s).1 = m - 5 := by
        rw [hcur, hsm5]
        omega
      have hsNextNotLeft : ¬ s.1 + 1 < 2 := by
        omega
      have hsNextNotLast : (s.1 + 1) - (1 + 1) ≠ 3 * qCaseIIModTen m + 2 := by
        omega
      have hdst : (pointT0CaseIIModTenZero (m := m) ⟨s.1 + 1, hs⟩).1 = m - 1 := by
        rw [pointT0CaseIIModTenZero_val_right (m := m) (s := ⟨s.1 + 1, hs⟩) hsNextNotLeft,
          if_neg hsNextNotLast]
        have hnextOff : (s.1 + 1) - (1 + 1) = 3 * qCaseIIModTen m + 1 := by
          omega
        rw [hnextOff]
        omega
      apply Fin.ext
      change
        (T0CaseII (m := m) hm6 (pointT0CaseIIModTenZero (m := m) s)).1 =
          (pointT0CaseIIModTenZero (m := m) ⟨s.1 + 1, hs⟩).1
      rw [T0CaseII_eq_m_sub_one_of_val_eq_m_sub_five (m := m) hm6 hsrc, hdst]
    · by_cases hsm1 : s.1 - (1 + 1) = 3 * qCaseIIModTen m + 1
      · have hsNotLast : s.1 - (1 + 1) ≠ 3 * qCaseIIModTen m + 2 := by
          have hsLtLen : s.1 < lenT0CaseIIModTen m 0 := by
            omega
          simp [lenT0CaseIIModTen] at hsLtLen
          omega
        have hcur : (pointT0CaseIIModTenZero (m := m) s).1 = 5 + 4 * (s.1 - (1 + 1)) := by
          rw [pointT0CaseIIModTenZero_val_right (m := m) (s := s) hsNotLeft, if_neg hsNotLast]
        have hsrc : (pointT0CaseIIModTenZero (m := m) s).1 = m - 1 := by
          rw [hcur, hsm1]
          omega
        have hsNextNotLeft : ¬ s.1 + 1 < 2 := by
          omega
        have hsNextLast : (s.1 + 1) - (1 + 1) = 3 * qCaseIIModTen m + 2 := by
          omega
        have hdst : (pointT0CaseIIModTenZero (m := m) ⟨s.1 + 1, hs⟩).1 = 1 := by
          rw [pointT0CaseIIModTenZero_val_right (m := m) (s := ⟨s.1 + 1, hs⟩) hsNextNotLeft,
            if_pos hsNextLast]
        apply Fin.ext
        change
          (T0CaseII (m := m) hm6 (pointT0CaseIIModTenZero (m := m) s)).1 =
            (pointT0CaseIIModTenZero (m := m) ⟨s.1 + 1, hs⟩).1
        rw [T0CaseII_eq_one_of_val_eq_m_sub_one (m := m) hm6 hsrc, hdst]
      · have hsNotLast : s.1 - (1 + 1) ≠ 3 * qCaseIIModTen m + 2 := by
          have hsLtLen : s.1 < lenT0CaseIIModTen m 0 := by
            omega
          simp [lenT0CaseIIModTen] at hsLtLen
          omega
        have hcur : (pointT0CaseIIModTenZero (m := m) s).1 = 5 + 4 * (s.1 - (1 + 1)) := by
          rw [pointT0CaseIIModTenZero_val_right (m := m) (s := s) hsNotLeft, if_neg hsNotLast]
        have hx0 : (pointT0CaseIIModTenZero (m := m) s).1 ≠ 0 := by
          rw [hcur]
          omega
        have hx1 : (pointT0CaseIIModTenZero (m := m) s).1 ≠ 1 := by
          rw [hcur]
          omega
        have hx2 : (pointT0CaseIIModTenZero (m := m) s).1 ≠ 2 := by
          rw [hcur]
          omega
        have hxm6 : (pointT0CaseIIModTenZero (m := m) s).1 ≠ m - 6 := by
          rw [hcur]
          omega
        have hxm5 : (pointT0CaseIIModTenZero (m := m) s).1 ≠ m - 5 := by
          rw [hcur]
          omega
        have hxm4 : (pointT0CaseIIModTenZero (m := m) s).1 ≠ m - 4 := by
          rw [hcur]
          omega
        have hxm3 : (pointT0CaseIIModTenZero (m := m) s).1 ≠ m - 3 := by
          rw [hcur]
          omega
        have hxm2 : (pointT0CaseIIModTenZero (m := m) s).1 ≠ m - 2 := by
          rw [hcur]
          omega
        have hxm1 : (pointT0CaseIIModTenZero (m := m) s).1 ≠ m - 1 := by
          rw [hcur]
          omega
        have hsNextNotLeft : ¬ s.1 + 1 < 2 := by
          omega
        have hsNextNotLast : (s.1 + 1) - (1 + 1) ≠ 3 * qCaseIIModTen m + 2 := by
          omega
        have hnext : (pointT0CaseIIModTenZero (m := m) ⟨s.1 + 1, hs⟩).1 =
            5 + 4 * ((s.1 + 1) - (1 + 1)) := by
          rw [pointT0CaseIIModTenZero_val_right (m := m) (s := ⟨s.1 + 1, hs⟩) hsNextNotLeft,
            if_neg hsNextNotLast]
        apply Fin.ext
        change
          (T0CaseII (m := m) hm6 (pointT0CaseIIModTenZero (m := m) s)).1 =
            (pointT0CaseIIModTenZero (m := m) ⟨s.1 + 1, hs⟩).1
        rw [T0CaseII_eq_add_four_of_ne_special (m := m) hm6 hx0 hx1 hx2 hxm6 hxm5 hxm4 hxm3
          hxm2 hxm1]
        rw [hcur, hnext]
        omega

theorem pointT0CaseIIModTen_step [Fact (9 < m)] (hm : m % 12 = 10) {j : Fin 4}
    (s : Fin (lenT0CaseIIModTen m j + 1)) (hs : s.1 + 1 < lenT0CaseIIModTen m j + 1) :
    T0CaseII (m := m) (mod_six_eq_four_of_mod_twelve_eq_ten (m := m) hm)
      (pointT0CaseIIModTen (m := m) j s) =
      pointT0CaseIIModTen (m := m) j ⟨s.1 + 1, hs⟩ := by
  fin_cases j
  · simpa using pointT0CaseIIModTenZero_step (m := m) hm s hs
  · simpa using pointT0CaseIIModTenOne_step (m := m) hm s hs
  · simpa using pointT0CaseIIModTenTwo_step (m := m) hm s hs
  · simpa using pointT0CaseIIModTenThree_step (m := m) hm s hs

theorem pointT0CaseIIModTen_wrap [Fact (9 < m)] (hm : m % 12 = 10) :
    ∀ j : Fin 4,
      T0CaseII (m := m) (mod_six_eq_four_of_mod_twelve_eq_ten (m := m) hm)
        (pointT0CaseIIModTen (m := m) j ⟨lenT0CaseIIModTen m j, Nat.lt_succ_self _⟩) =
      pointT0CaseIIModTen (m := m) (nextBlock j) 0 := by
  intro j
  have hm6 : m % 6 = 4 := mod_six_eq_four_of_mod_twelve_eq_ten (m := m) hm
  fin_cases j
  · apply Fin.ext
    change
      (T0CaseII (m := m) hm6
        (pointT0CaseIIModTen (m := m) 0 ⟨lenT0CaseIIModTen m 0, Nat.lt_succ_self _⟩)).1 =
      (pointT0CaseIIModTen (m := m) (nextBlock 0) 0).1
    have hsrc :
        (pointT0CaseIIModTen (m := m) 0 ⟨lenT0CaseIIModTen m 0, Nat.lt_succ_self _⟩).1 = 1 :=
      pointT0CaseIIModTen_last_zero_val (m := m)
    have hdst : (pointT0CaseIIModTen (m := m) (nextBlock 0) 0).1 = 4 := by
      simpa [nextBlock] using pointT0CaseIIModTen_one_zero_val (m := m)
    rw [T0CaseII_eq_four_of_val_eq_one (m := m) hm6 hsrc, hdst]
  · apply Fin.ext
    change
      (T0CaseII (m := m) hm6
        (pointT0CaseIIModTen (m := m) 1 ⟨lenT0CaseIIModTen m 1, Nat.lt_succ_self _⟩)).1 =
      (pointT0CaseIIModTen (m := m) (nextBlock 1) 0).1
    have hsrc :
        (pointT0CaseIIModTen (m := m) 1 ⟨lenT0CaseIIModTen m 1, Nat.lt_succ_self _⟩).1 = m - 6 :=
      pointT0CaseIIModTen_last_one_val (m := m) hm
    have hdst : (pointT0CaseIIModTen (m := m) (nextBlock 1) 0).1 = 3 := by
      simpa [nextBlock] using pointT0CaseIIModTen_two_zero_val (m := m)
    rw [T0CaseII_eq_three_of_val_eq_m_sub_six (m := m) hm6 hsrc, hdst]
  · apply Fin.ext
    change
      (T0CaseII (m := m) hm6
        (pointT0CaseIIModTen (m := m) 2 ⟨lenT0CaseIIModTen m 2, Nat.lt_succ_self _⟩)).1 =
      (pointT0CaseIIModTen (m := m) (nextBlock 2) 0).1
    have hsrc :
        (pointT0CaseIIModTen (m := m) 2 ⟨lenT0CaseIIModTen m 2, Nat.lt_succ_self _⟩).1 = m - 3 :=
      pointT0CaseIIModTen_last_two_val (m := m) hm
    have hdst : (pointT0CaseIIModTen (m := m) (nextBlock 2) 0).1 = 2 := by
      simpa [nextBlock] using pointT0CaseIIModTen_three_zero_val (m := m)
    rw [T0CaseII_eq_two_of_val_eq_m_sub_three (m := m) hm6 hsrc, hdst]
  · apply Fin.ext
    change
      (T0CaseII (m := m) hm6
        (pointT0CaseIIModTen (m := m) 3 ⟨lenT0CaseIIModTen m 3, Nat.lt_succ_self _⟩)).1 =
      (pointT0CaseIIModTen (m := m) (nextBlock 3) 0).1
    have hsrc :
        (pointT0CaseIIModTen (m := m) 3 ⟨lenT0CaseIIModTen m 3, Nat.lt_succ_self _⟩).1 = m - 4 :=
      pointT0CaseIIModTen_last_three_val (m := m) hm
    have hdst : (pointT0CaseIIModTen (m := m) (nextBlock 3) 0).1 = 0 := by
      simpa [nextBlock] using pointT0CaseIIModTen_zero_zero_val (m := m)
    rw [T0CaseII_eq_zero_of_val_eq_m_sub_four (m := m) hm6 hsrc, hdst]

theorem cycleOn_T0CaseIIModTen [Fact (9 < m)] (hm : m % 12 = 10) :
    TorusD4.CycleOn m
      (T0CaseII (m := m) (mod_six_eq_four_of_mod_twelve_eq_ten (m := m) hm))
      ⟨0, by
        have hm9 : 9 < m := Fact.out
        omega⟩ := by
  have hcycle :=
    cycleOn_of_spliceBlocks
      (len := lenT0CaseIIModTen m)
      (e := spliceEquivT0CaseIIModTen (m := m) hm)
      (T := T0CaseII (m := m) (mod_six_eq_four_of_mod_twelve_eq_ten (m := m) hm))
      (hstep := by
        intro j s hs
        simpa using pointT0CaseIIModTen_step (m := m) hm (j := j) s hs)
      (hwrap := by
        intro j
        simpa using pointT0CaseIIModTen_wrap (m := m) hm j)
  simpa [spliceStart, spliceEquivT0CaseIIModTen, pointT0CaseIIModTenSigma,
    pointT0CaseIIModTen, lenT0CaseIIModTen] using hcycle

theorem eq_twelve_mul_add_four_of_mod_twelve_eq_four (hm : m % 12 = 4) :
    ∃ q, m = 12 * q + 4 := by
  refine ⟨m / 12, ?_⟩
  have hdiv := Nat.mod_add_div m 12
  omega

def qT0CaseIIModFour (m : ℕ) : ℕ := (m - 4) / 12

private theorem qT0CaseIIModFour_eq (q : ℕ) :
    qT0CaseIIModFour (12 * q + 4) = q := by
  unfold qT0CaseIIModFour
  omega

private theorem twelve_mul_qT0CaseIIModFour_eq (hm : m % 12 = 4) :
    12 * qT0CaseIIModFour m = m - 4 := by
  rcases eq_twelve_mul_add_four_of_mod_twelve_eq_four (m := m) hm with ⟨q, rfl⟩
  simp [qT0CaseIIModFour_eq]

def lenT0CaseIIModFour (m : ℕ) : Fin 4 → ℕ
  | ⟨0, _⟩ => 3 * qT0CaseIIModFour m + 1
  | ⟨1, _⟩ => 3 * qT0CaseIIModFour m - 1
  | ⟨2, _⟩ => 3 * qT0CaseIIModFour m + 1
  | _ => 3 * qT0CaseIIModFour m - 1

private def pointT0CaseIIModFourZeroLeft [Fact (9 < m)] : Fin 2 → Fin m := by
  intro s
  by_cases hs0 : s.1 = 0
  · exact ⟨0, by
      have hm9 : 9 < m := Fact.out
      omega⟩
  · exact ⟨m - 2, by
      have hm9 : 9 < m := Fact.out
      omega⟩

private def pointT0CaseIIModFourZeroRight [Fact (9 < m)] (hm : m % 12 = 4) :
    Fin (3 * qT0CaseIIModFour m - 1 + 1) → Fin m := by
  have hm9 : 9 < m := Fact.out
  have hmq : 12 * qT0CaseIIModFour m = m - 4 := twelve_mul_qT0CaseIIModFour_eq (m := m) hm
  have hbound : 5 + 4 * (3 * qT0CaseIIModFour m - 1) < m := by
    omega
  exact affinePoint m 5 4 (3 * qT0CaseIIModFour m - 1) hbound

private def pointT0CaseIIModFourZero [Fact (9 < m)] (hm : m % 12 = 4) :
    Fin (lenT0CaseIIModFour m 0 + 1) → Fin m := by
  have hq : 1 ≤ qT0CaseIIModFour m := by
    have hm9 : 9 < m := Fact.out
    have hmq : 12 * qT0CaseIIModFour m = m - 4 := twelve_mul_qT0CaseIIModFour_eq (m := m) hm
    omega
  have hlen : 1 + (3 * qT0CaseIIModFour m - 1) + 2 = lenT0CaseIIModFour m 0 + 1 := by
    simp [lenT0CaseIIModFour]
    omega
  exact castFinFun hlen
    (appendPoint (n := 1) (k := 3 * qT0CaseIIModFour m - 1)
      (pointT0CaseIIModFourZeroLeft (m := m))
      (pointT0CaseIIModFourZeroRight (m := m) hm))

private def pointT0CaseIIModFourOne [Fact (9 < m)] (hm : m % 12 = 4) :
    Fin (lenT0CaseIIModFour m 1 + 1) → Fin m := by
  have hm9 : 9 < m := Fact.out
  have hmq : 12 * qT0CaseIIModFour m = m - 4 := twelve_mul_qT0CaseIIModFour_eq (m := m) hm
  have hbound : 2 + 4 * (3 * qT0CaseIIModFour m - 1) < m := by
    omega
  exact affinePoint m 2 4 (3 * qT0CaseIIModFour m - 1) hbound

private def pointT0CaseIIModFourTwo [Fact (9 < m)] (hm : m % 12 = 4) :
    Fin (lenT0CaseIIModFour m 2 + 1) → Fin m := by
  have hm9 : 9 < m := Fact.out
  have hmq : 12 * qT0CaseIIModFour m = m - 4 := twelve_mul_qT0CaseIIModFour_eq (m := m) hm
  have htail : 1 < m := by omega
  have hbound : 3 + 4 * ((3 * qT0CaseIIModFour m + 1) - 1) < m := by
    omega
  exact affineThenTailPoint m 3 4 (3 * qT0CaseIIModFour m + 1) 1 htail hbound

private def pointT0CaseIIModFourThree [Fact (9 < m)] (hm : m % 12 = 4) :
    Fin (lenT0CaseIIModFour m 3 + 1) → Fin m := by
  have hm9 : 9 < m := Fact.out
  have hmq : 12 * qT0CaseIIModFour m = m - 4 := twelve_mul_qT0CaseIIModFour_eq (m := m) hm
  have hbound : 4 + 4 * (3 * qT0CaseIIModFour m - 1) < m := by
    omega
  exact affinePoint m 4 4 (3 * qT0CaseIIModFour m - 1) hbound

def pointT0CaseIIModFour [Fact (9 < m)] (hm : m % 12 = 4) (j : Fin 4) :
    Fin (lenT0CaseIIModFour m j + 1) → Fin m :=
  match j with
  | ⟨0, _⟩ => pointT0CaseIIModFourZero (m := m) hm
  | ⟨1, _⟩ => pointT0CaseIIModFourOne (m := m) hm
  | ⟨2, _⟩ => pointT0CaseIIModFourTwo (m := m) hm
  | ⟨_ + 3, _⟩ => pointT0CaseIIModFourThree (m := m) hm

def pointT0CaseIIModFourSigma [Fact (9 < m)] (hm : m % 12 = 4) :
    SplicePoint (lenT0CaseIIModFour m) → Fin m
  | ⟨j, s⟩ => pointT0CaseIIModFour (m := m) hm j s

private theorem lenT0CaseIIModFour_zero_eq (q : ℕ) :
    lenT0CaseIIModFour (12 * q + 4) 0 = 3 * q + 1 := by
  simp [lenT0CaseIIModFour, qT0CaseIIModFour_eq]

private theorem lenT0CaseIIModFour_one_eq (q : ℕ) :
    lenT0CaseIIModFour (12 * q + 4) 1 = 3 * q - 1 := by
  simp [lenT0CaseIIModFour, qT0CaseIIModFour_eq]

private theorem lenT0CaseIIModFour_two_eq (q : ℕ) :
    lenT0CaseIIModFour (12 * q + 4) 2 = 3 * q + 1 := by
  simp [lenT0CaseIIModFour, qT0CaseIIModFour_eq]

private theorem lenT0CaseIIModFour_three_eq (q : ℕ) :
    lenT0CaseIIModFour (12 * q + 4) 3 = 3 * q - 1 := by
  simp [lenT0CaseIIModFour, qT0CaseIIModFour_eq]

theorem card_splicePoint_lenT0CaseIIModFour [Fact (9 < m)] (hm : m % 12 = 4) :
    Fintype.card (SplicePoint (lenT0CaseIIModFour m)) = m := by
  rcases eq_twelve_mul_add_four_of_mod_twelve_eq_four (m := m) hm with ⟨q, rfl⟩
  have hq : 1 ≤ q := by
    have hm9 : 9 < 12 * q + 4 := Fact.out
    omega
  have hcard :
      Fintype.card (SplicePoint (lenT0CaseIIModFour (12 * q + 4)))
        = ∑ j : Fin 4, (lenT0CaseIIModFour (12 * q + 4) j + 1) := by
    simpa [SplicePoint] using
      (Fintype.card_sigma (α := fun j : Fin 4 => Fin (lenT0CaseIIModFour (12 * q + 4) j + 1)))
  rw [hcard, Fin.sum_univ_four,
    lenT0CaseIIModFour_zero_eq (q := q),
    lenT0CaseIIModFour_one_eq (q := q),
    lenT0CaseIIModFour_two_eq (q := q),
    lenT0CaseIIModFour_three_eq (q := q)]
  omega

theorem pointT0CaseIIModFourZeroLeft_val [Fact (9 < m)] (s : Fin 2) :
    (pointT0CaseIIModFourZeroLeft (m := m) s).1 = if s.1 = 0 then 0 else m - 2 := by
  fin_cases s
  · simp [pointT0CaseIIModFourZeroLeft]
  · simp [pointT0CaseIIModFourZeroLeft]

theorem pointT0CaseIIModFourZeroRight_val [Fact (9 < m)] (hm : m % 12 = 4)
    (s : Fin (3 * qT0CaseIIModFour m - 1 + 1)) :
    (pointT0CaseIIModFourZeroRight (m := m) hm s).1 = 5 + 4 * s.1 := by
  simpa [pointT0CaseIIModFourZeroRight] using
    (affinePoint_val
      (m := m) (a := 5) (d := 4) (n := 3 * qT0CaseIIModFour m - 1) (s := s))

theorem pointT0CaseIIModFourOne_val [Fact (9 < m)] (hm : m % 12 = 4)
    (s : Fin (lenT0CaseIIModFour m 1 + 1)) :
    (pointT0CaseIIModFourOne (m := m) hm s).1 = 2 + 4 * s.1 := by
  simpa [pointT0CaseIIModFourOne, lenT0CaseIIModFour] using
    (affinePoint_val (m := m) (a := 2) (d := 4) (n := 3 * qT0CaseIIModFour m - 1) (s := s))

theorem pointT0CaseIIModFourTwo_val [Fact (9 < m)] (hm : m % 12 = 4)
    (s : Fin (lenT0CaseIIModFour m 2 + 1)) :
    (pointT0CaseIIModFourTwo (m := m) hm s).1 =
      if s.1 = 3 * qT0CaseIIModFour m + 1 then 1 else 3 + 4 * s.1 := by
  simpa [pointT0CaseIIModFourTwo, lenT0CaseIIModFour] using
    (affineThenTailPoint_val
      (m := m) (a := 3) (d := 4) (k := 3 * qT0CaseIIModFour m + 1) (tail := 1) (s := s))

theorem pointT0CaseIIModFourThree_val [Fact (9 < m)] (hm : m % 12 = 4)
    (s : Fin (lenT0CaseIIModFour m 3 + 1)) :
    (pointT0CaseIIModFourThree (m := m) hm s).1 = 4 + 4 * s.1 := by
  simpa [pointT0CaseIIModFourThree, lenT0CaseIIModFour] using
    (affinePoint_val (m := m) (a := 4) (d := 4) (n := 3 * qT0CaseIIModFour m - 1) (s := s))

private theorem pointT0CaseIIModFourZeroLeft_injective [Fact (9 < m)] :
    Function.Injective (pointT0CaseIIModFourZeroLeft (m := m)) := by
  intro s t h
  fin_cases s <;> fin_cases t
  · rfl
  · exfalso
    have hm9 : 9 < m := Fact.out
    have hv := congrArg Fin.val h
    have h0 : (pointT0CaseIIModFourZeroLeft (m := m) 0).1 = 0 := by
      simp [pointT0CaseIIModFourZeroLeft]
    have h1 : (pointT0CaseIIModFourZeroLeft (m := m) 1).1 = m - 2 := by
      simp [pointT0CaseIIModFourZeroLeft]
    have : (0 : ℕ) = m - 2 := by
      simpa [h0, h1] using hv
    omega
  · exfalso
    have hm9 : 9 < m := Fact.out
    have hv := congrArg Fin.val h
    have h0 : (pointT0CaseIIModFourZeroLeft (m := m) 0).1 = 0 := by
      simp [pointT0CaseIIModFourZeroLeft]
    have h1 : (pointT0CaseIIModFourZeroLeft (m := m) 1).1 = m - 2 := by
      simp [pointT0CaseIIModFourZeroLeft]
    have : m - 2 = (0 : ℕ) := by
      simpa [h0, h1] using hv
    omega
  · rfl

private theorem pointT0CaseIIModFourZeroRight_injective [Fact (9 < m)] (hm : m % 12 = 4) :
    Function.Injective (pointT0CaseIIModFourZeroRight (m := m) hm) := by
  simpa [pointT0CaseIIModFourZeroRight] using
    (affinePoint_injective
      (m := m) (a := 5) (d := 4) (n := 3 * qT0CaseIIModFour m - 1) (by omega))

private theorem pointT0CaseIIModFourOne_injective [Fact (9 < m)] (hm : m % 12 = 4) :
    Function.Injective (pointT0CaseIIModFourOne (m := m) hm) := by
  simpa [pointT0CaseIIModFourOne, lenT0CaseIIModFour] using
    (affinePoint_injective
      (m := m) (a := 2) (d := 4) (n := 3 * qT0CaseIIModFour m - 1) (by omega))

private theorem pointT0CaseIIModFourTwo_injective [Fact (9 < m)] (hm : m % 12 = 4) :
    Function.Injective (pointT0CaseIIModFourTwo (m := m) hm) := by
  have hm9 : 9 < m := Fact.out
  have htail : 1 < m := by omega
  have hmq : 12 * qT0CaseIIModFour m = m - 4 := twelve_mul_qT0CaseIIModFour_eq (m := m) hm
  have hbound : 3 + 4 * ((3 * qT0CaseIIModFour m + 1) - 1) < m := by
    omega
  simpa [pointT0CaseIIModFourTwo, lenT0CaseIIModFour] using
    (affineThenTailPoint_injective
      (m := m) (a := 3) (d := 4) (k := 3 * qT0CaseIIModFour m + 1) (tail := 1)
      (hsep := by
        intro j hj
        omega)
      (hd := by omega))

private theorem pointT0CaseIIModFourThree_injective [Fact (9 < m)] (hm : m % 12 = 4) :
    Function.Injective (pointT0CaseIIModFourThree (m := m) hm) := by
  simpa [pointT0CaseIIModFourThree, lenT0CaseIIModFour] using
    (affinePoint_injective
      (m := m) (a := 4) (d := 4) (n := 3 * qT0CaseIIModFour m - 1) (by omega))

private theorem pointT0CaseIIModFourZero_disjoint [Fact (9 < m)] (hm : m % 12 = 4) :
    ∀ s t,
      pointT0CaseIIModFourZeroLeft (m := m) s ≠ pointT0CaseIIModFourZeroRight (m := m) hm t := by
  intro s t h
  have hv := congrArg Fin.val h
  fin_cases s
  · have : (0 : ℕ) = 5 + 4 * t.1 := by
      simpa [pointT0CaseIIModFourZeroLeft_val, pointT0CaseIIModFourZeroRight_val] using hv
    omega
  · have hmq : 12 * qT0CaseIIModFour m = m - 4 := twelve_mul_qT0CaseIIModFour_eq (m := m) hm
    have : m - 2 = 5 + 4 * t.1 := by
      simpa [pointT0CaseIIModFourZeroLeft_val, pointT0CaseIIModFourZeroRight_val] using hv
    omega

private theorem pointT0CaseIIModFourZero_injective [Fact (9 < m)] (hm : m % 12 = 4) :
    Function.Injective (pointT0CaseIIModFourZero (m := m) hm) := by
  have hq : 1 ≤ qT0CaseIIModFour m := by
    have hm9 : 9 < m := Fact.out
    have hmq : 12 * qT0CaseIIModFour m = m - 4 := twelve_mul_qT0CaseIIModFour_eq (m := m) hm
    omega
  have hlen : 1 + (3 * qT0CaseIIModFour m - 1) + 2 = lenT0CaseIIModFour m 0 + 1 := by
    simp [lenT0CaseIIModFour]
    omega
  simpa [pointT0CaseIIModFourZero, hlen] using
    (castFinFun_injective hlen
      (appendPoint_injective
        (f := pointT0CaseIIModFourZeroLeft (m := m))
        (g := pointT0CaseIIModFourZeroRight (m := m) hm)
        (pointT0CaseIIModFourZeroLeft_injective (m := m))
        (pointT0CaseIIModFourZeroRight_injective (m := m) hm)
        (pointT0CaseIIModFourZero_disjoint (m := m) hm)))

private theorem pointT0CaseIIModFourZero_apply_left [Fact (9 < m)] (hm : m % 12 = 4) {i : ℕ}
    (hi : i < 2) (hmem : i < lenT0CaseIIModFour m 0 + 1) :
    pointT0CaseIIModFourZero (m := m) hm ⟨i, hmem⟩ =
      pointT0CaseIIModFourZeroLeft (m := m) ⟨i, hi⟩ := by
  have hq : 1 ≤ qT0CaseIIModFour m := by
    have hm9 : 9 < m := Fact.out
    have hmq : 12 * qT0CaseIIModFour m = m - 4 := twelve_mul_qT0CaseIIModFour_eq (m := m) hm
    omega
  have hlen : 1 + (3 * qT0CaseIIModFour m - 1) + 2 = lenT0CaseIIModFour m 0 + 1 := by
    simp [lenT0CaseIIModFour]
    omega
  have hmem' : i < 1 + (3 * qT0CaseIIModFour m - 1) + 2 := by
    simpa [hlen] using hmem
  simpa [pointT0CaseIIModFourZero, hlen] using
    (appendPoint_apply_left
      (n := 1) (k := 3 * qT0CaseIIModFour m - 1)
      (f := pointT0CaseIIModFourZeroLeft (m := m))
      (g := pointT0CaseIIModFourZeroRight (m := m) hm)
      (i := i) hi hmem')

private theorem pointT0CaseIIModFourZero_apply_right [Fact (9 < m)] (hm : m % 12 = 4) {i : ℕ}
    (hi : ¬ i < 2) (hmem : i < lenT0CaseIIModFour m 0 + 1) :
    pointT0CaseIIModFourZero (m := m) hm ⟨i, hmem⟩ =
      pointT0CaseIIModFourZeroRight (m := m) hm
        ⟨i - (1 + 1), by
          have hq : 1 ≤ qT0CaseIIModFour m := by
            have hm9 : 9 < m := Fact.out
            have hmq : 12 * qT0CaseIIModFour m = m - 4 :=
              twelve_mul_qT0CaseIIModFour_eq (m := m) hm
            omega
          have hlen : 1 + (3 * qT0CaseIIModFour m - 1) + 2 = lenT0CaseIIModFour m 0 + 1 := by
            simp [lenT0CaseIIModFour]
            omega
          have hmem' : i < 1 + (3 * qT0CaseIIModFour m - 1) + 2 := by
            simpa [hlen] using hmem
          omega⟩ := by
  have hq : 1 ≤ qT0CaseIIModFour m := by
    have hm9 : 9 < m := Fact.out
    have hmq : 12 * qT0CaseIIModFour m = m - 4 := twelve_mul_qT0CaseIIModFour_eq (m := m) hm
    omega
  have hlen : 1 + (3 * qT0CaseIIModFour m - 1) + 2 = lenT0CaseIIModFour m 0 + 1 := by
    simp [lenT0CaseIIModFour]
    omega
  have hmem' : i < 1 + (3 * qT0CaseIIModFour m - 1) + 2 := by
    simpa [hlen] using hmem
  simpa [pointT0CaseIIModFourZero, hlen] using
    (appendPoint_apply_right
      (n := 1) (k := 3 * qT0CaseIIModFour m - 1)
      (f := pointT0CaseIIModFourZeroLeft (m := m))
      (g := pointT0CaseIIModFourZeroRight (m := m) hm)
      (i := i) hi hmem')

private theorem pointT0CaseIIModFourZero_val_left [Fact (9 < m)] (hm : m % 12 = 4)
    (s : Fin (lenT0CaseIIModFour m 0 + 1)) (hs : s.1 < 2) :
    (pointT0CaseIIModFourZero (m := m) hm s).1 = if s.1 = 0 then 0 else m - 2 := by
  rw [pointT0CaseIIModFourZero_apply_left (m := m) hm (i := s.1) hs s.2]
  simpa using pointT0CaseIIModFourZeroLeft_val (m := m) (s := ⟨s.1, hs⟩)

private theorem pointT0CaseIIModFourZero_val_right [Fact (9 < m)] (hm : m % 12 = 4)
    (s : Fin (lenT0CaseIIModFour m 0 + 1)) (hs : ¬ s.1 < 2) :
    (pointT0CaseIIModFourZero (m := m) hm s).1 = 5 + 4 * (s.1 - (1 + 1)) := by
  rw [pointT0CaseIIModFourZero_apply_right (m := m) hm (i := s.1) hs s.2]
  simpa using
    pointT0CaseIIModFourZeroRight_val (m := m) hm
      (s := ⟨s.1 - (1 + 1), by
        have hq : 1 ≤ qT0CaseIIModFour m := by
          have hm9 : 9 < m := Fact.out
          have hmq : 12 * qT0CaseIIModFour m = m - 4 := twelve_mul_qT0CaseIIModFour_eq (m := m) hm
          omega
        have hlen : 1 + (3 * qT0CaseIIModFour m - 1) + 2 = lenT0CaseIIModFour m 0 + 1 := by
          simp [lenT0CaseIIModFour]
          omega
        have hmem' : s.1 < 1 + (3 * qT0CaseIIModFour m - 1) + 2 := by
          simpa [hlen] using s.2
        omega⟩)

theorem pointT0CaseIIModFour_zero_zero_val [Fact (9 < m)] (hm : m % 12 = 4) :
    (pointT0CaseIIModFour (m := m) hm 0 0).1 = 0 := by
  simpa [pointT0CaseIIModFour] using
    (pointT0CaseIIModFourZero_val_left (m := m) hm
      (s := (0 : Fin (lenT0CaseIIModFour m 0 + 1))) (by simp))

theorem pointT0CaseIIModFour_zero_one_val [Fact (9 < m)] (hm : m % 12 = 4) :
    (pointT0CaseIIModFour (m := m) hm 0 1).1 = m - 2 := by
  let s : Fin (lenT0CaseIIModFour m 0 + 1) := ⟨1, by
    simp [lenT0CaseIIModFour]⟩
  have hs : s.1 < 2 := by simp [s]
  change (pointT0CaseIIModFourZero (m := m) hm s).1 = m - 2
  rw [pointT0CaseIIModFourZero_val_left (m := m) hm (s := s) hs]
  simp [s]

theorem pointT0CaseIIModFour_first_right_zero_val [Fact (9 < m)] (hm : m % 12 = 4) :
    (pointT0CaseIIModFour (m := m) hm 0 ⟨2, by
      have hq0 : 0 < qT0CaseIIModFour m := by
        have hm9 : 9 < m := Fact.out
        have hmq : 12 * qT0CaseIIModFour m = m - 4 :=
          twelve_mul_qT0CaseIIModFour_eq (m := m) hm
        omega
      have hmem : 2 < lenT0CaseIIModFour m 0 + 1 := by
        simp [lenT0CaseIIModFour]
        omega
      exact hmem⟩).1 = 5 := by
  have hq : 1 ≤ qT0CaseIIModFour m := by
    have hm9 : 9 < m := Fact.out
    have hmq : 12 * qT0CaseIIModFour m = m - 4 := twelve_mul_qT0CaseIIModFour_eq (m := m) hm
    omega
  let s : Fin (lenT0CaseIIModFour m 0 + 1) := ⟨2, by
    have hq0 : 0 < qT0CaseIIModFour m := by omega
    have hmem : 2 < lenT0CaseIIModFour m 0 + 1 := by
      simp [lenT0CaseIIModFour]
      omega
    exact hmem⟩
  have hsNotLeft : ¬ s.1 < 2 := by simp [s]
  change (pointT0CaseIIModFourZero (m := m) hm s).1 = 5
  rw [pointT0CaseIIModFourZero_val_right (m := m) hm (s := s) hsNotLeft]
  simp [s]

theorem pointT0CaseIIModFour_last_zero_val [Fact (9 < m)] (hm : m % 12 = 4) :
    (pointT0CaseIIModFour (m := m) hm 0 ⟨lenT0CaseIIModFour m 0, Nat.lt_succ_self _⟩).1 = m - 3 := by
  have hq : 1 ≤ qT0CaseIIModFour m := by
    have hm9 : 9 < m := Fact.out
    have hmq : 12 * qT0CaseIIModFour m = m - 4 := twelve_mul_qT0CaseIIModFour_eq (m := m) hm
    omega
  let s : Fin (lenT0CaseIIModFour m 0 + 1) := ⟨lenT0CaseIIModFour m 0, Nat.lt_succ_self _⟩
  have hsNotLeft : ¬ s.1 < 2 := by
    have h2 : 2 ≤ lenT0CaseIIModFour m 0 := by
      simp [lenT0CaseIIModFour]
      omega
    simpa [s] using h2
  have hmq : 12 * qT0CaseIIModFour m = m - 4 := twelve_mul_qT0CaseIIModFour_eq (m := m) hm
  change (pointT0CaseIIModFourZero (m := m) hm s).1 = m - 3
  rw [pointT0CaseIIModFourZero_val_right (m := m) hm (s := s) hsNotLeft]
  have hval : 5 + 4 * (lenT0CaseIIModFour m 0 - (1 + 1)) = m - 3 := by
    simp [lenT0CaseIIModFour]
    omega
  simpa [s] using hval

theorem pointT0CaseIIModFour_one_zero_val [Fact (9 < m)] (hm : m % 12 = 4) :
    (pointT0CaseIIModFour (m := m) hm 1 0).1 = 2 := by
  simp [pointT0CaseIIModFour, pointT0CaseIIModFourOne_val]

theorem pointT0CaseIIModFour_two_zero_val [Fact (9 < m)] (hm : m % 12 = 4) :
    (pointT0CaseIIModFour (m := m) hm 2 0).1 = 3 := by
  simp [pointT0CaseIIModFour, pointT0CaseIIModFourTwo_val]

theorem pointT0CaseIIModFour_three_zero_val [Fact (9 < m)] (hm : m % 12 = 4) :
    (pointT0CaseIIModFour (m := m) hm 3 0).1 = 4 := by
  simp [pointT0CaseIIModFour, pointT0CaseIIModFourThree_val]

theorem pointT0CaseIIModFour_last_one_val [Fact (9 < m)] (hm : m % 12 = 4) :
    (pointT0CaseIIModFour (m := m) hm 1 ⟨lenT0CaseIIModFour m 1, Nat.lt_succ_self _⟩).1 = m - 6 := by
  have hq : 1 ≤ qT0CaseIIModFour m := by
    have hm9 : 9 < m := Fact.out
    have hmq : 12 * qT0CaseIIModFour m = m - 4 := twelve_mul_qT0CaseIIModFour_eq (m := m) hm
    omega
  let s : Fin (lenT0CaseIIModFour m 1 + 1) := ⟨lenT0CaseIIModFour m 1, Nat.lt_succ_self _⟩
  change (pointT0CaseIIModFourOne (m := m) hm s).1 = m - 6
  rw [pointT0CaseIIModFourOne_val (m := m) hm (s := s)]
  have hmq : 12 * qT0CaseIIModFour m = m - 4 := twelve_mul_qT0CaseIIModFour_eq (m := m) hm
  have hval : 2 + 4 * lenT0CaseIIModFour m 1 = m - 6 := by
    simp [lenT0CaseIIModFour]
    omega
  simpa [s] using hval

theorem pointT0CaseIIModFour_prelast_two_val [Fact (9 < m)] (hm : m % 12 = 4) :
    let s : Fin (lenT0CaseIIModFour m 2 + 1) := ⟨lenT0CaseIIModFour m 2 - 1, by
      simp [lenT0CaseIIModFour]⟩
    (pointT0CaseIIModFour (m := m) hm 2 s).1 = m - 1 := by
  let s : Fin (lenT0CaseIIModFour m 2 + 1) := ⟨lenT0CaseIIModFour m 2 - 1, by
    simp [lenT0CaseIIModFour]⟩
  change (pointT0CaseIIModFourTwo (m := m) hm s).1 = m - 1
  rw [pointT0CaseIIModFourTwo_val (m := m) hm (s := s)]
  have hsNotLast : s.1 ≠ 3 * qT0CaseIIModFour m + 1 := by
    simp [s, lenT0CaseIIModFour]
  rw [if_neg hsNotLast]
  have hmq : 12 * qT0CaseIIModFour m = m - 4 := twelve_mul_qT0CaseIIModFour_eq (m := m) hm
  simp [s, lenT0CaseIIModFour] at *
  omega

theorem pointT0CaseIIModFour_last_two_val [Fact (9 < m)] (hm : m % 12 = 4) :
    (pointT0CaseIIModFour (m := m) hm 2 ⟨lenT0CaseIIModFour m 2, Nat.lt_succ_self _⟩).1 = 1 := by
  let s : Fin (lenT0CaseIIModFour m 2 + 1) := ⟨lenT0CaseIIModFour m 2, Nat.lt_succ_self _⟩
  change (pointT0CaseIIModFourTwo (m := m) hm s).1 = 1
  rw [pointT0CaseIIModFourTwo_val (m := m) hm (s := s)]
  have hsLast : s.1 = 3 * qT0CaseIIModFour m + 1 := by
    simp [s, lenT0CaseIIModFour]
  rw [if_pos hsLast]

theorem pointT0CaseIIModFour_last_three_val [Fact (9 < m)] (hm : m % 12 = 4) :
    (pointT0CaseIIModFour (m := m) hm 3 ⟨lenT0CaseIIModFour m 3, Nat.lt_succ_self _⟩).1 = m - 4 := by
  have hq : 1 ≤ qT0CaseIIModFour m := by
    have hm9 : 9 < m := Fact.out
    have hmq : 12 * qT0CaseIIModFour m = m - 4 := twelve_mul_qT0CaseIIModFour_eq (m := m) hm
    omega
  let s : Fin (lenT0CaseIIModFour m 3 + 1) := ⟨lenT0CaseIIModFour m 3, Nat.lt_succ_self _⟩
  change (pointT0CaseIIModFourThree (m := m) hm s).1 = m - 4
  rw [pointT0CaseIIModFourThree_val (m := m) hm (s := s)]
  have hmq : 12 * qT0CaseIIModFour m = m - 4 := twelve_mul_qT0CaseIIModFour_eq (m := m) hm
  have hval : 4 + 4 * lenT0CaseIIModFour m 3 = m - 4 := by
    simp [lenT0CaseIIModFour]
    omega
  simpa [s] using hval

private theorem pointT0CaseIIModFourZero_One_disjoint [Fact (9 < m)] (hm : m % 12 = 4) :
    ∀ s t, pointT0CaseIIModFour (m := m) hm 0 s ≠ pointT0CaseIIModFour (m := m) hm 1 t := by
  intro s t h
  have hv := congrArg Fin.val h
  have hv' : (pointT0CaseIIModFourZero (m := m) hm s).1 = (pointT0CaseIIModFourOne (m := m) hm t).1 := by
    simpa [pointT0CaseIIModFour] using hv
  have hmq : 12 * qT0CaseIIModFour m = m - 4 := twelve_mul_qT0CaseIIModFour_eq (m := m) hm
  by_cases hs : s.1 < 2
  · rw [pointT0CaseIIModFourZero_val_left (m := m) hm (s := s) hs,
      pointT0CaseIIModFourOne_val (m := m) hm (s := t)] at hv'
    by_cases hs0 : s.1 = 0
    · have : (0 : ℕ) = 2 + 4 * t.1 := by simpa [hs0] using hv'
      omega
    · have : m - 2 = 2 + 4 * t.1 := by simpa [hs0] using hv'
      have hq : 1 ≤ qT0CaseIIModFour m := by
        have hm9 : 9 < m := Fact.out
        omega
      have htLe : t.1 ≤ 3 * qT0CaseIIModFour m - 1 := by
        simpa [lenT0CaseIIModFour, hq] using Nat.le_of_lt_succ t.2
      omega
  · rw [pointT0CaseIIModFourZero_val_right (m := m) hm (s := s) hs,
      pointT0CaseIIModFourOne_val (m := m) hm (s := t)] at hv'
    have : 5 + 4 * (s.1 - (1 + 1)) = 2 + 4 * t.1 := by simpa using hv'
    omega

private theorem pointT0CaseIIModFourZero_Two_disjoint [Fact (9 < m)] (hm : m % 12 = 4) :
    ∀ s t, pointT0CaseIIModFour (m := m) hm 0 s ≠ pointT0CaseIIModFour (m := m) hm 2 t := by
  intro s t h
  have hv := congrArg Fin.val h
  have hv' : (pointT0CaseIIModFourZero (m := m) hm s).1 = (pointT0CaseIIModFourTwo (m := m) hm t).1 := by
    simpa [pointT0CaseIIModFour] using hv
  have hmq : 12 * qT0CaseIIModFour m = m - 4 := twelve_mul_qT0CaseIIModFour_eq (m := m) hm
  by_cases hs : s.1 < 2
  · rw [pointT0CaseIIModFourZero_val_left (m := m) hm (s := s) hs,
      pointT0CaseIIModFourTwo_val (m := m) hm (s := t)] at hv'
    by_cases hs0 : s.1 = 0
    · by_cases htLast : t.1 = 3 * qT0CaseIIModFour m + 1
      · have : (0 : ℕ) = 1 := by simpa [hs0, htLast] using hv'
        omega
      · have : (0 : ℕ) = 3 + 4 * t.1 := by simpa [hs0, htLast] using hv'
        omega
    · by_cases htLast : t.1 = 3 * qT0CaseIIModFour m + 1
      · have : m - 2 = (1 : ℕ) := by simpa [hs0, htLast] using hv'
        omega
      · have : m - 2 = 3 + 4 * t.1 := by simpa [hs0, htLast] using hv'
        omega
  · rw [pointT0CaseIIModFourZero_val_right (m := m) hm (s := s) hs,
      pointT0CaseIIModFourTwo_val (m := m) hm (s := t)] at hv'
    by_cases htLast : t.1 = 3 * qT0CaseIIModFour m + 1
    · have : 5 + 4 * (s.1 - (1 + 1)) = (1 : ℕ) := by simpa [htLast] using hv'
      omega
    · have : 5 + 4 * (s.1 - (1 + 1)) = 3 + 4 * t.1 := by simpa [htLast] using hv'
      omega

private theorem pointT0CaseIIModFourZero_Three_disjoint [Fact (9 < m)] (hm : m % 12 = 4) :
    ∀ s t, pointT0CaseIIModFour (m := m) hm 0 s ≠ pointT0CaseIIModFour (m := m) hm 3 t := by
  intro s t h
  have hv := congrArg Fin.val h
  have hv' :
      (pointT0CaseIIModFourZero (m := m) hm s).1 = (pointT0CaseIIModFourThree (m := m) hm t).1 := by
    simpa [pointT0CaseIIModFour] using hv
  have hmq : 12 * qT0CaseIIModFour m = m - 4 := twelve_mul_qT0CaseIIModFour_eq (m := m) hm
  by_cases hs : s.1 < 2
  · rw [pointT0CaseIIModFourZero_val_left (m := m) hm (s := s) hs,
      pointT0CaseIIModFourThree_val (m := m) hm (s := t)] at hv'
    by_cases hs0 : s.1 = 0
    · have : (0 : ℕ) = 4 + 4 * t.1 := by simpa [hs0] using hv'
      omega
    · have : m - 2 = 4 + 4 * t.1 := by simpa [hs0] using hv'
      omega
  · rw [pointT0CaseIIModFourZero_val_right (m := m) hm (s := s) hs,
      pointT0CaseIIModFourThree_val (m := m) hm (s := t)] at hv'
    have : 5 + 4 * (s.1 - (1 + 1)) = 4 + 4 * t.1 := by simpa using hv'
    omega

private theorem pointT0CaseIIModFourOne_Two_disjoint [Fact (9 < m)] (hm : m % 12 = 4) :
    ∀ s t, pointT0CaseIIModFour (m := m) hm 1 s ≠ pointT0CaseIIModFour (m := m) hm 2 t := by
  intro s t h
  have hv := congrArg Fin.val h
  have hv' : (pointT0CaseIIModFourOne (m := m) hm s).1 = (pointT0CaseIIModFourTwo (m := m) hm t).1 := by
    simpa [pointT0CaseIIModFour] using hv
  rw [pointT0CaseIIModFourOne_val (m := m) hm (s := s),
    pointT0CaseIIModFourTwo_val (m := m) hm (s := t)] at hv'
  by_cases htLast : t.1 = 3 * qT0CaseIIModFour m + 1
  · have : 2 + 4 * s.1 = (1 : ℕ) := by simpa [htLast] using hv'
    omega
  · have : 2 + 4 * s.1 = 3 + 4 * t.1 := by simpa [htLast] using hv'
    omega

private theorem pointT0CaseIIModFourOne_Three_disjoint [Fact (9 < m)] (hm : m % 12 = 4) :
    ∀ s t, pointT0CaseIIModFour (m := m) hm 1 s ≠ pointT0CaseIIModFour (m := m) hm 3 t := by
  intro s t h
  have hv := congrArg Fin.val h
  have hv' :
      (pointT0CaseIIModFourOne (m := m) hm s).1 = (pointT0CaseIIModFourThree (m := m) hm t).1 := by
    simpa [pointT0CaseIIModFour] using hv
  have : 2 + 4 * s.1 = 4 + 4 * t.1 := by
    simpa [pointT0CaseIIModFourOne_val, pointT0CaseIIModFourThree_val] using hv'
  omega

private theorem pointT0CaseIIModFourTwo_Three_disjoint [Fact (9 < m)] (hm : m % 12 = 4) :
    ∀ s t, pointT0CaseIIModFour (m := m) hm 2 s ≠ pointT0CaseIIModFour (m := m) hm 3 t := by
  intro s t h
  have hv := congrArg Fin.val h
  have hv' :
      (pointT0CaseIIModFourTwo (m := m) hm s).1 = (pointT0CaseIIModFourThree (m := m) hm t).1 := by
    simpa [pointT0CaseIIModFour] using hv
  rw [pointT0CaseIIModFourTwo_val (m := m) hm (s := s),
    pointT0CaseIIModFourThree_val (m := m) hm (s := t)] at hv'
  by_cases hsLast : s.1 = 3 * qT0CaseIIModFour m + 1
  · have : (1 : ℕ) = 4 + 4 * t.1 := by simpa [hsLast] using hv'
    omega
  · have : 3 + 4 * s.1 = 4 + 4 * t.1 := by simpa [hsLast] using hv'
    omega

theorem pointT0CaseIIModFourSigma_injective [Fact (9 < m)] (hm : m % 12 = 4) :
    Function.Injective (pointT0CaseIIModFourSigma (m := m) hm) := by
  intro p p' h
  rcases p with ⟨j, s⟩
  rcases p' with ⟨j', s'⟩
  fin_cases j <;> fin_cases j'
  · have hs : s = s' := pointT0CaseIIModFourZero_injective (m := m) hm h
    subst hs
    rfl
  · exfalso
    exact pointT0CaseIIModFourZero_One_disjoint (m := m) hm s s' h
  · exfalso
    exact pointT0CaseIIModFourZero_Two_disjoint (m := m) hm s s' h
  · exfalso
    exact pointT0CaseIIModFourZero_Three_disjoint (m := m) hm s s' h
  · exfalso
    exact pointT0CaseIIModFourZero_One_disjoint (m := m) hm s' s h.symm
  · have hs : s = s' := pointT0CaseIIModFourOne_injective (m := m) hm h
    subst hs
    rfl
  · exfalso
    exact pointT0CaseIIModFourOne_Two_disjoint (m := m) hm s s' h
  · exfalso
    exact pointT0CaseIIModFourOne_Three_disjoint (m := m) hm s s' h
  · exfalso
    exact pointT0CaseIIModFourZero_Two_disjoint (m := m) hm s' s h.symm
  · exfalso
    exact pointT0CaseIIModFourOne_Two_disjoint (m := m) hm s' s h.symm
  · have hs : s = s' := pointT0CaseIIModFourTwo_injective (m := m) hm h
    subst hs
    rfl
  · exfalso
    exact pointT0CaseIIModFourTwo_Three_disjoint (m := m) hm s s' h
  · exfalso
    exact pointT0CaseIIModFourZero_Three_disjoint (m := m) hm s' s h.symm
  · exfalso
    exact pointT0CaseIIModFourOne_Three_disjoint (m := m) hm s' s h.symm
  · exfalso
    exact pointT0CaseIIModFourTwo_Three_disjoint (m := m) hm s' s h.symm
  · have hs : s = s' := pointT0CaseIIModFourThree_injective (m := m) hm h
    subst hs
    rfl

noncomputable def spliceEquivT0CaseIIModFour [Fact (9 < m)] (hm : m % 12 = 4) :
    SplicePoint (lenT0CaseIIModFour m) ≃ Fin m := by
  let f := pointT0CaseIIModFourSigma (m := m) hm
  have hinj : Function.Injective f := pointT0CaseIIModFourSigma_injective (m := m) hm
  have hcard : Fintype.card (SplicePoint (lenT0CaseIIModFour m)) = Fintype.card (Fin m) := by
    simpa using card_splicePoint_lenT0CaseIIModFour (m := m) hm
  exact Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩)

@[simp] theorem spliceEquivT0CaseIIModFour_apply [Fact (9 < m)] (hm : m % 12 = 4)
    (p : SplicePoint (lenT0CaseIIModFour m)) :
    spliceEquivT0CaseIIModFour (m := m) hm p = pointT0CaseIIModFourSigma (m := m) hm p := by
  rfl

private theorem mod_six_eq_four_of_mod_twelve_eq_four (hm : m % 12 = 4) :
    m % 6 = 4 := by
  omega

private theorem pointT0CaseIIModFourZero_step [Fact (9 < m)] (hm : m % 12 = 4)
    (s : Fin (lenT0CaseIIModFour m 0 + 1)) (hs : s.1 + 1 < lenT0CaseIIModFour m 0 + 1) :
    T0CaseII (m := m) (mod_six_eq_four_of_mod_twelve_eq_four (m := m) hm)
      (pointT0CaseIIModFour (m := m) hm 0 s) =
      pointT0CaseIIModFour (m := m) hm 0 ⟨s.1 + 1, hs⟩ := by
  have hm6 : m % 6 = 4 := mod_six_eq_four_of_mod_twelve_eq_four (m := m) hm
  have hmq : 12 * qT0CaseIIModFour m = m - 4 := twelve_mul_qT0CaseIIModFour_eq (m := m) hm
  change T0CaseII (m := m) hm6 (pointT0CaseIIModFourZero (m := m) hm s) =
    pointT0CaseIIModFourZero (m := m) hm ⟨s.1 + 1, hs⟩
  by_cases hsLeft : s.1 < 2
  · have hsCases : s.1 = 0 ∨ s.1 = 1 := by
      omega
    cases hsCases with
    | inl hs0 =>
        have hsrc : (pointT0CaseIIModFourZero (m := m) hm s).1 = 0 := by
          rw [pointT0CaseIIModFourZero_val_left (m := m) hm (s := s) hsLeft]
          simp [hs0]
        have hsNextLeft : s.1 + 1 < 2 := by
          omega
        have hdst : (pointT0CaseIIModFourZero (m := m) hm ⟨s.1 + 1, hs⟩).1 = m - 2 := by
          rw [pointT0CaseIIModFourZero_val_left (m := m) hm (s := ⟨s.1 + 1, hs⟩) hsNextLeft]
          simp [hs0]
        apply Fin.ext
        change
          (T0CaseII (m := m) hm6 (pointT0CaseIIModFourZero (m := m) hm s)).1 =
            (pointT0CaseIIModFourZero (m := m) hm ⟨s.1 + 1, hs⟩).1
        rw [T0CaseII_eq_m_sub_two_of_val_eq_zero (m := m) hm6 hsrc, hdst]
    | inr hs1 =>
        have hsrc : (pointT0CaseIIModFourZero (m := m) hm s).1 = m - 2 := by
          rw [pointT0CaseIIModFourZero_val_left (m := m) hm (s := s) hsLeft]
          simp [hs1]
        have hsNextNotLeft : ¬ s.1 + 1 < 2 := by
          omega
        have hdst : (pointT0CaseIIModFourZero (m := m) hm ⟨s.1 + 1, hs⟩).1 = 5 := by
          rw [pointT0CaseIIModFourZero_val_right (m := m) hm (s := ⟨s.1 + 1, hs⟩) hsNextNotLeft]
          have hoff : (s.1 + 1) - (1 + 1) = 0 := by
            omega
          rw [hoff]
        apply Fin.ext
        change
          (T0CaseII (m := m) hm6 (pointT0CaseIIModFourZero (m := m) hm s)).1 =
            (pointT0CaseIIModFourZero (m := m) hm ⟨s.1 + 1, hs⟩).1
        rw [T0CaseII_eq_five_of_val_eq_m_sub_two (m := m) hm6 hsrc, hdst]
  · have hsNotLeft : ¬ s.1 < 2 := hsLeft
    have hsLtLen : s.1 < lenT0CaseIIModFour m 0 := by
      omega
    have hsOffLt : s.1 - (1 + 1) < 3 * qT0CaseIIModFour m - 1 := by
      simp [lenT0CaseIIModFour] at hsLtLen
      omega
    have hcur : (pointT0CaseIIModFourZero (m := m) hm s).1 = 5 + 4 * (s.1 - (1 + 1)) := by
      rw [pointT0CaseIIModFourZero_val_right (m := m) hm (s := s) hsNotLeft]
    have hx0 : (pointT0CaseIIModFourZero (m := m) hm s).1 ≠ 0 := by
      rw [hcur]
      omega
    have hx1 : (pointT0CaseIIModFourZero (m := m) hm s).1 ≠ 1 := by
      rw [hcur]
      omega
    have hx2 : (pointT0CaseIIModFourZero (m := m) hm s).1 ≠ 2 := by
      rw [hcur]
      omega
    have hxm6 : (pointT0CaseIIModFourZero (m := m) hm s).1 ≠ m - 6 := by
      rw [hcur]
      omega
    have hxm5 : (pointT0CaseIIModFourZero (m := m) hm s).1 ≠ m - 5 := by
      rw [hcur]
      omega
    have hxm4 : (pointT0CaseIIModFourZero (m := m) hm s).1 ≠ m - 4 := by
      rw [hcur]
      omega
    have hxm3 : (pointT0CaseIIModFourZero (m := m) hm s).1 ≠ m - 3 := by
      rw [hcur]
      omega
    have hxm2 : (pointT0CaseIIModFourZero (m := m) hm s).1 ≠ m - 2 := by
      rw [hcur]
      omega
    have hxm1 : (pointT0CaseIIModFourZero (m := m) hm s).1 ≠ m - 1 := by
      rw [hcur]
      omega
    have hsNextNotLeft : ¬ s.1 + 1 < 2 := by
      omega
    have hnext : (pointT0CaseIIModFourZero (m := m) hm ⟨s.1 + 1, hs⟩).1 =
        5 + 4 * ((s.1 + 1) - (1 + 1)) := by
      rw [pointT0CaseIIModFourZero_val_right (m := m) hm (s := ⟨s.1 + 1, hs⟩) hsNextNotLeft]
    apply Fin.ext
    change
      (T0CaseII (m := m) hm6 (pointT0CaseIIModFourZero (m := m) hm s)).1 =
        (pointT0CaseIIModFourZero (m := m) hm ⟨s.1 + 1, hs⟩).1
    rw [T0CaseII_eq_add_four_of_ne_special (m := m) hm6 hx0 hx1 hx2 hxm6 hxm5 hxm4 hxm3 hxm2 hxm1]
    rw [hcur, hnext]
    omega

private theorem pointT0CaseIIModFourOne_step [Fact (9 < m)] (hm : m % 12 = 4)
    (s : Fin (lenT0CaseIIModFour m 1 + 1)) (hs : s.1 + 1 < lenT0CaseIIModFour m 1 + 1) :
    T0CaseII (m := m) (mod_six_eq_four_of_mod_twelve_eq_four (m := m) hm)
      (pointT0CaseIIModFour (m := m) hm 1 s) =
      pointT0CaseIIModFour (m := m) hm 1 ⟨s.1 + 1, hs⟩ := by
  have hm6 : m % 6 = 4 := mod_six_eq_four_of_mod_twelve_eq_four (m := m) hm
  have hmq : 12 * qT0CaseIIModFour m = m - 4 := twelve_mul_qT0CaseIIModFour_eq (m := m) hm
  have hq : 1 ≤ qT0CaseIIModFour m := by
    have hm9 : 9 < m := Fact.out
    omega
  by_cases hs0 : s.1 = 0
  · apply Fin.ext
    change
      (T0CaseII (m := m) hm6 (pointT0CaseIIModFour (m := m) hm 1 s)).1 =
        (pointT0CaseIIModFour (m := m) hm 1 ⟨s.1 + 1, hs⟩).1
    have hsEq : s = 0 := Fin.ext hs0
    subst hsEq
    have hsrc : (pointT0CaseIIModFour (m := m) hm 1 0).1 = 2 :=
      pointT0CaseIIModFour_one_zero_val (m := m) hm
    have hlen : 1 < lenT0CaseIIModFour m 1 + 1 := by
      simp [lenT0CaseIIModFour]
      omega
    have h1 :
        (⟨0 + 1, hs⟩ : Fin (lenT0CaseIIModFour m 1 + 1)) =
          ⟨1, hlen⟩ := by
      apply Fin.ext
      simp
    have hdst : (pointT0CaseIIModFour (m := m) hm 1 ⟨0 + 1, hs⟩).1 = 6 := by
      rw [h1]
      change (pointT0CaseIIModFourOne (m := m) hm ⟨1, hlen⟩).1 = 6
      rw [pointT0CaseIIModFourOne_val (m := m) hm (s := ⟨1, hlen⟩)]
      norm_num
    rw [T0CaseII_eq_six_of_val_eq_two (m := m) hm6 hsrc]
    change 6 = (pointT0CaseIIModFour (m := m) hm 1 ⟨0 + 1, hs⟩).1
    rw [hdst]
  · have hsLt : s.1 < lenT0CaseIIModFour m 1 := by
      omega
    have hsLt' : s.1 < 3 * qT0CaseIIModFour m - 1 := by
      simpa [lenT0CaseIIModFour] using hsLt
    have hcur : (pointT0CaseIIModFour (m := m) hm 1 s).1 = 2 + 4 * s.1 := by
      simpa [pointT0CaseIIModFour] using pointT0CaseIIModFourOne_val (m := m) hm (s := s)
    have hx0 : (pointT0CaseIIModFour (m := m) hm 1 s).1 ≠ 0 := by
      rw [hcur]
      omega
    have hx1 : (pointT0CaseIIModFour (m := m) hm 1 s).1 ≠ 1 := by
      rw [hcur]
      omega
    have hx2 : (pointT0CaseIIModFour (m := m) hm 1 s).1 ≠ 2 := by
      rw [hcur]
      omega
    have hxm6 : (pointT0CaseIIModFour (m := m) hm 1 s).1 ≠ m - 6 := by
      rw [hcur]
      omega
    have hxm5 : (pointT0CaseIIModFour (m := m) hm 1 s).1 ≠ m - 5 := by
      rw [hcur]
      omega
    have hxm4 : (pointT0CaseIIModFour (m := m) hm 1 s).1 ≠ m - 4 := by
      rw [hcur]
      omega
    have hxm3 : (pointT0CaseIIModFour (m := m) hm 1 s).1 ≠ m - 3 := by
      rw [hcur]
      omega
    have hxm2 : (pointT0CaseIIModFour (m := m) hm 1 s).1 ≠ m - 2 := by
      rw [hcur]
      omega
    have hxm1 : (pointT0CaseIIModFour (m := m) hm 1 s).1 ≠ m - 1 := by
      rw [hcur]
      omega
    apply Fin.ext
    change
      (T0CaseII (m := m) hm6 (pointT0CaseIIModFour (m := m) hm 1 s)).1 =
        (pointT0CaseIIModFour (m := m) hm 1 ⟨s.1 + 1, hs⟩).1
    rw [T0CaseII_eq_add_four_of_ne_special (m := m) hm6 hx0 hx1 hx2 hxm6 hxm5 hxm4 hxm3 hxm2 hxm1]
    rw [hcur]
    have hnext : (pointT0CaseIIModFour (m := m) hm 1 ⟨s.1 + 1, hs⟩).1 = 2 + 4 * (s.1 + 1) := by
      simpa [pointT0CaseIIModFour] using
        pointT0CaseIIModFourOne_val (m := m) hm (s := ⟨s.1 + 1, hs⟩)
    rw [hnext]
    omega

private theorem pointT0CaseIIModFourTwo_step [Fact (9 < m)] (hm : m % 12 = 4)
    (s : Fin (lenT0CaseIIModFour m 2 + 1)) (hs : s.1 + 1 < lenT0CaseIIModFour m 2 + 1) :
    T0CaseII (m := m) (mod_six_eq_four_of_mod_twelve_eq_four (m := m) hm)
      (pointT0CaseIIModFour (m := m) hm 2 s) =
      pointT0CaseIIModFour (m := m) hm 2 ⟨s.1 + 1, hs⟩ := by
  have hm6 : m % 6 = 4 := mod_six_eq_four_of_mod_twelve_eq_four (m := m) hm
  have hmq : 12 * qT0CaseIIModFour m = m - 4 := twelve_mul_qT0CaseIIModFour_eq (m := m) hm
  have hq : 1 ≤ qT0CaseIIModFour m := by
    have hm9 : 9 < m := Fact.out
    omega
  by_cases hsm5 : s.1 = 3 * qT0CaseIIModFour m - 1
  · have hsNotLast : s.1 ≠ 3 * qT0CaseIIModFour m + 1 := by
      omega
    have hcur : (pointT0CaseIIModFour (m := m) hm 2 s).1 = 3 + 4 * s.1 := by
      change (pointT0CaseIIModFourTwo (m := m) hm s).1 = 3 + 4 * s.1
      rw [pointT0CaseIIModFourTwo_val (m := m) hm (s := s)]
      rw [if_neg hsNotLast]
    have hsrc : (pointT0CaseIIModFour (m := m) hm 2 s).1 = m - 5 := by
      calc
        (pointT0CaseIIModFour (m := m) hm 2 s).1 = 3 + 4 * s.1 := hcur
        _ = 3 + 4 * (3 * qT0CaseIIModFour m - 1) := by rw [hsm5]
        _ = 12 * qT0CaseIIModFour m - 1 := by omega
        _ = m - 5 := by omega
    have hsNextNotLast : (s.1 + 1) ≠ 3 * qT0CaseIIModFour m + 1 := by
      omega
    have hdst : (pointT0CaseIIModFour (m := m) hm 2 ⟨s.1 + 1, hs⟩).1 = m - 1 := by
      change (pointT0CaseIIModFourTwo (m := m) hm ⟨s.1 + 1, hs⟩).1 = m - 1
      rw [pointT0CaseIIModFourTwo_val (m := m) hm (s := ⟨s.1 + 1, hs⟩)]
      rw [if_neg hsNextNotLast]
      have hnextOff : s.1 + 1 = 3 * qT0CaseIIModFour m := by
        omega
      calc
        3 + 4 * ((⟨s.1 + 1, hs⟩ : Fin (lenT0CaseIIModFour m 2 + 1)).1) = 3 + 4 * (s.1 + 1) := by
          rfl
        _ = 3 + 4 * (3 * qT0CaseIIModFour m) := by rw [hnextOff]
        _ = m - 1 := by omega
    apply Fin.ext
    change
      (T0CaseII (m := m) hm6 (pointT0CaseIIModFour (m := m) hm 2 s)).1 =
        (pointT0CaseIIModFour (m := m) hm 2 ⟨s.1 + 1, hs⟩).1
    rw [T0CaseII_eq_m_sub_one_of_val_eq_m_sub_five (m := m) hm6 hsrc, hdst]
  · by_cases hsm1 : s.1 = 3 * qT0CaseIIModFour m
    · have hsNotLast : s.1 ≠ 3 * qT0CaseIIModFour m + 1 := by
        omega
      have hcur : (pointT0CaseIIModFour (m := m) hm 2 s).1 = 3 + 4 * s.1 := by
        change (pointT0CaseIIModFourTwo (m := m) hm s).1 = 3 + 4 * s.1
        rw [pointT0CaseIIModFourTwo_val (m := m) hm (s := s)]
        rw [if_neg hsNotLast]
      have hsrc : (pointT0CaseIIModFour (m := m) hm 2 s).1 = m - 1 := by
        calc
          (pointT0CaseIIModFour (m := m) hm 2 s).1 = 3 + 4 * s.1 := hcur
          _ = 3 + 4 * (3 * qT0CaseIIModFour m) := by rw [hsm1]
          _ = m - 1 := by omega
      have hsNextLast : s.1 + 1 = 3 * qT0CaseIIModFour m + 1 := by
        omega
      have hdst : (pointT0CaseIIModFour (m := m) hm 2 ⟨s.1 + 1, hs⟩).1 = 1 := by
        change (pointT0CaseIIModFourTwo (m := m) hm ⟨s.1 + 1, hs⟩).1 = 1
        rw [pointT0CaseIIModFourTwo_val (m := m) hm (s := ⟨s.1 + 1, hs⟩)]
        rw [if_pos hsNextLast]
      apply Fin.ext
      change
        (T0CaseII (m := m) hm6 (pointT0CaseIIModFour (m := m) hm 2 s)).1 =
          (pointT0CaseIIModFour (m := m) hm 2 ⟨s.1 + 1, hs⟩).1
      rw [T0CaseII_eq_one_of_val_eq_m_sub_one (m := m) hm6 hsrc, hdst]
    · have hsLtLen : s.1 < lenT0CaseIIModFour m 2 := by
        omega
      have hsNotLast : s.1 ≠ 3 * qT0CaseIIModFour m + 1 := by
        simp [lenT0CaseIIModFour] at hsLtLen
        omega
      have hcur : (pointT0CaseIIModFour (m := m) hm 2 s).1 = 3 + 4 * s.1 := by
        change (pointT0CaseIIModFourTwo (m := m) hm s).1 = 3 + 4 * s.1
        rw [pointT0CaseIIModFourTwo_val (m := m) hm (s := s)]
        rw [if_neg hsNotLast]
      have hx0 : (pointT0CaseIIModFour (m := m) hm 2 s).1 ≠ 0 := by
        rw [hcur]
        omega
      have hx1 : (pointT0CaseIIModFour (m := m) hm 2 s).1 ≠ 1 := by
        rw [hcur]
        omega
      have hx2 : (pointT0CaseIIModFour (m := m) hm 2 s).1 ≠ 2 := by
        rw [hcur]
        omega
      have hxm6 : (pointT0CaseIIModFour (m := m) hm 2 s).1 ≠ m - 6 := by
        rw [hcur]
        omega
      have hxm5 : (pointT0CaseIIModFour (m := m) hm 2 s).1 ≠ m - 5 := by
        rw [hcur]
        omega
      have hxm4 : (pointT0CaseIIModFour (m := m) hm 2 s).1 ≠ m - 4 := by
        rw [hcur]
        omega
      have hxm3 : (pointT0CaseIIModFour (m := m) hm 2 s).1 ≠ m - 3 := by
        rw [hcur]
        omega
      have hxm2 : (pointT0CaseIIModFour (m := m) hm 2 s).1 ≠ m - 2 := by
        rw [hcur]
        omega
      have hxm1 : (pointT0CaseIIModFour (m := m) hm 2 s).1 ≠ m - 1 := by
        rw [hcur]
        omega
      have hsNextNotLast : s.1 + 1 ≠ 3 * qT0CaseIIModFour m + 1 := by
        omega
      have hnext : (pointT0CaseIIModFour (m := m) hm 2 ⟨s.1 + 1, hs⟩).1 =
          3 + 4 * (s.1 + 1) := by
        change (pointT0CaseIIModFourTwo (m := m) hm ⟨s.1 + 1, hs⟩).1 = 3 + 4 * (s.1 + 1)
        rw [pointT0CaseIIModFourTwo_val (m := m) hm (s := ⟨s.1 + 1, hs⟩)]
        rw [if_neg hsNextNotLast]
      apply Fin.ext
      change
        (T0CaseII (m := m) hm6 (pointT0CaseIIModFour (m := m) hm 2 s)).1 =
          (pointT0CaseIIModFour (m := m) hm 2 ⟨s.1 + 1, hs⟩).1
      rw [T0CaseII_eq_add_four_of_ne_special (m := m) hm6 hx0 hx1 hx2 hxm6 hxm5 hxm4 hxm3
        hxm2 hxm1]
      rw [hcur, hnext]
      omega

private theorem pointT0CaseIIModFourThree_step [Fact (9 < m)] (hm : m % 12 = 4)
    (s : Fin (lenT0CaseIIModFour m 3 + 1)) (hs : s.1 + 1 < lenT0CaseIIModFour m 3 + 1) :
    T0CaseII (m := m) (mod_six_eq_four_of_mod_twelve_eq_four (m := m) hm)
      (pointT0CaseIIModFour (m := m) hm 3 s) =
      pointT0CaseIIModFour (m := m) hm 3 ⟨s.1 + 1, hs⟩ := by
  have hm6 : m % 6 = 4 := mod_six_eq_four_of_mod_twelve_eq_four (m := m) hm
  have hmq : 12 * qT0CaseIIModFour m = m - 4 := twelve_mul_qT0CaseIIModFour_eq (m := m) hm
  have hsLt : s.1 < lenT0CaseIIModFour m 3 := by
    omega
  have hsLt' : s.1 < 3 * qT0CaseIIModFour m - 1 := by
    simpa [lenT0CaseIIModFour] using hsLt
  have hcur : (pointT0CaseIIModFour (m := m) hm 3 s).1 = 4 + 4 * s.1 := by
    simpa [pointT0CaseIIModFour] using pointT0CaseIIModFourThree_val (m := m) hm (s := s)
  have hx0 : (pointT0CaseIIModFour (m := m) hm 3 s).1 ≠ 0 := by
    rw [hcur]
    omega
  have hx1 : (pointT0CaseIIModFour (m := m) hm 3 s).1 ≠ 1 := by
    rw [hcur]
    omega
  have hx2 : (pointT0CaseIIModFour (m := m) hm 3 s).1 ≠ 2 := by
    rw [hcur]
    omega
  have hxm6 : (pointT0CaseIIModFour (m := m) hm 3 s).1 ≠ m - 6 := by
    rw [hcur]
    omega
  have hxm5 : (pointT0CaseIIModFour (m := m) hm 3 s).1 ≠ m - 5 := by
    rw [hcur]
    omega
  have hxm4 : (pointT0CaseIIModFour (m := m) hm 3 s).1 ≠ m - 4 := by
    rw [hcur]
    omega
  have hxm3 : (pointT0CaseIIModFour (m := m) hm 3 s).1 ≠ m - 3 := by
    rw [hcur]
    omega
  have hxm2 : (pointT0CaseIIModFour (m := m) hm 3 s).1 ≠ m - 2 := by
    rw [hcur]
    omega
  have hxm1 : (pointT0CaseIIModFour (m := m) hm 3 s).1 ≠ m - 1 := by
    rw [hcur]
    omega
  have hnext : (pointT0CaseIIModFour (m := m) hm 3 ⟨s.1 + 1, hs⟩).1 = 4 + 4 * (s.1 + 1) := by
    simpa [pointT0CaseIIModFour] using
      pointT0CaseIIModFourThree_val (m := m) hm (s := ⟨s.1 + 1, hs⟩)
  apply Fin.ext
  change
    (T0CaseII (m := m) hm6 (pointT0CaseIIModFour (m := m) hm 3 s)).1 =
      (pointT0CaseIIModFour (m := m) hm 3 ⟨s.1 + 1, hs⟩).1
  rw [T0CaseII_eq_add_four_of_ne_special (m := m) hm6 hx0 hx1 hx2 hxm6 hxm5 hxm4 hxm3 hxm2 hxm1]
  rw [hcur, hnext]
  omega

theorem pointT0CaseIIModFour_step [Fact (9 < m)] (hm : m % 12 = 4) {j : Fin 4}
    (s : Fin (lenT0CaseIIModFour m j + 1)) (hs : s.1 + 1 < lenT0CaseIIModFour m j + 1) :
    T0CaseII (m := m) (mod_six_eq_four_of_mod_twelve_eq_four (m := m) hm)
      (pointT0CaseIIModFour (m := m) hm j s) =
      pointT0CaseIIModFour (m := m) hm j ⟨s.1 + 1, hs⟩ := by
  fin_cases j
  · simpa using pointT0CaseIIModFourZero_step (m := m) hm s hs
  · simpa using pointT0CaseIIModFourOne_step (m := m) hm s hs
  · simpa using pointT0CaseIIModFourTwo_step (m := m) hm s hs
  · simpa using pointT0CaseIIModFourThree_step (m := m) hm s hs

theorem pointT0CaseIIModFour_wrap [Fact (9 < m)] (hm : m % 12 = 4) :
    ∀ j : Fin 4,
      T0CaseII (m := m) (mod_six_eq_four_of_mod_twelve_eq_four (m := m) hm)
        (pointT0CaseIIModFour (m := m) hm j ⟨lenT0CaseIIModFour m j, Nat.lt_succ_self _⟩) =
      pointT0CaseIIModFour (m := m) hm (nextBlock j) 0 := by
  intro j
  have hm6 : m % 6 = 4 := mod_six_eq_four_of_mod_twelve_eq_four (m := m) hm
  fin_cases j
  · apply Fin.ext
    change
      (T0CaseII (m := m) hm6
        (pointT0CaseIIModFour (m := m) hm 0 ⟨lenT0CaseIIModFour m 0, Nat.lt_succ_self _⟩)).1 =
      (pointT0CaseIIModFour (m := m) hm (nextBlock 0) 0).1
    have hsrc :
        (pointT0CaseIIModFour (m := m) hm 0 ⟨lenT0CaseIIModFour m 0, Nat.lt_succ_self _⟩).1 =
          m - 3 :=
      pointT0CaseIIModFour_last_zero_val (m := m) hm
    have hdst : (pointT0CaseIIModFour (m := m) hm (nextBlock 0) 0).1 = 2 := by
      simpa [nextBlock] using pointT0CaseIIModFour_one_zero_val (m := m) hm
    rw [T0CaseII_eq_two_of_val_eq_m_sub_three (m := m) hm6 hsrc, hdst]
  · apply Fin.ext
    change
      (T0CaseII (m := m) hm6
        (pointT0CaseIIModFour (m := m) hm 1 ⟨lenT0CaseIIModFour m 1, Nat.lt_succ_self _⟩)).1 =
      (pointT0CaseIIModFour (m := m) hm (nextBlock 1) 0).1
    have hsrc :
        (pointT0CaseIIModFour (m := m) hm 1 ⟨lenT0CaseIIModFour m 1, Nat.lt_succ_self _⟩).1 =
          m - 6 :=
      pointT0CaseIIModFour_last_one_val (m := m) hm
    have hdst : (pointT0CaseIIModFour (m := m) hm (nextBlock 1) 0).1 = 3 := by
      simpa [nextBlock] using pointT0CaseIIModFour_two_zero_val (m := m) hm
    rw [T0CaseII_eq_three_of_val_eq_m_sub_six (m := m) hm6 hsrc, hdst]
  · apply Fin.ext
    change
      (T0CaseII (m := m) hm6
        (pointT0CaseIIModFour (m := m) hm 2 ⟨lenT0CaseIIModFour m 2, Nat.lt_succ_self _⟩)).1 =
      (pointT0CaseIIModFour (m := m) hm (nextBlock 2) 0).1
    have hsrc :
        (pointT0CaseIIModFour (m := m) hm 2 ⟨lenT0CaseIIModFour m 2, Nat.lt_succ_self _⟩).1 =
          1 :=
      pointT0CaseIIModFour_last_two_val (m := m) hm
    have hdst : (pointT0CaseIIModFour (m := m) hm (nextBlock 2) 0).1 = 4 := by
      simpa [nextBlock] using pointT0CaseIIModFour_three_zero_val (m := m) hm
    rw [T0CaseII_eq_four_of_val_eq_one (m := m) hm6 hsrc, hdst]
  · apply Fin.ext
    change
      (T0CaseII (m := m) hm6
        (pointT0CaseIIModFour (m := m) hm 3 ⟨lenT0CaseIIModFour m 3, Nat.lt_succ_self _⟩)).1 =
      (pointT0CaseIIModFour (m := m) hm (nextBlock 3) 0).1
    have hsrc :
        (pointT0CaseIIModFour (m := m) hm 3 ⟨lenT0CaseIIModFour m 3, Nat.lt_succ_self _⟩).1 =
          m - 4 :=
      pointT0CaseIIModFour_last_three_val (m := m) hm
    have hdst : (pointT0CaseIIModFour (m := m) hm (nextBlock 3) 0).1 = 0 := by
      simpa [nextBlock] using pointT0CaseIIModFour_zero_zero_val (m := m) hm
    rw [T0CaseII_eq_zero_of_val_eq_m_sub_four (m := m) hm6 hsrc, hdst]

theorem cycleOn_T0CaseIIModFour [Fact (9 < m)] (hm : m % 12 = 4) :
    TorusD4.CycleOn m
      (T0CaseII (m := m) (mod_six_eq_four_of_mod_twelve_eq_four (m := m) hm))
      ⟨0, by
        have hm9 : 9 < m := Fact.out
        omega⟩ := by
  have hcycle :=
    cycleOn_of_spliceBlocks
      (len := lenT0CaseIIModFour m)
      (e := spliceEquivT0CaseIIModFour (m := m) hm)
      (T := T0CaseII (m := m) (mod_six_eq_four_of_mod_twelve_eq_four (m := m) hm))
      (hstep := by
        intro j s hs
        simpa using pointT0CaseIIModFour_step (m := m) hm (j := j) s hs)
      (hwrap := by
        intro j
        simpa using pointT0CaseIIModFour_wrap (m := m) hm j)
  simpa [spliceStart, spliceEquivT0CaseIIModFour, pointT0CaseIIModFourSigma,
    pointT0CaseIIModFour, lenT0CaseIIModFour] using hcycle

end TorusD3Even
