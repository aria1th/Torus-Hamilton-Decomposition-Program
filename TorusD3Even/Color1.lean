import TorusD3Even.Splice
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace TorusD3Even

local instance : Fact (0 < 3) := ⟨by decide⟩

/-
Color 1, Case I (`m ≡ 0,2 mod 6`) from the splice-integrated manuscript.

This file currently sets up the first splice row

  F11 = (0,2,5,...,m-3)
  F12 = (1,4,7,...,m-1)
  F13 = (3,6,9,...,m-2)

for the subcase `m ≡ 2 mod 6`, together with the common Case-I formulas

  0    ↦ 2
  x    ↦ x + 3    for 1 ≤ x ≤ m - 4
  m-3  ↦ 1
  m-2  ↦ 0
  m-1  ↦ 3.
-/

def T1CaseI [Fact (5 < m)] (x : Fin m) : Fin m :=
  let hm5 : 5 < m := Fact.out
  if hx0 : x.1 = 0 then
    ⟨2, by omega⟩
  else if hxm3 : x.1 = m - 3 then
    ⟨1, by omega⟩
  else if hxm2 : x.1 = m - 2 then
    ⟨0, by omega⟩
  else if hxm1 : x.1 = m - 1 then
    ⟨3, by omega⟩
  else
    ⟨x.1 + 3, by omega⟩

def rho1CaseI [Fact (5 < m)] (x : Fin m) : ℕ :=
  if _hx0 : x.1 = 0 then
    1
  else if _hxm2 : x.1 = m - 2 then
    1
  else if _hxm3 : x.1 = m - 3 then
    m + 3
  else if _hxm1 : x.1 = m - 1 then
    m + 3
  else
    m + 2

theorem eq_six_mul_add_two_of_mod_six_eq_two (hm : m % 6 = 2) :
    ∃ q, m = 6 * q + 2 := by
  refine ⟨m / 6, ?_⟩
  have hdiv := Nat.mod_add_div m 6
  omega

def lenT1CaseIModTwo (m : ℕ) : Fin 3 → ℕ
  | ⟨0, _⟩ => (m - 2) / 3
  | ⟨1, _⟩ => (m - 2) / 3
  | _ => (m - 5) / 3

def pointT1CaseIModTwo [Fact (7 < m)] (j : Fin 3) :
    Fin (lenT1CaseIModTwo m j + 1) → Fin m :=
  match j with
  | ⟨0, _⟩ => fun s =>
      by
        have hm7 : 7 < m := Fact.out
        by_cases hs0 : s.1 = 0
        · exact ⟨0, by omega⟩
        · exact ⟨3 * s.1 - 1, by
            have hsPos : 0 < s.1 := Nat.pos_of_ne_zero hs0
            have hsLe : s.1 ≤ (m - 2) / 3 := Nat.lt_succ_iff.mp s.2
            have hmul : 3 * s.1 ≤ 3 * ((m - 2) / 3) := Nat.mul_le_mul_left 3 hsLe
            have hdiv : 3 * ((m - 2) / 3) ≤ m - 2 := Nat.mul_div_le (m - 2) 3
            omega⟩
  | ⟨1, _⟩ => fun s =>
      by
        have hm7 : 7 < m := Fact.out
        exact ⟨3 * s.1 + 1, by
          have hsLe : s.1 ≤ (m - 2) / 3 := Nat.lt_succ_iff.mp s.2
          have hmul : 3 * s.1 ≤ 3 * ((m - 2) / 3) := Nat.mul_le_mul_left 3 hsLe
          have hdiv : 3 * ((m - 2) / 3) ≤ m - 2 := Nat.mul_div_le (m - 2) 3
          omega⟩
  | ⟨_ + 2, _⟩ => fun s =>
      by
        have hm7 : 7 < m := Fact.out
        exact ⟨3 * s.1 + 3, by
          have hsLe : s.1 ≤ (m - 5) / 3 := Nat.lt_succ_iff.mp s.2
          have hmul : 3 * s.1 ≤ 3 * ((m - 5) / 3) := Nat.mul_le_mul_left 3 hsLe
          have hdiv : 3 * ((m - 5) / 3) ≤ m - 5 := Nat.mul_div_le (m - 5) 3
          omega⟩

def pointT1CaseIModTwoSigma [Fact (7 < m)] :
    SplicePoint (lenT1CaseIModTwo m) → Fin m
  | ⟨j, s⟩ => pointT1CaseIModTwo (m := m) j s

def indexT1CaseIModTwo [Fact (7 < m)] (hm : m % 6 = 2) (x : Fin m) :
    SplicePoint (lenT1CaseIModTwo m) :=
  if hx0 : x.1 = 0 then
    ⟨(0 : Fin 3), (0 : Fin ((m - 2) / 3 + 1))⟩
  else if hx1 : x.1 % 3 = 1 then
    ⟨(1 : Fin 3), ⟨((x.1 - 1) / 3) % (((m - 2) / 3) + 1), by
      have hm7 : 7 < m := Fact.out
      exact Nat.mod_lt _ (by omega)⟩⟩
  else if hx2 : x.1 % 3 = 2 then
    ⟨(0 : Fin 3), ⟨((x.1 + 1) / 3) % (((m - 2) / 3) + 1), by
      have hm7 : 7 < m := Fact.out
      exact Nat.mod_lt _ (by omega)⟩⟩
  else
    ⟨(2 : Fin 3), ⟨(x.1 / 3 - 1) % (((m - 5) / 3) + 1), by
      have hm7 : 7 < m := Fact.out
      exact Nat.mod_lt _ (by omega)⟩⟩

theorem card_splicePoint_lenT1CaseIModTwo [Fact (7 < m)] (hm : m % 6 = 2) :
    Fintype.card (SplicePoint (lenT1CaseIModTwo m)) = m := by
  rcases eq_six_mul_add_two_of_mod_six_eq_two (m := m) hm with ⟨q, rfl⟩
  have hq : 1 ≤ q := by
    have hm7 : 7 < 6 * q + 2 := Fact.out
    omega
  have hcard :
      Fintype.card (SplicePoint (lenT1CaseIModTwo (6 * q + 2)))
        = ∑ j : Fin 3, (lenT1CaseIModTwo (6 * q + 2) j + 1) := by
    simpa [SplicePoint] using
      (Fintype.card_sigma (α := fun j : Fin 3 => Fin (lenT1CaseIModTwo (6 * q + 2) j + 1)))
  have hdiv6 : 6 * q / 3 = 2 * q := by
    calc
      6 * q / 3 = (3 * (2 * q)) / 3 := by ring_nf
      _ = 2 * q := Nat.mul_div_right (2 * q) (by decide : 0 < 3)
  have h0 : lenT1CaseIModTwo (6 * q + 2) 0 = 2 * q := by
    simp [lenT1CaseIModTwo, hdiv6]
  have h1 : lenT1CaseIModTwo (6 * q + 2) 1 = 2 * q := by
    simp [lenT1CaseIModTwo, hdiv6]
  have h2 : lenT1CaseIModTwo (6 * q + 2) 2 = 2 * q - 1 := by
    have hq' : q ≠ 0 := by omega
    calc
      lenT1CaseIModTwo (6 * q + 2) 2 = (6 * q - 3) / 3 := by simp [lenT1CaseIModTwo]
      _ = (3 * (2 * q - 1)) / 3 := by
            have : 6 * q - 3 = 3 * (2 * q - 1) := by omega
            rw [this]
      _ = 2 * q - 1 := Nat.mul_div_right (2 * q - 1) (by decide : 0 < 3)
  rw [hcard, Fin.sum_univ_three, h0, h1, h2]
  omega

theorem pointT1CaseIModTwo_zero_val [Fact (7 < m)]
    (s : Fin (lenT1CaseIModTwo m 0 + 1)) :
    (pointT1CaseIModTwo (m := m) 0 s).1 = if s.1 = 0 then 0 else 3 * s.1 - 1 := by
  by_cases hs0 : s.1 = 0
  · simp [pointT1CaseIModTwo, lenT1CaseIModTwo, hs0]
  · simp [pointT1CaseIModTwo, lenT1CaseIModTwo, hs0]

theorem pointT1CaseIModTwo_one_val [Fact (7 < m)]
    (s : Fin (lenT1CaseIModTwo m 1 + 1)) :
    (pointT1CaseIModTwo (m := m) 1 s).1 = 3 * s.1 + 1 := by
  simp [pointT1CaseIModTwo, lenT1CaseIModTwo]

theorem pointT1CaseIModTwo_two_val [Fact (7 < m)]
    (s : Fin (lenT1CaseIModTwo m 2 + 1)) :
    (pointT1CaseIModTwo (m := m) 2 s).1 = 3 * s.1 + 3 := by
  simp [pointT1CaseIModTwo, lenT1CaseIModTwo]

private theorem lenT1CaseIModTwo_zero_eq (q : ℕ) :
    lenT1CaseIModTwo (6 * q + 2) 0 = 2 * q := by
  have hdiv6 : 6 * q / 3 = 2 * q := by
    calc
      6 * q / 3 = (3 * (2 * q)) / 3 := by ring_nf
      _ = 2 * q := Nat.mul_div_right (2 * q) (by decide : 0 < 3)
  simp [lenT1CaseIModTwo, hdiv6]

private theorem lenT1CaseIModTwo_one_eq (q : ℕ) :
    lenT1CaseIModTwo (6 * q + 2) 1 = 2 * q := by
  have hdiv6 : 6 * q / 3 = 2 * q := by
    calc
      6 * q / 3 = (3 * (2 * q)) / 3 := by ring_nf
      _ = 2 * q := Nat.mul_div_right (2 * q) (by decide : 0 < 3)
  simp [lenT1CaseIModTwo, hdiv6]

private theorem lenT1CaseIModTwo_two_eq (q : ℕ) :
    lenT1CaseIModTwo (6 * q + 2) 2 = 2 * q - 1 := by
  calc
    lenT1CaseIModTwo (6 * q + 2) 2 = (6 * q - 3) / 3 := by
      simp [lenT1CaseIModTwo]
    _ = (3 * (2 * q - 1)) / 3 := by
          have : 6 * q - 3 = 3 * (2 * q - 1) := by omega
          rw [this]
    _ = 2 * q - 1 := Nat.mul_div_right (2 * q - 1) (by decide : 0 < 3)

theorem pointT1CaseIModTwo_zero_zero_val [Fact (7 < m)] :
    (pointT1CaseIModTwo (m := m) 0 0).1 = 0 := by
  simp [pointT1CaseIModTwo, lenT1CaseIModTwo]

theorem pointT1CaseIModTwo_one_zero_val [Fact (7 < m)] :
    (pointT1CaseIModTwo (m := m) 1 0).1 = 1 := by
  simp [pointT1CaseIModTwo, lenT1CaseIModTwo]

theorem pointT1CaseIModTwo_two_zero_val [Fact (7 < m)] :
    (pointT1CaseIModTwo (m := m) 2 0).1 = 3 := by
  simp [pointT1CaseIModTwo, lenT1CaseIModTwo]

theorem pointT1CaseIModTwo_last_zero_val [Fact (7 < m)] (hm : m % 6 = 2) :
    (pointT1CaseIModTwo (m := m) 0 ⟨lenT1CaseIModTwo m 0, Nat.lt_succ_self _⟩).1 = m - 3 := by
  rcases eq_six_mul_add_two_of_mod_six_eq_two (m := m) hm with ⟨q, rfl⟩
  have hq : 1 ≤ q := by
    have hm7 : 7 < 6 * q + 2 := Fact.out
    omega
  let s0 : Fin (lenT1CaseIModTwo (6 * q + 2) 0 + 1) :=
    ⟨lenT1CaseIModTwo (6 * q + 2) 0, Nat.lt_succ_self _⟩
  change (pointT1CaseIModTwo (m := 6 * q + 2) 0 s0).1 = 6 * q + 2 - 3
  have hs0 : s0.1 ≠ 0 := by
    change lenT1CaseIModTwo (6 * q + 2) 0 ≠ 0
    rw [lenT1CaseIModTwo_zero_eq (q := q)]
    omega
  rw [pointT1CaseIModTwo_zero_val (m := 6 * q + 2) (s := s0), if_neg hs0]
  change 3 * lenT1CaseIModTwo (6 * q + 2) 0 - 1 = 6 * q + 2 - 3
  rw [lenT1CaseIModTwo_zero_eq (q := q)]
  omega

theorem pointT1CaseIModTwo_last_one_val [Fact (7 < m)] (hm : m % 6 = 2) :
    (pointT1CaseIModTwo (m := m) 1 ⟨lenT1CaseIModTwo m 1, Nat.lt_succ_self _⟩).1 = m - 1 := by
  rcases eq_six_mul_add_two_of_mod_six_eq_two (m := m) hm with ⟨q, rfl⟩
  let s1 : Fin (lenT1CaseIModTwo (6 * q + 2) 1 + 1) :=
    ⟨lenT1CaseIModTwo (6 * q + 2) 1, Nat.lt_succ_self _⟩
  change (pointT1CaseIModTwo (m := 6 * q + 2) 1 s1).1 = 6 * q + 2 - 1
  rw [pointT1CaseIModTwo_one_val (m := 6 * q + 2) (s := s1)]
  change 3 * lenT1CaseIModTwo (6 * q + 2) 1 + 1 = 6 * q + 2 - 1
  rw [lenT1CaseIModTwo_one_eq (q := q)]
  omega

theorem pointT1CaseIModTwo_last_two_val [Fact (7 < m)] (hm : m % 6 = 2) :
    (pointT1CaseIModTwo (m := m) 2 ⟨lenT1CaseIModTwo m 2, Nat.lt_succ_self _⟩).1 = m - 2 := by
  rcases eq_six_mul_add_two_of_mod_six_eq_two (m := m) hm with ⟨q, rfl⟩
  have hq : 1 ≤ q := by
    have hm7 : 7 < 6 * q + 2 := Fact.out
    omega
  let s2 : Fin (lenT1CaseIModTwo (6 * q + 2) 2 + 1) :=
    ⟨lenT1CaseIModTwo (6 * q + 2) 2, Nat.lt_succ_self _⟩
  change (pointT1CaseIModTwo (m := 6 * q + 2) 2 s2).1 = 6 * q + 2 - 2
  rw [pointT1CaseIModTwo_two_val (m := 6 * q + 2) (s := s2)]
  change 3 * lenT1CaseIModTwo (6 * q + 2) 2 + 3 = 6 * q + 2 - 2
  rw [lenT1CaseIModTwo_two_eq (q := q)]
  have hcalc : 3 * (2 * q - 1) + 3 = 6 * q := by omega
  rw [hcalc]
  omega

theorem T1CaseI_eq_one_of_val_eq_m_sub_three [Fact (5 < m)] {x : Fin m} (hx : x.1 = m - 3) :
    (T1CaseI (m := m) x).1 = 1 := by
  rcases x with ⟨x, hxlt⟩
  simp only at hx
  subst x
  have hm30 : m - 3 ≠ 0 := by
    have hm5 : 5 < m := Fact.out
    omega
  have hm32 : m - 3 ≠ m - 2 := by omega
  have hm31 : m - 3 ≠ m - 1 := by omega
  simp [T1CaseI, hm30, hm32, hm31]

theorem T1CaseI_eq_three_of_val_eq_m_sub_one [Fact (5 < m)] {x : Fin m} (hx : x.1 = m - 1) :
    (T1CaseI (m := m) x).1 = 3 := by
  rcases x with ⟨x, hxlt⟩
  simp only at hx
  subst x
  have hm10 : m - 1 ≠ 0 := by
    have hm5 : 5 < m := Fact.out
    omega
  have hm13 : m - 1 ≠ m - 3 := by omega
  have hm12 : m - 1 ≠ m - 2 := by omega
  simp [T1CaseI, hm10, hm13, hm12]

theorem T1CaseI_eq_zero_of_val_eq_m_sub_two [Fact (5 < m)] {x : Fin m} (hx : x.1 = m - 2) :
    (T1CaseI (m := m) x).1 = 0 := by
  rcases x with ⟨x, hxlt⟩
  simp only at hx
  subst x
  have hm20 : m - 2 ≠ 0 := by
    have hm5 : 5 < m := Fact.out
    omega
  have hm23 : m - 2 ≠ m - 3 := by omega
  simp [T1CaseI, hm20, hm23]

theorem pointT1CaseIModTwoSigma_injective [Fact (7 < m)] :
    Function.Injective (pointT1CaseIModTwoSigma (m := m)) := by
  rintro ⟨j, s⟩ ⟨j', s'⟩ h
  have hv :
      (pointT1CaseIModTwo (m := m) j s).1 = (pointT1CaseIModTwo (m := m) j' s').1 :=
    congrArg Fin.val h
  fin_cases j <;> fin_cases j'
  · by_cases hs0 : s.1 = 0
    · by_cases hs'0 : s'.1 = 0
      · have hsEq : s = 0 := Fin.ext hs0
        have hs'Eq : s' = 0 := Fin.ext hs'0
        subst hsEq; subst hs'Eq
        rfl
      · have hsEq : s = 0 := Fin.ext hs0
        subst hsEq
        have hv' : 0 = 3 * s'.1 - 1 := by
          simpa [pointT1CaseIModTwo_zero_val, hs'0] using hv
        omega
    · by_cases hs'0 : s'.1 = 0
      · have hs'Eq : s' = 0 := Fin.ext hs'0
        subst hs'Eq
        have hv' : 3 * s.1 - 1 = 0 := by
          simpa [pointT1CaseIModTwo_zero_val, hs0] using hv
        omega
      · have hv : 3 * s.1 - 1 = 3 * s'.1 - 1 := by
          simpa [pointT1CaseIModTwo_zero_val, hs0, hs'0] using hv
        have hsval : s.1 = s'.1 := by omega
        have hfin : s = s' := Fin.ext hsval
        cases hfin
        rfl
  · by_cases hs0 : s.1 = 0
    · have hsEq : s = 0 := Fin.ext hs0
      subst hsEq
      have hv' : 0 = 3 * s'.1 + 1 := by
        simpa [pointT1CaseIModTwo_zero_val, pointT1CaseIModTwo_one_val] using hv
      omega
    · have hsPos : 0 < s.1 := Nat.pos_of_ne_zero hs0
      have hv' : 3 * s.1 - 1 = 3 * s'.1 + 1 := by
        simpa [pointT1CaseIModTwo_zero_val, hs0, pointT1CaseIModTwo_one_val] using hv
      omega
  · by_cases hs0 : s.1 = 0
    · have hsEq : s = 0 := Fin.ext hs0
      subst hsEq
      have hv' : 0 = 3 * s'.1 + 3 := by
        simpa [pointT1CaseIModTwo_zero_val, pointT1CaseIModTwo_two_val] using hv
      omega
    · have hv : 3 * s.1 - 1 = 3 * s'.1 + 3 := by
        simpa [pointT1CaseIModTwo_zero_val, hs0, pointT1CaseIModTwo_two_val] using hv
      omega
  · have hv' : 3 * s.1 + 1 = if s'.1 = 0 then 0 else 3 * s'.1 - 1 := by
      simpa [pointT1CaseIModTwo_one_val, pointT1CaseIModTwo_zero_val] using hv
    by_cases hs'0 : s'.1 = 0
    · rw [if_pos hs'0] at hv'
      omega
    · rw [if_neg hs'0] at hv'
      omega
  · have hv : 3 * s.1 + 1 = 3 * s'.1 + 1 := by
      simpa [pointT1CaseIModTwo_one_val] using hv
    have hsval : s.1 = s'.1 := by omega
    have hfin : s = s' := Fin.ext hsval
    cases hfin
    rfl
  · have hv : 3 * s.1 + 1 = 3 * s'.1 + 3 := by
      simpa [pointT1CaseIModTwo_one_val, pointT1CaseIModTwo_two_val] using hv
    omega
  · have hv' : 3 * s.1 + 3 = if s'.1 = 0 then 0 else 3 * s'.1 - 1 := by
      simpa [pointT1CaseIModTwo_two_val, pointT1CaseIModTwo_zero_val] using hv
    by_cases hs'0 : s'.1 = 0
    · rw [if_pos hs'0] at hv'
      omega
    · rw [if_neg hs'0] at hv'
      omega
  · have hv : 3 * s.1 + 3 = 3 * s'.1 + 1 := by
      simpa [pointT1CaseIModTwo_two_val, pointT1CaseIModTwo_one_val] using hv
    omega
  · have hv : 3 * s.1 + 3 = 3 * s'.1 + 3 := by
      simpa [pointT1CaseIModTwo_two_val] using hv
    have hsval : s.1 = s'.1 := by omega
    have hfin : s = s' := Fin.ext hsval
    cases hfin
    rfl

theorem index_pointT1CaseIModTwo [Fact (7 < m)] (hm : m % 6 = 2) :
    ∀ p : SplicePoint (lenT1CaseIModTwo m),
      indexT1CaseIModTwo (m := m) hm (pointT1CaseIModTwoSigma (m := m) p) = p := by
  rcases eq_six_mul_add_two_of_mod_six_eq_two (m := m) hm with ⟨q, rfl⟩
  rintro ⟨j, s⟩
  fin_cases j
  · by_cases hs0 : s.1 = 0
    · have hsEq : s = 0 := Fin.ext hs0
      subst hsEq
      simp [indexT1CaseIModTwo, pointT1CaseIModTwoSigma, pointT1CaseIModTwo,
        lenT1CaseIModTwo]
      all_goals first | rfl | (apply Sigma.ext <;> simp)
    · have hsPos : 0 < s.1 := Nat.pos_of_ne_zero hs0
      have hx0 : 3 * s.1 - 1 ≠ 0 := by omega
      have hmod1 : (3 * s.1 - 1) % 3 ≠ 1 := by omega
      have hmod2 : (3 * s.1 - 1) % 3 = 2 := by omega
      let sIdx : Fin (lenT1CaseIModTwo (6 * q + 2) 0 + 1) :=
        ⟨((3 * s.1 - 1 + 1) / 3) % (lenT1CaseIModTwo (6 * q + 2) 0 + 1),
          Nat.mod_lt _ (Nat.succ_pos _)⟩
      have hdiv : (3 * s.1 - 1 + 1) / 3 = s.1 := by
        omega
      have hsIdx :
          sIdx = s := by
        apply Fin.ext
        change ((3 * s.1 - 1 + 1) / 3) % (lenT1CaseIModTwo (6 * q + 2) 0 + 1) = s.1
        have hlt : ((3 * s.1 - 1 + 1) / 3) < lenT1CaseIModTwo (6 * q + 2) 0 + 1 := by
          simpa [hdiv] using s.2
        rw [Nat.mod_eq_of_lt hlt]
        simpa [hdiv]
      simp [indexT1CaseIModTwo, pointT1CaseIModTwoSigma, pointT1CaseIModTwo,
        lenT1CaseIModTwo, hs0, hx0, hmod1, hmod2]
      exact congrArg (fun t => (⟨0, t⟩ : SplicePoint (lenT1CaseIModTwo (6 * q + 2)))) hsIdx
  · have hx0 : 3 * s.1 + 1 ≠ 0 := by omega
    have hmod1 : (3 * s.1 + 1) % 3 = 1 := by omega
    let sIdx : Fin (lenT1CaseIModTwo (6 * q + 2) 1 + 1) :=
      ⟨((3 * s.1 + 1 - 1) / 3) % (lenT1CaseIModTwo (6 * q + 2) 1 + 1),
        Nat.mod_lt _ (Nat.succ_pos _)⟩
    have hdiv : (3 * s.1 + 1 - 1) / 3 = s.1 := by
      omega
    have hsIdx :
        sIdx = s := by
      apply Fin.ext
      change ((3 * s.1 + 1 - 1) / 3) % (lenT1CaseIModTwo (6 * q + 2) 1 + 1) = s.1
      have hlt : ((3 * s.1 + 1 - 1) / 3) < lenT1CaseIModTwo (6 * q + 2) 1 + 1 := by
        simpa [hdiv] using s.2
      rw [Nat.mod_eq_of_lt hlt]
      simpa [hdiv]
    have hsMod :
        (⟨s.1 % (lenT1CaseIModTwo (6 * q + 2) 1 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩ :
          Fin (lenT1CaseIModTwo (6 * q + 2) 1 + 1)) = s := by
      have hsLt : s.1 < lenT1CaseIModTwo (6 * q + 2) 1 + 1 := by
        simpa using s.2
      apply Fin.ext
      change s.1 % (lenT1CaseIModTwo (6 * q + 2) 1 + 1) = s.1
      rw [Nat.mod_eq_of_lt hsLt]
    have hsPair :
        ((⟨(1 : Fin 3),
            (⟨s.1 % (lenT1CaseIModTwo (6 * q + 2) 1 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩ :
              Fin (lenT1CaseIModTwo (6 * q + 2) 1 + 1))⟩ :
            SplicePoint (lenT1CaseIModTwo (6 * q + 2))) = ⟨1, s⟩) :=
      congrArg
        (fun t => ((⟨(1 : Fin 3), t⟩ : SplicePoint (lenT1CaseIModTwo (6 * q + 2)))))
        hsMod
    simp [indexT1CaseIModTwo, pointT1CaseIModTwoSigma, pointT1CaseIModTwo,
      lenT1CaseIModTwo, hx0, hmod1, sIdx, hsIdx, hdiv]
    exact hsPair
  · have hx0 : 3 * s.1 + 3 ≠ 0 := by omega
    have hmod1 : (3 * s.1 + 3) % 3 ≠ 1 := by omega
    have hmod2 : (3 * s.1 + 3) % 3 ≠ 2 := by omega
    let sIdx : Fin (lenT1CaseIModTwo (6 * q + 2) 2 + 1) :=
      ⟨((3 * s.1 + 3) / 3 - 1) % (lenT1CaseIModTwo (6 * q + 2) 2 + 1),
        Nat.mod_lt _ (Nat.succ_pos _)⟩
    have hdiv : (3 * s.1 + 3) / 3 - 1 = s.1 := by
      omega
    have hsIdx :
        sIdx = s := by
      apply Fin.ext
      change ((3 * s.1 + 3) / 3 - 1) % (lenT1CaseIModTwo (6 * q + 2) 2 + 1) = s.1
      have hlt : ((3 * s.1 + 3) / 3 - 1) < lenT1CaseIModTwo (6 * q + 2) 2 + 1 := by
        simpa [hdiv] using s.2
      rw [Nat.mod_eq_of_lt hlt]
      simpa [hdiv]
    have hsMod :
        (⟨s.1 % (lenT1CaseIModTwo (6 * q + 2) 2 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩ :
          Fin (lenT1CaseIModTwo (6 * q + 2) 2 + 1)) = s := by
      have hsLt : s.1 < lenT1CaseIModTwo (6 * q + 2) 2 + 1 := by
        simpa using s.2
      apply Fin.ext
      change s.1 % (lenT1CaseIModTwo (6 * q + 2) 2 + 1) = s.1
      rw [Nat.mod_eq_of_lt hsLt]
    have hsPair :
        ((⟨(2 : Fin 3),
            (⟨s.1 % (lenT1CaseIModTwo (6 * q + 2) 2 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩ :
              Fin (lenT1CaseIModTwo (6 * q + 2) 2 + 1))⟩ :
            SplicePoint (lenT1CaseIModTwo (6 * q + 2))) = ⟨2, s⟩) :=
      congrArg
        (fun t => ((⟨(2 : Fin 3), t⟩ : SplicePoint (lenT1CaseIModTwo (6 * q + 2)))))
        hsMod
    simp [indexT1CaseIModTwo, pointT1CaseIModTwoSigma, pointT1CaseIModTwo,
      lenT1CaseIModTwo, hx0, hmod1, hmod2, sIdx, hsIdx, hdiv]
    exact hsPair

noncomputable def spliceEquivT1CaseIModTwo [Fact (7 < m)] (hm : m % 6 = 2) :
    SplicePoint (lenT1CaseIModTwo m) ≃ Fin m := by
  let f := pointT1CaseIModTwoSigma (m := m)
  have hinj : Function.Injective f := pointT1CaseIModTwoSigma_injective (m := m)
  have hcard : Fintype.card (SplicePoint (lenT1CaseIModTwo m)) = Fintype.card (Fin m) := by
    simpa using card_splicePoint_lenT1CaseIModTwo (m := m) hm
  exact Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩)

@[simp] theorem spliceEquivT1CaseIModTwo_apply [Fact (7 < m)] (hm : m % 6 = 2)
    (p : SplicePoint (lenT1CaseIModTwo m)) :
    spliceEquivT1CaseIModTwo (m := m) hm p = pointT1CaseIModTwoSigma (m := m) p := by
  rfl

theorem pointT1CaseIModTwo_step [Fact (5 < m)] [Fact (7 < m)] {j : Fin 3}
    (s : Fin (lenT1CaseIModTwo m j + 1)) (hs : s.1 + 1 < lenT1CaseIModTwo m j + 1) :
    T1CaseI (m := m) (pointT1CaseIModTwo (m := m) j s) =
      pointT1CaseIModTwo (m := m) j ⟨s.1 + 1, hs⟩ := by
  fin_cases j
  · by_cases hs0 : s.1 = 0
    · have hsEq : s = 0 := Fin.ext hs0
      subst hsEq
      apply Fin.ext
      simp [pointT1CaseIModTwo, T1CaseI, lenT1CaseIModTwo]
    · have hsPos : 0 < s.1 := Nat.pos_of_ne_zero hs0
      have hsLe : s.1 + 1 ≤ (m - 2) / 3 := Nat.lt_succ_iff.mp hs
      have hmul : 3 * (s.1 + 1) ≤ 3 * ((m - 2) / 3) := Nat.mul_le_mul_left 3 hsLe
      have hdiv : 3 * ((m - 2) / 3) ≤ m - 2 := Nat.mul_div_le (m - 2) 3
      have hx0 : 3 * s.1 - 1 ≠ 0 := by omega
      have hxm3 : 3 * s.1 - 1 ≠ m - 3 := by omega
      have hxm2 : 3 * s.1 - 1 ≠ m - 2 := by omega
      have hxm1 : 3 * s.1 - 1 ≠ m - 1 := by omega
      have hs1nz : s.1 + 1 ≠ 0 := by omega
      apply Fin.ext
      simp [pointT1CaseIModTwo, T1CaseI, lenT1CaseIModTwo, hs0, hs1nz, hx0, hxm3, hxm2, hxm1]
      omega
  · have hsLe : s.1 + 1 ≤ (m - 2) / 3 := Nat.lt_succ_iff.mp hs
    have hmul : 3 * (s.1 + 1) ≤ 3 * ((m - 2) / 3) := Nat.mul_le_mul_left 3 hsLe
    have hdiv : 3 * ((m - 2) / 3) ≤ m - 2 := Nat.mul_div_le (m - 2) 3
    have hx0 : 3 * s.1 + 1 ≠ 0 := by omega
    have hxm3 : 3 * s.1 + 1 ≠ m - 3 := by omega
    have hxm2 : 3 * s.1 + 1 ≠ m - 2 := by omega
    have hxm1 : 3 * s.1 + 1 ≠ m - 1 := by omega
    apply Fin.ext
    simp [pointT1CaseIModTwo, T1CaseI, lenT1CaseIModTwo, hx0, hxm3, hxm2, hxm1]
    omega
  · have hsLe : s.1 + 1 ≤ (m - 5) / 3 := Nat.lt_succ_iff.mp hs
    have hmul : 3 * (s.1 + 1) ≤ 3 * ((m - 5) / 3) := Nat.mul_le_mul_left 3 hsLe
    have hdiv : 3 * ((m - 5) / 3) ≤ m - 5 := Nat.mul_div_le (m - 5) 3
    have hx0 : 3 * s.1 + 3 ≠ 0 := by omega
    have hxm3 : 3 * s.1 + 3 ≠ m - 3 := by omega
    have hxm2 : 3 * s.1 + 3 ≠ m - 2 := by omega
    have hxm1 : 3 * s.1 + 3 ≠ m - 1 := by omega
    apply Fin.ext
    simp [pointT1CaseIModTwo, T1CaseI, lenT1CaseIModTwo, hx0, hxm3, hxm2, hxm1]
    omega

theorem pointT1CaseIModTwo_wrap [Fact (5 < m)] [Fact (7 < m)] (hm : m % 6 = 2) :
    ∀ j : Fin 3,
      T1CaseI (m := m)
        (pointT1CaseIModTwo (m := m) j ⟨lenT1CaseIModTwo m j, Nat.lt_succ_self _⟩) =
      pointT1CaseIModTwo (m := m) (nextBlock j) 0 := by
  intro j
  fin_cases j
  · change
      T1CaseI (m := m)
        (pointT1CaseIModTwo (m := m) 0 ⟨lenT1CaseIModTwo m 0, Nat.lt_succ_self _⟩) =
      pointT1CaseIModTwo (m := m) (nextBlock 0) 0
    apply Fin.ext
    have hsrc :
        (pointT1CaseIModTwo (m := m) 0 ⟨lenT1CaseIModTwo m 0, Nat.lt_succ_self _⟩).1 = m - 3 :=
      pointT1CaseIModTwo_last_zero_val (m := m) hm
    have hdst : (pointT1CaseIModTwo (m := m) (nextBlock 0) 0).1 = 1 := by
      simpa [nextBlock] using pointT1CaseIModTwo_one_zero_val (m := m)
    rw [T1CaseI_eq_one_of_val_eq_m_sub_three (m := m) hsrc, hdst]
  · change
      T1CaseI (m := m)
        (pointT1CaseIModTwo (m := m) 1 ⟨lenT1CaseIModTwo m 1, Nat.lt_succ_self _⟩) =
      pointT1CaseIModTwo (m := m) (nextBlock 1) 0
    apply Fin.ext
    have hsrc :
        (pointT1CaseIModTwo (m := m) 1 ⟨lenT1CaseIModTwo m 1, Nat.lt_succ_self _⟩).1 = m - 1 :=
      pointT1CaseIModTwo_last_one_val (m := m) hm
    have hdst : (pointT1CaseIModTwo (m := m) (nextBlock 1) 0).1 = 3 := by
      simpa [nextBlock] using pointT1CaseIModTwo_two_zero_val (m := m)
    rw [T1CaseI_eq_three_of_val_eq_m_sub_one (m := m) hsrc, hdst]
  · change
      T1CaseI (m := m)
        (pointT1CaseIModTwo (m := m) 2 ⟨lenT1CaseIModTwo m 2, Nat.lt_succ_self _⟩) =
      pointT1CaseIModTwo (m := m) (nextBlock 2) 0
    apply Fin.ext
    have hsrc :
        (pointT1CaseIModTwo (m := m) 2 ⟨lenT1CaseIModTwo m 2, Nat.lt_succ_self _⟩).1 = m - 2 :=
      pointT1CaseIModTwo_last_two_val (m := m) hm
    have hdst : (pointT1CaseIModTwo (m := m) (nextBlock 2) 0).1 = 0 := by
      simpa [nextBlock] using pointT1CaseIModTwo_zero_zero_val (m := m)
    rw [T1CaseI_eq_zero_of_val_eq_m_sub_two (m := m) hsrc, hdst]

theorem cycleOn_T1CaseIModTwo [Fact (5 < m)] [Fact (7 < m)] (hm : m % 6 = 2) :
    TorusD4.CycleOn m (T1CaseI (m := m)) ⟨0, by omega⟩ := by
  have hcycle :=
    cycleOn_of_spliceBlocks
      (len := lenT1CaseIModTwo m)
      (e := spliceEquivT1CaseIModTwo (m := m) hm)
      (T := T1CaseI (m := m))
      (hstep := by
        intro j s hs
        simpa using pointT1CaseIModTwo_step (m := m) (j := j) s hs)
      (hwrap := by
        intro j
        simpa using pointT1CaseIModTwo_wrap (m := m) hm j)
  simpa [spliceStart, spliceEquivT1CaseIModTwo, pointT1CaseIModTwoSigma,
    pointT1CaseIModTwo, lenT1CaseIModTwo] using hcycle

theorem T1CaseI_eq_add_three_of_ne_special [Fact (5 < m)] {x : Fin m}
    (hx0 : x.1 ≠ 0) (hxm3 : x.1 ≠ m - 3) (hxm2 : x.1 ≠ m - 2) (hxm1 : x.1 ≠ m - 1) :
    (T1CaseI (m := m) x).1 = x.1 + 3 := by
  simp [T1CaseI, hx0, hxm3, hxm2, hxm1]

theorem T1CaseI_eq_four_of_val_eq_one [Fact (5 < m)] {x : Fin m} (hx : x.1 = 1) :
    (T1CaseI (m := m) x).1 = 4 := by
  have hx0 : x.1 ≠ 0 := by omega
  have hxm3 : x.1 ≠ m - 3 := by
    have hm5 : 5 < m := Fact.out
    omega
  have hxm2 : x.1 ≠ m - 2 := by
    have hm5 : 5 < m := Fact.out
    omega
  have hxm1 : x.1 ≠ m - 1 := by
    have hm5 : 5 < m := Fact.out
    omega
  rw [T1CaseI_eq_add_three_of_ne_special (m := m) hx0 hxm3 hxm2 hxm1, hx]

theorem eq_six_mul_of_mod_six_eq_zero (hm : m % 6 = 0) :
    ∃ q, m = 6 * q := by
  refine ⟨m / 6, ?_⟩
  have hdiv := Nat.mod_add_div m 6
  omega

def lenT1CaseIModZero (m : ℕ) : Fin 3 → ℕ
  | ⟨0, _⟩ => m / 3
  | ⟨1, _⟩ => (m - 3) / 3
  | _ => (m - 6) / 3

def pointT1CaseIModZero [Fact (5 < m)] (j : Fin 3) :
    Fin (lenT1CaseIModZero m j + 1) → Fin m :=
  match j with
  | ⟨0, _⟩ => by
      have hm5 : 5 < m := Fact.out
      refine headThenAffinePoint m 0 2 3 (m / 3) ?_ ?_
      · omega
      · have hdiv : 3 * (m / 3) ≤ m := Nat.mul_div_le m 3
        have hpos : 0 < m / 3 := by omega
        omega
  | ⟨1, _⟩ => by
      have hm5 : 5 < m := Fact.out
      refine affineThenTailPoint m 3 3 ((m - 3) / 3) 1 ?_ ?_
      · omega
      · have hdiv : 3 * ((m - 3) / 3) ≤ m - 3 := Nat.mul_div_le (m - 3) 3
        have hpos : 0 < (m - 3) / 3 := by omega
        omega
  | ⟨_ + 2, _⟩ => by
      have hm5 : 5 < m := Fact.out
      refine affinePoint m 4 3 ((m - 6) / 3) ?_
      have hdiv : 3 * ((m - 6) / 3) ≤ m - 6 := Nat.mul_div_le (m - 6) 3
      omega

def pointT1CaseIModZeroSigma [Fact (5 < m)] :
    SplicePoint (lenT1CaseIModZero m) → Fin m
  | ⟨j, s⟩ => pointT1CaseIModZero (m := m) j s

private theorem lenT1CaseIModZero_zero_eq (q : ℕ) :
    lenT1CaseIModZero (6 * q) 0 = 2 * q := by
  have hdiv6 : 6 * q / 3 = 2 * q := by
    calc
      6 * q / 3 = (3 * (2 * q)) / 3 := by ring_nf
      _ = 2 * q := Nat.mul_div_right (2 * q) (by decide : 0 < 3)
  simp [lenT1CaseIModZero, hdiv6]

private theorem lenT1CaseIModZero_one_eq (q : ℕ) :
    lenT1CaseIModZero (6 * q) 1 = 2 * q - 1 := by
  calc
    lenT1CaseIModZero (6 * q) 1 = (6 * q - 3) / 3 := by
      simp [lenT1CaseIModZero]
    _ = (3 * (2 * q - 1)) / 3 := by
          have : 6 * q - 3 = 3 * (2 * q - 1) := by omega
          rw [this]
    _ = 2 * q - 1 := Nat.mul_div_right (2 * q - 1) (by decide : 0 < 3)

private theorem lenT1CaseIModZero_two_eq (q : ℕ) :
    lenT1CaseIModZero (6 * q) 2 = 2 * q - 2 := by
  calc
    lenT1CaseIModZero (6 * q) 2 = (6 * q - 6) / 3 := by
      simp [lenT1CaseIModZero]
    _ = (3 * (2 * q - 2)) / 3 := by
          have : 6 * q - 6 = 3 * (2 * q - 2) := by omega
          rw [this]
    _ = 2 * q - 2 := Nat.mul_div_right (2 * q - 2) (by decide : 0 < 3)

theorem card_splicePoint_lenT1CaseIModZero [Fact (5 < m)] (hm : m % 6 = 0) :
    Fintype.card (SplicePoint (lenT1CaseIModZero m)) = m := by
  rcases eq_six_mul_of_mod_six_eq_zero (m := m) hm with ⟨q, rfl⟩
  have hq : 1 ≤ q := by
    have hm5 : 5 < 6 * q := Fact.out
    omega
  have hcard :
      Fintype.card (SplicePoint (lenT1CaseIModZero (6 * q)))
        = ∑ j : Fin 3, (lenT1CaseIModZero (6 * q) j + 1) := by
    simpa [SplicePoint] using
      (Fintype.card_sigma (α := fun j : Fin 3 => Fin (lenT1CaseIModZero (6 * q) j + 1)))
  rw [hcard, Fin.sum_univ_three,
    lenT1CaseIModZero_zero_eq (q := q),
    lenT1CaseIModZero_one_eq (q := q),
    lenT1CaseIModZero_two_eq (q := q)]
  omega

theorem pointT1CaseIModZero_zero_val [Fact (5 < m)]
    (s : Fin (lenT1CaseIModZero m 0 + 1)) :
    (pointT1CaseIModZero (m := m) 0 s).1 = if s.1 = 0 then 0 else 2 + 3 * (s.1 - 1) := by
  simpa [pointT1CaseIModZero, lenT1CaseIModZero] using
    (headThenAffinePoint_val (m := m) (head := 0) (a := 2) (d := 3) (k := m / 3) (s := s))

theorem pointT1CaseIModZero_one_val [Fact (5 < m)]
    (s : Fin (lenT1CaseIModZero m 1 + 1)) :
    (pointT1CaseIModZero (m := m) 1 s).1 =
      if s.1 = lenT1CaseIModZero m 1 then 1 else 3 + 3 * s.1 := by
  simpa [pointT1CaseIModZero, lenT1CaseIModZero] using
    (affineThenTailPoint_val
      (m := m) (a := 3) (d := 3) (k := (m - 3) / 3) (tail := 1) (s := s))

theorem pointT1CaseIModZero_two_val [Fact (5 < m)]
    (s : Fin (lenT1CaseIModZero m 2 + 1)) :
    (pointT1CaseIModZero (m := m) 2 s).1 = 4 + 3 * s.1 := by
  simp [pointT1CaseIModZero, lenT1CaseIModZero]

theorem pointT1CaseIModZero_zero_zero_val [Fact (5 < m)] :
    (pointT1CaseIModZero (m := m) 0 0).1 = 0 := by
  simp [pointT1CaseIModZero, lenT1CaseIModZero, headThenAffinePoint]

theorem pointT1CaseIModZero_one_zero_val [Fact (5 < m)] :
    (pointT1CaseIModZero (m := m) 1 0).1 = 3 := by
  have hlast : (0 : ℕ) ≠ lenT1CaseIModZero m 1 := by
    change 0 ≠ (m - 3) / 3
    have hm5 : 5 < m := Fact.out
    omega
  simpa [hlast] using (pointT1CaseIModZero_one_val (m := m) (s := (0 : Fin (lenT1CaseIModZero m 1 + 1))))

theorem pointT1CaseIModZero_two_zero_val [Fact (5 < m)] :
    (pointT1CaseIModZero (m := m) 2 0).1 = 4 := by
  simp [pointT1CaseIModZero, lenT1CaseIModZero]

theorem pointT1CaseIModZero_last_zero_val [Fact (5 < m)] (hm : m % 6 = 0) :
    (pointT1CaseIModZero (m := m) 0 ⟨lenT1CaseIModZero m 0, Nat.lt_succ_self _⟩).1 = m - 1 := by
  rcases eq_six_mul_of_mod_six_eq_zero (m := m) hm with ⟨q, rfl⟩
  have hq : 1 ≤ q := by
    have hm5 : 5 < 6 * q := Fact.out
    omega
  let s0 : Fin (lenT1CaseIModZero (6 * q) 0 + 1) :=
    ⟨lenT1CaseIModZero (6 * q) 0, Nat.lt_succ_self _⟩
  change (pointT1CaseIModZero (m := 6 * q) 0 s0).1 = 6 * q - 1
  have hs0 : s0.1 ≠ 0 := by
    change lenT1CaseIModZero (6 * q) 0 ≠ 0
    rw [lenT1CaseIModZero_zero_eq (q := q)]
    omega
  rw [pointT1CaseIModZero_zero_val (m := 6 * q) (s := s0), if_neg hs0]
  change 2 + 3 * (lenT1CaseIModZero (6 * q) 0 - 1) = 6 * q - 1
  rw [lenT1CaseIModZero_zero_eq (q := q)]
  omega

theorem pointT1CaseIModZero_last_one_val [Fact (5 < m)] :
    (pointT1CaseIModZero (m := m) 1 ⟨lenT1CaseIModZero m 1, Nat.lt_succ_self _⟩).1 = 1 := by
  rw [pointT1CaseIModZero_one_val (m := m)
    (s := ⟨lenT1CaseIModZero m 1, Nat.lt_succ_self _⟩)]
  simp

theorem pointT1CaseIModZero_last_two_val [Fact (5 < m)] (hm : m % 6 = 0) :
    (pointT1CaseIModZero (m := m) 2 ⟨lenT1CaseIModZero m 2, Nat.lt_succ_self _⟩).1 = m - 2 := by
  rcases eq_six_mul_of_mod_six_eq_zero (m := m) hm with ⟨q, rfl⟩
  have hq : 1 ≤ q := by
    have hm5 : 5 < 6 * q := Fact.out
    omega
  let s2 : Fin (lenT1CaseIModZero (6 * q) 2 + 1) :=
    ⟨lenT1CaseIModZero (6 * q) 2, Nat.lt_succ_self _⟩
  change (pointT1CaseIModZero (m := 6 * q) 2 s2).1 = 6 * q - 2
  rw [pointT1CaseIModZero_two_val (m := 6 * q) (s := s2)]
  change 4 + 3 * lenT1CaseIModZero (6 * q) 2 = 6 * q - 2
  rw [lenT1CaseIModZero_two_eq (q := q)]
  omega

private theorem pointT1CaseIModZero_zero_injective [Fact (5 < m)] :
    Function.Injective (pointT1CaseIModZero (m := m) 0) := by
  intro s t h
  have hv := congrArg Fin.val h
  by_cases hs0 : s.1 = 0
  · by_cases ht0 : t.1 = 0
    · exact Fin.ext (by omega)
    · have hv' : 0 = 2 + 3 * (t.1 - 1) := by
        simpa [pointT1CaseIModZero_zero_val, hs0, ht0] using hv
      omega
  · by_cases ht0 : t.1 = 0
    · have hv' : 2 + 3 * (s.1 - 1) = 0 := by
        simpa [pointT1CaseIModZero_zero_val, hs0, ht0] using hv
      omega
    · apply Fin.ext
      have hv' : 2 + 3 * (s.1 - 1) = 2 + 3 * (t.1 - 1) := by
        simpa [pointT1CaseIModZero_zero_val, hs0, ht0] using hv
      omega

private theorem pointT1CaseIModZero_one_injective [Fact (5 < m)] :
    Function.Injective (pointT1CaseIModZero (m := m) 1) := by
  intro s t h
  have hv := congrArg Fin.val h
  by_cases hsLast : s.1 = lenT1CaseIModZero m 1
  · by_cases htLast : t.1 = lenT1CaseIModZero m 1
    · exact Fin.ext (by omega)
    · have hv' : 1 = 3 + 3 * t.1 := by
        simpa [pointT1CaseIModZero_one_val, hsLast, htLast] using hv
      omega
  · by_cases htLast : t.1 = lenT1CaseIModZero m 1
    · have hv' : 3 + 3 * s.1 = 1 := by
        simpa [pointT1CaseIModZero_one_val, hsLast, htLast] using hv
      omega
    · apply Fin.ext
      have hv' : 3 + 3 * s.1 = 3 + 3 * t.1 := by
        simpa [pointT1CaseIModZero_one_val, hsLast, htLast] using hv
      omega

private theorem pointT1CaseIModZero_two_injective [Fact (5 < m)] :
    Function.Injective (pointT1CaseIModZero (m := m) 2) := by
  intro s t h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simpa [pointT1CaseIModZero_two_val] using hv

theorem pointT1CaseIModZeroSigma_injective [Fact (5 < m)] :
    Function.Injective (pointT1CaseIModZeroSigma (m := m)) := by
  intro p p' h
  rcases p with ⟨j, s⟩
  rcases p' with ⟨j', s'⟩
  fin_cases j <;> fin_cases j'
  · have hs : s = s' := pointT1CaseIModZero_zero_injective (m := m) h
    subst hs
    rfl
  · have hv := congrArg Fin.val h
    simp [pointT1CaseIModZeroSigma] at hv
    by_cases hs0 : s.1 = 0
    · by_cases hs'Last : s'.1 = lenT1CaseIModZero m 1
      · have : (0 : ℕ) = 1 := by
          simpa [pointT1CaseIModZero_zero_val, pointT1CaseIModZero_one_val, hs0, hs'Last] using hv
        omega
      · have : (0 : ℕ) = 3 + 3 * s'.1 := by
          simpa [pointT1CaseIModZero_zero_val, pointT1CaseIModZero_one_val, hs0, hs'Last] using hv
        omega
    · by_cases hs'Last : s'.1 = lenT1CaseIModZero m 1
      · have : 2 + 3 * (s.1 - 1) = 1 := by
          simpa [pointT1CaseIModZero_zero_val, pointT1CaseIModZero_one_val, hs0, hs'Last] using hv
        omega
      · have : 2 + 3 * (s.1 - 1) = 3 + 3 * s'.1 := by
          simpa [pointT1CaseIModZero_zero_val, pointT1CaseIModZero_one_val, hs0, hs'Last] using hv
        omega
  · have hv := congrArg Fin.val h
    simp [pointT1CaseIModZeroSigma] at hv
    exfalso
    by_cases hs0 : s.1 = 0
    · have : (0 : ℕ) = 4 + 3 * s'.1 := by
        simpa [pointT1CaseIModZero_zero_val, pointT1CaseIModZero_two_val, hs0] using hv
      omega
    · have : 2 + 3 * (s.1 - 1) = 4 + 3 * s'.1 := by
        simpa [pointT1CaseIModZero_zero_val, pointT1CaseIModZero_two_val, hs0] using hv
      omega
  · have hv := congrArg Fin.val h
    simp [pointT1CaseIModZeroSigma] at hv
    by_cases hsLast : s.1 = lenT1CaseIModZero m 1
    · by_cases hs'0 : s'.1 = 0
      · have : (1 : ℕ) = 0 := by
          simpa [pointT1CaseIModZero_one_val, pointT1CaseIModZero_zero_val, hsLast, hs'0] using hv
        omega
      · have : 1 = 2 + 3 * (s'.1 - 1) := by
          simpa [pointT1CaseIModZero_one_val, pointT1CaseIModZero_zero_val, hsLast, hs'0] using hv
        omega
    · by_cases hs'0 : s'.1 = 0
      · have : 3 + 3 * s.1 = 0 := by
          simpa [pointT1CaseIModZero_one_val, pointT1CaseIModZero_zero_val, hsLast, hs'0] using hv
        omega
      · have : 3 + 3 * s.1 = 2 + 3 * (s'.1 - 1) := by
          simpa [pointT1CaseIModZero_one_val, pointT1CaseIModZero_zero_val, hsLast, hs'0] using hv
        omega
  · have hs : s = s' := pointT1CaseIModZero_one_injective (m := m) h
    subst hs
    rfl
  · have hv := congrArg Fin.val h
    simp [pointT1CaseIModZeroSigma] at hv
    exfalso
    by_cases hsLast : s.1 = lenT1CaseIModZero m 1
    · have : (1 : ℕ) = 4 + 3 * s'.1 := by
        simpa [pointT1CaseIModZero_one_val, pointT1CaseIModZero_two_val, hsLast] using hv
      omega
    · have : 3 + 3 * s.1 = 4 + 3 * s'.1 := by
        simpa [pointT1CaseIModZero_one_val, pointT1CaseIModZero_two_val, hsLast] using hv
      omega
  · have hv := congrArg Fin.val h
    simp [pointT1CaseIModZeroSigma] at hv
    exfalso
    by_cases hs'0 : s'.1 = 0
    · have : 4 + 3 * s.1 = 0 := by
        simpa [pointT1CaseIModZero_two_val, pointT1CaseIModZero_zero_val, hs'0] using hv
      omega
    · have : 4 + 3 * s.1 = 2 + 3 * (s'.1 - 1) := by
        simpa [pointT1CaseIModZero_two_val, pointT1CaseIModZero_zero_val, hs'0] using hv
      omega
  · have hv := congrArg Fin.val h
    simp [pointT1CaseIModZeroSigma] at hv
    by_cases hs'Last : s'.1 = lenT1CaseIModZero m 1
    · have : 4 + 3 * s.1 = 1 := by
        simpa [pointT1CaseIModZero_two_val, pointT1CaseIModZero_one_val, hs'Last] using hv
      omega
    · have : 4 + 3 * s.1 = 3 + 3 * s'.1 := by
        simpa [pointT1CaseIModZero_two_val, pointT1CaseIModZero_one_val, hs'Last] using hv
      omega
  · have hs : s = s' := pointT1CaseIModZero_two_injective (m := m) h
    subst hs
    rfl

noncomputable def spliceEquivT1CaseIModZero [Fact (5 < m)] (hm : m % 6 = 0) :
    SplicePoint (lenT1CaseIModZero m) ≃ Fin m := by
  let f := pointT1CaseIModZeroSigma (m := m)
  have hinj : Function.Injective f := pointT1CaseIModZeroSigma_injective (m := m)
  have hcard : Fintype.card (SplicePoint (lenT1CaseIModZero m)) = Fintype.card (Fin m) := by
    simpa using card_splicePoint_lenT1CaseIModZero (m := m) hm
  exact Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩)

@[simp] theorem spliceEquivT1CaseIModZero_apply [Fact (5 < m)] (hm : m % 6 = 0)
    (p : SplicePoint (lenT1CaseIModZero m)) :
    spliceEquivT1CaseIModZero (m := m) hm p = pointT1CaseIModZeroSigma (m := m) p := by
  rfl

private theorem three_mul_lenT1CaseIModZero_one_eq [Fact (5 < m)] (hm : m % 6 = 0) :
    3 * lenT1CaseIModZero m 1 = m - 3 := by
  rcases eq_six_mul_of_mod_six_eq_zero (m := m) hm with ⟨q, rfl⟩
  rw [lenT1CaseIModZero_one_eq (q := q)]
  omega

theorem pointT1CaseIModZero_step [Fact (5 < m)] (hm : m % 6 = 0) {j : Fin 3}
    (s : Fin (lenT1CaseIModZero m j + 1)) (hs : s.1 + 1 < lenT1CaseIModZero m j + 1) :
    T1CaseI (m := m) (pointT1CaseIModZero (m := m) j s) =
      pointT1CaseIModZero (m := m) j ⟨s.1 + 1, hs⟩ := by
  fin_cases j
  · change T1CaseI (m := m) (pointT1CaseIModZero (m := m) 0 s) =
      pointT1CaseIModZero (m := m) 0 ⟨s.1 + 1, hs⟩
    by_cases hs0 : s.1 = 0
    · have hsEq : s = 0 := Fin.ext hs0
      subst hsEq
      have hs1 : 1 < lenT1CaseIModZero m 0 + 1 := by simpa using hs
      let s1 : Fin (lenT1CaseIModZero m 0 + 1) := ⟨1, hs1⟩
      have hnext : (pointT1CaseIModZero (m := m) 0 s1).1 = 2 := by
        rw [pointT1CaseIModZero_zero_val (m := m) (s := s1)]
        simp [s1]
      apply Fin.ext
      change (T1CaseI (m := m) (pointT1CaseIModZero (m := m) 0 0)).1 =
        (pointT1CaseIModZero (m := m) 0 s1).1
      rw [show (T1CaseI (m := m) (pointT1CaseIModZero (m := m) 0 0)).1 = 2 by
          simp [pointT1CaseIModZero, lenT1CaseIModZero, T1CaseI, headThenAffinePoint], hnext]
    · have hcur : (pointT1CaseIModZero (m := m) 0 s).1 = 2 + 3 * (s.1 - 1) := by
        rw [pointT1CaseIModZero_zero_val (m := m) (s := s)]
        simp [hs0]
      have hx0 : (pointT1CaseIModZero (m := m) 0 s).1 ≠ 0 := by
        rw [hcur]
        omega
      have hxm3 : (pointT1CaseIModZero (m := m) 0 s).1 ≠ m - 3 := by
        rw [hcur]
        have hdiv : 3 * (m / 3) ≤ m := Nat.mul_div_le m 3
        omega
      have hxm2 : (pointT1CaseIModZero (m := m) 0 s).1 ≠ m - 2 := by
        rw [hcur]
        have hdiv : 3 * (m / 3) ≤ m := Nat.mul_div_le m 3
        omega
      have hxm1 : (pointT1CaseIModZero (m := m) 0 s).1 ≠ m - 1 := by
        rw [hcur]
        rcases eq_six_mul_of_mod_six_eq_zero (m := m) hm with ⟨q, rfl⟩
        have hsq : s.1 + 1 < 2 * q + 1 := by
          simpa [lenT1CaseIModZero_zero_eq (q := q)] using hs
        omega
      have hs1nz : s.1 + 1 ≠ 0 := by omega
      apply Fin.ext
      change (T1CaseI (m := m) (pointT1CaseIModZero (m := m) 0 s)).1 =
        (pointT1CaseIModZero (m := m) 0 ⟨s.1 + 1, hs⟩).1
      rw [T1CaseI_eq_add_three_of_ne_special (m := m) hx0 hxm3 hxm2 hxm1]
      rw [pointT1CaseIModZero_zero_val (m := m) (s := s),
        pointT1CaseIModZero_zero_val (m := m) (s := ⟨s.1 + 1, hs⟩)]
      simp [hs0, hs1nz]
      omega
  · change T1CaseI (m := m) (pointT1CaseIModZero (m := m) 1 s) =
      pointT1CaseIModZero (m := m) 1 ⟨s.1 + 1, hs⟩
    by_cases hsLast : s.1 + 1 = lenT1CaseIModZero m 1
    · have hsNotLast : s.1 ≠ lenT1CaseIModZero m 1 := by omega
      have hcur : (pointT1CaseIModZero (m := m) 1 s).1 = 3 + 3 * s.1 := by
        rw [pointT1CaseIModZero_one_val (m := m) (s := s)]
        simp [hsNotLast]
      have hsrc : (pointT1CaseIModZero (m := m) 1 s).1 = m - 3 := by
        rw [hcur]
        have hlen : 3 * lenT1CaseIModZero m 1 = m - 3 :=
          three_mul_lenT1CaseIModZero_one_eq (m := m) hm
        omega
      have hdst : (pointT1CaseIModZero (m := m) 1 ⟨s.1 + 1, hs⟩).1 = 1 := by
        rw [pointT1CaseIModZero_one_val (m := m) (s := ⟨s.1 + 1, hs⟩)]
        simp [hsLast]
      apply Fin.ext
      change (T1CaseI (m := m) (pointT1CaseIModZero (m := m) 1 s)).1 =
        (pointT1CaseIModZero (m := m) 1 ⟨s.1 + 1, hs⟩).1
      rw [T1CaseI_eq_one_of_val_eq_m_sub_three (m := m) hsrc, hdst]
    · have hsLe : s.1 + 1 ≤ lenT1CaseIModZero m 1 := Nat.lt_succ_iff.mp hs
      have hsNextLt : s.1 + 1 < lenT1CaseIModZero m 1 := lt_of_le_of_ne hsLe hsLast
      have hsNotLast : s.1 ≠ lenT1CaseIModZero m 1 := by omega
      have hs1NotLast : s.1 + 1 ≠ lenT1CaseIModZero m 1 := by omega
      have hcur : (pointT1CaseIModZero (m := m) 1 s).1 = 3 + 3 * s.1 := by
        rw [pointT1CaseIModZero_one_val (m := m) (s := s)]
        simp [hsNotLast]
      have hx0 : (pointT1CaseIModZero (m := m) 1 s).1 ≠ 0 := by
        rw [hcur]
        omega
      have hxm3 : (pointT1CaseIModZero (m := m) 1 s).1 ≠ m - 3 := by
        rw [hcur]
        have hlen : 3 * lenT1CaseIModZero m 1 = m - 3 :=
          three_mul_lenT1CaseIModZero_one_eq (m := m) hm
        omega
      have hxm2 : (pointT1CaseIModZero (m := m) 1 s).1 ≠ m - 2 := by
        rw [hcur]
        have hlen : 3 * lenT1CaseIModZero m 1 = m - 3 :=
          three_mul_lenT1CaseIModZero_one_eq (m := m) hm
        omega
      have hxm1 : (pointT1CaseIModZero (m := m) 1 s).1 ≠ m - 1 := by
        rw [hcur]
        have hlen : 3 * lenT1CaseIModZero m 1 = m - 3 :=
          three_mul_lenT1CaseIModZero_one_eq (m := m) hm
        omega
      apply Fin.ext
      change (T1CaseI (m := m) (pointT1CaseIModZero (m := m) 1 s)).1 =
        (pointT1CaseIModZero (m := m) 1 ⟨s.1 + 1, hs⟩).1
      rw [T1CaseI_eq_add_three_of_ne_special (m := m) hx0 hxm3 hxm2 hxm1]
      rw [pointT1CaseIModZero_one_val (m := m) (s := s),
        pointT1CaseIModZero_one_val (m := m) (s := ⟨s.1 + 1, hs⟩)]
      simp [hsNotLast, hs1NotLast]
      omega
  · change T1CaseI (m := m) (pointT1CaseIModZero (m := m) 2 s) =
      pointT1CaseIModZero (m := m) 2 ⟨s.1 + 1, hs⟩
    have hcur : (pointT1CaseIModZero (m := m) 2 s).1 = 4 + 3 * s.1 := by
      rw [pointT1CaseIModZero_two_val (m := m) (s := s)]
    have hx0 : (pointT1CaseIModZero (m := m) 2 s).1 ≠ 0 := by
      rw [hcur]
      omega
    have hxm3 : (pointT1CaseIModZero (m := m) 2 s).1 ≠ m - 3 := by
      rw [hcur]
      have hdiv : 3 * ((m - 6) / 3) ≤ m - 6 := Nat.mul_div_le (m - 6) 3
      omega
    have hxm2 : (pointT1CaseIModZero (m := m) 2 s).1 ≠ m - 2 := by
      rcases eq_six_mul_of_mod_six_eq_zero (m := m) hm with ⟨q, rfl⟩
      change 4 + 3 * s.1 ≠ 6 * q - 2
      have hsLt : s.1 < 2 * q - 2 := by
        have hsLe : s.1 + 1 ≤ lenT1CaseIModZero (6 * q) 2 := Nat.lt_succ_iff.mp hs
        have hsLt' : s.1 < lenT1CaseIModZero (6 * q) 2 := by omega
        rw [lenT1CaseIModZero_two_eq (q := q)] at hsLt'
        exact hsLt'
      omega
    have hxm1 : (pointT1CaseIModZero (m := m) 2 s).1 ≠ m - 1 := by
      rw [hcur]
      have hdiv : 3 * ((m - 6) / 3) ≤ m - 6 := Nat.mul_div_le (m - 6) 3
      omega
    apply Fin.ext
    change (T1CaseI (m := m) (pointT1CaseIModZero (m := m) 2 s)).1 =
      (pointT1CaseIModZero (m := m) 2 ⟨s.1 + 1, hs⟩).1
    rw [T1CaseI_eq_add_three_of_ne_special (m := m) hx0 hxm3 hxm2 hxm1]
    rw [pointT1CaseIModZero_two_val (m := m) (s := s),
      pointT1CaseIModZero_two_val (m := m) (s := ⟨s.1 + 1, hs⟩)]
    change 4 + 3 * s.1 + 3 = 4 + 3 * (s.1 + 1)
    omega

theorem pointT1CaseIModZero_wrap [Fact (5 < m)] (hm : m % 6 = 0) :
    ∀ j : Fin 3,
      T1CaseI (m := m)
        (pointT1CaseIModZero (m := m) j ⟨lenT1CaseIModZero m j, Nat.lt_succ_self _⟩) =
      pointT1CaseIModZero (m := m) (nextBlock j) 0 := by
  intro j
  fin_cases j
  · change
      T1CaseI (m := m)
        (pointT1CaseIModZero (m := m) 0 ⟨lenT1CaseIModZero m 0, Nat.lt_succ_self _⟩) =
      pointT1CaseIModZero (m := m) (nextBlock 0) 0
    apply Fin.ext
    change
      (T1CaseI (m := m)
        (pointT1CaseIModZero (m := m) 0 ⟨lenT1CaseIModZero m 0, Nat.lt_succ_self _⟩)).1 =
      (pointT1CaseIModZero (m := m) (nextBlock 0) 0).1
    have hsrc :
        (pointT1CaseIModZero (m := m) 0 ⟨lenT1CaseIModZero m 0, Nat.lt_succ_self _⟩).1 = m - 1 :=
      pointT1CaseIModZero_last_zero_val (m := m) hm
    have hdst : (pointT1CaseIModZero (m := m) (nextBlock 0) 0).1 = 3 := by
      simpa [nextBlock] using pointT1CaseIModZero_one_zero_val (m := m)
    rw [T1CaseI_eq_three_of_val_eq_m_sub_one (m := m) hsrc, hdst]
  · change
      T1CaseI (m := m)
        (pointT1CaseIModZero (m := m) 1 ⟨lenT1CaseIModZero m 1, Nat.lt_succ_self _⟩) =
      pointT1CaseIModZero (m := m) (nextBlock 1) 0
    apply Fin.ext
    change
      (T1CaseI (m := m)
        (pointT1CaseIModZero (m := m) 1 ⟨lenT1CaseIModZero m 1, Nat.lt_succ_self _⟩)).1 =
      (pointT1CaseIModZero (m := m) (nextBlock 1) 0).1
    have hsrc :
        (pointT1CaseIModZero (m := m) 1 ⟨lenT1CaseIModZero m 1, Nat.lt_succ_self _⟩).1 = 1 :=
      pointT1CaseIModZero_last_one_val (m := m)
    have hdst : (pointT1CaseIModZero (m := m) (nextBlock 1) 0).1 = 4 := by
      simpa [nextBlock] using pointT1CaseIModZero_two_zero_val (m := m)
    rw [T1CaseI_eq_four_of_val_eq_one (m := m) hsrc, hdst]
  · change
      T1CaseI (m := m)
        (pointT1CaseIModZero (m := m) 2 ⟨lenT1CaseIModZero m 2, Nat.lt_succ_self _⟩) =
      pointT1CaseIModZero (m := m) (nextBlock 2) 0
    apply Fin.ext
    change
      (T1CaseI (m := m)
        (pointT1CaseIModZero (m := m) 2 ⟨lenT1CaseIModZero m 2, Nat.lt_succ_self _⟩)).1 =
      (pointT1CaseIModZero (m := m) (nextBlock 2) 0).1
    have hsrc :
        (pointT1CaseIModZero (m := m) 2 ⟨lenT1CaseIModZero m 2, Nat.lt_succ_self _⟩).1 = m - 2 :=
      pointT1CaseIModZero_last_two_val (m := m) hm
    have hdst : (pointT1CaseIModZero (m := m) (nextBlock 2) 0).1 = 0 := by
      simpa [nextBlock] using pointT1CaseIModZero_zero_zero_val (m := m)
    rw [T1CaseI_eq_zero_of_val_eq_m_sub_two (m := m) hsrc, hdst]

theorem cycleOn_T1CaseIModZero [Fact (5 < m)] (hm : m % 6 = 0) :
    TorusD4.CycleOn m (T1CaseI (m := m)) ⟨0, by
      have hm5 : 5 < m := Fact.out
      omega⟩ := by
  have hcycle :=
    cycleOn_of_spliceBlocks
      (len := lenT1CaseIModZero m)
      (e := spliceEquivT1CaseIModZero (m := m) hm)
      (T := T1CaseI (m := m))
      (hstep := by
        intro j s hs
        simpa using pointT1CaseIModZero_step (m := m) hm (j := j) s hs)
      (hwrap := by
        intro j
        simpa using pointT1CaseIModZero_wrap (m := m) hm j)
  simpa [spliceStart, spliceEquivT1CaseIModZero, pointT1CaseIModZeroSigma,
    pointT1CaseIModZero, lenT1CaseIModZero] using hcycle

def T1CaseII (hm : m % 6 = 4) [Fact (9 < m)] (x : Fin m) : Fin m :=
  let hm9 : 9 < m := Fact.out
  if hx0 : x.1 = 0 then
    ⟨2, by omega⟩
  else if hx1 : x.1 = 1 then
    ⟨3, by omega⟩
  else if hx2 : x.1 = 2 then
    ⟨5, by omega⟩
  else if hxm5 : x.1 = m - 5 then
    ⟨1, by omega⟩
  else if hxm3 : x.1 = m - 3 then
    ⟨4, by omega⟩
  else if hxm2 : x.1 = m - 2 then
    ⟨0, by omega⟩
  else if hxm1 : x.1 = m - 1 then
    ⟨7, by omega⟩
  else if hodd : x.1 % 2 = 1 then
    ⟨x.1 + 6, by
      have hxLt : x.1 < m := x.2
      have hmeven : m % 2 = 0 := by omega
      omega⟩
  else
    ⟨x.1 + 2, by
      have hxLt : x.1 < m := x.2
      have hmeven : m % 2 = 0 := by omega
      have heven : x.1 % 2 = 0 := by omega
      omega⟩

theorem eq_six_mul_add_four_of_mod_six_eq_four (hm : m % 6 = 4) :
    ∃ q, m = 6 * q + 4 := by
  refine ⟨m / 6, ?_⟩
  have hdiv := Nat.mod_add_div m 6
  omega

def qCaseIIModFour (m : ℕ) : ℕ := (m - 4) / 6

private theorem qCaseIIModFour_pos [Fact (9 < m)] :
    0 < qCaseIIModFour m := by
  have hm9 : 9 < m := Fact.out
  have hmod : (m - 4) % 6 < 6 := Nat.mod_lt _ (by decide : 0 < 6)
  have hdiv := Nat.mod_add_div (m - 4) 6
  unfold qCaseIIModFour
  omega

private theorem qCaseIIModFour_eq (q : ℕ) :
    qCaseIIModFour (6 * q + 4) = q := by
  unfold qCaseIIModFour
  calc
    (6 * q + 4 - 4) / 6 = (6 * q) / 6 := by omega
    _ = q := by
      simpa [Nat.mul_comm] using Nat.mul_div_right q (by decide : 0 < 6)

def lenT1CaseIIModFour (m : ℕ) : Fin 3 → ℕ
  | ⟨0, _⟩ => qCaseIIModFour m + 2
  | ⟨1, _⟩ => 2 * qCaseIIModFour m
  | _ => 3 * qCaseIIModFour m - 1

private def pointT1CaseIIModFourZeroLeft [Fact (9 < m)] : Fin 2 → Fin m := by
  have hm9 : 9 < m := Fact.out
  refine headThenAffinePoint m 0 2 6 1 ?_ ?_
  · omega
  · omega

private def pointT1CaseIIModFourZeroRight [Fact (9 < m)] :
    Fin (qCaseIIModFour m + 1) → Fin m := by
  have hm9 : 9 < m := Fact.out
  have hq : 0 < qCaseIIModFour m := qCaseIIModFour_pos (m := m)
  have hdiv : 6 * qCaseIIModFour m ≤ m - 4 := by
    unfold qCaseIIModFour
    exact Nat.mul_div_le (m - 4) 6
  refine affineThenTailPoint m 5 6 (qCaseIIModFour m) 1 ?_ ?_
  · omega
  · omega

private def pointT1CaseIIModFourOneLeft [Fact (9 < m)] :
    Fin (qCaseIIModFour m + 1) → Fin m := by
  have hm9 : 9 < m := Fact.out
  have hdiv : 6 * qCaseIIModFour m ≤ m - 4 := by
    unfold qCaseIIModFour
    exact Nat.mul_div_le (m - 4) 6
  refine affinePoint m 3 6 (qCaseIIModFour m) ?_
  omega

private def pointT1CaseIIModFourOneRight [Fact (9 < m)] :
    Fin (qCaseIIModFour m - 1 + 1) → Fin m := by
  have hm9 : 9 < m := Fact.out
  have hq : 0 < qCaseIIModFour m := qCaseIIModFour_pos (m := m)
  have hdiv : 6 * qCaseIIModFour m ≤ m - 4 := by
    unfold qCaseIIModFour
    exact Nat.mul_div_le (m - 4) 6
  exact affinePoint m 7 6 (qCaseIIModFour m - 1) (by omega)

private def pointT1CaseIIModFourTwo [Fact (9 < m)] :
    Fin (3 * qCaseIIModFour m - 1 + 1) → Fin m := by
  have hm9 : 9 < m := Fact.out
  have hq : 0 < qCaseIIModFour m := qCaseIIModFour_pos (m := m)
  have hdiv : 6 * qCaseIIModFour m ≤ m - 4 := by
    unfold qCaseIIModFour
    exact Nat.mul_div_le (m - 4) 6
  exact affinePoint m 4 2 (3 * qCaseIIModFour m - 1) (by omega)

private def pointT1CaseIIModFourZero [Fact (9 < m)] :
    Fin (lenT1CaseIIModFour m 0 + 1) → Fin m := by
  have hlen : 1 + qCaseIIModFour m + 2 = lenT1CaseIIModFour m 0 + 1 := by
    simp [lenT1CaseIIModFour]
    omega
  exact
    castFinFun hlen
      (appendPoint (n := 1) (k := qCaseIIModFour m)
        (pointT1CaseIIModFourZeroLeft (m := m))
        (pointT1CaseIIModFourZeroRight (m := m)))

private def pointT1CaseIIModFourOne [Fact (9 < m)] :
    Fin (lenT1CaseIIModFour m 1 + 1) → Fin m := by
  have hq : 0 < qCaseIIModFour m := qCaseIIModFour_pos (m := m)
  have hq1 : 1 ≤ qCaseIIModFour m := Nat.succ_le_of_lt hq
  have hlen :
      qCaseIIModFour m + (qCaseIIModFour m - 1) + 2 =
        lenT1CaseIIModFour m (1 : Fin 3) + 1 := by
    simp [lenT1CaseIIModFour]
    omega
  exact
    castFinFun hlen
      (appendPoint (n := qCaseIIModFour m) (k := qCaseIIModFour m - 1)
        (pointT1CaseIIModFourOneLeft (m := m))
        (pointT1CaseIIModFourOneRight (m := m)))

private def pointT1CaseIIModFourThree [Fact (9 < m)] :
    Fin (lenT1CaseIIModFour m 2 + 1) → Fin m := by
  have hq : 0 < qCaseIIModFour m := qCaseIIModFour_pos (m := m)
  have hlen : 3 * qCaseIIModFour m - 1 + 1 = lenT1CaseIIModFour m 2 + 1 := by
    simp [lenT1CaseIIModFour]
  exact castFinFun hlen (pointT1CaseIIModFourTwo (m := m))

def pointT1CaseIIModFour [Fact (9 < m)] (j : Fin 3) :
    Fin (lenT1CaseIIModFour m j + 1) → Fin m :=
  match j with
  | ⟨0, _⟩ => pointT1CaseIIModFourZero (m := m)
  | ⟨1, _⟩ => pointT1CaseIIModFourOne (m := m)
  | ⟨_ + 2, _⟩ => pointT1CaseIIModFourThree (m := m)

def pointT1CaseIIModFourSigma [Fact (9 < m)] :
    SplicePoint (lenT1CaseIIModFour m) → Fin m
  | ⟨j, s⟩ => pointT1CaseIIModFour (m := m) j s

private theorem lenT1CaseIIModFour_zero_eq (q : ℕ) :
    lenT1CaseIIModFour (6 * q + 4) 0 = q + 2 := by
  simp [lenT1CaseIIModFour, qCaseIIModFour_eq]

private theorem lenT1CaseIIModFour_one_eq (q : ℕ) :
    lenT1CaseIIModFour (6 * q + 4) 1 = 2 * q := by
  simp [lenT1CaseIIModFour, qCaseIIModFour_eq]

private theorem lenT1CaseIIModFour_two_eq (q : ℕ) :
    lenT1CaseIIModFour (6 * q + 4) 2 = 3 * q - 1 := by
  simp [lenT1CaseIIModFour, qCaseIIModFour_eq]

theorem card_splicePoint_lenT1CaseIIModFour [Fact (9 < m)] (hm : m % 6 = 4) :
    Fintype.card (SplicePoint (lenT1CaseIIModFour m)) = m := by
  rcases eq_six_mul_add_four_of_mod_six_eq_four (m := m) hm with ⟨q, rfl⟩
  have hq : 1 ≤ q := by
    have hm9 : 9 < 6 * q + 4 := Fact.out
    omega
  have hcard :
      Fintype.card (SplicePoint (lenT1CaseIIModFour (6 * q + 4)))
        = ∑ j : Fin 3, (lenT1CaseIIModFour (6 * q + 4) j + 1) := by
    simpa [SplicePoint] using
      (Fintype.card_sigma (α := fun j : Fin 3 => Fin (lenT1CaseIIModFour (6 * q + 4) j + 1)))
  rw [hcard, Fin.sum_univ_three,
    lenT1CaseIIModFour_zero_eq (q := q),
    lenT1CaseIIModFour_one_eq (q := q),
    lenT1CaseIIModFour_two_eq (q := q)]
  omega

theorem T1CaseII_eq_two_of_val_eq_zero (hm : m % 6 = 4) [Fact (9 < m)] {x : Fin m}
    (hx : x.1 = 0) :
    (T1CaseII hm x).1 = 2 := by
  simp [T1CaseII, hx]

theorem T1CaseII_eq_three_of_val_eq_one (hm : m % 6 = 4) [Fact (9 < m)] {x : Fin m}
    (hx : x.1 = 1) :
    (T1CaseII hm x).1 = 3 := by
  have hx0 : x.1 ≠ 0 := by omega
  simp [T1CaseII, hx0, hx]

theorem T1CaseII_eq_five_of_val_eq_two (hm : m % 6 = 4) [Fact (9 < m)] {x : Fin m}
    (hx : x.1 = 2) :
    (T1CaseII hm x).1 = 5 := by
  have hx0 : x.1 ≠ 0 := by omega
  have hx1 : x.1 ≠ 1 := by omega
  simp [T1CaseII, hx0, hx1, hx]

theorem T1CaseII_eq_one_of_val_eq_m_sub_five (hm : m % 6 = 4) [Fact (9 < m)] {x : Fin m}
    (hx : x.1 = m - 5) :
    (T1CaseII hm x).1 = 1 := by
  have hm9 : 9 < m := Fact.out
  have hm50 : m - 5 ≠ 0 := by omega
  have hm51 : m - 5 ≠ 1 := by omega
  have hm52 : m - 5 ≠ 2 := by omega
  simpa [T1CaseII, hx, hm50, hm51, hm52]

theorem T1CaseII_eq_four_of_val_eq_m_sub_three (hm : m % 6 = 4) [Fact (9 < m)] {x : Fin m}
    (hx : x.1 = m - 3) :
    (T1CaseII hm x).1 = 4 := by
  have hm9 : 9 < m := Fact.out
  have hm30 : m - 3 ≠ 0 := by omega
  have hm31 : m - 3 ≠ 1 := by omega
  have hm32 : m - 3 ≠ 2 := by omega
  have hm35 : m - 3 ≠ m - 5 := by omega
  simpa [T1CaseII, hx, hm30, hm31, hm32, hm35]

theorem T1CaseII_eq_zero_of_val_eq_m_sub_two (hm : m % 6 = 4) [Fact (9 < m)] {x : Fin m}
    (hx : x.1 = m - 2) :
    (T1CaseII hm x).1 = 0 := by
  have hm9 : 9 < m := Fact.out
  have hm20 : m - 2 ≠ 0 := by omega
  have hm21 : m - 2 ≠ 1 := by omega
  have hm22 : m - 2 ≠ 2 := by omega
  have hm25 : m - 2 ≠ m - 5 := by omega
  have hm23 : m - 2 ≠ m - 3 := by omega
  simpa [T1CaseII, hx, hm20, hm21, hm22, hm25, hm23]

theorem T1CaseII_eq_seven_of_val_eq_m_sub_one (hm : m % 6 = 4) [Fact (9 < m)] {x : Fin m}
    (hx : x.1 = m - 1) :
    (T1CaseII hm x).1 = 7 := by
  have hm9 : 9 < m := Fact.out
  have hm10 : m - 1 ≠ 0 := by omega
  have hm11 : m - 1 ≠ 1 := by omega
  have hm12 : m - 1 ≠ 2 := by omega
  have hm15 : m - 1 ≠ m - 5 := by omega
  have hm13 : m - 1 ≠ m - 3 := by omega
  have hm12' : m - 1 ≠ m - 2 := by omega
  simpa [T1CaseII, hx, hm10, hm11, hm12, hm15, hm13, hm12']

theorem T1CaseII_eq_add_six_of_odd_ne_special (hm : m % 6 = 4) [Fact (9 < m)] {x : Fin m}
    (hx1 : x.1 ≠ 1) (hxm5 : x.1 ≠ m - 5) (hxm3 : x.1 ≠ m - 3) (hxm1 : x.1 ≠ m - 1)
    (hodd : x.1 % 2 = 1) :
    (T1CaseII hm x).1 = x.1 + 6 := by
  have hx0 : x.1 ≠ 0 := by omega
  have hx2 : x.1 ≠ 2 := by omega
  have hxm2 : x.1 ≠ m - 2 := by
    have hmeven : m % 2 = 0 := by omega
    omega
  simp [T1CaseII, hm, hx0, hx1, hx2, hxm5, hxm3, hxm2, hxm1, hodd]

theorem T1CaseII_eq_add_two_of_even_ne_special (hm : m % 6 = 4) [Fact (9 < m)] {x : Fin m}
    (hx0 : x.1 ≠ 0) (hx2 : x.1 ≠ 2) (hxm2 : x.1 ≠ m - 2) (heven : x.1 % 2 = 0) :
    (T1CaseII hm x).1 = x.1 + 2 := by
  have hx1 : x.1 ≠ 1 := by omega
  have hxm5 : x.1 ≠ m - 5 := by
    have hmeven : m % 2 = 0 := by omega
    omega
  have hxm3 : x.1 ≠ m - 3 := by
    have hmeven : m % 2 = 0 := by omega
    omega
  have hxm1 : x.1 ≠ m - 1 := by
    have hmeven : m % 2 = 0 := by omega
    omega
  have hodd : x.1 % 2 ≠ 1 := by omega
  simp [T1CaseII, hm, hx0, hx1, hx2, hxm5, hxm3, hxm2, hxm1, hodd]

theorem pointT1CaseIIModFourZeroLeft_val [Fact (9 < m)] (s : Fin 2) :
    (pointT1CaseIIModFourZeroLeft (m := m) s).1 = if s.1 = 0 then 0 else 2 := by
  fin_cases s
  · simp [pointT1CaseIIModFourZeroLeft]
  · simpa [pointT1CaseIIModFourZeroLeft] using
      (headThenAffinePoint_val (m := m) (head := 0) (a := 2) (d := 6) (k := 1)
        (s := (1 : Fin 2)))

theorem pointT1CaseIIModFourZeroRight_val [Fact (9 < m)]
    (s : Fin (qCaseIIModFour m + 1)) :
    (pointT1CaseIIModFourZeroRight (m := m) s).1 =
      if s.1 = qCaseIIModFour m then 1 else 5 + 6 * s.1 := by
  simpa [pointT1CaseIIModFourZeroRight] using
    (affineThenTailPoint_val
      (m := m) (a := 5) (d := 6) (k := qCaseIIModFour m) (tail := 1) (s := s))

theorem pointT1CaseIIModFourOneLeft_val [Fact (9 < m)]
    (s : Fin (qCaseIIModFour m + 1)) :
    (pointT1CaseIIModFourOneLeft (m := m) s).1 = 3 + 6 * s.1 := by
  simpa [pointT1CaseIIModFourOneLeft] using
    (affinePoint_val (m := m) (a := 3) (d := 6) (n := qCaseIIModFour m) (s := s))

theorem pointT1CaseIIModFourOneRight_val [Fact (9 < m)]
    (s : Fin (qCaseIIModFour m - 1 + 1)) :
    (pointT1CaseIIModFourOneRight (m := m) s).1 = 7 + 6 * s.1 := by
  simpa [pointT1CaseIIModFourOneRight] using
    (affinePoint_val (m := m) (a := 7) (d := 6) (n := qCaseIIModFour m - 1) (s := s))

theorem pointT1CaseIIModFourTwo_val [Fact (9 < m)]
    (s : Fin (3 * qCaseIIModFour m - 1 + 1)) :
    (pointT1CaseIIModFourTwo (m := m) s).1 = 4 + 2 * s.1 := by
  simpa [pointT1CaseIIModFourTwo] using
    (affinePoint_val (m := m) (a := 4) (d := 2) (n := 3 * qCaseIIModFour m - 1) (s := s))

private theorem pointT1CaseIIModFourZeroLeft_injective [Fact (9 < m)] :
    Function.Injective (pointT1CaseIIModFourZeroLeft (m := m)) := by
  intro s t h
  fin_cases s <;> fin_cases t
  · rfl
  · exfalso
    have hv := congrArg Fin.val h
    simp [pointT1CaseIIModFourZeroLeft_val] at hv
  · exfalso
    have hv := congrArg Fin.val h
    simp [pointT1CaseIIModFourZeroLeft_val] at hv
  · rfl

private theorem pointT1CaseIIModFourZeroRight_injective [Fact (9 < m)] :
    Function.Injective (pointT1CaseIIModFourZeroRight (m := m)) := by
  intro s t h
  have hv := congrArg Fin.val h
  by_cases hsLast : s.1 = qCaseIIModFour m
  · by_cases htLast : t.1 = qCaseIIModFour m
    · exact Fin.ext (by omega)
    · have : (1 : ℕ) = 5 + 6 * t.1 := by
        simpa [pointT1CaseIIModFourZeroRight_val, hsLast, htLast] using hv
      omega
  · by_cases htLast : t.1 = qCaseIIModFour m
    · have : 5 + 6 * s.1 = (1 : ℕ) := by
        simpa [pointT1CaseIIModFourZeroRight_val, hsLast, htLast] using hv
      omega
    · apply Fin.ext
      have : 5 + 6 * s.1 = 5 + 6 * t.1 := by
        simpa [pointT1CaseIIModFourZeroRight_val, hsLast, htLast] using hv
      omega

private theorem pointT1CaseIIModFourOneLeft_injective [Fact (9 < m)] :
    Function.Injective (pointT1CaseIIModFourOneLeft (m := m)) := by
  intro s t h
  apply Fin.ext
  have hv := congrArg Fin.val h
  have : 3 + 6 * s.1 = 3 + 6 * t.1 := by
    simpa [pointT1CaseIIModFourOneLeft_val] using hv
  omega

private theorem pointT1CaseIIModFourOneRight_injective [Fact (9 < m)] :
    Function.Injective (pointT1CaseIIModFourOneRight (m := m)) := by
  intro s t h
  apply Fin.ext
  have hv := congrArg Fin.val h
  have : 7 + 6 * s.1 = 7 + 6 * t.1 := by
    simpa [pointT1CaseIIModFourOneRight_val] using hv
  omega

private theorem pointT1CaseIIModFourTwo_injective [Fact (9 < m)] :
    Function.Injective (pointT1CaseIIModFourTwo (m := m)) := by
  intro s t h
  apply Fin.ext
  have hv := congrArg Fin.val h
  have : 4 + 2 * s.1 = 4 + 2 * t.1 := by
    simpa [pointT1CaseIIModFourTwo_val] using hv
  omega

private theorem pointT1CaseIIModFourZero_disjoint [Fact (9 < m)] :
    ∀ s t,
      pointT1CaseIIModFourZeroLeft (m := m) s ≠ pointT1CaseIIModFourZeroRight (m := m) t := by
  intro s t h
  have hv := congrArg Fin.val h
  fin_cases s
  · by_cases htLast : t.1 = qCaseIIModFour m
    · have : (0 : ℕ) = 1 := by
        simpa [pointT1CaseIIModFourZeroLeft_val, pointT1CaseIIModFourZeroRight_val, htLast] using hv
      omega
    · have : (0 : ℕ) = 5 + 6 * t.1 := by
        simpa [pointT1CaseIIModFourZeroLeft_val, pointT1CaseIIModFourZeroRight_val, htLast] using hv
      omega
  · by_cases htLast : t.1 = qCaseIIModFour m
    · have : (2 : ℕ) = 1 := by
        simpa [pointT1CaseIIModFourZeroLeft_val, pointT1CaseIIModFourZeroRight_val, htLast] using hv
      omega
    · have : (2 : ℕ) = 5 + 6 * t.1 := by
        simpa [pointT1CaseIIModFourZeroLeft_val, pointT1CaseIIModFourZeroRight_val, htLast] using hv
      omega

private theorem pointT1CaseIIModFourOne_disjoint [Fact (9 < m)] :
    ∀ s t,
      pointT1CaseIIModFourOneLeft (m := m) s ≠ pointT1CaseIIModFourOneRight (m := m) t := by
  intro s t h
  have hv := congrArg Fin.val h
  have : 3 + 6 * s.1 = 7 + 6 * t.1 := by
    simpa [pointT1CaseIIModFourOneLeft_val, pointT1CaseIIModFourOneRight_val] using hv
  omega

private theorem pointT1CaseIIModFourZero_injective [Fact (9 < m)] :
    Function.Injective (pointT1CaseIIModFourZero (m := m)) := by
  have hlen : 1 + qCaseIIModFour m + 2 = lenT1CaseIIModFour m 0 + 1 := by
    simp [lenT1CaseIIModFour]
    omega
  simpa [pointT1CaseIIModFourZero, hlen] using
    (castFinFun_injective hlen
      (appendPoint_injective
        (f := pointT1CaseIIModFourZeroLeft (m := m))
        (g := pointT1CaseIIModFourZeroRight (m := m))
        (pointT1CaseIIModFourZeroLeft_injective (m := m))
        (pointT1CaseIIModFourZeroRight_injective (m := m))
        (pointT1CaseIIModFourZero_disjoint (m := m))))

private theorem pointT1CaseIIModFourOne_injective [Fact (9 < m)] :
    Function.Injective (pointT1CaseIIModFourOne (m := m)) := by
  have hq : 0 < qCaseIIModFour m := qCaseIIModFour_pos (m := m)
  have hq1 : 1 ≤ qCaseIIModFour m := Nat.succ_le_of_lt hq
  have hlen : qCaseIIModFour m + (qCaseIIModFour m - 1) + 2 = lenT1CaseIIModFour m 1 + 1 := by
    simp [lenT1CaseIIModFour]
    omega
  simpa [pointT1CaseIIModFourOne, hlen] using
    (castFinFun_injective hlen
      (appendPoint_injective
        (f := pointT1CaseIIModFourOneLeft (m := m))
        (g := pointT1CaseIIModFourOneRight (m := m))
        (pointT1CaseIIModFourOneLeft_injective (m := m))
        (pointT1CaseIIModFourOneRight_injective (m := m))
        (pointT1CaseIIModFourOne_disjoint (m := m))))

private theorem pointT1CaseIIModFourThree_injective [Fact (9 < m)] :
    Function.Injective (pointT1CaseIIModFourThree (m := m)) := by
  have hq : 0 < qCaseIIModFour m := qCaseIIModFour_pos (m := m)
  have hlen : 3 * qCaseIIModFour m - 1 + 1 = lenT1CaseIIModFour m 2 + 1 := by
    simp [lenT1CaseIIModFour]
  simpa [pointT1CaseIIModFourThree, hlen] using
    (castFinFun_injective hlen (pointT1CaseIIModFourTwo_injective (m := m)))

private theorem pointT1CaseIIModFourZero_apply_left [Fact (9 < m)] {i : ℕ}
    (hi : i < 2) (hmem : i < lenT1CaseIIModFour m 0 + 1) :
    pointT1CaseIIModFourZero (m := m) ⟨i, hmem⟩ =
      pointT1CaseIIModFourZeroLeft (m := m) ⟨i, hi⟩ := by
  have hlen : 1 + qCaseIIModFour m + 2 = lenT1CaseIIModFour m 0 + 1 := by
    simp [lenT1CaseIIModFour]
    omega
  have hmem' : i < 1 + qCaseIIModFour m + 2 := by
    simpa [hlen] using hmem
  simpa [pointT1CaseIIModFourZero, hlen] using
    (appendPoint_apply_left
      (n := 1) (k := qCaseIIModFour m)
      (f := pointT1CaseIIModFourZeroLeft (m := m))
      (g := pointT1CaseIIModFourZeroRight (m := m))
      (i := i) hi hmem')

private theorem pointT1CaseIIModFourZero_apply_right [Fact (9 < m)] {i : ℕ}
    (hi : ¬ i < 2) (hmem : i < lenT1CaseIIModFour m 0 + 1) :
    pointT1CaseIIModFourZero (m := m) ⟨i, hmem⟩ =
      pointT1CaseIIModFourZeroRight (m := m)
        ⟨i - (1 + 1), by
          have hlen : 1 + qCaseIIModFour m + 2 = lenT1CaseIIModFour m 0 + 1 := by
            simp [lenT1CaseIIModFour]
            omega
          have hmem' : i < 1 + qCaseIIModFour m + 2 := by
            simpa [hlen] using hmem
          omega⟩ := by
  have hlen : 1 + qCaseIIModFour m + 2 = lenT1CaseIIModFour m 0 + 1 := by
    simp [lenT1CaseIIModFour]
    omega
  have hmem' : i < 1 + qCaseIIModFour m + 2 := by
    simpa [hlen] using hmem
  simpa [pointT1CaseIIModFourZero, hlen] using
    (appendPoint_apply_right
      (n := 1) (k := qCaseIIModFour m)
      (f := pointT1CaseIIModFourZeroLeft (m := m))
      (g := pointT1CaseIIModFourZeroRight (m := m))
      (i := i) hi hmem')

private theorem pointT1CaseIIModFourOne_apply_left [Fact (9 < m)] {i : ℕ}
    (hi : i < qCaseIIModFour m + 1) (hmem : i < lenT1CaseIIModFour m 1 + 1) :
    pointT1CaseIIModFourOne (m := m) ⟨i, hmem⟩ =
      pointT1CaseIIModFourOneLeft (m := m) ⟨i, hi⟩ := by
  have hq : 0 < qCaseIIModFour m := qCaseIIModFour_pos (m := m)
  have hq1 : 1 ≤ qCaseIIModFour m := Nat.succ_le_of_lt hq
  have hlen : qCaseIIModFour m + (qCaseIIModFour m - 1) + 2 = lenT1CaseIIModFour m 1 + 1 := by
    simp [lenT1CaseIIModFour]
    omega
  have hmem' : i < qCaseIIModFour m + (qCaseIIModFour m - 1) + 2 := by
    simpa [hlen] using hmem
  simpa [pointT1CaseIIModFourOne, hlen] using
    (appendPoint_apply_left
      (n := qCaseIIModFour m) (k := qCaseIIModFour m - 1)
      (f := pointT1CaseIIModFourOneLeft (m := m))
      (g := pointT1CaseIIModFourOneRight (m := m))
      (i := i) hi hmem')

private theorem pointT1CaseIIModFourOne_apply_right [Fact (9 < m)] {i : ℕ}
    (hi : ¬ i < qCaseIIModFour m + 1) (hmem : i < lenT1CaseIIModFour m 1 + 1) :
    pointT1CaseIIModFourOne (m := m) ⟨i, hmem⟩ =
      pointT1CaseIIModFourOneRight (m := m)
        ⟨i - (qCaseIIModFour m + 1),
          by
            have hq : 0 < qCaseIIModFour m := qCaseIIModFour_pos (m := m)
            have hq1 : 1 ≤ qCaseIIModFour m := Nat.succ_le_of_lt hq
            have hlen :
                qCaseIIModFour m + (qCaseIIModFour m - 1) + 2 =
                  lenT1CaseIIModFour m 1 + 1 := by
              simp [lenT1CaseIIModFour]
              omega
            have hmem' : i < qCaseIIModFour m + (qCaseIIModFour m - 1) + 2 := by
              simpa [hlen] using hmem
            omega⟩ := by
  have hq : 0 < qCaseIIModFour m := qCaseIIModFour_pos (m := m)
  have hq1 : 1 ≤ qCaseIIModFour m := Nat.succ_le_of_lt hq
  have hlen : qCaseIIModFour m + (qCaseIIModFour m - 1) + 2 = lenT1CaseIIModFour m 1 + 1 := by
    simp [lenT1CaseIIModFour]
    omega
  have hmem' : i < qCaseIIModFour m + (qCaseIIModFour m - 1) + 2 := by
    simpa [hlen] using hmem
  simpa [pointT1CaseIIModFourOne, hlen] using
    (appendPoint_apply_right
      (n := qCaseIIModFour m) (k := qCaseIIModFour m - 1)
      (f := pointT1CaseIIModFourOneLeft (m := m))
      (g := pointT1CaseIIModFourOneRight (m := m))
      (i := i) hi hmem')

private theorem pointT1CaseIIModFourThree_val [Fact (9 < m)]
    (s : Fin (lenT1CaseIIModFour m 2 + 1)) :
    (pointT1CaseIIModFourThree (m := m) s).1 = 4 + 2 * s.1 := by
  have hlen : 3 * qCaseIIModFour m - 1 + 1 = lenT1CaseIIModFour m 2 + 1 := by
    simp [lenT1CaseIIModFour]
  simpa [pointT1CaseIIModFourThree, hlen] using
    (pointT1CaseIIModFourTwo_val (m := m) (s := Fin.cast hlen.symm s))

private theorem pointT1CaseIIModFourZero_val_left [Fact (9 < m)]
    (s : Fin (lenT1CaseIIModFour m 0 + 1)) (hs : s.1 < 2) :
    (pointT1CaseIIModFourZero (m := m) s).1 = if s.1 = 0 then 0 else 2 := by
  rw [pointT1CaseIIModFourZero_apply_left (m := m) (i := s.1) hs s.2]
  simpa using pointT1CaseIIModFourZeroLeft_val (m := m) (s := ⟨s.1, hs⟩)

private theorem pointT1CaseIIModFourZero_val_right [Fact (9 < m)]
    (s : Fin (lenT1CaseIIModFour m 0 + 1)) (hs : ¬ s.1 < 2) :
    (pointT1CaseIIModFourZero (m := m) s).1 =
      if s.1 - (1 + 1) = qCaseIIModFour m then 1 else 5 + 6 * (s.1 - (1 + 1)) := by
  rw [pointT1CaseIIModFourZero_apply_right (m := m) (i := s.1) hs s.2]
  simpa using
    pointT1CaseIIModFourZeroRight_val (m := m)
      (s := ⟨s.1 - (1 + 1), by
        have hlen : 1 + qCaseIIModFour m + 2 = lenT1CaseIIModFour m 0 + 1 := by
          simp [lenT1CaseIIModFour]
          omega
        have hmem' : s.1 < 1 + qCaseIIModFour m + 2 := by
          simpa [hlen] using s.2
        omega⟩)

private theorem pointT1CaseIIModFourOne_val_left [Fact (9 < m)]
    (s : Fin (lenT1CaseIIModFour m 1 + 1)) (hs : s.1 < qCaseIIModFour m + 1) :
    (pointT1CaseIIModFourOne (m := m) s).1 = 3 + 6 * s.1 := by
  rw [pointT1CaseIIModFourOne_apply_left (m := m) (i := s.1) hs s.2]
  simpa using pointT1CaseIIModFourOneLeft_val (m := m) (s := ⟨s.1, hs⟩)

private theorem pointT1CaseIIModFourOne_val_right [Fact (9 < m)]
    (s : Fin (lenT1CaseIIModFour m 1 + 1)) (hs : ¬ s.1 < qCaseIIModFour m + 1) :
    (pointT1CaseIIModFourOne (m := m) s).1 =
      7 + 6 * (s.1 - (qCaseIIModFour m + 1)) := by
  rw [pointT1CaseIIModFourOne_apply_right (m := m) (i := s.1) hs s.2]
  simpa using
    pointT1CaseIIModFourOneRight_val (m := m)
      (s := ⟨s.1 - (qCaseIIModFour m + 1), by
        have hq : 0 < qCaseIIModFour m := qCaseIIModFour_pos (m := m)
        have hq1 : 1 ≤ qCaseIIModFour m := Nat.succ_le_of_lt hq
        have hlen : qCaseIIModFour m + (qCaseIIModFour m - 1) + 2 = lenT1CaseIIModFour m 1 + 1 := by
          simp [lenT1CaseIIModFour]
          omega
        have hmem' : s.1 < qCaseIIModFour m + (qCaseIIModFour m - 1) + 2 := by
          simpa [hlen] using s.2
        omega⟩)

private theorem six_mul_qCaseIIModFour_eq (hm : m % 6 = 4) :
    6 * qCaseIIModFour m = m - 4 := by
  rcases eq_six_mul_add_four_of_mod_six_eq_four (m := m) hm with ⟨q, rfl⟩
  simp [qCaseIIModFour_eq]

theorem pointT1CaseIIModFour_zero_zero_val [Fact (9 < m)] :
    (pointT1CaseIIModFour (m := m) 0 0).1 = 0 := by
  simpa [pointT1CaseIIModFour] using
    (pointT1CaseIIModFourZero_val_left (m := m)
      (s := (0 : Fin (lenT1CaseIIModFour m 0 + 1))) (by simp))

theorem pointT1CaseIIModFour_zero_one_val [Fact (9 < m)] :
    (pointT1CaseIIModFour (m := m) 0 1).1 = 2 := by
  let s : Fin (lenT1CaseIIModFour m 0 + 1) := ⟨1, by
    have hq : 0 < qCaseIIModFour m := qCaseIIModFour_pos (m := m)
    simp [lenT1CaseIIModFour]⟩
  have hs : s.1 < 2 := by
    simp [s]
  change (pointT1CaseIIModFourZero (m := m) s).1 = 2
  rw [pointT1CaseIIModFourZero_val_left (m := m) (s := s) hs]
  simp [s]

theorem pointT1CaseIIModFour_one_zero_val [Fact (9 < m)] :
    (pointT1CaseIIModFour (m := m) 1 0).1 = 3 := by
  have hq : 0 < qCaseIIModFour m := qCaseIIModFour_pos (m := m)
  let s : Fin (lenT1CaseIIModFour m 1 + 1) := 0
  have hs : s.1 < qCaseIIModFour m + 1 := by
    simp [s]
  change (pointT1CaseIIModFourOne (m := m) s).1 = 3
  rw [pointT1CaseIIModFourOne_val_left (m := m) (s := s) hs]
  simp [s]

theorem pointT1CaseIIModFour_three_zero_val [Fact (9 < m)] :
    (pointT1CaseIIModFour (m := m) 2 0).1 = 4 := by
  simp [pointT1CaseIIModFour, pointT1CaseIIModFourThree_val]

theorem pointT1CaseIIModFour_prelast_zero_val [Fact (9 < m)] (hm : m % 6 = 4) :
    let s : Fin (lenT1CaseIIModFour m 0 + 1) :=
      ⟨lenT1CaseIIModFour m 0 - 1, by
        have hq : 0 < qCaseIIModFour m := qCaseIIModFour_pos (m := m)
        have hq1 : 1 ≤ qCaseIIModFour m := Nat.succ_le_of_lt hq
        simp [lenT1CaseIIModFour]⟩
    (pointT1CaseIIModFour (m := m) 0 s).1 = m - 5 := by
  let s : Fin (lenT1CaseIIModFour m 0 + 1) :=
    ⟨lenT1CaseIIModFour m 0 - 1, by
      have hq : 0 < qCaseIIModFour m := qCaseIIModFour_pos (m := m)
      have hq1 : 1 ≤ qCaseIIModFour m := Nat.succ_le_of_lt hq
      simp [lenT1CaseIIModFour]⟩
  have hq : 0 < qCaseIIModFour m := qCaseIIModFour_pos (m := m)
  have hsNotLeft : ¬ s.1 < 2 := by
    simp [s, lenT1CaseIIModFour]
    have hq1 : 1 ≤ qCaseIIModFour m := Nat.succ_le_of_lt hq
    omega
  have hsNotLast : s.1 - (1 + 1) ≠ qCaseIIModFour m := by
    simp [s, lenT1CaseIIModFour]
    omega
  change (pointT1CaseIIModFourZero (m := m) s).1 = m - 5
  rw [pointT1CaseIIModFourZero_val_right (m := m) (s := s) hsNotLeft, if_neg hsNotLast]
  have hmq : 6 * qCaseIIModFour m = m - 4 := six_mul_qCaseIIModFour_eq (m := m) hm
  have : 5 + 6 * (s.1 - (1 + 1)) = m - 5 := by
    simp [s, lenT1CaseIIModFour] at *
    omega
  simpa using this

theorem pointT1CaseIIModFour_last_zero_val [Fact (9 < m)] :
    (pointT1CaseIIModFour (m := m) 0 ⟨lenT1CaseIIModFour m 0, Nat.lt_succ_self _⟩).1 = 1 := by
  let s : Fin (lenT1CaseIIModFour m 0 + 1) := ⟨lenT1CaseIIModFour m 0, Nat.lt_succ_self _⟩
  have hsNotLeft : ¬ s.1 < 2 := by
    have hq : 0 < qCaseIIModFour m := qCaseIIModFour_pos (m := m)
    simp [s, lenT1CaseIIModFour]
  have hsLast : s.1 - (1 + 1) = qCaseIIModFour m := by
    simp [s, lenT1CaseIIModFour]
  change (pointT1CaseIIModFourZero (m := m) s).1 = 1
  rw [pointT1CaseIIModFourZero_val_right (m := m) (s := s) hsNotLeft, if_pos hsLast]

theorem pointT1CaseIIModFour_boundary_one_val [Fact (9 < m)] (hm : m % 6 = 4) :
    let s : Fin (lenT1CaseIIModFour m 1 + 1) :=
      ⟨qCaseIIModFour m, by
        have hq : 0 < qCaseIIModFour m := qCaseIIModFour_pos (m := m)
        have hq1 : 1 ≤ qCaseIIModFour m := Nat.succ_le_of_lt hq
        simp [lenT1CaseIIModFour]
        omega⟩
    (pointT1CaseIIModFour (m := m) 1 s).1 = m - 1 := by
  let s : Fin (lenT1CaseIIModFour m 1 + 1) :=
    ⟨qCaseIIModFour m, by
      have hq : 0 < qCaseIIModFour m := qCaseIIModFour_pos (m := m)
      have hq1 : 1 ≤ qCaseIIModFour m := Nat.succ_le_of_lt hq
      simp [lenT1CaseIIModFour]
      omega⟩
  have hsLeft : s.1 < qCaseIIModFour m + 1 := by
    simp [s]
  change (pointT1CaseIIModFourOne (m := m) s).1 = m - 1
  rw [pointT1CaseIIModFourOne_val_left (m := m) (s := s) hsLeft]
  have hmq : 6 * qCaseIIModFour m = m - 4 := six_mul_qCaseIIModFour_eq (m := m) hm
  have : 3 + 6 * s.1 = m - 1 := by
    simp [s] at *
    omega
  simpa using this

theorem pointT1CaseIIModFour_first_right_one_val [Fact (9 < m)] :
    let s : Fin (lenT1CaseIIModFour m 1 + 1) :=
      ⟨qCaseIIModFour m + 1, by
        have hq : 0 < qCaseIIModFour m := qCaseIIModFour_pos (m := m)
        have hq1 : 1 ≤ qCaseIIModFour m := Nat.succ_le_of_lt hq
        simp [lenT1CaseIIModFour]
        omega⟩
    (pointT1CaseIIModFour (m := m) 1 s).1 = 7 := by
  let s : Fin (lenT1CaseIIModFour m 1 + 1) :=
    ⟨qCaseIIModFour m + 1, by
      have hq : 0 < qCaseIIModFour m := qCaseIIModFour_pos (m := m)
      have hq1 : 1 ≤ qCaseIIModFour m := Nat.succ_le_of_lt hq
      simp [lenT1CaseIIModFour]
      omega⟩
  have hsNotLeft : ¬ s.1 < qCaseIIModFour m + 1 := by
    simp [s]
  change (pointT1CaseIIModFourOne (m := m) s).1 = 7
  rw [pointT1CaseIIModFourOne_val_right (m := m) (s := s) hsNotLeft]
  simp [s]

theorem pointT1CaseIIModFour_last_one_val [Fact (9 < m)] (hm : m % 6 = 4) :
    (pointT1CaseIIModFour (m := m) 1 ⟨lenT1CaseIIModFour m 1, Nat.lt_succ_self _⟩).1 = m - 3 := by
  let s : Fin (lenT1CaseIIModFour m 1 + 1) := ⟨lenT1CaseIIModFour m 1, Nat.lt_succ_self _⟩
  have hq : 0 < qCaseIIModFour m := qCaseIIModFour_pos (m := m)
  have hsNotLeft : ¬ s.1 < qCaseIIModFour m + 1 := by
    simp [s, lenT1CaseIIModFour]
    omega
  change (pointT1CaseIIModFourOne (m := m) s).1 = m - 3
  rw [pointT1CaseIIModFourOne_val_right (m := m) (s := s) hsNotLeft]
  have hmq : 6 * qCaseIIModFour m = m - 4 := six_mul_qCaseIIModFour_eq (m := m) hm
  simp [s, lenT1CaseIIModFour] at *
  omega

theorem pointT1CaseIIModFour_last_three_val [Fact (9 < m)] (hm : m % 6 = 4) :
    (pointT1CaseIIModFour (m := m) 2 ⟨lenT1CaseIIModFour m 2, Nat.lt_succ_self _⟩).1 = m - 2 := by
  let s : Fin (lenT1CaseIIModFour m 2 + 1) := ⟨lenT1CaseIIModFour m 2, Nat.lt_succ_self _⟩
  change (pointT1CaseIIModFourThree (m := m) s).1 = m - 2
  rw [pointT1CaseIIModFourThree_val (m := m) (s := s)]
  have hmq : 6 * qCaseIIModFour m = m - 4 := six_mul_qCaseIIModFour_eq (m := m) hm
  have hsval : s.1 = 3 * qCaseIIModFour m - 1 := by
    simp [s, lenT1CaseIIModFour]
  have hq : 0 < qCaseIIModFour m := qCaseIIModFour_pos (m := m)
  calc
    4 + 2 * s.1 = 4 + 2 * (3 * qCaseIIModFour m - 1) := by rw [hsval]
    _ = 6 * qCaseIIModFour m + 2 := by
      have hq1 : 1 ≤ qCaseIIModFour m := Nat.succ_le_of_lt hq
      omega
    _ = m - 2 := by omega

private theorem pointT1CaseIIModFourZero_One_disjoint [Fact (9 < m)] :
    ∀ s t,
      pointT1CaseIIModFourZero (m := m) s ≠ pointT1CaseIIModFourOne (m := m) t := by
  intro s t h
  have hv := congrArg Fin.val h
  by_cases hs : s.1 < 2
  · by_cases ht : t.1 < qCaseIIModFour m + 1
    · rw [pointT1CaseIIModFourZero_val_left (m := m) (s := s) hs,
        pointT1CaseIIModFourOne_val_left (m := m) (s := t) ht] at hv
      by_cases hs0 : s.1 = 0
      · have : (0 : ℕ) = 3 + 6 * t.1 := by simpa [hs0] using hv
        omega
      · have : (2 : ℕ) = 3 + 6 * t.1 := by simpa [hs0] using hv
        omega
    · rw [pointT1CaseIIModFourZero_val_left (m := m) (s := s) hs,
        pointT1CaseIIModFourOne_val_right (m := m) (s := t) ht] at hv
      by_cases hs0 : s.1 = 0
      · have : (0 : ℕ) = 7 + 6 * (t.1 - (qCaseIIModFour m + 1)) := by simpa [hs0] using hv
        omega
      · have : (2 : ℕ) = 7 + 6 * (t.1 - (qCaseIIModFour m + 1)) := by simpa [hs0] using hv
        omega
  · by_cases ht : t.1 < qCaseIIModFour m + 1
    · rw [pointT1CaseIIModFourZero_val_right (m := m) (s := s) hs,
        pointT1CaseIIModFourOne_val_left (m := m) (s := t) ht] at hv
      by_cases hsLast : s.1 - (1 + 1) = qCaseIIModFour m
      · have : (1 : ℕ) = 3 + 6 * t.1 := by simpa [hsLast] using hv
        omega
      · have : 5 + 6 * (s.1 - (1 + 1)) = 3 + 6 * t.1 := by simpa [hsLast] using hv
        omega
    · rw [pointT1CaseIIModFourZero_val_right (m := m) (s := s) hs,
        pointT1CaseIIModFourOne_val_right (m := m) (s := t) ht] at hv
      by_cases hsLast : s.1 - (1 + 1) = qCaseIIModFour m
      · have : (1 : ℕ) = 7 + 6 * (t.1 - (qCaseIIModFour m + 1)) := by simpa [hsLast] using hv
        omega
      · have : 5 + 6 * (s.1 - (1 + 1)) = 7 + 6 * (t.1 - (qCaseIIModFour m + 1)) := by
          simpa [hsLast] using hv
        omega

private theorem pointT1CaseIIModFourZero_Three_disjoint [Fact (9 < m)] :
    ∀ s t,
      pointT1CaseIIModFourZero (m := m) s ≠ pointT1CaseIIModFourThree (m := m) t := by
  intro s t h
  have hv := congrArg Fin.val h
  by_cases hs : s.1 < 2
  · rw [pointT1CaseIIModFourZero_val_left (m := m) (s := s) hs,
      pointT1CaseIIModFourThree_val (m := m) (s := t)] at hv
    by_cases hs0 : s.1 = 0
    · have : (0 : ℕ) = 4 + 2 * t.1 := by simpa [hs0] using hv
      omega
    · have : (2 : ℕ) = 4 + 2 * t.1 := by simpa [hs0] using hv
      omega
  · rw [pointT1CaseIIModFourZero_val_right (m := m) (s := s) hs,
      pointT1CaseIIModFourThree_val (m := m) (s := t)] at hv
    by_cases hsLast : s.1 - (1 + 1) = qCaseIIModFour m
    · have : (1 : ℕ) = 4 + 2 * t.1 := by simpa [hsLast] using hv
      omega
    · have : 5 + 6 * (s.1 - (1 + 1)) = 4 + 2 * t.1 := by simpa [hsLast] using hv
      omega

private theorem pointT1CaseIIModFourOne_Three_disjoint [Fact (9 < m)] :
    ∀ s t,
      pointT1CaseIIModFourOne (m := m) s ≠ pointT1CaseIIModFourThree (m := m) t := by
  intro s t h
  have hv := congrArg Fin.val h
  by_cases hs : s.1 < qCaseIIModFour m + 1
  · rw [pointT1CaseIIModFourOne_val_left (m := m) (s := s) hs,
      pointT1CaseIIModFourThree_val (m := m) (s := t)] at hv
    have : 3 + 6 * s.1 = 4 + 2 * t.1 := hv
    omega
  · rw [pointT1CaseIIModFourOne_val_right (m := m) (s := s) hs,
      pointT1CaseIIModFourThree_val (m := m) (s := t)] at hv
    have : 7 + 6 * (s.1 - (qCaseIIModFour m + 1)) = 4 + 2 * t.1 := hv
    omega

theorem pointT1CaseIIModFourSigma_injective [Fact (9 < m)] :
    Function.Injective (pointT1CaseIIModFourSigma (m := m)) := by
  intro p p' h
  rcases p with ⟨j, s⟩
  rcases p' with ⟨j', s'⟩
  fin_cases j <;> fin_cases j'
  · have hs : s = s' := pointT1CaseIIModFourZero_injective (m := m) h
    subst hs
    rfl
  · exfalso
    exact pointT1CaseIIModFourZero_One_disjoint (m := m) s s' h
  · exfalso
    exact pointT1CaseIIModFourZero_Three_disjoint (m := m) s s' h
  · exfalso
    exact pointT1CaseIIModFourZero_One_disjoint (m := m) s' s h.symm
  · have hs : s = s' := pointT1CaseIIModFourOne_injective (m := m) h
    subst hs
    rfl
  · exfalso
    exact pointT1CaseIIModFourOne_Three_disjoint (m := m) s s' h
  · exfalso
    exact pointT1CaseIIModFourZero_Three_disjoint (m := m) s' s h.symm
  · exfalso
    exact pointT1CaseIIModFourOne_Three_disjoint (m := m) s' s h.symm
  · have hs : s = s' := pointT1CaseIIModFourThree_injective (m := m) h
    subst hs
    rfl

noncomputable def spliceEquivT1CaseIIModFour [Fact (9 < m)] (hm : m % 6 = 4) :
    SplicePoint (lenT1CaseIIModFour m) ≃ Fin m := by
  let f := pointT1CaseIIModFourSigma (m := m)
  have hinj : Function.Injective f := pointT1CaseIIModFourSigma_injective (m := m)
  have hcard : Fintype.card (SplicePoint (lenT1CaseIIModFour m)) = Fintype.card (Fin m) := by
    simpa using card_splicePoint_lenT1CaseIIModFour (m := m) hm
  exact Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩)

@[simp] theorem spliceEquivT1CaseIIModFour_apply [Fact (9 < m)] (hm : m % 6 = 4)
    (p : SplicePoint (lenT1CaseIIModFour m)) :
    spliceEquivT1CaseIIModFour (m := m) hm p = pointT1CaseIIModFourSigma (m := m) p := by
  rfl

private theorem pointT1CaseIIModFourThree_step [Fact (9 < m)] (hm : m % 6 = 4)
    (s : Fin (lenT1CaseIIModFour m 2 + 1)) (hs : s.1 + 1 < lenT1CaseIIModFour m 2 + 1) :
    T1CaseII hm (pointT1CaseIIModFour (m := m) 2 s) =
      pointT1CaseIIModFour (m := m) 2 ⟨s.1 + 1, hs⟩ := by
  have hq : 0 < qCaseIIModFour m := qCaseIIModFour_pos (m := m)
  have hq1 : 1 ≤ qCaseIIModFour m := Nat.succ_le_of_lt hq
  have hmq : 6 * qCaseIIModFour m = m - 4 := six_mul_qCaseIIModFour_eq (m := m) hm
  have hcur : (pointT1CaseIIModFour (m := m) 2 s).1 = 4 + 2 * s.1 := by
    simpa [pointT1CaseIIModFour] using pointT1CaseIIModFourThree_val (m := m) (s := s)
  have hx0 : (pointT1CaseIIModFour (m := m) 2 s).1 ≠ 0 := by
    rw [hcur]
    omega
  have hx2 : (pointT1CaseIIModFour (m := m) 2 s).1 ≠ 2 := by
    rw [hcur]
    omega
  have hxm2 : (pointT1CaseIIModFour (m := m) 2 s).1 ≠ m - 2 := by
    rw [hcur]
    have hsLt : s.1 < lenT1CaseIIModFour m 2 := by omega
    simp [lenT1CaseIIModFour] at hsLt
    omega
  have heven : (pointT1CaseIIModFour (m := m) 2 s).1 % 2 = 0 := by
    rw [hcur]
    omega
  apply Fin.ext
  change (T1CaseII hm (pointT1CaseIIModFour (m := m) 2 s)).1 =
    (pointT1CaseIIModFour (m := m) 2 ⟨s.1 + 1, hs⟩).1
  rw [T1CaseII_eq_add_two_of_even_ne_special (m := m) hm hx0 hx2 hxm2 heven]
  have hnext : (pointT1CaseIIModFour (m := m) 2 ⟨s.1 + 1, hs⟩).1 = 4 + 2 * (s.1 + 1) := by
    simpa [pointT1CaseIIModFour] using
      pointT1CaseIIModFourThree_val (m := m) (s := ⟨s.1 + 1, hs⟩)
  rw [hcur, hnext]
  omega

private theorem pointT1CaseIIModFourOne_step [Fact (9 < m)] (hm : m % 6 = 4)
    (s : Fin (lenT1CaseIIModFour m 1 + 1)) (hs : s.1 + 1 < lenT1CaseIIModFour m 1 + 1) :
    T1CaseII hm (pointT1CaseIIModFour (m := m) 1 s) =
      pointT1CaseIIModFour (m := m) 1 ⟨s.1 + 1, hs⟩ := by
  change T1CaseII hm (pointT1CaseIIModFourOne (m := m) s) =
    pointT1CaseIIModFourOne (m := m) ⟨s.1 + 1, hs⟩
  have hq : 0 < qCaseIIModFour m := qCaseIIModFour_pos (m := m)
  have hq1 : 1 ≤ qCaseIIModFour m := Nat.succ_le_of_lt hq
  have hmq : 6 * qCaseIIModFour m = m - 4 := six_mul_qCaseIIModFour_eq (m := m) hm
  by_cases hsLeft : s.1 < qCaseIIModFour m + 1
  · by_cases hsBoundary : s.1 = qCaseIIModFour m
    · have hsrc : (pointT1CaseIIModFourOne (m := m) s).1 = m - 1 := by
        rw [pointT1CaseIIModFourOne_val_left (m := m) (s := s) hsLeft]
        omega
      have hsNextNotLeft : ¬ s.1 + 1 < qCaseIIModFour m + 1 := by
        omega
      have hdst : (pointT1CaseIIModFourOne (m := m) ⟨s.1 + 1, hs⟩).1 = 7 := by
        rw [pointT1CaseIIModFourOne_val_right (m := m) (s := ⟨s.1 + 1, hs⟩) hsNextNotLeft]
        have hoff : (s.1 + 1) - (qCaseIIModFour m + 1) = 0 := by
          omega
        simp [hoff]
      apply Fin.ext
      change (T1CaseII hm (pointT1CaseIIModFourOne (m := m) s)).1 =
        (pointT1CaseIIModFourOne (m := m) ⟨s.1 + 1, hs⟩).1
      rw [T1CaseII_eq_seven_of_val_eq_m_sub_one (m := m) hm hsrc, hdst]
    · have hsStrict : s.1 < qCaseIIModFour m := by
        omega
      have hsNextLeft : s.1 + 1 < qCaseIIModFour m + 1 := by
        omega
      have hcur : (pointT1CaseIIModFourOne (m := m) s).1 = 3 + 6 * s.1 := by
        rw [pointT1CaseIIModFourOne_val_left (m := m) (s := s) hsLeft]
      have hx1 : (pointT1CaseIIModFourOne (m := m) s).1 ≠ 1 := by
        rw [hcur]
        omega
      have hxm5 : (pointT1CaseIIModFourOne (m := m) s).1 ≠ m - 5 := by
        rw [hcur]
        omega
      have hxm3 : (pointT1CaseIIModFourOne (m := m) s).1 ≠ m - 3 := by
        rw [hcur]
        omega
      have hxm1 : (pointT1CaseIIModFourOne (m := m) s).1 ≠ m - 1 := by
        rw [hcur]
        omega
      have hodd : (pointT1CaseIIModFourOne (m := m) s).1 % 2 = 1 := by
        rw [hcur]
        omega
      have hnext : (pointT1CaseIIModFourOne (m := m) ⟨s.1 + 1, hs⟩).1 = 3 + 6 * (s.1 + 1) := by
        rw [pointT1CaseIIModFourOne_val_left (m := m) (s := ⟨s.1 + 1, hs⟩) hsNextLeft]
      apply Fin.ext
      change (T1CaseII hm (pointT1CaseIIModFourOne (m := m) s)).1 =
        (pointT1CaseIIModFourOne (m := m) ⟨s.1 + 1, hs⟩).1
      rw [T1CaseII_eq_add_six_of_odd_ne_special (m := m) hm hx1 hxm5 hxm3 hxm1 hodd]
      rw [hcur, hnext]
      omega
  · have hsNotLeft : ¬ s.1 < qCaseIIModFour m + 1 := hsLeft
    have hsNextNotLeft : ¬ s.1 + 1 < qCaseIIModFour m + 1 := by
      omega
    have hcur : (pointT1CaseIIModFourOne (m := m) s).1 =
        7 + 6 * (s.1 - (qCaseIIModFour m + 1)) := by
      rw [pointT1CaseIIModFourOne_val_right (m := m) (s := s) hsNotLeft]
    have hsLt : s.1 < lenT1CaseIIModFour m 1 := by
      omega
    have hx1 : (pointT1CaseIIModFourOne (m := m) s).1 ≠ 1 := by
      rw [hcur]
      omega
    have hxm5 : (pointT1CaseIIModFourOne (m := m) s).1 ≠ m - 5 := by
      rw [hcur]
      simp [lenT1CaseIIModFour] at hsLt
      omega
    have hxm3 : (pointT1CaseIIModFourOne (m := m) s).1 ≠ m - 3 := by
      rw [hcur]
      simp [lenT1CaseIIModFour] at hsLt
      omega
    have hxm1 : (pointT1CaseIIModFourOne (m := m) s).1 ≠ m - 1 := by
      rw [hcur]
      simp [lenT1CaseIIModFour] at hsLt
      omega
    have hodd : (pointT1CaseIIModFourOne (m := m) s).1 % 2 = 1 := by
      rw [hcur]
      omega
    have hnext : (pointT1CaseIIModFourOne (m := m) ⟨s.1 + 1, hs⟩).1 =
        7 + 6 * ((s.1 + 1) - (qCaseIIModFour m + 1)) := by
      rw [pointT1CaseIIModFourOne_val_right (m := m) (s := ⟨s.1 + 1, hs⟩) hsNextNotLeft]
    apply Fin.ext
    change (T1CaseII hm (pointT1CaseIIModFourOne (m := m) s)).1 =
      (pointT1CaseIIModFourOne (m := m) ⟨s.1 + 1, hs⟩).1
    rw [T1CaseII_eq_add_six_of_odd_ne_special (m := m) hm hx1 hxm5 hxm3 hxm1 hodd]
    rw [hcur, hnext]
    omega

private theorem pointT1CaseIIModFourZero_step [Fact (9 < m)] (hm : m % 6 = 4)
    (s : Fin (lenT1CaseIIModFour m 0 + 1)) (hs : s.1 + 1 < lenT1CaseIIModFour m 0 + 1) :
    T1CaseII hm (pointT1CaseIIModFour (m := m) 0 s) =
      pointT1CaseIIModFour (m := m) 0 ⟨s.1 + 1, hs⟩ := by
  change T1CaseII hm (pointT1CaseIIModFourZero (m := m) s) =
    pointT1CaseIIModFourZero (m := m) ⟨s.1 + 1, hs⟩
  have hq : 0 < qCaseIIModFour m := qCaseIIModFour_pos (m := m)
  have hq1 : 1 ≤ qCaseIIModFour m := Nat.succ_le_of_lt hq
  have hmq : 6 * qCaseIIModFour m = m - 4 := six_mul_qCaseIIModFour_eq (m := m) hm
  by_cases hsLeft : s.1 < 2
  · have hsCases : s.1 = 0 ∨ s.1 = 1 := by
      omega
    cases hsCases with
    | inl hs0 =>
        have hsrc : (pointT1CaseIIModFourZero (m := m) s).1 = 0 := by
          rw [pointT1CaseIIModFourZero_val_left (m := m) (s := s) hsLeft]
          simp [hs0]
        have hsNextLeft : (s.1 + 1) < 2 := by
          omega
        have hdst : (pointT1CaseIIModFourZero (m := m) ⟨s.1 + 1, hs⟩).1 = 2 := by
          rw [pointT1CaseIIModFourZero_val_left (m := m) (s := ⟨s.1 + 1, hs⟩) hsNextLeft]
          simp [hs0]
        apply Fin.ext
        change (T1CaseII hm (pointT1CaseIIModFourZero (m := m) s)).1 =
          (pointT1CaseIIModFourZero (m := m) ⟨s.1 + 1, hs⟩).1
        rw [T1CaseII_eq_two_of_val_eq_zero (m := m) hm hsrc, hdst]
    | inr hs1 =>
        have hsrc : (pointT1CaseIIModFourZero (m := m) s).1 = 2 := by
          rw [pointT1CaseIIModFourZero_val_left (m := m) (s := s) hsLeft]
          simp [hs1]
        have hsNextNotLeft : ¬ s.1 + 1 < 2 := by
          omega
        have hdst : (pointT1CaseIIModFourZero (m := m) ⟨s.1 + 1, hs⟩).1 = 5 := by
          rw [pointT1CaseIIModFourZero_val_right (m := m) (s := ⟨s.1 + 1, hs⟩) hsNextNotLeft]
          have hoff : (s.1 + 1) - (1 + 1) = 0 := by
            omega
          have hneq : 0 ≠ qCaseIIModFour m := by omega
          simp [hoff, hneq]
        apply Fin.ext
        change (T1CaseII hm (pointT1CaseIIModFourZero (m := m) s)).1 =
          (pointT1CaseIIModFourZero (m := m) ⟨s.1 + 1, hs⟩).1
        rw [T1CaseII_eq_five_of_val_eq_two (m := m) hm hsrc, hdst]
  · have hsNotLeft : ¬ s.1 < 2 := hsLeft
    by_cases hsPrelast : s.1 + 1 = lenT1CaseIIModFour m 0
    · have hsNotLast : s.1 - (1 + 1) ≠ qCaseIIModFour m := by
        simp [lenT1CaseIIModFour] at hsPrelast
        omega
      have hcur : (pointT1CaseIIModFourZero (m := m) s).1 =
          5 + 6 * (s.1 - (1 + 1)) := by
        rw [pointT1CaseIIModFourZero_val_right (m := m) (s := s) hsNotLeft, if_neg hsNotLast]
      have hsrc : (pointT1CaseIIModFourZero (m := m) s).1 = m - 5 := by
        rw [hcur]
        simp [lenT1CaseIIModFour] at hsPrelast
        omega
      have hnextEq :
          (⟨s.1 + 1, hs⟩ : Fin (lenT1CaseIIModFour m 0 + 1)) =
            ⟨lenT1CaseIIModFour m 0, Nat.lt_succ_self _⟩ := by
        apply Fin.ext
        exact hsPrelast
      have hdst : (pointT1CaseIIModFourZero (m := m) ⟨s.1 + 1, hs⟩).1 = 1 := by
        rw [hnextEq]
        exact pointT1CaseIIModFour_last_zero_val (m := m)
      apply Fin.ext
      change (T1CaseII hm (pointT1CaseIIModFourZero (m := m) s)).1 =
        (pointT1CaseIIModFourZero (m := m) ⟨s.1 + 1, hs⟩).1
      rw [T1CaseII_eq_one_of_val_eq_m_sub_five (m := m) hm hsrc, hdst]
    · have hsBeforeLast : s.1 + 1 < lenT1CaseIIModFour m 0 := by
        omega
      have hsNotLast : s.1 - (1 + 1) ≠ qCaseIIModFour m := by
        simp [lenT1CaseIIModFour] at hsBeforeLast
        omega
      have hcur : (pointT1CaseIIModFourZero (m := m) s).1 =
          5 + 6 * (s.1 - (1 + 1)) := by
        rw [pointT1CaseIIModFourZero_val_right (m := m) (s := s) hsNotLeft, if_neg hsNotLast]
      have hx1 : (pointT1CaseIIModFourZero (m := m) s).1 ≠ 1 := by
        rw [hcur]
        omega
      have hxm5 : (pointT1CaseIIModFourZero (m := m) s).1 ≠ m - 5 := by
        rw [hcur]
        simp [lenT1CaseIIModFour] at hsBeforeLast
        omega
      have hxm3 : (pointT1CaseIIModFourZero (m := m) s).1 ≠ m - 3 := by
        rw [hcur]
        simp [lenT1CaseIIModFour] at hsBeforeLast
        omega
      have hxm1 : (pointT1CaseIIModFourZero (m := m) s).1 ≠ m - 1 := by
        rw [hcur]
        simp [lenT1CaseIIModFour] at hsBeforeLast
        omega
      have hodd : (pointT1CaseIIModFourZero (m := m) s).1 % 2 = 1 := by
        rw [hcur]
        omega
      have hsNextNotLeft : ¬ s.1 + 1 < 2 := by
        omega
      have hsNextNotLast : (s.1 + 1) - (1 + 1) ≠ qCaseIIModFour m := by
        simp [lenT1CaseIIModFour] at hsBeforeLast
        omega
      have hnext : (pointT1CaseIIModFourZero (m := m) ⟨s.1 + 1, hs⟩).1 =
          5 + 6 * ((s.1 + 1) - (1 + 1)) := by
        rw [pointT1CaseIIModFourZero_val_right (m := m) (s := ⟨s.1 + 1, hs⟩) hsNextNotLeft,
          if_neg hsNextNotLast]
      apply Fin.ext
      change (T1CaseII hm (pointT1CaseIIModFourZero (m := m) s)).1 =
        (pointT1CaseIIModFourZero (m := m) ⟨s.1 + 1, hs⟩).1
      rw [T1CaseII_eq_add_six_of_odd_ne_special (m := m) hm hx1 hxm5 hxm3 hxm1 hodd]
      rw [hcur, hnext]
      omega

theorem pointT1CaseIIModFour_step [Fact (9 < m)] (hm : m % 6 = 4) {j : Fin 3}
    (s : Fin (lenT1CaseIIModFour m j + 1)) (hs : s.1 + 1 < lenT1CaseIIModFour m j + 1) :
    T1CaseII hm (pointT1CaseIIModFour (m := m) j s) =
      pointT1CaseIIModFour (m := m) j ⟨s.1 + 1, hs⟩ := by
  fin_cases j
  · simpa using pointT1CaseIIModFourZero_step (m := m) hm s hs
  · simpa using pointT1CaseIIModFourOne_step (m := m) hm s hs
  · simpa using pointT1CaseIIModFourThree_step (m := m) hm s hs

theorem pointT1CaseIIModFour_wrap [Fact (9 < m)] (hm : m % 6 = 4) :
    ∀ j : Fin 3,
      T1CaseII hm
        (pointT1CaseIIModFour (m := m) j ⟨lenT1CaseIIModFour m j, Nat.lt_succ_self _⟩) =
      pointT1CaseIIModFour (m := m) (nextBlock j) 0 := by
  intro j
  fin_cases j
  · change
      T1CaseII hm
        (pointT1CaseIIModFour (m := m) 0 ⟨lenT1CaseIIModFour m 0, Nat.lt_succ_self _⟩) =
      pointT1CaseIIModFour (m := m) (nextBlock 0) 0
    apply Fin.ext
    change
      (T1CaseII hm
        (pointT1CaseIIModFour (m := m) 0 ⟨lenT1CaseIIModFour m 0, Nat.lt_succ_self _⟩)).1 =
      (pointT1CaseIIModFour (m := m) (nextBlock 0) 0).1
    have hsrc :
        (pointT1CaseIIModFour (m := m) 0 ⟨lenT1CaseIIModFour m 0, Nat.lt_succ_self _⟩).1 = 1 :=
      pointT1CaseIIModFour_last_zero_val (m := m)
    have hdst : (pointT1CaseIIModFour (m := m) (nextBlock 0) 0).1 = 3 := by
      simpa [nextBlock] using pointT1CaseIIModFour_one_zero_val (m := m)
    rw [T1CaseII_eq_three_of_val_eq_one (m := m) hm hsrc, hdst]
  · change
      T1CaseII hm
        (pointT1CaseIIModFour (m := m) 1 ⟨lenT1CaseIIModFour m 1, Nat.lt_succ_self _⟩) =
      pointT1CaseIIModFour (m := m) (nextBlock 1) 0
    apply Fin.ext
    change
      (T1CaseII hm
        (pointT1CaseIIModFour (m := m) 1 ⟨lenT1CaseIIModFour m 1, Nat.lt_succ_self _⟩)).1 =
      (pointT1CaseIIModFour (m := m) (nextBlock 1) 0).1
    have hsrc :
        (pointT1CaseIIModFour (m := m) 1 ⟨lenT1CaseIIModFour m 1, Nat.lt_succ_self _⟩).1 = m - 3 :=
      pointT1CaseIIModFour_last_one_val (m := m) hm
    have hdst : (pointT1CaseIIModFour (m := m) (nextBlock 1) 0).1 = 4 := by
      simpa [nextBlock] using pointT1CaseIIModFour_three_zero_val (m := m)
    rw [T1CaseII_eq_four_of_val_eq_m_sub_three (m := m) hm hsrc, hdst]
  · change
      T1CaseII hm
        (pointT1CaseIIModFour (m := m) 2 ⟨lenT1CaseIIModFour m 2, Nat.lt_succ_self _⟩) =
      pointT1CaseIIModFour (m := m) (nextBlock 2) 0
    apply Fin.ext
    change
      (T1CaseII hm
        (pointT1CaseIIModFour (m := m) 2 ⟨lenT1CaseIIModFour m 2, Nat.lt_succ_self _⟩)).1 =
      (pointT1CaseIIModFour (m := m) (nextBlock 2) 0).1
    have hsrc :
        (pointT1CaseIIModFour (m := m) 2 ⟨lenT1CaseIIModFour m 2, Nat.lt_succ_self _⟩).1 = m - 2 :=
      pointT1CaseIIModFour_last_three_val (m := m) hm
    have hdst : (pointT1CaseIIModFour (m := m) (nextBlock 2) 0).1 = 0 := by
      simpa [nextBlock] using pointT1CaseIIModFour_zero_zero_val (m := m)
    rw [T1CaseII_eq_zero_of_val_eq_m_sub_two (m := m) hm hsrc, hdst]

theorem cycleOn_T1CaseIIModFour [Fact (9 < m)] (hm : m % 6 = 4) :
    TorusD4.CycleOn m (T1CaseII hm) ⟨0, by
      have hm9 : 9 < m := Fact.out
      omega⟩ := by
  have hcycle :=
    cycleOn_of_spliceBlocks
      (len := lenT1CaseIIModFour m)
      (e := spliceEquivT1CaseIIModFour (m := m) hm)
      (T := T1CaseII hm)
      (hstep := by
        intro j s hs
        simpa using pointT1CaseIIModFour_step (m := m) hm (j := j) s hs)
      (hwrap := by
        intro j
        simpa using pointT1CaseIIModFour_wrap (m := m) hm j)
  simpa [spliceStart, spliceEquivT1CaseIIModFour, pointT1CaseIIModFourSigma,
    pointT1CaseIIModFour, lenT1CaseIIModFour] using hcycle

end TorusD3Even
