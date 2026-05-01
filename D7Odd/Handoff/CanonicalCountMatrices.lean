import D7Odd.Handoff.ReturnCriterion

set_option linter.style.longLine false

namespace D7Odd
namespace Handoff

abbrev CountMatrix := Fin 7 → Fin 7 → Nat

def rowSum (A : CountMatrix) (i : Fin 7) : Nat :=
  Finset.univ.sum fun j : Fin 7 => A i j

def colSum (A : CountMatrix) (j : Fin 7) : Nat :=
  Finset.univ.sum fun i : Fin 7 => A i j

def CountMatrixValid (m : Nat) (A : CountMatrix) : Prop :=
  (∀ i : Fin 7, rowSum A i = m) ∧ (∀ j : Fin 7, colSum A j = m)

def canonicalRowPrimitive (m : Nat) (row : Fin 7 → Nat) : Prop :=
  Nat.Coprime (row 0) m ∧
    ∀ k : Fin 7, 2 ≤ k.val →
      Nat.Coprime (Int.natAbs (Int.ofNat (row k) - Int.ofNat (row 1))) m

def CountMatrixPrimitive (m : Nat) (A : CountMatrix) : Prop :=
  ∀ c : Fin 7, canonicalRowPrimitive m (fun sym => A c sym)

def CountMatrixCertified (m : Nat) (A : CountMatrix) : Prop :=
  CountMatrixValid m A ∧ CountMatrixPrimitive m A

-- Symbol order: 0, Delta, 2, 3, 4, 5, 6.
def matrix7 : CountMatrix
  | 0, 0 => 1 | 0, 1 => 2 | 0, 2 => 0 | 0, 3 => 0 | 0, 4 => 0 | 0, 5 => 0 | 0, 6 => 4
  | 1, 0 => 1 | 1, 1 => 2 | 1, 2 => 0 | 1, 3 => 0 | 1, 4 => 0 | 1, 5 => 3 | 1, 6 => 1
  | 2, 0 => 1 | 2, 1 => 1 | 2, 2 => 0 | 2, 3 => 0 | 2, 4 => 3 | 2, 5 => 2 | 2, 6 => 0
  | 3, 0 => 1 | 3, 1 => 1 | 3, 2 => 0 | 3, 3 => 3 | 3, 4 => 2 | 3, 5 => 0 | 3, 6 => 0
  | 4, 0 => 1 | 4, 1 => 1 | 4, 2 => 3 | 4, 3 => 2 | 4, 4 => 0 | 4, 5 => 0 | 4, 6 => 0
  | 5, 0 => 1 | 5, 1 => 0 | 5, 2 => 2 | 5, 3 => 1 | 5, 4 => 1 | 5, 5 => 1 | 5, 6 => 1
  | 6, 0 => 1 | 6, 1 => 0 | 6, 2 => 2 | 6, 3 => 1 | 6, 4 => 1 | 6, 5 => 1 | 6, 6 => 1

def matrix6s1 (s : Nat) : CountMatrix
  | 0, 0 => 1       | 0, 1 => s + 1 | 0, 2 => s - 1 | 0, 3 => s - 1 | 0, 4 => s - 1 | 0, 5 => s - 1 | 0, 6 => s + 3
  | 1, 0 => 1       | 1, 1 => s + 1 | 1, 2 => s - 1 | 1, 3 => s - 1 | 1, 4 => s - 1 | 1, 5 => s - 1 | 1, 6 => s + 3
  | 2, 0 => 1       | 2, 1 => s + 1 | 2, 2 => s - 1 | 2, 3 => s - 1 | 2, 4 => s - 1 | 2, 5 => s + 2 | 2, 6 => s
  | 3, 0 => 1       | 3, 1 => s     | 3, 2 => s + 1 | 3, 3 => s + 1 | 3, 4 => s + 1 | 3, 5 => s - 1 | 3, 6 => s - 2
  | 4, 0 => 2       | 4, 1 => s - 1 | 4, 2 => s     | 4, 3 => s     | 4, 4 => s + 1 | 4, 5 => s + 1 | 4, 6 => s - 2
  | 5, 0 => 2       | 5, 1 => s - 1 | 5, 2 => s + 1 | 5, 3 => s + 1 | 5, 4 => s     | 5, 5 => s     | 5, 6 => s - 2
  | 6, 0 => 6*s - 7 | 6, 1 => 0     | 6, 2 => 2     | 6, 3 => 2     | 6, 4 => 2     | 6, 5 => 1     | 6, 6 => 1

def matrix6s3 (s : Nat) : CountMatrix
  | 0, 0 => 1       | 0, 1 => s + 2 | 0, 2 => s     | 0, 3 => s     | 0, 4 => s     | 0, 5 => s     | 0, 6 => s
  | 1, 0 => 1       | 1, 1 => s + 2 | 1, 2 => s     | 1, 3 => s     | 1, 4 => s     | 1, 5 => s     | 1, 6 => s
  | 2, 0 => 1       | 2, 1 => s + 2 | 2, 2 => s     | 2, 3 => s     | 2, 4 => s     | 2, 5 => s     | 2, 6 => s
  | 3, 0 => 1       | 3, 1 => s - 1 | 3, 2 => s     | 3, 3 => s     | 3, 4 => s + 1 | 3, 5 => s + 1 | 3, 6 => s + 1
  | 4, 0 => 2       | 4, 1 => s - 1 | 4, 2 => s     | 4, 3 => s     | 4, 4 => s     | 4, 5 => s + 1 | 4, 6 => s + 1
  | 5, 0 => 2       | 5, 1 => s - 1 | 5, 2 => s + 1 | 5, 3 => s + 1 | 5, 4 => s     | 5, 5 => s     | 5, 6 => s
  | 6, 0 => 6*s - 5 | 6, 1 => 0     | 6, 2 => 2     | 6, 3 => 2     | 6, 4 => 2     | 6, 5 => 1     | 6, 6 => 1

def matrix6s5 (s : Nat) : CountMatrix
  | 0, 0 => 1       | 0, 1 => s + 2 | 0, 2 => s     | 0, 3 => s     | 0, 4 => s     | 0, 5 => s + 1 | 0, 6 => s + 1
  | 1, 0 => 1       | 1, 1 => s + 2 | 1, 2 => s     | 1, 3 => s     | 1, 4 => s     | 1, 5 => s + 1 | 1, 6 => s + 1
  | 2, 0 => 1       | 2, 1 => s + 2 | 2, 2 => s     | 2, 3 => s     | 2, 4 => s     | 2, 5 => s + 1 | 2, 6 => s + 1
  | 3, 0 => 1       | 3, 1 => s     | 3, 2 => s + 1 | 3, 3 => s + 1 | 3, 4 => s + 1 | 3, 5 => s - 1 | 3, 6 => s + 2
  | 4, 0 => 2       | 4, 1 => s     | 4, 2 => s + 1 | 4, 3 => s + 1 | 4, 4 => s + 1 | 4, 5 => s + 1 | 4, 6 => s - 1
  | 5, 0 => 2       | 5, 1 => s - 1 | 5, 2 => s + 1 | 5, 3 => s + 1 | 5, 4 => s + 1 | 5, 5 => s + 1 | 5, 6 => s
  | 6, 0 => 6*s - 3 | 6, 1 => 0     | 6, 2 => 2     | 6, 3 => 2     | 6, 4 => 2     | 6, 5 => 1     | 6, 6 => 1

theorem matrix7_valid : CountMatrixValid 7 matrix7 := by
  constructor
  · intro i
    fin_cases i <;> decide
  · intro j
    fin_cases j <;> decide

theorem odd_6s1 (s : Nat) : Odd (6*s + 1) := by
  refine ⟨3*s, ?_⟩
  omega

theorem odd_6s3 (s : Nat) : Odd (6*s + 3) := by
  refine ⟨3*s + 1, ?_⟩
  omega

theorem odd_6s5 (s : Nat) : Odd (6*s + 5) := by
  refine ⟨3*s + 2, ?_⟩
  omega

theorem coprime_two_of_odd {n : Nat} (h : Odd n) : Nat.Coprime 2 n :=
  Nat.coprime_two_left.mpr h

theorem coprime_eight_of_odd {n : Nat} (h : Odd n) : Nat.Coprime n 8 := by
  rw [show 8 = 2^3 by norm_num]
  rw [Nat.coprime_pow_right_iff (by norm_num)]
  exact Nat.coprime_two_right.mpr h

theorem odd_6s1_sub8 (s : Nat) (hs : 2 ≤ s) : Odd (6*s - 7) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hs
  subst s
  refine ⟨3*k + 2, ?_⟩
  omega

theorem odd_6s3_sub8 (s : Nat) (hs : 1 ≤ s) : Odd (6*s - 5) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hs
  subst s
  refine ⟨3*k, ?_⟩
  omega

theorem odd_6s5_sub8 (s : Nat) (hs : 1 ≤ s) : Odd (6*s - 3) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hs
  subst s
  refine ⟨3*k + 1, ?_⟩
  omega

theorem coprime_6s1_sub8 (s : Nat) (hs : 2 ≤ s) :
    Nat.Coprime (6*s - 7) (6*s + 1) := by
  have hsum : 6*s + 1 = (6*s - 7) + 8 := by omega
  rw [hsum, Nat.coprime_self_add_right]
  exact coprime_eight_of_odd (odd_6s1_sub8 s hs)

theorem coprime_6s3_sub8 (s : Nat) (hs : 1 ≤ s) :
    Nat.Coprime (6*s - 5) (6*s + 3) := by
  have hsum : 6*s + 3 = (6*s - 5) + 8 := by omega
  rw [hsum, Nat.coprime_self_add_right]
  exact coprime_eight_of_odd (odd_6s3_sub8 s hs)

theorem coprime_6s5_sub8 (s : Nat) (hs : 1 ≤ s) :
    Nat.Coprime (6*s - 3) (6*s + 5) := by
  have hsum : 6*s + 5 = (6*s - 3) + 8 := by omega
  rw [hsum, Nat.coprime_self_add_right]
  exact coprime_eight_of_odd (odd_6s5_sub8 s hs)

-- The primitive proofs split finite rows/columns and simplify indexed goals in place.
set_option linter.flexible false in
theorem matrix7_primitive : CountMatrixPrimitive 7 matrix7 := by
  intro c
  fin_cases c <;> constructor
  all_goals
    first
    | intro sym hsym
      fin_cases sym <;> simp at hsym ⊢ <;> norm_num [canonicalRowPrimitive, matrix7]
    | norm_num [canonicalRowPrimitive, matrix7]

theorem matrix7_certified : CountMatrixCertified 7 matrix7 :=
  ⟨matrix7_valid, matrix7_primitive⟩

def Matrix6s1ValidTarget (s : Nat) : Prop :=
  2 ≤ s → CountMatrixValid (6*s + 1) (matrix6s1 s)

def Matrix6s3ValidTarget (s : Nat) : Prop :=
  1 ≤ s → CountMatrixValid (6*s + 3) (matrix6s3 s)

def Matrix6s5ValidTarget (s : Nat) : Prop :=
  1 ≤ s → CountMatrixValid (6*s + 5) (matrix6s5 s)

def Matrix6s1PrimitiveTarget (s : Nat) : Prop :=
  2 ≤ s → CountMatrixPrimitive (6*s + 1) (matrix6s1 s)

def Matrix6s3PrimitiveTarget (s : Nat) : Prop :=
  1 ≤ s → CountMatrixPrimitive (6*s + 3) (matrix6s3 s)

def Matrix6s5PrimitiveTarget (s : Nat) : Prop :=
  1 ≤ s → CountMatrixPrimitive (6*s + 5) (matrix6s5 s)

def Matrix6s1CertifiedTarget (s : Nat) : Prop :=
  2 ≤ s → CountMatrixCertified (6*s + 1) (matrix6s1 s)

def Matrix6s3CertifiedTarget (s : Nat) : Prop :=
  1 ≤ s → CountMatrixCertified (6*s + 3) (matrix6s3 s)

def Matrix6s5CertifiedTarget (s : Nat) : Prop :=
  1 ≤ s → CountMatrixCertified (6*s + 5) (matrix6s5 s)

theorem matrix6s1_valid (s : Nat) : Matrix6s1ValidTarget s := by
  intro hs
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hs
  subst s
  constructor
  · intro i
    fin_cases i <;> unfold rowSum <;> rw [Fin.sum_univ_seven] <;>
      norm_num [matrix6s1] <;> omega
  · intro j
    fin_cases j <;> unfold colSum <;> rw [Fin.sum_univ_seven] <;>
      norm_num [matrix6s1] <;> omega

theorem matrix6s3_valid (s : Nat) : Matrix6s3ValidTarget s := by
  intro hs
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hs
  subst s
  constructor
  · intro i
    fin_cases i <;> unfold rowSum <;> rw [Fin.sum_univ_seven] <;>
      norm_num [matrix6s3] <;> omega
  · intro j
    fin_cases j <;> unfold colSum <;> rw [Fin.sum_univ_seven] <;>
      norm_num [matrix6s3] <;> omega

theorem matrix6s5_valid (s : Nat) : Matrix6s5ValidTarget s := by
  intro hs
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hs
  subst s
  constructor
  · intro i
    fin_cases i <;> unfold rowSum <;> rw [Fin.sum_univ_seven] <;>
      norm_num [matrix6s5] <;> omega
  · intro j
    fin_cases j <;> unfold colSum <;> rw [Fin.sum_univ_seven] <;>
      norm_num [matrix6s5] <;> omega

-- The primitive proofs split finite rows/columns and simplify indexed goals in place.
set_option linter.flexible false in
theorem matrix6s1_primitive (s : Nat) : Matrix6s1PrimitiveTarget s := by
  intro hs c
  fin_cases c <;> constructor
  all_goals
    first
    | intro sym hsym
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hs
      subst s
      fin_cases sym <;> simp at hsym ⊢ <;> norm_num [canonicalRowPrimitive, matrix6s1] <;>
        try (ring_nf; norm_num; refine ⟨3*k + 6, ?_⟩; omega)
    | exact coprime_two_of_odd (odd_6s1 s)
    | exact coprime_6s1_sub8 s hs
    | norm_num [canonicalRowPrimitive, matrix6s1]

-- The primitive proofs split finite rows/columns and simplify indexed goals in place.
set_option linter.flexible false in
theorem matrix6s3_primitive (s : Nat) : Matrix6s3PrimitiveTarget s := by
  intro hs c
  fin_cases c <;> constructor
  all_goals
    first
    | intro sym hsym
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hs
      subst s
      fin_cases sym <;> simp at hsym ⊢ <;> norm_num [canonicalRowPrimitive, matrix6s3] <;>
        try (ring_nf; norm_num; refine ⟨3*k + 4, ?_⟩; omega)
    | exact coprime_two_of_odd (odd_6s3 s)
    | exact coprime_6s3_sub8 s hs
    | norm_num [canonicalRowPrimitive, matrix6s3]

-- The primitive proofs split finite rows/columns and simplify indexed goals in place.
set_option linter.flexible false in
theorem matrix6s5_primitive (s : Nat) : Matrix6s5PrimitiveTarget s := by
  intro hs c
  fin_cases c <;> constructor
  all_goals
    first
    | intro sym hsym
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hs
      subst s
      fin_cases sym <;> simp at hsym ⊢ <;> norm_num [canonicalRowPrimitive, matrix6s5] <;>
        try (ring_nf; norm_num; refine ⟨3*k + 5, ?_⟩; omega)
    | exact coprime_two_of_odd (odd_6s5 s)
    | exact coprime_6s5_sub8 s hs
    | norm_num [canonicalRowPrimitive, matrix6s5]

theorem matrix6s1_certified (s : Nat) : Matrix6s1CertifiedTarget s := by
  intro hs
  exact ⟨matrix6s1_valid s hs, matrix6s1_primitive s hs⟩

theorem matrix6s3_certified (s : Nat) : Matrix6s3CertifiedTarget s := by
  intro hs
  exact ⟨matrix6s3_valid s hs, matrix6s3_primitive s hs⟩

theorem matrix6s5_certified (s : Nat) : Matrix6s5CertifiedTarget s := by
  intro hs
  exact ⟨matrix6s5_valid s hs, matrix6s5_primitive s hs⟩

def GenericCountMatrixCertified (m : Nat) : Prop :=
  ∃ A : CountMatrix, CountMatrixCertified m A

theorem generic_count_matrix_certified {m : Nat} (hm7 : 7 ≤ m) (hodd : Odd m) :
    GenericCountMatrixCertified m := by
  rcases hodd with ⟨t, rfl⟩
  have ht3 : 3 ≤ t := by omega
  let q := t / 3
  let r := t % 3
  have hrlt : r < 3 := by
    simpa [r] using Nat.mod_lt t (by norm_num : 0 < 3)
  have htdecomp : t = 3*q + r := by
    have h := Nat.div_add_mod t 3
    unfold q r
    omega
  interval_cases r
  · have ht0 : t = 3*q := by omega
    by_cases hq1 : q = 1
    · refine ⟨matrix7, ?_⟩
      rw [ht0, hq1]
      norm_num
      exact matrix7_certified
    · have hq2 : 2 ≤ q := by omega
      refine ⟨matrix6s1 q, ?_⟩
      rw [ht0]
      rw [show 2 * (3 * q) + 1 = 6*q + 1 by omega]
      exact matrix6s1_certified q hq2
  · have ht1 : t = 3*q + 1 := by omega
    have hq1 : 1 ≤ q := by omega
    refine ⟨matrix6s3 q, ?_⟩
    rw [ht1]
    rw [show 2 * (3 * q + 1) + 1 = 6*q + 3 by omega]
    exact matrix6s3_certified q hq1
  · have ht2 : t = 3*q + 2 := by omega
    have hq1 : 1 ≤ q := by omega
    refine ⟨matrix6s5 q, ?_⟩
    rw [ht2]
    rw [show 2 * (3 * q + 2) + 1 = 6*q + 5 by omega]
    exact matrix6s5_certified q hq1

end Handoff
end D7Odd
