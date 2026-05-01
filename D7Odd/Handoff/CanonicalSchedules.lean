import D7Odd.Handoff.CanonicalCountMatrices

set_option linter.style.longLine false

namespace D7Odd
namespace Handoff

abbrev SymbolPerm7 := Fin 7 → Fin 7

def perm7 (a0 a1 a2 a3 a4 a5 a6 : Fin 7) : SymbolPerm7
  | 0 => a0
  | 1 => a1
  | 2 => a2
  | 3 => a3
  | 4 => a4
  | 5 => a5
  | 6 => a6

def scheduleCount (L : List SymbolPerm7) (c sym : Fin 7) : Nat :=
  L.countP fun σ => σ c == sym

def repeatSchedule : Nat → List SymbolPerm7 → List SymbolPerm7
  | 0, _ => []
  | k + 1, L => L ++ repeatSchedule k L

def canonicalBlockSchedule : List SymbolPerm7 := [
  perm7 1 2 3 4 5 6 0,
  perm7 2 1 4 3 6 5 0,
  perm7 3 4 5 6 1 2 0,
  perm7 4 3 6 5 2 1 0,
  perm7 5 6 1 2 3 4 0,
  perm7 6 5 2 1 4 3 0
]

def canonicalSchedule7 : List SymbolPerm7 := [
  perm7 0 1 4 3 2 5 6,
  perm7 1 0 4 3 2 6 5,
  perm7 1 6 5 0 2 3 4,
  perm7 6 1 5 3 0 4 2,
  perm7 6 5 0 4 1 2 3,
  perm7 6 5 1 4 3 0 2,
  perm7 6 5 4 1 3 2 0
]

def canonicalBase6s1Schedule : List SymbolPerm7 := [
  perm7 0 1 2 3 4 5 6,
  perm7 1 0 6 2 3 4 5,
  perm7 1 2 6 0 3 5 4,
  perm7 1 6 0 2 5 3 4,
  perm7 2 6 1 3 5 4 0,
  perm7 3 6 1 4 5 0 2,
  perm7 4 6 1 5 0 2 3,
  perm7 5 6 3 1 4 0 2,
  perm7 6 1 5 2 4 3 0,
  perm7 6 1 5 4 0 2 3,
  perm7 6 3 5 4 1 2 0,
  perm7 6 4 5 1 2 3 0,
  perm7 6 5 4 3 2 1 0
]

def canonicalBase6s3Schedule : List SymbolPerm7 := [
  perm7 0 1 2 3 4 5 6,
  perm7 1 0 3 2 5 6 4,
  perm7 1 2 0 4 6 3 5,
  perm7 1 3 4 5 6 0 2,
  perm7 2 1 5 6 0 3 4,
  perm7 3 1 6 0 5 4 2,
  perm7 4 5 1 6 0 2 3,
  perm7 5 6 1 4 2 0 3,
  perm7 6 4 1 5 3 2 0
]

def canonicalBase6s5Schedule : List SymbolPerm7 := [
  perm7 0 1 2 3 4 5 6,
  perm7 1 0 3 2 4 6 5,
  perm7 1 2 0 6 3 5 4,
  perm7 1 3 4 6 5 0 2,
  perm7 2 1 5 6 0 3 4,
  perm7 3 1 6 0 5 4 2,
  perm7 4 5 6 1 0 2 3,
  perm7 5 6 1 2 3 4 0,
  perm7 5 6 1 4 2 0 3,
  perm7 6 4 5 3 1 2 0,
  perm7 6 5 1 4 2 3 0
]

def canonicalSchedule6s1 (s : Nat) : List SymbolPerm7 :=
  canonicalBase6s1Schedule ++ repeatSchedule (s - 2) canonicalBlockSchedule

def canonicalSchedule6s3 (s : Nat) : List SymbolPerm7 :=
  canonicalBase6s3Schedule ++ repeatSchedule (s - 1) canonicalBlockSchedule

def canonicalSchedule6s5 (s : Nat) : List SymbolPerm7 :=
  canonicalBase6s5Schedule ++ repeatSchedule (s - 1) canonicalBlockSchedule

theorem scheduleCount_repeat (L : List SymbolPerm7) (k : Nat) (c sym : Fin 7) :
    scheduleCount (repeatSchedule k L) c sym = k * scheduleCount L c sym := by
  induction k with
  | zero => simp [repeatSchedule, scheduleCount]
  | succ k ih =>
      rw [repeatSchedule, scheduleCount, List.countP_append]
      change scheduleCount L c sym + scheduleCount (repeatSchedule k L) c sym =
        (k + 1) * scheduleCount L c sym
      rw [ih, Nat.succ_mul]
      omega

theorem repeatSchedule_length (L : List SymbolPerm7) (k : Nat) :
    (repeatSchedule k L).length = k * L.length := by
  induction k with
  | zero => simp [repeatSchedule]
  | succ k ih =>
      rw [repeatSchedule, List.length_append, ih, Nat.succ_mul]
      omega

def scheduleListLatin (L : List SymbolPerm7) : Prop :=
  List.Forall Function.Bijective L

set_option maxRecDepth 100000 in
-- Native evaluation checks the six fixed 7-symbol permutations.
set_option linter.style.nativeDecide false in
theorem canonicalBlockSchedule_latin : scheduleListLatin canonicalBlockSchedule := by
  change List.Forall Function.Bijective canonicalBlockSchedule
  native_decide

set_option maxRecDepth 100000 in
-- Native evaluation checks the thirteen fixed base permutations.
set_option linter.style.nativeDecide false in
theorem canonicalBase6s1Schedule_latin : scheduleListLatin canonicalBase6s1Schedule := by
  change List.Forall Function.Bijective canonicalBase6s1Schedule
  native_decide

set_option maxRecDepth 100000 in
-- Native evaluation checks the nine fixed base permutations.
set_option linter.style.nativeDecide false in
theorem canonicalBase6s3Schedule_latin : scheduleListLatin canonicalBase6s3Schedule := by
  change List.Forall Function.Bijective canonicalBase6s3Schedule
  native_decide

set_option maxRecDepth 100000 in
-- Native evaluation checks the eleven fixed base permutations.
set_option linter.style.nativeDecide false in
theorem canonicalBase6s5Schedule_latin : scheduleListLatin canonicalBase6s5Schedule := by
  change List.Forall Function.Bijective canonicalBase6s5Schedule
  native_decide

set_option maxRecDepth 100000 in
-- Native evaluation checks the seven fixed `m = 7` permutations.
set_option linter.style.nativeDecide false in
theorem canonicalSchedule7_latin : scheduleListLatin canonicalSchedule7 := by
  change List.Forall Function.Bijective canonicalSchedule7
  native_decide

-- This proof unfolds `List.Forall` over concatenated finite schedules.
set_option linter.flexible false in
theorem scheduleListLatin_append {L₁ L₂ : List SymbolPerm7}
    (h₁ : scheduleListLatin L₁) (h₂ : scheduleListLatin L₂) :
    scheduleListLatin (L₁ ++ L₂) := by
  induction L₁ with
  | nil => simpa [scheduleListLatin] using h₂
  | cons _ _ _ =>
      simp [scheduleListLatin] at h₁ ⊢
      exact ⟨h₁.1, h₁.2, h₂⟩

theorem scheduleListLatin_repeat {L : List SymbolPerm7} (h : scheduleListLatin L) (k : Nat) :
    scheduleListLatin (repeatSchedule k L) := by
  induction k with
  | zero => simp [repeatSchedule, scheduleListLatin]
  | succ _ ih =>
      rw [repeatSchedule]
      exact scheduleListLatin_append h ih

theorem canonicalSchedule6s1_latin (s : Nat) : scheduleListLatin (canonicalSchedule6s1 s) :=
  scheduleListLatin_append canonicalBase6s1Schedule_latin
    (scheduleListLatin_repeat canonicalBlockSchedule_latin (s - 2))

theorem canonicalSchedule6s3_latin (s : Nat) : scheduleListLatin (canonicalSchedule6s3 s) :=
  scheduleListLatin_append canonicalBase6s3Schedule_latin
    (scheduleListLatin_repeat canonicalBlockSchedule_latin (s - 1))

theorem canonicalSchedule6s5_latin (s : Nat) : scheduleListLatin (canonicalSchedule6s5 s) :=
  scheduleListLatin_append canonicalBase6s5Schedule_latin
    (scheduleListLatin_repeat canonicalBlockSchedule_latin (s - 1))

theorem canonicalSchedule7_length : canonicalSchedule7.length = 7 := by
  norm_num [canonicalSchedule7]

theorem canonicalSchedule6s1_length (s : Nat) (hs : 2 ≤ s) :
    (canonicalSchedule6s1 s).length = 6*s + 1 := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hs
  subst s
  rw [canonicalSchedule6s1, List.length_append, repeatSchedule_length]
  norm_num [canonicalBase6s1Schedule, canonicalBlockSchedule]
  omega

theorem canonicalSchedule6s3_length (s : Nat) (hs : 1 ≤ s) :
    (canonicalSchedule6s3 s).length = 6*s + 3 := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hs
  subst s
  rw [canonicalSchedule6s3, List.length_append, repeatSchedule_length]
  norm_num [canonicalBase6s3Schedule, canonicalBlockSchedule]
  omega

theorem canonicalSchedule6s5_length (s : Nat) (hs : 1 ≤ s) :
    (canonicalSchedule6s5 s).length = 6*s + 5 := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hs
  subst s
  rw [canonicalSchedule6s5, List.length_append, repeatSchedule_length]
  norm_num [canonicalBase6s5Schedule, canonicalBlockSchedule]
  omega

set_option maxRecDepth 100000 in
-- Native evaluation checks the fixed 13-layer base count matrix.
set_option linter.style.nativeDecide false in
theorem canonicalBase6s1_count :
    ∀ c sym : Fin 7, scheduleCount canonicalBase6s1Schedule c sym = matrix6s1 2 c sym := by
  native_decide

set_option maxRecDepth 100000 in
-- Native evaluation checks the fixed 9-layer base count matrix.
set_option linter.style.nativeDecide false in
theorem canonicalBase6s3_count :
    ∀ c sym : Fin 7, scheduleCount canonicalBase6s3Schedule c sym = matrix6s3 1 c sym := by
  native_decide

set_option maxRecDepth 100000 in
-- Native evaluation checks the fixed 11-layer base count matrix.
set_option linter.style.nativeDecide false in
theorem canonicalBase6s5_count :
    ∀ c sym : Fin 7, scheduleCount canonicalBase6s5Schedule c sym = matrix6s5 1 c sym := by
  native_decide

set_option maxRecDepth 100000 in
-- Native evaluation checks the fixed 6-layer increment block.
set_option linter.style.nativeDecide false in
theorem canonicalBlock_count :
    ∀ c sym : Fin 7,
      scheduleCount canonicalBlockSchedule c sym = matrix6s1 3 c sym - matrix6s1 2 c sym := by
  native_decide

set_option maxRecDepth 100000 in
-- Native evaluation checks the fixed `m = 7` count matrix.
set_option linter.style.nativeDecide false in
theorem canonicalSchedule7_count :
    ∀ c sym : Fin 7, scheduleCount canonicalSchedule7 c sym = matrix7 c sym := by
  native_decide

theorem canonicalSchedule6s1_count (s : Nat) (hs : 2 ≤ s) :
    ∀ c sym : Fin 7, scheduleCount (canonicalSchedule6s1 s) c sym = matrix6s1 s c sym := by
  intro c sym
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hs
  subst s
  rw [canonicalSchedule6s1, show 2 + k - 2 = k by omega, scheduleCount, List.countP_append]
  change scheduleCount canonicalBase6s1Schedule c sym +
      scheduleCount (repeatSchedule k canonicalBlockSchedule) c sym = matrix6s1 (2 + k) c sym
  rw [scheduleCount_repeat, canonicalBase6s1_count, canonicalBlock_count]
  fin_cases c <;> fin_cases sym <;> norm_num [matrix6s1] <;> omega

theorem canonicalSchedule6s3_count (s : Nat) (hs : 1 ≤ s) :
    ∀ c sym : Fin 7, scheduleCount (canonicalSchedule6s3 s) c sym = matrix6s3 s c sym := by
  intro c sym
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hs
  subst s
  rw [canonicalSchedule6s3, show 1 + k - 1 = k by omega, scheduleCount, List.countP_append]
  change scheduleCount canonicalBase6s3Schedule c sym +
      scheduleCount (repeatSchedule k canonicalBlockSchedule) c sym = matrix6s3 (1 + k) c sym
  rw [scheduleCount_repeat, canonicalBase6s3_count, canonicalBlock_count]
  fin_cases c <;> fin_cases sym <;> norm_num [matrix6s1, matrix6s3] <;> omega

theorem canonicalSchedule6s5_count (s : Nat) (hs : 1 ≤ s) :
    ∀ c sym : Fin 7, scheduleCount (canonicalSchedule6s5 s) c sym = matrix6s5 s c sym := by
  intro c sym
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hs
  subst s
  rw [canonicalSchedule6s5, show 1 + k - 1 = k by omega, scheduleCount, List.countP_append]
  change scheduleCount canonicalBase6s5Schedule c sym +
      scheduleCount (repeatSchedule k canonicalBlockSchedule) c sym = matrix6s5 (1 + k) c sym
  rw [scheduleCount_repeat, canonicalBase6s5_count, canonicalBlock_count]
  fin_cases c <;> fin_cases sym <;> norm_num [matrix6s1, matrix6s5] <;> omega

structure CountMatrixSchedule (m : Nat) where
  matrix : CountMatrix
  schedule : List SymbolPerm7
  certified : CountMatrixCertified m matrix
  latin : scheduleListLatin schedule
  length_eq : schedule.length = m
  count_eq : ∀ c sym : Fin 7, scheduleCount schedule c sym = matrix c sym

def canonicalSchedule7_certified : CountMatrixSchedule 7 where
  matrix := matrix7
  schedule := canonicalSchedule7
  certified := matrix7_certified
  latin := canonicalSchedule7_latin
  length_eq := canonicalSchedule7_length
  count_eq := canonicalSchedule7_count

def canonicalSchedule6s1_certified (s : Nat) (hs : 2 ≤ s) :
    CountMatrixSchedule (6*s + 1) where
  matrix := matrix6s1 s
  schedule := canonicalSchedule6s1 s
  certified := matrix6s1_certified s hs
  latin := canonicalSchedule6s1_latin s
  length_eq := canonicalSchedule6s1_length s hs
  count_eq := canonicalSchedule6s1_count s hs

def canonicalSchedule6s3_certified (s : Nat) (hs : 1 ≤ s) :
    CountMatrixSchedule (6*s + 3) where
  matrix := matrix6s3 s
  schedule := canonicalSchedule6s3 s
  certified := matrix6s3_certified s hs
  latin := canonicalSchedule6s3_latin s
  length_eq := canonicalSchedule6s3_length s hs
  count_eq := canonicalSchedule6s3_count s hs

def canonicalSchedule6s5_certified (s : Nat) (hs : 1 ≤ s) :
    CountMatrixSchedule (6*s + 5) where
  matrix := matrix6s5 s
  schedule := canonicalSchedule6s5 s
  certified := matrix6s5_certified s hs
  latin := canonicalSchedule6s5_latin s
  length_eq := canonicalSchedule6s5_length s hs
  count_eq := canonicalSchedule6s5_count s hs

theorem generic_count_matrix_schedule {m : Nat} (hm7 : 7 ≤ m) (hodd : Odd m) :
    Nonempty (CountMatrixSchedule m) := by
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
    · rw [ht0, hq1]
      norm_num
      exact ⟨canonicalSchedule7_certified⟩
    · have hq2 : 2 ≤ q := by omega
      rw [ht0]
      rw [show 2 * (3 * q) + 1 = 6*q + 1 by omega]
      exact ⟨canonicalSchedule6s1_certified q hq2⟩
  · have ht1 : t = 3*q + 1 := by omega
    have hq1 : 1 ≤ q := by omega
    rw [ht1]
    rw [show 2 * (3 * q + 1) + 1 = 6*q + 3 by omega]
    exact ⟨canonicalSchedule6s3_certified q hq1⟩
  · have ht2 : t = 3*q + 2 := by omega
    have hq1 : 1 ≤ q := by omega
    rw [ht2]
    rw [show 2 * (3 * q + 2) + 1 = 6*q + 5 by omega]
    exact ⟨canonicalSchedule6s5_certified q hq1⟩

end Handoff
end D7Odd
