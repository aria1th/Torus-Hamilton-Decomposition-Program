import Mathlib

namespace RoundComposite
namespace PrefixCount

open scoped BigOperators

/-- Integer primitiveity condition used by signed prefix-count differences. -/
def IntCoprime (a : Int) (m : Nat) : Prop :=
  Nat.Coprime a.natAbs m

/-- Counts for symbols `0`, `Delta`, and the numeric prefix symbols. -/
structure Parts (d : Nat) where
  zero : Fin d → Nat
  delta : Fin d → Nat
  step : Fin d → Fin (d - 2) → Nat

namespace Parts

/--
Prefix-count admissibility, stated before any conversion to a dense
`Fin d × Fin d` matrix.  The primitive conditions are exactly the row
conditions consumed by the prefix-count return lemma.
-/
structure Admissible {d : Nat} (m : Nat) (C : Parts d) : Prop where
  row_sum :
    ∀ i : Fin d,
      C.zero i + C.delta i + (∑ k : Fin (d - 2), C.step i k) = m
  col_zero :
    (∑ i : Fin d, C.zero i) = m
  col_delta :
    (∑ i : Fin d, C.delta i) = m
  col_step :
    ∀ k : Fin (d - 2), (∑ i : Fin d, C.step i k) = m
  prim_zero :
    ∀ i : Fin d, Nat.Coprime (C.zero i) m
  prim_step :
    ∀ i : Fin d, ∀ k : Fin (d - 2),
      IntCoprime ((C.step i k : Int) - (C.delta i : Int)) m

end Parts

/-- The signed differences used by the high-modulus transportation branch. -/
def signedVals : Finset Int :=
  {-2, -1, 1, 2}

def IsSignedVal (a : Int) : Prop :=
  a ∈ signedVals

theorem signedVal_coprime_of_odd
    {a : Int} {m : Nat} (ha : IsSignedVal a) (hm : Odd m) :
    IntCoprime a m := by
  have ha' : a = -2 ∨ a = -1 ∨ a = 1 ∨ a = 2 := by
    simpa [IsSignedVal, signedVals] using ha
  rcases ha' with rfl | rfl | rfl | rfl
  · simpa [IntCoprime] using hm.coprime_two_left
  · simp [IntCoprime]
  · simp [IntCoprime]
  · simpa [IntCoprime] using hm.coprime_two_left

theorem one_le_div_pred_of_le {d m : Nat} (hd2 : 2 ≤ d) (hmd : d ≤ m) :
    1 ≤ m / (d - 1) := by
  have hden : 0 < d - 1 := by omega
  exact (Nat.le_div_iff_mul_le hden).2 (by omega)

theorem pred_mod_pos_of_odd
    {d m : Nat} (hdodd : Odd d) (hmodd : Odd m) (hd2 : 2 ≤ d) :
    0 < m % (d - 1) := by
  have hden : 0 < d - 1 := by omega
  by_contra hnot
  have hr0 : m % (d - 1) = 0 := by omega
  rcases hdodd with ⟨k, hk⟩
  have hpred : d - 1 = 2 * k := by omega
  have hm_eq : m = (d - 1) * (m / (d - 1)) := by
    have hdiv := Nat.div_add_mod m (d - 1)
    omega
  have hmeven : Even m := by
    refine ⟨k * (m / (d - 1)), ?_⟩
    calc
      m = (d - 1) * (m / (d - 1)) := hm_eq
      _ = (2 * k) * (m / (d - 1)) := by rw [hpred]
      _ = k * (m / (d - 1)) + k * (m / (d - 1)) := by ring
  exact (Nat.not_even_iff_odd.mpr hmodd) hmeven

/--
A signed prefix-count certificate.

`diff i k` is intended to be `step i k - delta i`.  The remaining fields are
the algebraic side conditions needed before conversion to an admissible
prefix-count matrix.
-/
structure SignedPrefixCounts (d m : Nat) where
  zero : Fin d → Nat
  delta : Fin d → Nat
  diff : Fin d → Fin (d - 2) → Int
  diff_signed : ∀ i k, IsSignedVal (diff i k)
  step_nonneg : ∀ i k, 0 ≤ (delta i : Int) + diff i k
  row_eq :
    ∀ i : Fin d,
      (zero i : Int)
        + (((d - 1 : Nat) : Int) * (delta i : Int))
        + (∑ k : Fin (d - 2), diff i k)
        = (m : Int)
  col_zero :
    (∑ i : Fin d, zero i) = m
  col_delta :
    (∑ i : Fin d, delta i) = m
  diff_col_zero :
    ∀ k : Fin (d - 2), (∑ i : Fin d, diff i k) = 0
  prim_zero :
    ∀ i : Fin d, Nat.Coprime (zero i) m

namespace SignedPrefixCounts

def toParts {d m : Nat} (S : SignedPrefixCounts d m) : Parts d where
  zero := S.zero
  delta := S.delta
  step := fun i k => Int.toNat ((S.delta i : Int) + S.diff i k)

@[simp] theorem toParts_zero {d m : Nat}
    (S : SignedPrefixCounts d m) (i : Fin d) :
    S.toParts.zero i = S.zero i :=
  rfl

@[simp] theorem toParts_delta {d m : Nat}
    (S : SignedPrefixCounts d m) (i : Fin d) :
    S.toParts.delta i = S.delta i :=
  rfl

@[simp] theorem toParts_step {d m : Nat}
    (S : SignedPrefixCounts d m) (i : Fin d) (k : Fin (d - 2)) :
    S.toParts.step i k = Int.toNat ((S.delta i : Int) + S.diff i k) :=
  rfl

theorem diff_coprime {d m : Nat} (S : SignedPrefixCounts d m)
    (hm : Odd m) (i : Fin d) (k : Fin (d - 2)) :
    IntCoprime (S.diff i k) m :=
  signedVal_coprime_of_odd (S.diff_signed i k) hm

theorem toParts_step_int {d m : Nat} (S : SignedPrefixCounts d m)
    (i : Fin d) (k : Fin (d - 2)) :
    (S.toParts.step i k : Int) = (S.delta i : Int) + S.diff i k := by
  simp [toParts, Int.toNat_of_nonneg (S.step_nonneg i k)]

theorem toParts_row_sum {d m : Nat} (S : SignedPrefixCounts d m)
    (hd2 : 2 ≤ d) (i : Fin d) :
    S.toParts.zero i + S.toParts.delta i
      + (∑ k : Fin (d - 2), S.toParts.step i k) = m := by
  apply Int.ofNat.inj
  calc
    (((S.toParts.zero i + S.toParts.delta i
        + (∑ k : Fin (d - 2), S.toParts.step i k) : Nat) : Int))
        = (S.zero i : Int) + (S.delta i : Int)
          + (∑ k : Fin (d - 2), ((S.toParts.step i k : Nat) : Int)) := by
            simp
    _ = (S.zero i : Int) + (S.delta i : Int)
          + (∑ k : Fin (d - 2), ((S.delta i : Int) + S.diff i k)) := by
            simp_rw [S.toParts_step_int]
    _ = (S.zero i : Int)
          + (((d - 1 : Nat) : Int) * (S.delta i : Int))
          + (∑ k : Fin (d - 2), S.diff i k) := by
            rw [Finset.sum_add_distrib]
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
            have hdsub :
                (((d - 1 : Nat) : Int)) = (((d - 2 : Nat) : Int)) + 1 := by
              omega
            rw [hdsub]
            ring
    _ = (m : Int) := S.row_eq i

theorem toParts_col_step {d m : Nat} (S : SignedPrefixCounts d m)
    (k : Fin (d - 2)) :
    (∑ i : Fin d, S.toParts.step i k) = m := by
  apply Int.ofNat.inj
  calc
    (((∑ i : Fin d, S.toParts.step i k) : Nat) : Int)
        = (∑ i : Fin d, ((S.toParts.step i k : Nat) : Int)) := by
          simp
    _ = (∑ i : Fin d, ((S.delta i : Int) + S.diff i k)) := by
          simp_rw [S.toParts_step_int]
    _ = (∑ i : Fin d, (S.delta i : Int)) + (∑ i : Fin d, S.diff i k) := by
          rw [Finset.sum_add_distrib]
    _ = (m : Int) := by
          have hdelta : (∑ i : Fin d, (S.delta i : Int)) = (m : Int) := by
            exact_mod_cast S.col_delta
          rw [hdelta, S.diff_col_zero k]
          simp

theorem toParts_prim_step {d m : Nat} (S : SignedPrefixCounts d m)
    (hm : Odd m) (i : Fin d) (k : Fin (d - 2)) :
    IntCoprime ((S.toParts.step i k : Int) - (S.toParts.delta i : Int)) m := by
  have hstep := S.toParts_step_int i k
  have hdiff :
      (S.toParts.step i k : Int) - (S.toParts.delta i : Int) = S.diff i k := by
    rw [hstep]
    simp
  rw [hdiff]
  exact signedVal_coprime_of_odd (S.diff_signed i k) hm

theorem toParts_admissible {d m : Nat} (S : SignedPrefixCounts d m)
    (hd2 : 2 ≤ d) (hm : Odd m) :
    S.toParts.Admissible m where
  row_sum := S.toParts_row_sum hd2
  col_zero := S.col_zero
  col_delta := S.col_delta
  col_step := S.toParts_col_step
  prim_zero := S.prim_zero
  prim_step := S.toParts_prim_step hm

end SignedPrefixCounts

end PrefixCount
end RoundComposite
