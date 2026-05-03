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

/--
Algebraic transportation data for the high-modulus branch, before it is turned
into signed prefix counts.  The fields match the decomposition
`m = (d - 1) * q + r`.
-/
structure QuotientTransport (d m q r : Nat) where
  zero : Fin d → Nat
  tau : Fin d → Int
  eps : Fin d → Fin (d - 2) → Int
  eps_signed : ∀ i k, IsSignedVal (eps i k)
  eps_col_zero : ∀ k : Fin (d - 2), (∑ i : Fin d, eps i k) = 0
  tau_sum : (∑ i : Fin d, tau i) = (q : Int) - (r : Int)
  delta_nonneg : ∀ i : Fin d, 0 ≤ (q : Int) - tau i
  step_nonneg : ∀ i k, 0 ≤ (q : Int) - tau i + eps i k
  zero_eq :
    ∀ i : Fin d,
      (zero i : Int)
        = (r : Int)
          + (((d - 1 : Nat) : Int) * tau i)
          - (∑ k : Fin (d - 2), eps i k)
  prim_zero : ∀ i : Fin d, Nat.Coprime (zero i) m

namespace QuotientTransport

def delta {d m q r : Nat} (T : QuotientTransport d m q r)
    (i : Fin d) : Nat :=
  Int.toNat ((q : Int) - T.tau i)

theorem delta_int {d m q r : Nat} (T : QuotientTransport d m q r)
    (i : Fin d) :
    (T.delta i : Int) = (q : Int) - T.tau i := by
  simp [delta, Int.toNat_of_nonneg (T.delta_nonneg i)]

theorem step_nonneg_delta {d m q r : Nat} (T : QuotientTransport d m q r)
    (i : Fin d) (k : Fin (d - 2)) :
    0 ≤ (T.delta i : Int) + T.eps i k := by
  rw [T.delta_int i]
  exact T.step_nonneg i k

theorem row_eq_signed {d m q r : Nat} (T : QuotientTransport d m q r)
    (hmqr : m = (d - 1) * q + r) (i : Fin d) :
    (T.zero i : Int)
      + (((d - 1 : Nat) : Int) * (T.delta i : Int))
      + (∑ k : Fin (d - 2), T.eps i k)
      = (m : Int) := by
  rw [T.zero_eq i, T.delta_int i]
  have hmqrInt :
      (m : Int) = (((d - 1 : Nat) : Int) * (q : Int)) + (r : Int) := by
    rw [hmqr]
    norm_num [Nat.cast_add, Nat.cast_mul]
  rw [hmqrInt]
  ring

theorem col_delta_signed {d m q r : Nat} (T : QuotientTransport d m q r)
    (hdpos : 0 < d) (hmqr : m = (d - 1) * q + r) :
    (∑ i : Fin d, T.delta i) = m := by
  apply Int.ofNat.inj
  calc
    (((∑ i : Fin d, T.delta i) : Nat) : Int)
        = (∑ i : Fin d, (T.delta i : Int)) := by
          simp
    _ = (∑ i : Fin d, ((q : Int) - T.tau i)) := by
          simp_rw [T.delta_int]
    _ = ((d : Int) * (q : Int)) - ((q : Int) - (r : Int)) := by
          rw [Finset.sum_sub_distrib, T.tau_sum]
          simp [Finset.sum_const]
    _ = (m : Int) := by
          have hmqrInt :
              (m : Int) = (((d - 1 : Nat) : Int) * (q : Int)) + (r : Int) := by
            rw [hmqr]
            norm_num [Nat.cast_add, Nat.cast_mul]
          rw [hmqrInt]
          have hdsub : (d : Int) = ((d - 1 : Nat) : Int) + 1 := by
            omega
          rw [hdsub]
          ring

theorem col_zero_signed {d m q r : Nat} (T : QuotientTransport d m q r)
    (hdpos : 0 < d) (hmqr : m = (d - 1) * q + r) :
    (∑ i : Fin d, T.zero i) = m := by
  apply Int.ofNat.inj
  calc
    (((∑ i : Fin d, T.zero i) : Nat) : Int)
        = (∑ i : Fin d, (T.zero i : Int)) := by
          simp
    _ = (∑ i : Fin d,
          ((r : Int) + (((d - 1 : Nat) : Int) * T.tau i)
            - (∑ k : Fin (d - 2), T.eps i k))) := by
          simp_rw [T.zero_eq]
    _ = (d : Int) * (r : Int)
          + (((d - 1 : Nat) : Int) * ((q : Int) - (r : Int))) - 0 := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
          have htau :
              (∑ i : Fin d, ((d - 1 : Nat) : Int) * T.tau i)
                = ((d - 1 : Nat) : Int) * ((q : Int) - (r : Int)) := by
            rw [← Finset.mul_sum, T.tau_sum]
          have heps :
              (∑ i : Fin d, ∑ k : Fin (d - 2), T.eps i k) = 0 := by
            rw [Finset.sum_comm]
            simp [T.eps_col_zero]
          rw [htau, heps]
          simp [Finset.sum_const]
    _ = (m : Int) := by
          have hmqrInt :
              (m : Int) = (((d - 1 : Nat) : Int) * (q : Int)) + (r : Int) := by
            rw [hmqr]
            norm_num [Nat.cast_add, Nat.cast_mul]
          rw [hmqrInt]
          have hdsub : (d : Int) = ((d - 1 : Nat) : Int) + 1 := by
            omega
          rw [hdsub]
          ring

def toSigned {d m q r : Nat} (T : QuotientTransport d m q r)
    (hdpos : 0 < d) (hmqr : m = (d - 1) * q + r) :
    SignedPrefixCounts d m where
  zero := T.zero
  delta := T.delta
  diff := T.eps
  diff_signed := T.eps_signed
  step_nonneg := T.step_nonneg_delta
  row_eq := T.row_eq_signed hmqr
  col_zero := T.col_zero_signed hdpos hmqr
  col_delta := T.col_delta_signed hdpos hmqr
  diff_col_zero := T.eps_col_zero
  prim_zero := T.prim_zero

theorem toSigned_admissible {d m q r : Nat}
    (T : QuotientTransport d m q r)
    (hd2 : 2 ≤ d) (hmodd : Odd m)
    (hmqr : m = (d - 1) * q + r) :
    (T.toSigned (by omega) hmqr).toParts.Admissible m :=
  (T.toSigned (by omega) hmqr).toParts_admissible hd2 hmodd

end QuotientTransport

end PrefixCount
end RoundComposite
