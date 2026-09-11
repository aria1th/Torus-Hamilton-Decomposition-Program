-- STATUS: main-path
import TorusEven.Entry.Star.Support

namespace TorusEven.Entry.Star

open Surgery

variable {m : ℕ} [NeZero m]

omit [NeZero m] in
theorem mem_support_iff (p : Plane m) : p ∈ support m ↔
    (p.1 ≠ 0 ∧ p.2 = 0) ∨ (p.1 = 0 ∧ p.2 ≠ 0) ∨
      p = cornerPlus ∨ p = cornerMinus := by
  constructor
  · rintro ⟨⟨s, z⟩, rfl⟩
    by_cases hz : z = 0 <;> by_cases hs : s = 0 <;>
      simp [word, hz, hs]
  · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩ | rfl | rfl)
    · exact ⟨(p.1, 0), by simpa [word, ha] using (Prod.ext rfl hb.symm : (p.1, 0) = p)⟩
    · exact ⟨(p.2, 1), by simpa [word, hb] using (Prod.ext ha.symm rfl : (0, p.2) = p)⟩
    · exact ⟨(0, 0), by simp [word]⟩
    · exact ⟨(0, 1), by simp [word]⟩

def EqFour (m a b : ℕ) : Prop :=
  a = b ∨ a = b + m ∨ a = b + 2 * m ∨ a = b + 3 * m

theorem natCast_eq_iff_four {a b : ℕ} (ha : a < 4 * m) (hb : b < m) :
    (a : ZMod m) = (b : ZMod m) ↔ EqFour m a b := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hb]
  have hd : a / m < 4 := (Nat.div_lt_iff_lt_mul (NeZero.pos m)).mpr (by omega)
  have he := Nat.mod_add_div a m
  constructor
  · intro h
    unfold EqFour
    interval_cases hq : a / m <;> omega
  · intro h
    rcases h with h | h | h | h <;> rw [h] <;>
      simp [Nat.add_mod, Nat.mod_eq_of_lt hb]

def hitTest (m a b : ℕ) : Prop :=
  (¬ EqFour m a 0 ∧ EqFour m b 0) ∨
  (EqFour m a 0 ∧ ¬ EqFour m b 0) ∨
  (EqFour m a 1 ∧ EqFour m b (m - 1)) ∨
  (EqFour m a (m - 1) ∧ EqFour m b 1)

theorem hitTest_iff (hm : 2 ≤ m) {a b : ℕ} (ha : a < 4 * m) (hb : b < 4 * m) :
    ((a : ZMod m), (b : ZMod m)) ∈ support m ↔ hitTest m a b := by
  have hn : ((m - 1 : ℕ) : ZMod m) = -1 := by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one, zero_sub]
  rw [mem_support_iff]
  simp only [cornerPlus, cornerMinus, Prod.mk.injEq]
  rw [← hn]
  simp only [ne_eq, ← Nat.cast_zero (R := ZMod m), ← Nat.cast_one (R := ZMod m),
    natCast_eq_iff_four ha (by omega : 0 < m),
    natCast_eq_iff_four hb (by omega : 0 < m),
    natCast_eq_iff_four ha (by omega : 1 < m),
    natCast_eq_iff_four hb (by omega : 1 < m),
    natCast_eq_iff_four ha (by omega : m - 1 < m),
    natCast_eq_iff_four hb (by omega : m - 1 < m), hitTest]

omit [NeZero m] in
theorem translation_iterate_nat (d a b k : ℕ) :
    (Equiv.addRight (1, (d : ZMod m)))^[k] ((a : ZMod m), (b : ZMod m)) =
      (((a + k : ℕ) : ZMod m), ((b + d * k : ℕ) : ZMod m)) := by
  change ((fun p : Plane m => p + (1, (d : ZMod m)))^[k] _) = _
  rw [add_right_iterate_apply, nsmul_eq_mul]
  apply Prod.ext <;> simp [Nat.cast_add, Nat.cast_mul, mul_comm]

theorem translation_ret_nat (hm : 2 ≤ m) (d a b n : ℕ)
    (hu : ((a : ZMod m), (b : ZMod m)) ∈ support m) (hn : 0 < n)
    (ha : a + n < 4 * m) (hb : b + d * n < 4 * m)
    (hh : hitTest m (a + n) (b + d * n))
    (hf : ∀ k, 0 < k → k < n → ¬ hitTest m (a + k) (b + d * k)) :
    ret (Equiv.addRight (1, (d : ZMod m))) (support m) ((a : ZMod m), (b : ZMod m)) =
      (((a + n : ℕ) : ZMod m), ((b + d * n : ℕ) : ZMod m)) := by
  have ht := retTime_eq_of_first (Equiv.addRight (1, (d : ZMod m))) (support m) hu hn
    (by rw [translation_iterate_nat]; exact (hitTest_iff hm ha hb).mpr hh) (by
      intro k hk hkn
      rw [translation_iterate_nat, hitTest_iff hm (by omega) (by nlinarith)]
      exact hf k hk hkn)
  simp only [ret, ht, translation_iterate_nat]

end TorusEven.Entry.Star
