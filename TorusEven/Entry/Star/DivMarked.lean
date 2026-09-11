-- STATUS: main-path
import TorusEven.Entry.Star.DivTranslation

namespace TorusEven.Entry.Star.Divisible

variable (q : ℕ) [NeZero (6 * q)] (hq : 2 ≤ q)

def x (s : ℕ) : ZMod (6 * q) × ZMod 2 := (s, 0)
def y (s : ℕ) : ZMod (6 * q) × ZMod 2 := (s, 1)

noncomputable def phi : Equiv.Perm (ZMod (6 * q) × ZMod 2) := markedReturn (by omega)

omit [NeZero (6 * q)] in
theorem word_x (s : ℕ) (hs : 0 < s) (hsm : s < 6 * q) : word (x q s) = point q s 0 := by
  simp [x, word, point, cast_ne_zero hs hsm]

omit [NeZero (6 * q)] in
theorem word_y (s : ℕ) (hs : 0 < s) (hsm : s < 6 * q) : word (y q s) = point q 0 s := by
  simp [y, word, point, cast_ne_zero hs hsm]

theorem cast_last : ((6 * q - 1 : ℕ) : ZMod (6 * q)) = -1 := by
  rw [Nat.cast_sub (by have := NeZero.pos (6 * q); omega), ZMod.natCast_self,
    Nat.cast_one, zero_sub]

theorem word_plus : word (x q 0) = point q 1 (6 * q - 1) := by
  simp [word, x, point, cornerPlus, cast_last]

theorem word_minus : word (y q 0) = point q (6 * q - 1) 1 := by
  simp [word, y, point, cornerMinus, cast_last]

theorem phi_word (u : ZMod (6 * q) × ZMod 2) :
    word (phi q hq u) = nu q (surgeryMap 0 (word u)) := by
  rw [phi, markedReturn_word, ← surgery_word (by omega)]
  have hd : 3 ∣ 6 * q := ⟨2 * q, by omega⟩
  simp only [nu, voltage, if_pos hd, Matrix.cons_val_zero]

omit [NeZero (6 * q)] in
theorem surgery_x (s : ℕ) (hs : 0 < s) (hsm : s + 1 < 6 * q) :
    surgeryMap 0 (point q s 0) = point q (s + 1) 0 := by
  have h0 : (s : ZMod (6 * q)) ≠ 0 := cast_ne_zero hs (by omega)
  have hn : (s : ZMod (6 * q)) ≠ -1 := by
    intro h
    have hh := cast_ne_zero (m := 6 * q) (n := s + 1) (by omega) hsm
    apply hh
    simp [Nat.cast_add, h]
  simp [point, surgery_zero_x _ h0, hn]

omit [NeZero (6 * q)] in
theorem surgery_y (s : ℕ) (hs : 0 < s) (hsm : s + 1 < 6 * q) :
    surgeryMap 0 (point q 0 s) = point q 0 (s + 1) := by
  have h0 : (s : ZMod (6 * q)) ≠ 0 := cast_ne_zero hs (by omega)
  have hn : (s : ZMod (6 * q)) ≠ -1 := by
    intro h
    have hh := cast_ne_zero (m := 6 * q) (n := s + 1) (by omega) hsm
    apply hh
    simp [Nat.cast_add, h]
  simp [point, surgery_zero_y (by omega) _ h0, hn]

theorem phi_x_low (s : ℕ) (hs : 0 < s) (hsm : s < 4 * q - 1) :
    phi q hq (x q s) = x q (s + 2 * q + 1) := by
  apply word_injective (by omega)
  rw [phi_word, word_x q s hs (by omega), surgery_x q s hs (by omega),
    nu_x_low q hq (s + 1) (by omega) (by omega), word_x q _ (by omega) (by omega)]
  congr 1; omega

theorem phi_x_middle : phi q hq (x q (4 * q - 1)) = x q (2 * q) := by
  apply word_injective (by omega)
  rw [phi_word, word_x q _ (by omega) (by omega), surgery_x q _ (by omega) (by omega),
    show 4 * q - 1 + 1 = 4 * q by omega, nu_x_middle q hq,
    word_x q _ (by omega) (by omega)]

theorem phi_x_high (s : ℕ) (hs : 4 * q ≤ s) (hsm : s < 6 * q - 1) :
    phi q hq (x q s) = y q (3 * (6 * q - s - 1)) := by
  apply word_injective (by omega)
  rw [phi_word, word_x q _ (by omega) (by omega), surgery_x q _ (by omega) (by omega),
    nu_x_high q hq (s + 1) (by omega) (by omega), word_y q _ (by omega) (by omega)]
  congr 2

theorem phi_x_last : phi q hq (x q (6 * q - 1)) = y q 4 := by
  apply word_injective (by omega)
  rw [phi_word, word_x q _ (by omega) (by omega)]
  have hs : surgeryMap 0 (point q (6 * q - 1) 0) = point q (6 * q - 1) 1 := by
    have h0 : (-1 : ZMod (6 * q)) ≠ 0 := neg_ne_zero.mpr (one_ne_zero_of_four_le (by omega))
    simpa [point, cast_last, cornerMinus] using surgery_zero_x (-1 : ZMod (6 * q)) h0
  rw [hs, nu_cornerMinus q hq, word_y q _ (by omega) (by omega)]

theorem phi_y_fixed (s : ℕ) (hs : 0 < s) (hsm : s + 1 < 6 * q)
    (hs3 : (s + 1) % 3 ≠ 0) (hs4 : s ≠ 3) (hse : s ≠ 6 * q - 5) :
    phi q hq (y q s) = y q (s + 1) := by
  apply word_injective (by omega)
  rw [phi_word, word_y q _ hs (by omega), surgery_y q s hs hsm,
    nu_y_fixed q hq (s + 1) (by omega) hsm hs3 (by omega) (by omega),
    word_y q _ (by omega) hsm]

theorem phi_y_axis (r : ℕ) (hr : 0 < r) (hrm : r < 2 * q) :
    phi q hq (y q (3 * r - 1)) = x q (2 * q - r) := by
  apply word_injective (by omega)
  rw [phi_word, word_y q _ (by omega) (by omega),
    surgery_y q _ (by omega) (by omega), show 3 * r - 1 + 1 = 3 * r by omega,
    nu_y_axis q hq r hr hrm, word_x q _ (by omega) (by omega)]

theorem phi_y_three : phi q hq (y q 3) = y q 0 := by
  apply word_injective (by omega)
  rw [phi_word, word_y q _ (by omega) (by omega), surgery_y q _ (by omega) (by omega),
    nu_y_four q hq, word_minus]

theorem phi_y_end : phi q hq (y q (6 * q - 5)) = x q 0 := by
  apply word_injective (by omega)
  rw [phi_word, word_y q _ (by omega) (by omega), surgery_y q _ (by omega) (by omega),
    show 6 * q - 5 + 1 = 6 * q - 4 by omega, nu_y_end q hq, word_plus]

theorem phi_y_last : phi q hq (y q (6 * q - 1)) = y q (6 * q - 4) := by
  apply word_injective (by omega)
  rw [phi_word, word_y q _ (by omega) (by omega)]
  have hs : surgeryMap 0 (point q 0 (6 * q - 1)) = point q 1 (6 * q - 1) := by
    have h0 : (-1 : ZMod (6 * q)) ≠ 0 := neg_ne_zero.mpr (one_ne_zero_of_four_le (by omega))
    simpa [point, cast_last, cornerPlus] using surgery_zero_y (m := 6 * q) (by omega) (-1) h0
  rw [hs, nu_cornerPlus q hq, word_y q _ (by omega) (by omega)]

theorem phi_plus : phi q hq (x q 0) = x q (2 * q + 1) := by
  apply word_injective (by omega)
  rw [phi_word]
  have hs : surgeryMap 0 (word (x q 0)) = point q 1 0 := by
    simpa [word, x, point] using (surgery_zero_corners (m := 6 * q) (by omega)).1
  rw [hs, nu_x_low q hq 1 (by omega) (by omega), word_x q _ (by omega) (by omega)]
  congr 1; omega

theorem phi_minus : phi q hq (y q 0) = y q 1 := by
  apply word_injective (by omega)
  rw [phi_word]
  have hs : surgeryMap 0 (word (y q 0)) = point q 0 1 := by
    simpa [word, y, point] using (surgery_zero_corners (m := 6 * q) (by omega)).2
  rw [hs, nu_y_fixed q hq 1 (by omega) (by omega) (by decide) (by decide) (by omega),
    word_y q _ (by omega) (by omega)]

end TorusEven.Entry.Star.Divisible
