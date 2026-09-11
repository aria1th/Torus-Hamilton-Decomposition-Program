-- STATUS: main-path
import TorusEven.Entry.Star.NondivTranslation

namespace TorusEven.Entry.Star.Nondivisible

variable (k : ℕ) [NeZero (2 * k)] (hk : 4 ≤ k)

def x (s : ℕ) : ZMod (2 * k) × ZMod 2 := (s, 0)
def y (s : ℕ) : ZMod (2 * k) × ZMod 2 := (s, 1)

noncomputable def phi : Equiv.Perm (ZMod (2 * k) × ZMod 2) := markedReturn (by omega)

omit [NeZero (2 * k)] in
theorem word_x (s : ℕ) (hs : 0 < s) (hsm : s < 2 * k) : word (x k s) = point k s 0 := by
  simp [x, word, point, cast_ne_zero hs hsm]

omit [NeZero (2 * k)] in
theorem word_y (s : ℕ) (hs : 0 < s) (hsm : s < 2 * k) : word (y k s) = point k 0 s := by
  simp [y, word, point, cast_ne_zero hs hsm]

theorem cast_last : ((2 * k - 1 : ℕ) : ZMod (2 * k)) = -1 := by
  rw [Nat.cast_sub (by have := NeZero.pos (2 * k); omega), ZMod.natCast_self,
    Nat.cast_one, zero_sub]

theorem word_plus : word (x k 0) = point k 1 (2 * k - 1) := by
  simp [word, x, point, cornerPlus, cast_last]

theorem word_minus : word (y k 0) = point k (2 * k - 1) 1 := by
  simp [word, y, point, cornerMinus, cast_last]

omit [NeZero (2 * k)] in
theorem surgery_x (s : ℕ) (hs : 0 < s) (hsm : s + 1 < 2 * k) :
    surgeryMap 0 (point k s 0) = point k (s + 1) 0 := by
  have h0 : (s : ZMod (2 * k)) ≠ 0 := cast_ne_zero hs (by omega)
  have hn : (s : ZMod (2 * k)) ≠ -1 := by
    intro h
    have hh := cast_ne_zero (m := 2 * k) (n := s + 1) (by omega) hsm
    apply hh
    simp [Nat.cast_add, h]
  simp [point, surgery_zero_x _ h0, hn]

omit [NeZero (2 * k)] in
theorem surgery_y (s : ℕ) (hs : 0 < s) (hsm : s + 1 < 2 * k) :
    surgeryMap 0 (point k 0 s) = point k 0 (s + 1) := by
  have h0 : (s : ZMod (2 * k)) ≠ 0 := cast_ne_zero hs (by omega)
  have hn : (s : ZMod (2 * k)) ≠ -1 := by
    intro h
    have hh := cast_ne_zero (m := 2 * k) (n := s + 1) (by omega) hsm
    apply hh
    simp [Nat.cast_add, h]
  simp [point, surgery_zero_y (by omega) _ h0, hn]

variable (hd : ¬ 3 ∣ 2 * k)
include hd

theorem phi_word (u : ZMod (2 * k) × ZMod 2) :
    word (phi k hk u) = nu k (surgeryMap 0 (word u)) := by
  rw [phi, markedReturn_word, ← surgery_word (by omega)]
  simp only [nu, voltage, if_neg hd, Matrix.cons_val_zero]

theorem phi_x_low (s : ℕ) (hs : 0 < s) (hsm : s < k - 1) :
    phi k hk (x k s) = x k (s + k + 1) := by
  apply word_injective (by omega)
  rw [phi_word k hk hd, word_x k s hs (by omega), surgery_x k s hs (by omega),
    nu_x_low k hk (s + 1) (by omega) (by omega), word_x k _ (by omega) (by omega)]
  congr 1; omega

theorem phi_x_middle : phi k hk (x k (k - 1)) = x k k := by
  apply word_injective (by omega)
  rw [phi_word k hk hd, word_x k _ (by omega) (by omega),
    surgery_x k _ (by omega) (by omega), show k - 1 + 1 = k by omega,
    nu_x_middle k hk, word_x k _ (by omega) (by omega)]

theorem phi_x_high (s : ℕ) (hs : k ≤ s) (hsm : s < 2 * k - 1) :
    phi k hk (x k s) = y k (2 * s - 2 * k + 2) := by
  apply word_injective (by omega)
  rw [phi_word k hk hd, word_x k _ (by omega) (by omega),
    surgery_x k _ (by omega) (by omega), nu_x_high k hk (s + 1) (by omega) (by omega),
    word_y k _ (by omega) (by omega)]
  congr 1; omega

theorem phi_x_last : phi k hk (x k (2 * k - 1)) = y k (2 * k - 1) := by
  apply word_injective (by omega)
  rw [phi_word k hk hd, word_x k _ (by omega) (by omega)]
  have hs : surgeryMap 0 (point k (2 * k - 1) 0) = point k (2 * k - 1) 1 := by
    have h0 : (-1 : ZMod (2 * k)) ≠ 0 := neg_ne_zero.mpr (one_ne_zero_of_four_le (by omega))
    simpa [point, cast_last, cornerMinus] using surgery_zero_x (-1 : ZMod (2 * k)) h0
  rw [hs, nu_cornerMinus k hk, word_y k _ (by omega) (by omega)]

theorem phi_y_fixed (s : ℕ) (hs : 0 < s) (hsm : s < 2 * k - 2) (hs2 : s % 2 = 0) :
    phi k hk (y k s) = y k (s + 1) := by
  apply word_injective (by omega)
  rw [phi_word k hk hd, word_y k _ hs (by omega), surgery_y k s hs (by omega),
    nu_y_fixed k hk (s + 1) (by omega) (by omega) (by omega) (by omega) (by omega),
    word_y k _ (by omega) (by omega)]

theorem phi_y_axis (r : ℕ) (hr : 0 < r) (hrm : r < k) :
    phi k hk (y k (2 * r - 1)) = x k r := by
  apply word_injective (by omega)
  rw [phi_word k hk hd, word_y k _ (by omega) (by omega),
    surgery_y k _ (by omega) (by omega), show 2 * r - 1 + 1 = 2 * r by omega,
    nu_y_axis k hk r hr hrm, word_x k _ (by omega) (by omega)]

theorem phi_y_penultimate : phi k hk (y k (2 * k - 2)) = y k 0 := by
  apply word_injective (by omega)
  rw [phi_word k hk hd, word_y k _ (by omega) (by omega),
    surgery_y k _ (by omega) (by omega), show 2 * k - 2 + 1 = 2 * k - 1 by omega,
    nu_y_last k hk, word_minus]

theorem phi_y_last : phi k hk (y k (2 * k - 1)) = y k 1 := by
  apply word_injective (by omega)
  rw [phi_word k hk hd, word_y k _ (by omega) (by omega)]
  have hs : surgeryMap 0 (point k 0 (2 * k - 1)) = point k 1 (2 * k - 1) := by
    have h0 : (-1 : ZMod (2 * k)) ≠ 0 := neg_ne_zero.mpr (one_ne_zero_of_four_le (by omega))
    simpa [point, cast_last, cornerPlus] using surgery_zero_y (m := 2 * k) (by omega) (-1) h0
  rw [hs, nu_cornerPlus k hk, word_y k _ (by omega) (by omega)]

theorem phi_plus : phi k hk (x k 0) = x k (k + 1) := by
  apply word_injective (by omega)
  rw [phi_word k hk hd]
  have hs : surgeryMap 0 (word (x k 0)) = point k 1 0 := by
    simpa [word, x, point] using (surgery_zero_corners (m := 2 * k) (by omega)).1
  rw [hs, nu_x_low k hk 1 (by omega) (by omega), word_x k _ (by omega) (by omega)]
  congr 1; omega

theorem phi_minus : phi k hk (y k 0) = x k 0 := by
  apply word_injective (by omega)
  rw [phi_word k hk hd]
  have hs : surgeryMap 0 (word (y k 0)) = point k 0 1 := by
    simpa [word, y, point] using (surgery_zero_corners (m := 2 * k) (by omega)).2
  rw [hs, nu_y_one k hk, word_plus]

end TorusEven.Entry.Star.Nondivisible
