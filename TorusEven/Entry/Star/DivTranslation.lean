-- STATUS: main-path
import TorusEven.Entry.Star.Hitting

namespace TorusEven.Entry.Star.Divisible

open Surgery

variable (q : ℕ) [NeZero (6 * q)]

def point (a b : ℕ) : Plane (6 * q) := (a, b)

noncomputable def nu : Plane (6 * q) → Plane (6 * q) :=
  ret (Equiv.addRight (1, 3)) (support (6 * q))

private theorem point_eq {a b c d : ℕ}
    (ha : a < 4 * (6 * q)) (hb : b < 4 * (6 * q))
    (hc : c < 6 * q) (hd : d < 6 * q)
    (hx : EqFour (6 * q) a c) (hy : EqFour (6 * q) b d) :
    point q a b = point q c d :=
  Prod.ext ((natCast_eq_iff_four ha hc).mpr hx) ((natCast_eq_iff_four hb hd).mpr hy)

variable (hq : 2 ≤ q)
include hq

theorem nu_x_low (s : ℕ) (hs0 : 0 < s) (hs : s < 4 * q) :
    nu q (point q (s) (0)) = point q (s + 2 * q) (0) := by
  have h := translation_ret_nat (m := 6 * q) (by omega) 3 (s) (0) (2 * q)
    (by apply (hitTest_iff (by omega) (by omega) (by omega)).mpr
        unfold hitTest EqFour; omega)
    (by omega) (by omega) (by omega)
    (by unfold hitTest EqFour; omega)
    (by intro k hk hkn; unfold hitTest EqFour; omega)
  exact h.trans (by apply point_eq <;> first | omega | (unfold EqFour; omega))

theorem nu_x_middle :
    nu q (point q (4 * q) (0)) = point q (2 * q) (0) := by
  have h := translation_ret_nat (m := 6 * q) (by omega) 3 (4 * q) (0) (4 * q)
    (by apply (hitTest_iff (by omega) (by omega) (by omega)).mpr
        unfold hitTest EqFour; omega)
    (by omega) (by omega) (by omega)
    (by unfold hitTest EqFour; omega)
    (by intro k hk hkn; unfold hitTest EqFour; omega)
  exact h.trans (by apply point_eq <;> first | omega | (unfold EqFour; omega))

theorem nu_x_high (s : ℕ) (hs : 4 * q < s) (hsm : s < 6 * q) :
    nu q (point q (s) (0)) = point q (0) (3 * (6 * q - s)) := by
  have h := translation_ret_nat (m := 6 * q) (by omega) 3 (s) (0) (6 * q - s)
    (by apply (hitTest_iff (by omega) (by omega) (by omega)).mpr
        unfold hitTest EqFour; omega)
    (by omega) (by omega) (by omega)
    (by unfold hitTest EqFour; omega)
    (by intro k hk hkn; unfold hitTest EqFour; omega)
  exact h.trans (by apply point_eq <;> first | omega | (unfold EqFour; omega))

theorem nu_y_axis (r : ℕ) (hr0 : 0 < r) (hr : r < 2 * q) :
    nu q (point q (0) (3 * r)) = point q (2 * q - r) (0) := by
  have h := translation_ret_nat (m := 6 * q) (by omega) 3 (0) (3 * r) (2 * q - r)
    (by apply (hitTest_iff (by omega) (by omega) (by omega)).mpr
        unfold hitTest EqFour; omega)
    (by omega) (by omega) (by omega)
    (by unfold hitTest EqFour; omega)
    (by intro k hk hkn; unfold hitTest EqFour; omega)
  exact h.trans (by apply point_eq <;> first | omega | (unfold EqFour; omega))

theorem nu_y_fixed (s : ℕ) (hs0 : 0 < s) (hsm : s < 6 * q)
    (hs3 : s % 3 ≠ 0) (hs4 : s ≠ 4) (hsend : s ≠ 6 * q - 4) :
    nu q (point q (0) (s)) = point q (0) (s) := by
  have h := translation_ret_nat (m := 6 * q) (by omega) 3 (0) (s) (6 * q)
    (by apply (hitTest_iff (by omega) (by omega) (by omega)).mpr
        unfold hitTest EqFour; omega)
    (by omega) (by omega) (by omega)
    (by unfold hitTest EqFour; omega)
    (by intro k hk hkn; unfold hitTest EqFour; omega)
  exact h.trans (by apply point_eq <;> first | omega | (unfold EqFour; omega))

theorem nu_y_four :
    nu q (point q (0) (4)) = point q (6 * q - 1) (1) := by
  have h := translation_ret_nat (m := 6 * q) (by omega) 3 (0) (4) (6 * q - 1)
    (by apply (hitTest_iff (by omega) (by omega) (by omega)).mpr
        unfold hitTest EqFour; omega)
    (by omega) (by omega) (by omega)
    (by unfold hitTest EqFour; omega)
    (by intro k hk hkn; unfold hitTest EqFour; omega)
  exact h.trans (by apply point_eq <;> first | omega | (unfold EqFour; omega))

theorem nu_y_end :
    nu q (point q (0) (6 * q - 4)) = point q (1) (6 * q - 1) := by
  have h := translation_ret_nat (m := 6 * q) (by omega) 3 (0) (6 * q - 4) (1)
    (by apply (hitTest_iff (by omega) (by omega) (by omega)).mpr
        unfold hitTest EqFour; omega)
    (by omega) (by omega) (by omega)
    (by unfold hitTest EqFour; omega)
    (by intro k hk hkn; unfold hitTest EqFour; omega)
  exact h.trans (by apply point_eq <;> first | omega | (unfold EqFour; omega))

theorem nu_cornerPlus :
    nu q (point q (1) (6 * q - 1)) = point q (0) (6 * q - 4) := by
  have h := translation_ret_nat (m := 6 * q) (by omega) 3 (1) (6 * q - 1) (6 * q - 1)
    (by apply (hitTest_iff (by omega) (by omega) (by omega)).mpr
        unfold hitTest EqFour; omega)
    (by omega) (by omega) (by omega)
    (by unfold hitTest EqFour; omega)
    (by intro k hk hkn; unfold hitTest EqFour; omega)
  exact h.trans (by apply point_eq <;> first | omega | (unfold EqFour; omega))

theorem nu_cornerMinus :
    nu q (point q (6 * q - 1) (1)) = point q (0) (4) := by
  have h := translation_ret_nat (m := 6 * q) (by omega) 3 (6 * q - 1) (1) (1)
    (by apply (hitTest_iff (by omega) (by omega) (by omega)).mpr
        unfold hitTest EqFour; omega)
    (by omega) (by omega) (by omega)
    (by unfold hitTest EqFour; omega)
    (by intro k hk hkn; unfold hitTest EqFour; omega)
  exact h.trans (by apply point_eq <;> first | omega | (unfold EqFour; omega))

end TorusEven.Entry.Star.Divisible
