-- STATUS: main-path
import TorusEven.Entry.Star.Hitting

namespace TorusEven.Entry.Star.Nondivisible

open Surgery

variable (k : ℕ) [NeZero (2 * k)]

def point (a b : ℕ) : Plane (2 * k) := (a, b)

noncomputable def nu : Plane (2 * k) → Plane (2 * k) :=
  ret (Equiv.addRight (1, -2)) (support (2 * k))

private theorem point_eq {a b c d : ℕ}
    (ha : a < 4 * (2 * k)) (hb : b < 4 * (2 * k))
    (hc : c < 2 * k) (hd : d < 2 * k)
    (hx : EqFour (2 * k) a c) (hy : EqFour (2 * k) b d) :
    point k a b = point k c d :=
  Prod.ext ((natCast_eq_iff_four ha hc).mpr hx) ((natCast_eq_iff_four hb hd).mpr hy)

variable (hk : 4 ≤ k)
include hk

theorem nu_x_low (s : ℕ) (hs0 : 0 < s) (hs : s < k) :
    nu k (point k s 0) = point k (s + k) 0 := by
  have h := translation_ret_neg_two_nat (m := 2 * k) (by omega) s 0 k
    (by apply (hitTest_iff (by omega) (by omega) (by omega)).mpr
        unfold hitTest EqFour; omega)
    (by omega) (by omega) (by omega) (by omega)
    (by unfold hitTest EqFour; omega)
    (by intro t ht htn; unfold hitTest EqFour; omega)
  exact h.trans (by apply point_eq <;> first | omega | (unfold EqFour; omega))

theorem nu_x_middle :
    nu k (point k k 0) = point k k 0 := by
  have h := translation_ret_neg_two_nat (m := 2 * k) (by omega) k 0 (2 * k)
    (by apply (hitTest_iff (by omega) (by omega) (by omega)).mpr
        unfold hitTest EqFour; omega)
    (by omega) (by omega) (by omega) (by omega)
    (by unfold hitTest EqFour; omega)
    (by intro t ht htn; unfold hitTest EqFour; omega)
  exact h.trans (by apply point_eq <;> first | omega | (unfold EqFour; omega))

theorem nu_x_high (s : ℕ) (hs : k < s) (hsm : s < 2 * k) :
    nu k (point k s 0) = point k 0 (2 * s - 2 * k) := by
  have h := translation_ret_neg_two_nat (m := 2 * k) (by omega) s 0 (2 * k - s)
    (by apply (hitTest_iff (by omega) (by omega) (by omega)).mpr
        unfold hitTest EqFour; omega)
    (by omega) (by omega) (by omega) (by omega)
    (by unfold hitTest EqFour; omega)
    (by intro t ht htn; unfold hitTest EqFour; omega)
  exact h.trans (by apply point_eq <;> first | omega | (unfold EqFour; omega))

theorem nu_y_axis (r : ℕ) (hr0 : 0 < r) (hr : r < k) :
    nu k (point k 0 (2 * r)) = point k r 0 := by
  have h := translation_ret_neg_two_nat (m := 2 * k) (by omega) 0 (2 * r) r
    (by apply (hitTest_iff (by omega) (by omega) (by omega)).mpr
        unfold hitTest EqFour; omega)
    (by omega) (by omega) (by omega) (by omega)
    (by unfold hitTest EqFour; omega)
    (by intro t ht htn; unfold hitTest EqFour; omega)
  exact h.trans (by apply point_eq <;> first | omega | (unfold EqFour; omega))

theorem nu_y_fixed (s : ℕ) (hs0 : 0 < s) (hsm : s < 2 * k)
    (hs2 : s % 2 ≠ 0) (hs1 : s ≠ 1) (hsend : s ≠ 2 * k - 1) :
    nu k (point k 0 s) = point k 0 s := by
  have h := translation_ret_neg_two_nat (m := 2 * k) (by omega) 0 s (2 * k)
    (by apply (hitTest_iff (by omega) (by omega) (by omega)).mpr
        unfold hitTest EqFour; omega)
    (by omega) (by omega) (by omega) (by omega)
    (by unfold hitTest EqFour; omega)
    (by intro t ht htn; unfold hitTest EqFour; omega)
  exact h.trans (by apply point_eq <;> first | omega | (unfold EqFour; omega))

theorem nu_y_one :
    nu k (point k 0 1) = point k 1 (2 * k - 1) := by
  have h := translation_ret_neg_two_nat (m := 2 * k) (by omega) 0 1 1
    (by apply (hitTest_iff (by omega) (by omega) (by omega)).mpr
        unfold hitTest EqFour; omega)
    (by omega) (by omega) (by omega) (by omega)
    (by unfold hitTest EqFour; omega)
    (by intro t ht htn; unfold hitTest EqFour; omega)
  exact h.trans (by apply point_eq <;> first | omega | (unfold EqFour; omega))

theorem nu_y_last :
    nu k (point k 0 (2 * k - 1)) = point k (2 * k - 1) 1 := by
  have h := translation_ret_neg_two_nat (m := 2 * k) (by omega) 0 (2 * k - 1) (2 * k - 1)
    (by apply (hitTest_iff (by omega) (by omega) (by omega)).mpr
        unfold hitTest EqFour; omega)
    (by omega) (by omega) (by omega) (by omega)
    (by unfold hitTest EqFour; omega)
    (by intro t ht htn; unfold hitTest EqFour; omega)
  exact h.trans (by apply point_eq <;> first | omega | (unfold EqFour; omega))

theorem nu_cornerPlus :
    nu k (point k 1 (2 * k - 1)) = point k 0 1 := by
  have h := translation_ret_neg_two_nat (m := 2 * k) (by omega) 1 (2 * k - 1) (2 * k - 1)
    (by apply (hitTest_iff (by omega) (by omega) (by omega)).mpr
        unfold hitTest EqFour; omega)
    (by omega) (by omega) (by omega) (by omega)
    (by unfold hitTest EqFour; omega)
    (by intro t ht htn; unfold hitTest EqFour; omega)
  exact h.trans (by apply point_eq <;> first | omega | (unfold EqFour; omega))

theorem nu_cornerMinus :
    nu k (point k (2 * k - 1) 1) = point k 0 (2 * k - 1) := by
  have h := translation_ret_neg_two_nat (m := 2 * k) (by omega) (2 * k - 1) 1 1
    (by apply (hitTest_iff (by omega) (by omega) (by omega)).mpr
        unfold hitTest EqFour; omega)
    (by omega) (by omega) (by omega) (by omega)
    (by unfold hitTest EqFour; omega)
    (by intro t ht htn; unfold hitTest EqFour; omega)
  exact h.trans (by apply point_eq <;> first | omega | (unfold EqFour; omega))

end TorusEven.Entry.Star.Nondivisible
