-- STATUS: main-path
import TorusEven.Entry.Star.DivMarked

namespace TorusEven.Entry.Star.Divisible

open Surgery

variable (q : ℕ) [NeZero (6 * q)] (hq : 2 ≤ q)

def horizontal : Set (ZMod (6 * q) × ZMod 2) := {u | u.2 = 0 ∧ u.1 ≠ 0}

instance horizontalDecidable : DecidablePred (· ∈ horizontal q) :=
  fun u => inferInstanceAs (Decidable (u.2 = 0 ∧ u.1 ≠ 0))

omit [NeZero (6 * q)] in
theorem x_mem (s : ℕ) (hs : 0 < s) (hsm : s < 6 * q) : x q s ∈ horizontal q := by
  simp [horizontal, x, cast_ne_zero hs hsm]

omit [NeZero (6 * q)] in
theorem y_not_mem (s : ℕ) : y q s ∉ horizontal q := by simp [horizontal, y]

omit [NeZero (6 * q)] in
theorem plus_not_mem : x q 0 ∉ horizontal q := by simp [horizontal, x]

private theorem first_return {s t n : ℕ} (hs : 0 < s) (hsm : s < 6 * q)
    (ht : 0 < t) (htm : t < 6 * q) (hn : 0 < n)
    (hr : (phi q hq)^[n] (x q s) = x q t)
    (hf : ∀ k, 0 < k → k < n → (phi q hq)^[k] (x q s) ∉ horizontal q) :
    retTime (phi q hq) (horizontal q) (x q s) = n ∧
      ret (phi q hq) (horizontal q) (x q s) = x q t := by
  have he := retTime_eq_of_first (phi q hq) (horizontal q) (x_mem q s hs hsm) hn
    (hr ▸ x_mem q t ht htm) hf
  exact ⟨he, by simp only [ret, he, hr]⟩

theorem return_x_low (s : ℕ) (hs : 0 < s) (hsm : s < 4 * q - 1) :
    retTime (phi q hq) (horizontal q) (x q s) = 1 ∧
      ret (phi q hq) (horizontal q) (x q s) = x q (s + 2 * q + 1) := by
  apply first_return q hq hs (by omega) (by omega) (by omega) (by omega)
    (by simpa using phi_x_low q hq s hs hsm)
  intro k hk hkn
  omega

theorem return_x_middle :
    retTime (phi q hq) (horizontal q) (x q (4 * q - 1)) = 1 ∧
      ret (phi q hq) (horizontal q) (x q (4 * q - 1)) = x q (2 * q) := by
  apply first_return q hq (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simpa using phi_x_middle q hq)
  intro k hk hkn
  omega

theorem return_x_four :
    retTime (phi q hq) (horizontal q) (x q (4 * q)) = 5 ∧
      ret (phi q hq) (horizontal q) (x q (4 * q)) = x q 1 := by
  have h0 : phi q hq (x q (4 * q)) = y q (6 * q - 3) := by
    convert phi_x_high q hq (4 * q) (by omega) (by omega) using 1; congr 1; omega
  have h1 : phi q hq (y q (6 * q - 3)) = y q (6 * q - 2) := by
    convert phi_y_fixed q hq (6 * q - 3) (by omega) (by omega)
      (by omega) (by omega) (by omega) using 1; congr 1; omega
  have h2 : phi q hq (y q (6 * q - 2)) = y q (6 * q - 1) := by
    convert phi_y_fixed q hq (6 * q - 2) (by omega) (by omega)
      (by omega) (by omega) (by omega) using 1; congr 1; omega
  have h4 : phi q hq (y q (6 * q - 4)) = x q 1 := by
    simpa only [show 3 * (2 * q - 1) - 1 = 6 * q - 4 by omega,
      show 2 * q - (2 * q - 1) = 1 by omega] using
      phi_y_axis q hq (2 * q - 1) (by omega) (by omega)
  apply first_return q hq (by omega) (by omega) (by omega) (by omega) (by omega)
  · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, h0, h1, h2,
      phi_y_last, h4]
  · intro k hk hkn
    interval_cases k <;>
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, h0, h1, h2,
        phi_y_last, y_not_mem, not_false_eq_true]

theorem return_x_four_succ :
    retTime (phi q hq) (horizontal q) (x q (4 * q + 1)) = 4 ∧
      ret (phi q hq) (horizontal q) (x q (4 * q + 1)) = x q (2 * q + 1) := by
  have h0 : phi q hq (x q (4 * q + 1)) = y q (6 * q - 6) := by
    convert phi_x_high q hq (4 * q + 1) (by omega) (by omega) using 1; congr 1; omega
  have h1 : phi q hq (y q (6 * q - 6)) = y q (6 * q - 5) := by
    convert phi_y_fixed q hq (6 * q - 6) (by omega) (by omega)
      (by omega) (by omega) (by omega) using 1; congr 1; omega
  apply first_return q hq (by omega) (by omega) (by omega) (by omega) (by omega)
  · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, h0, h1,
      phi_y_end, phi_plus]
  · intro k hk hkn
    interval_cases k <;>
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, h0, h1,
        phi_y_end, y_not_mem, plus_not_mem, not_false_eq_true]

theorem return_x_high (s : ℕ) (hs : 4 * q + 2 ≤ s) (hsm : s < 6 * q - 2) :
    retTime (phi q hq) (horizontal q) (x q s) = 4 ∧
      ret (phi q hq) (horizontal q) (x q s) = x q (s - 4 * q) := by
  let r := 6 * q - s - 1
  have hr : 2 ≤ r ∧ r < 2 * q - 2 := by dsimp [r]; omega
  have h0 : phi q hq (x q s) = y q (3 * r) := phi_x_high q hq s (by omega) (by omega)
  have h1 : phi q hq (y q (3 * r)) = y q (3 * r + 1) :=
    phi_y_fixed q hq (3 * r) (by omega) (by omega) (by omega) (by omega) (by omega)
  have h2 : phi q hq (y q (3 * r + 1)) = y q (3 * r + 2) := by
    exact phi_y_fixed q hq (3 * r + 1) (by omega) (by omega)
      (by omega) (by omega) (by omega)
  have h3 : phi q hq (y q (3 * r + 2)) = x q (s - 4 * q) := by
    convert phi_y_axis q hq (r + 1) (by omega) (by omega) using 1; congr 1; dsimp [r]; omega
  apply first_return q hq (by omega) (by omega) (by omega) (by omega) (by omega)
  · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, h0, h1, h2, h3]
  · intro k hk hkn
    interval_cases k <;>
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, h0, h1, h2,
        y_not_mem, not_false_eq_true]

theorem return_x_penultimate :
    retTime (phi q hq) (horizontal q) (x q (6 * q - 2)) = 5 ∧
      ret (phi q hq) (horizontal q) (x q (6 * q - 2)) = x q (2 * q - 1) := by
  have h0 : phi q hq (x q (6 * q - 2)) = y q 3 := by
    convert phi_x_high q hq (6 * q - 2) (by omega) (by omega) using 1; congr 1; omega
  have h3 : phi q hq (y q 1) = y q 2 :=
    phi_y_fixed q hq 1 (by omega) (by omega) (by decide) (by decide) (by omega)
  have h4 : phi q hq (y q 2) = x q (2 * q - 1) := by
    simpa using phi_y_axis q hq 1 (by omega) (by omega)
  apply first_return q hq (by omega) (by omega) (by omega) (by omega) (by omega)
  · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, h0,
      phi_y_three, phi_minus, h3, h4]
  · intro k hk hkn
    interval_cases k <;>
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, h0,
        phi_y_three, phi_minus, h3, y_not_mem, not_false_eq_true]

theorem return_x_last :
    retTime (phi q hq) (horizontal q) (x q (6 * q - 1)) = 3 ∧
      ret (phi q hq) (horizontal q) (x q (6 * q - 1)) = x q (2 * q - 2) := by
  have h1 : phi q hq (y q 4) = y q 5 :=
    phi_y_fixed q hq 4 (by omega) (by omega) (by decide) (by decide) (by omega)
  have h2 : phi q hq (y q 5) = x q (2 * q - 2) := by
    simpa using phi_y_axis q hq 2 (by omega) (by omega)
  apply first_return q hq (by omega) (by omega) (by omega) (by omega) (by omega)
  · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, phi_x_last, h1, h2]
  · intro k hk hkn
    interval_cases k <;>
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, phi_x_last, h1,
        y_not_mem, not_false_eq_true]

end TorusEven.Entry.Star.Divisible
