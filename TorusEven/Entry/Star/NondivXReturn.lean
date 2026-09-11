-- STATUS: main-path
import TorusEven.Entry.Star.NondivMarked

namespace TorusEven.Entry.Star.Nondivisible

open Surgery

variable (k : ℕ) [NeZero (2 * k)] (hk : 4 ≤ k)

def horizontal : Set (ZMod (2 * k) × ZMod 2) := {u | u.2 = 0 ∧ u.1 ≠ 0}

instance horizontalDecidable : DecidablePred (· ∈ horizontal k) :=
  fun u => inferInstanceAs (Decidable (u.2 = 0 ∧ u.1 ≠ 0))

omit [NeZero (2 * k)] in
theorem x_mem (s : ℕ) (hs : 0 < s) (hsm : s < 2 * k) : x k s ∈ horizontal k := by
  simp [horizontal, x, cast_ne_zero hs hsm]

omit [NeZero (2 * k)] in
theorem y_not_mem (s : ℕ) : y k s ∉ horizontal k := by simp [horizontal, y]

omit [NeZero (2 * k)] in
theorem plus_not_mem : x k 0 ∉ horizontal k := by simp [horizontal, x]

private theorem first_return {s t n : ℕ} (hs : 0 < s) (hsm : s < 2 * k)
    (ht : 0 < t) (htm : t < 2 * k) (hn : 0 < n)
    (hr : (phi k hk)^[n] (x k s) = x k t)
    (hf : ∀ t, 0 < t → t < n → (phi k hk)^[t] (x k s) ∉ horizontal k) :
    retTime (phi k hk) (horizontal k) (x k s) = n ∧
      ret (phi k hk) (horizontal k) (x k s) = x k t := by
  have he := retTime_eq_of_first (phi k hk) (horizontal k) (x_mem k s hs hsm) hn
    (hr ▸ x_mem k t ht htm) hf
  exact ⟨he, by simp only [ret, he, hr]⟩

variable (hd : ¬ 3 ∣ 2 * k)
include hd

theorem return_x_low (s : ℕ) (hs : 0 < s) (hsm : s < k - 1) :
    retTime (phi k hk) (horizontal k) (x k s) = 1 ∧
      ret (phi k hk) (horizontal k) (x k s) = x k (s + k + 1) := by
  apply first_return k hk hs (by omega) (by omega) (by omega) (by omega)
    (by simpa using phi_x_low k hk hd s hs hsm)
  intro t ht htn
  omega

theorem return_x_middle :
    retTime (phi k hk) (horizontal k) (x k (k - 1)) = 1 ∧
      ret (phi k hk) (horizontal k) (x k (k - 1)) = x k k := by
  apply first_return k hk (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simpa using phi_x_middle k hk hd)
  intro t ht htn
  omega

theorem return_x_high (s : ℕ) (hs : k ≤ s) (hsm : s < 2 * k - 2) :
    retTime (phi k hk) (horizontal k) (x k s) = 3 ∧
      ret (phi k hk) (horizontal k) (x k s) = x k (s - k + 2) := by
  let r := s - k + 1
  have hr : 0 < r ∧ r < k - 1 := by dsimp [r]; omega
  have h0 : phi k hk (x k s) = y k (2 * r) := by
    convert phi_x_high k hk hd s hs (by omega) using 1; congr 1; dsimp [r]; omega
  have h1 : phi k hk (y k (2 * r)) = y k (2 * r + 1) :=
    phi_y_fixed k hk hd _ (by omega) (by omega) (by omega)
  have h2 : phi k hk (y k (2 * r + 1)) = x k (s - k + 2) := by
    convert phi_y_axis k hk hd (r + 1) (by omega) (by omega) using 1
  apply first_return k hk (by omega) (by omega) (by omega) (by omega) (by omega)
  · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, h0, h1, h2]
  · intro t ht htn
    interval_cases t <;>
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, h0, h1,
        y_not_mem, not_false_eq_true]

theorem return_x_penultimate :
    retTime (phi k hk) (horizontal k) (x k (2 * k - 2)) = 4 ∧
      ret (phi k hk) (horizontal k) (x k (2 * k - 2)) = x k (k + 1) := by
  have h0 : phi k hk (x k (2 * k - 2)) = y k (2 * k - 2) := by
    convert phi_x_high k hk hd (2 * k - 2) (by omega) (by omega) using 1; congr 1; omega
  apply first_return k hk (by omega) (by omega) (by omega) (by omega) (by omega)
  · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, h0,
      phi_y_penultimate k hk hd, phi_minus k hk hd, phi_plus k hk hd]
  · intro t ht htn
    interval_cases t <;>
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, h0,
        phi_y_penultimate k hk hd, phi_minus k hk hd, y_not_mem, plus_not_mem, not_false_eq_true]

theorem return_x_last :
    retTime (phi k hk) (horizontal k) (x k (2 * k - 1)) = 3 ∧
      ret (phi k hk) (horizontal k) (x k (2 * k - 1)) = x k 1 := by
  have h2 : phi k hk (y k 1) = x k 1 := by
    simpa using phi_y_axis k hk hd 1 (by omega) (by omega)
  apply first_return k hk (by omega) (by omega) (by omega) (by omega) (by omega)
  · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
      phi_x_last k hk hd, phi_y_last k hk hd, h2]
  · intro t ht htn
    interval_cases t <;>
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
        phi_x_last k hk hd, phi_y_last k hk hd, y_not_mem, not_false_eq_true]

end TorusEven.Entry.Star.Nondivisible
