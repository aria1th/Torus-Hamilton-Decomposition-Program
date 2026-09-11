-- STATUS: main-path
import TorusEven.Entry.Star.NondivXReturn
import TorusEven.Entry.Star.NondivPsi

namespace TorusEven.Entry.Star.Nondivisible

open Surgery

variable (k : ℕ) [NeZero (2 * k)] (hk : 4 ≤ k) (hd : ¬ 3 ∣ 2 * k)

def xReturnIndex (s : ℕ) : ℕ :=
  if s < k - 1 then s + k + 1 else
  if s = k - 1 then k else
  if s < 2 * k - 2 then s - k + 2 else
  if s = 2 * k - 2 then k + 1 else 1

def returnLength (s : ℕ) : ℕ :=
  if s < k then 1 else if s = 2 * k - 2 then 4 else 3

include hd in
theorem return_x_table (s : ℕ) (hs : 0 < s) (hsm : s < 2 * k) :
    retTime (phi k hk) (horizontal k) (x k s) = returnLength k s ∧
      ret (phi k hk) (horizontal k) (x k s) = x k (xReturnIndex k s) := by
  unfold returnLength xReturnIndex
  split_ifs <;> try omega
  all_goals subst_vars
  all_goals first
    | exact return_x_low k hk hd s hs (by omega)
    | exact return_x_middle k hk hd
    | exact return_x_high k hk hd s (by omega) (by omega)
    | exact return_x_penultimate k hk hd
    | simpa only [show s = 2 * k - 1 by omega] using return_x_last k hk hd

omit [NeZero (2 * k)] in
theorem psiIndex_succ (i : ℕ) :
    psiIndex k i + 1 = xReturnIndex k (i + 1) := by
  unfold psiIndex xReturnIndex
  split_ifs <;> omega

def xEmbedding (i : Fin (2 * k - 1)) : ZMod (2 * k) × ZMod 2 := x k (i.val + 1)

include hd in
theorem phi_ret_x (i : Fin (2 * k - 1)) :
    ret (phi k hk) (horizontal k) (xEmbedding k i) = xEmbedding k (psi k hk i) := by
  change ret (phi k hk) (horizontal k) (x k (i.val + 1)) = x k ((psi k hk i).val + 1)
  rw [(return_x_table k hk hd _ (by omega) (by have := i.isLt; omega)).2,
    psi_val, psiIndex_succ k i.val]

end TorusEven.Entry.Star.Nondivisible
