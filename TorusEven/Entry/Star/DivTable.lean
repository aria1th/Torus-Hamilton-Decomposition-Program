-- STATUS: main-path
import TorusEven.Entry.Star.DivXReturn
import TorusEven.Entry.Star.DivPsi

namespace TorusEven.Entry.Star.Divisible

open Surgery

variable (q : ℕ) [NeZero (6 * q)] (hq : 2 ≤ q)

def xReturnIndex (s : ℕ) : ℕ :=
  if s < 4 * q - 1 then s + 2 * q + 1 else
  if s = 4 * q - 1 then 2 * q else
  if s = 4 * q then 1 else
  if s = 4 * q + 1 then 2 * q + 1 else
  if s < 6 * q - 2 then s - 4 * q else
  if s = 6 * q - 2 then 2 * q - 1 else 2 * q - 2

def returnLength (s : ℕ) : ℕ :=
  if s < 4 * q then 1 else
  if s = 4 * q ∨ s = 6 * q - 2 then 5 else
  if s < 6 * q - 1 then 4 else 3

theorem return_x_table (s : ℕ) (hs : 0 < s) (hsm : s < 6 * q) :
    retTime (phi q hq) (horizontal q) (x q s) = returnLength q s ∧
      ret (phi q hq) (horizontal q) (x q s) = x q (xReturnIndex q s) := by
  unfold returnLength xReturnIndex
  split_ifs <;> try omega
  all_goals subst_vars
  all_goals first
    | exact return_x_low q hq s hs (by omega)
    | exact return_x_middle q hq
    | exact return_x_four q hq
    | exact return_x_four_succ q hq
    | exact return_x_high q hq s (by omega) (by omega)
    | exact return_x_penultimate q hq
    | simpa only [show s = 6 * q - 1 by omega] using return_x_last q hq

omit [NeZero (6 * q)] in
theorem psiIndex_succ (i : ℕ) (hi : i < 6 * q - 1) :
    psiIndex q i + 1 = xReturnIndex q (i + 1) := by
  unfold psiIndex betaIndex xReturnIndex
  split_ifs <;> try omega
  all_goals unfold InnerReturn.thetaIndex
  all_goals split_ifs <;> omega

def xEmbedding (i : Fin (6 * q - 1)) : ZMod (6 * q) × ZMod 2 := x q (i.val + 1)

theorem phi_ret_x (i : Fin (6 * q - 1)) :
    ret (phi q hq) (horizontal q) (xEmbedding q i) = xEmbedding q (psi q hq i) := by
  change ret (phi q hq) (horizontal q) (x q (i.val + 1)) = x q ((psi q hq i).val + 1)
  rw [(return_x_table q hq _ (by omega) (by have := i.isLt; omega)).2,
    psi_val, psiIndex_succ q i.val i.isLt]

end TorusEven.Entry.Star.Divisible
