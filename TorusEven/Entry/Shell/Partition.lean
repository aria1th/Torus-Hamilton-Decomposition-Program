-- STATUS: main-path
import TorusEven.Entry.Shell.Pairs

namespace TorusEven.Entry.Shell

def pairHeight (p c : ℕ) : ℕ :=
  if c = 0 ∨ c = p + 1 then 0 else if c < p ∨ c = p ∧ p % 2 = 0 then 1 else 2

variable (p : ℕ) (hp : 2 ≤ p)
include hp

omit hp in
theorem endpoint_height (h : ℕ) (i : Fin (pairCount p h)) (b : Bool) :
    pairHeight p (endpointIndex p h i.val b) = h := by
  have hi := i.isLt
  have hh := pairCount_height p h (by omega)
  interval_cases h <;> cases b <;> by_cases he : p % 2 = 0 <;> by_cases hi0 : i.val = 0
  all_goals norm_num only [pairCount, he, if_true, if_false] at hi
  all_goals simp (disch := omega) [endpointIndex, pairHeight, he, hi0] <;> try omega
  all_goals split_ifs <;> omega

abbrev PairSlot := Σ h : Fin 3, Fin (pairCount p h.val) × Bool

def globalEndpoint : PairSlot p ↪ Color p where
  toFun q := endpoint p hp q.1.val q.2
  inj' u v he := by
    obtain ⟨h, i, b⟩ := u
    obtain ⟨k, j, d⟩ := v
    have hv := congrArg (fun c : Color p => pairHeight p c.val) he
    change pairHeight p (endpointIndex p h.val i.val b) =
      pairHeight p (endpointIndex p k.val j.val d) at hv
    rw [endpoint_height p, endpoint_height p] at hv
    have hh : h = k := Fin.ext hv
    subst k
    exact Sigma.ext rfl (heq_of_eq ((endpoint p hp h.val).injective he))

theorem card_pairSlot : Fintype.card (PairSlot p) = 2 * p := by
  simp [PairSlot, Fintype.card_sigma, Fintype.card_prod, Fin.sum_univ_succ, pairCount]
  split_ifs <;> omega

noncomputable def pairEquiv : PairSlot p ≃ Color p := Equiv.ofBijective (globalEndpoint p hp)
  ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨(globalEndpoint p hp).injective, by simp [card_pairSlot p hp]⟩)

theorem pairEquiv_apply (q : PairSlot p) : pairEquiv p hp q = endpoint p hp q.1.val q.2 := rfl

end TorusEven.Entry.Shell
