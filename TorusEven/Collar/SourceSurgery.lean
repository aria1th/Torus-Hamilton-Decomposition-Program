-- STATUS: main-path
import TorusEven.Collar.Circuits

namespace TorusEven.Surgery

open Function

variable {α : Type*}
variable (S : Equiv.Perm α) (U : Set α) [DecidablePred (· ∈ U)]

def boundaryExtension (r : Equiv.Perm U) : Equiv.Perm α :=
  r.extendDomain (Equiv.refl U)

@[simp] theorem boundaryExtension_apply (r : Equiv.Perm U) (u : U) :
    boundaryExtension U r u.val = (r u).val :=
  r.extendDomain_apply_image (Equiv.refl U) u

theorem boundaryExtension_outside (r : Equiv.Perm U) {x : α} (hx : x ∉ U) :
    boundaryExtension U r x = x := r.extendDomain_apply_not_subtype (Equiv.refl U) hx

def patch (r : Equiv.Perm U) : Equiv.Perm α := (boundaryExtension U r).trans S

theorem patch_outside (r : Equiv.Perm U) {x : α} (hx : x ∉ U) :
    patch S U r x = S x := by simp only [patch, Equiv.trans_apply, boundaryExtension_outside U r hx]

variable [Fintype α] [DecidableEq α]

theorem patch_return (r : Equiv.Perm U) (u : U) :
    retTime (patch S U r) U u = retTime S U (r u) ∧
      ret (patch S U r) U u = ret S U (r u) := by
  have hmaps : ∀ x, x ∈ U → boundaryExtension U r x ∈ U := by
    intro x hx
    exact (boundaryExtension_apply U r ⟨x, hx⟩).symm ▸ (r (⟨x, hx⟩ : U)).property
  have hiter (k : ℕ) (hk : 1 ≤ k) (hkt : k ≤ retTime S U (r u)) :
      (patch S U r)^[k] u.val = S^[k] (r u).val := by
    have h := iterate_comp_eq S U (boundaryExtension U r)
      (fun x hx => boundaryExtension_outside U r hx) hmaps u.property k hk
    simp only [boundaryExtension_apply] at h
    exact h hkt
  have ht : retTime (patch S U r) U u = retTime S U (r u) := by
    apply retTime_eq_of_first _ _ u.property (retTime_pos S U (r u).property)
    · rw [hiter _ (retTime_pos S U (r u).property) le_rfl]
      exact ret_mem S U (r u).property
    · intro k hk hkt
      rw [hiter k hk hkt.le]
      exact not_mem_of_lt_retTime S U (r u).property hk hkt
  refine ⟨ht, ?_⟩
  unfold ret
  rw [ht, hiter _ (retTime_pos S U (r u).property) le_rfl]

theorem patch_retPerm (r : Equiv.Perm U) :
    retPerm (patch S U r) U = r.trans (retPerm S U) := by
  ext u
  exact (patch_return S U r u).2

theorem patch_circuitCount (r : Equiv.Perm U) :
    circuitCount (patch S U r) =
      circuitCount (r.trans (retPerm S U)) + Nat.card (UnhitCircuit S U) := by
  rw [circuitCount_eq_return_add_unhit (patch S U r) U, patch_retPerm]
  congr 1
  exact Nat.card_congr (unhitCircuitEquiv (patch S U r) U S
    (fun _ hx => patch_outside S U r hx))

end TorusEven.Surgery
