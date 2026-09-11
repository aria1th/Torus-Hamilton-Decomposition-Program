-- STATUS: main-path
import TorusEven.Collar.Transport

namespace TorusEven.Surgery

variable {α β : Type*} (S : Equiv.Perm α) (T : Equiv.Perm β)
variable (U : Set α) (V : Set β) [DecidablePred (· ∈ U)] [DecidablePred (· ∈ V)]

theorem patch_apply (r : Equiv.Perm U) (u : U) : patch S U r u.val = S (r u).val := by
  simp only [patch, Equiv.trans_apply, boundaryExtension_apply]

@[simp] theorem patch_refl : patch S U (Equiv.refl U) = S := by
  ext x
  by_cases hx : x ∈ U
  · exact patch_apply S U (Equiv.refl U) ⟨x, hx⟩
  · exact patch_outside S U (Equiv.refl U) hx

theorem patch_semiconj (e : α ≃ β) (he : Function.Semiconj e S T)
    (hmem : ∀ x, x ∈ U ↔ e x ∈ V) (r : Equiv.Perm U) :
    Function.Semiconj e (patch S U r) (patch T V ((e.subtypeEquiv hmem).permCongr r)) := by
  intro x
  by_cases hx : x ∈ U
  · let u : U := ⟨x, hx⟩
    let E : U ≃ V := e.subtypeEquiv hmem
    have hu : (E u).val = e x := rfl
    have hr : (E.permCongr r (E u)).val = e (r u).val := by
      rw [Equiv.permCongr_apply, E.symm_apply_apply]
      rfl
    rw [show patch S U r x = S (r u).val from patch_apply S U r u, ← hu,
      patch_apply T V (E.permCongr r) (E u), hr]
    exact he (r u).val
  · rw [patch_outside S U r hx, patch_outside T V _ ((hmem x).not.mp hx)]
    exact he x

variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem patch_circuitCount_congr (e : α ≃ β) (he : Function.Semiconj e S T)
    (hmem : ∀ x, x ∈ U ↔ e x ∈ V) (r : Equiv.Perm U) :
    circuitCount (patch S U r) = circuitCount (patch T V ((e.subtypeEquiv hmem).permCongr r)) :=
  circuitCount_congr _ _ e (patch_semiconj S T U V e he hmem r)

end TorusEven.Surgery
