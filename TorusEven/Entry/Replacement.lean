-- STATUS: main-path
import TorusEven.Collar.Recolouring

namespace TorusEven.Surgery

variable {α : Type*} (U : Set α) (e : Equiv.Perm α)

theorem supported_perm_mem_iff (he : ∀ x, x ∉ U → e x = x) (x : α) : e x ∈ U ↔ x ∈ U := by
  constructor
  · intro hx
    by_contra hn
    exact hn (he x hn ▸ hx)
  · intro hx
    by_contra hn
    have h := e.injective (he (e x) hn)
    exact hn (h.symm ▸ hx)

end TorusEven.Surgery

namespace TorusEven.Collar.Recolouring

open Surgery

variable {C I : Type*} [Fintype C] [DecidableEq I] {m : ℕ}
variable (F G : MultitorusFactorization C I m) (active : Finset C)
variable (U : Set (I → ZMod m)) [DecidablePred (· ∈ U)]
variable (routing : (I → ZMod m) → Equiv.Perm C)
variable (hinactive : ∀ x c, c ∉ active → routing x c = c)
variable (hdir : ∀ c x, G.direction c x = F.direction (routing x c) x)
variable (hout : ∀ c x, x ∉ U → G.step c x = F.step c x)

def ofReplacement : Recolouring F active U where
  boundary c := Equiv.Perm.subtypePerm ((G.step c).trans (F.step c).symm)
    (supported_perm_mem_iff U _ (fun x hx => by
      change (F.step c).symm (G.step c x) = x
      rw [hout c x hx, Equiv.symm_apply_apply]))
  routing u := routing u.val
  routing_inactive u c hc := hinactive u.val c hc
  head c u := by
    change F.step c ((F.step c).symm (G.step c u.val)) = F.step (routing u.val c) u.val
    rw [Equiv.apply_symm_apply]
    funext j
    rw [G.step_eq, F.step_eq, hdir]

theorem ofReplacement_step (c : C) :
    ((ofReplacement F G active U routing hinactive hdir hout).factorization.step c) = G.step c := by
  apply Equiv.ext
  intro x
  by_cases hx : x ∈ U
  · rw [Recolouring.factorization, patch_apply _ U _ ⟨x, hx⟩]
    exact (F.step c).apply_symm_apply (G.step c x)
  · exact (patch_outside _ U _ hx).trans (hout c x hx).symm

end TorusEven.Collar.Recolouring
