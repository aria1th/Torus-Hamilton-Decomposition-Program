-- STATUS: main-path
import TorusEven.Collar.Circuits

namespace TorusEven.Surgery

theorem singleCycle_of_induced_orbits {α β : Type*} [Finite α]
    (S : Equiv.Perm α) (e : β → α) (R : β → β) (hR : Shared.IsSingleCycleMap R)
    (hstep : ∀ b, e (R b) ∈ orbitSet S (e b))
    (hmeet : ∀ a, ∃ b, e b ∈ orbitSet S a) : Shared.IsSingleCycleMap S := by
  classical
  letI := Fintype.ofFinite α
  have hi (b : β) (n : ℕ) : e (R^[n] b) ∈ orbitSet S (e b) := by
    induction n with
    | zero => exact self_mem_orbitSet S (e b)
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      simpa only [orbitSet_eq_of_mem S.injective ih] using hstep (R^[n] b)
  refine ⟨S.bijective, fun a b => ?_⟩
  obtain ⟨u, hu⟩ := hmeet a
  obtain ⟨v, hv⟩ := hmeet b
  obtain ⟨n, hn⟩ := hR.2 u v
  have huv : e v ∈ orbitSet S (e u) := hn ▸ hi u n
  have hb := mem_orbitSet_symm S.injective hv
  rwa [orbitSet_eq_of_mem S.injective huv, orbitSet_eq_of_mem S.injective hu] at hb

end TorusEven.Surgery
