-- STATUS: main-path
import TorusEven.Collar.Circuits
import Shared.RankCycle

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

theorem singleCycle_of_cyclic_order {α : Type*} {n : ℕ} (hn : 0 < n)
    (e : Fin n ≃ α) (S : α → α)
    (hs : ∀ i, S (e i) = e (finRotate n i)) : Shared.IsSingleCycleMap S := by
  letI : NeZero n := ⟨by omega⟩
  apply Shared.single_cycle_of_zmod_rank_equiv S (e.symm.trans (ZMod.finEquiv n).toEquiv)
  intro x
  obtain ⟨i, rfl⟩ := e.surjective x
  rw [hs]
  change (ZMod.finEquiv n) (e.symm (e (finRotate n i))) = (ZMod.finEquiv n) (e.symm (e i)) + 1
  simp only [Equiv.symm_apply_apply, finRotate_apply, map_add, map_one]

end TorusEven.Surgery
