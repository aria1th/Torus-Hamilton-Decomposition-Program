-- STATUS: main-path
import TorusEven.Entry.Star.Return

namespace TorusEven.Entry.Star

open Surgery

private theorem return_cover_four :
    ∀ p : Plane 4, ∃ k : Fin 16, (returnMap 0)^[k.val] (0, 0) = p := by decide

private theorem return_cover_six :
    ∀ p : Plane 6, ∃ k : Fin 36, (returnMap 0)^[k.val] (0, 0) = p := by decide

private theorem return_singleCycle_of_cover {m n : ℕ} [NeZero m] (hm : 4 ≤ m)
    (h : ∀ p : Plane m, ∃ k : Fin n, (returnMap 0)^[k.val] (0, 0) = p) :
    Shared.IsSingleCycleMap (returnMap (m := m) 0) := by
  have he : (returnPerm hm 0 : Plane m → Plane m) = returnMap 0 := funext (returnPerm_apply hm 0)
  apply single_cycle_of_orbitSet_univ (he ▸ (returnPerm hm 0).bijective) (0, 0)
  apply Set.eq_univ_of_forall
  intro p
  obtain ⟨k, hk⟩ := h p
  exact ⟨k.val, hk⟩

theorem return_hamilton_four : Shared.IsSingleCycleMap (returnMap (m := 4) 0) :=
  return_singleCycle_of_cover (by decide) return_cover_four

theorem return_hamilton_six : Shared.IsSingleCycleMap (returnMap (m := 6) 0) :=
  return_singleCycle_of_cover (by decide) return_cover_six

theorem hamilton_four (c : Fin 3) :
    Shared.IsSingleCycleMap ((factorization (m := 4) (by decide)).step c) :=
  hamilton_of_return (by decide) return_hamilton_four c

theorem hamilton_six (c : Fin 3) :
    Shared.IsSingleCycleMap ((factorization (m := 6) (by decide)).step c) :=
  hamilton_of_return (by decide) return_hamilton_six c

end TorusEven.Entry.Star
