-- STATUS: main-path
import TorusEven.Entry.Star.NondivCoverage
import TorusEven.Entry.Star.Small

namespace TorusEven.Entry.Star

variable {m : ℕ} [NeZero m] (hm : 4 ≤ m) (heven : Even m) (hd : ¬ 3 ∣ m)
include hm heven hd

theorem return_hamilton_three_not_dvd : Shared.IsSingleCycleMap (returnMap (m := m) 0) := by
  obtain ⟨k, rfl⟩ := heven.two_dvd
  by_cases hk : k = 2
  · subst k
    exact return_hamilton_four
  have hk3 : k ≠ 3 := by
    rintro rfl
    exact hd (by decide)
  exact hamilton_of_markedReturn hm heven (Nondivisible.phi_hamilton k (by omega) hd)

theorem hamilton_three_not_dvd (c : Fin 3) : Shared.IsSingleCycleMap ((factorization hm).step c) :=
  hamilton_of_return hm (return_hamilton_three_not_dvd hm heven hd) c

theorem replacement_hamilton_three_not_dvd (c : Fin 3) :
    Shared.IsSingleCycleMap ((replacement hm).factorization.step c) :=
  replacement_hamilton_of_return hm (return_hamilton_three_not_dvd hm heven hd) c

end TorusEven.Entry.Star
