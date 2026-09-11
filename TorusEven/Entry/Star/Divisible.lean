-- STATUS: main-path
import TorusEven.Entry.Star.DivCoverage
import TorusEven.Entry.Star.Small

namespace TorusEven.Entry.Star

variable {m : ℕ} [NeZero m] (hm : 4 ≤ m) (heven : Even m) (hd : 3 ∣ m)

include hm heven hd

theorem return_hamilton_three_dvd : Shared.IsSingleCycleMap (returnMap (m := m) 0) := by
  have h2 := Nat.mod_eq_zero_of_dvd heven.two_dvd
  have h3 := Nat.mod_eq_zero_of_dvd hd
  have h6 : 6 ∣ m := Nat.dvd_of_mod_eq_zero (by omega)
  obtain ⟨q, rfl⟩ := h6
  by_cases hq : q = 1
  · subst q
    exact return_hamilton_six
  · exact hamilton_of_markedReturn hm heven (Divisible.phi_hamilton q (by omega))

theorem hamilton_three_dvd (c : Fin 3) : Shared.IsSingleCycleMap ((factorization hm).step c) :=
  hamilton_of_return hm (return_hamilton_three_dvd hm heven hd) c

theorem replacement_hamilton_three_dvd (c : Fin 3) :
    Shared.IsSingleCycleMap ((replacement hm).factorization.step c) :=
  replacement_hamilton_of_return hm (return_hamilton_three_dvd hm heven hd) c

end TorusEven.Entry.Star
