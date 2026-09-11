-- STATUS: main-path
import TorusEven.Entry.Star.Divisible
import TorusEven.Entry.Star.Nondivisible

namespace TorusEven.Entry.Star

variable {m : ℕ} [NeZero m] (hm : 4 ≤ m) (heven : Even m)
include hm heven

theorem return_hamilton : Shared.IsSingleCycleMap (returnMap (m := m) 0) := by
  by_cases hd : 3 ∣ m
  · exact return_hamilton_three_dvd hm heven hd
  · exact return_hamilton_three_not_dvd hm heven hd

theorem hamilton (c : Fin 3) : Shared.IsSingleCycleMap ((factorization hm).step c) :=
  hamilton_of_return hm (return_hamilton hm heven) c

theorem replacement_hamilton (c : Fin 3) :
    Shared.IsSingleCycleMap ((replacement hm).factorization.step c) :=
  replacement_hamilton_of_return hm (return_hamilton hm heven) c

end TorusEven.Entry.Star
