-- STATUS: main-path
import TorusEven.Endpoints
import RoundComposite.V75Endpoints

namespace TorusAll

theorem all_moduli_tori_all_dimensions {d m : ℕ} (hd : 2 ≤ d) (hm : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m := by
  by_cases he : Even m
  · exact TorusEven.even_modulus_tori_all_dimensions hd he (by obtain ⟨k, hk⟩ := he; omega)
  · exact RoundComposite.Concrete.odd_modulus_tori_all_dimensions_v75 hd
      (Nat.not_even_iff_odd.mp he) hm

end TorusAll
