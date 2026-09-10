-- STATUS: conditional (endpoint assembled from open goals; becomes main-path when all goals close)
import TorusEven.D5Four

namespace TorusEven

/-- Assembly along the odd dispatcher: seeds `3, 5, 7` and a successor closure. -/
theorem even_modulus_tori_all_dimensions_of_successor
    (h3 : D3EvenGoal) (h5 : D5EvenLargeGoal) (h7 : D7EvenGoal)
    (hSucc : EvenSuccessorGoal) :
    EvenModulusToriAllDimensionsGoal := by
  intro d m hd2 hm hm4
  exact evenClass.uniform_of_seeds_and_successor
    (fun h => h3 h.1 h.2) (d5_even_uniform_of_large h5) (fun h => h7 h.1 h.2)
    hSucc hd2 ⟨hm, hm4⟩

/-- Assembly along the manuscript: seeds `3, 5` and the collar route for odd `d ≥ 7`. -/
theorem even_modulus_tori_all_dimensions_of_collar
    (h3 : D3EvenGoal) (h5 : D5EvenLargeGoal) (hOdd : EvenOddDegreeGoal) :
    EvenModulusToriAllDimensionsGoal := by
  intro d m hd2 hm hm4
  exact evenClass.uniform_of_seeds_and_odd_degree
    (fun h => h3 h.1 h.2) (d5_even_uniform_of_large h5) hOdd hd2 ⟨hm, hm4⟩

/-- Partial unconditional result: every power-of-two dimension at every even modulus. -/
theorem even_modulus_two_pow_dimensions :
    ∀ {k m : Nat}, 1 ≤ k → Even m → 4 ≤ m → Solved (2 ^ k) m :=
  fun hk hm hm4 => even_two_pow_dimensions hk hm hm4

end TorusEven
