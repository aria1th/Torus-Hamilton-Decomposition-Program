-- STATUS: conditional (endpoint assembled from open goals; becomes main-path when all goals close)
import TorusEven.D5Four
import TorusEven.D3

namespace TorusEven

/-- Assembly along the odd dispatcher: seeds `5, 7` and a successor closure
(`d = 2, 3` are closed). -/
theorem even_modulus_tori_all_dimensions_of_successor
    (h5 : D5EvenLargeGoal) (h7 : D7EvenGoal) (hSucc : EvenSuccessorGoal) :
    EvenModulusToriAllDimensionsGoal := by
  intro d m hd2 hm hm4
  exact evenClass.uniform_of_seeds_and_successor
    d3_even_uniform (d5_even_uniform_of_large h5) (fun h => h7 h.1 h.2)
    hSucc hd2 ⟨hm, hm4⟩

/-- Assembly along the manuscript: seed `5` and the collar route for odd `d ≥ 7`
(`d = 2, 3` are closed). -/
theorem even_modulus_tori_all_dimensions_of_collar
    (h5 : D5EvenLargeGoal) (hOdd : EvenOddDegreeGoal) :
    EvenModulusToriAllDimensionsGoal := by
  intro d m hd2 hm hm4
  exact evenClass.uniform_of_seeds_and_odd_degree
    d3_even_uniform (d5_even_uniform_of_large h5) hOdd hd2 ⟨hm, hm4⟩

/-- Unconditional: `D_3(m)`, `D_6(m)`, `D_9(m)` for every even `m ≥ 4`. -/
theorem even_dimension_three {m : ℕ} (hm : Even m) (hm4 : 4 ≤ m) : Solved 3 m :=
  d3_even hm hm4

theorem even_dimension_six {m : ℕ} (hm : Even m) (hm4 : 4 ≤ m) : Solved 6 m :=
  evenClass.uniform_mul (a := 2) (b := 3) (by decide) (by decide)
    evenClass.uniform_two d3_even_uniform ⟨hm, hm4⟩

theorem even_dimension_nine {m : ℕ} (hm : Even m) (hm4 : 4 ≤ m) : Solved 9 m :=
  evenClass.uniform_mul (a := 3) (b := 3) (by decide) (by decide)
    d3_even_uniform d3_even_uniform ⟨hm, hm4⟩

/-- Partial unconditional result: every power-of-two dimension at every even modulus. -/
theorem even_modulus_two_pow_dimensions :
    ∀ {k m : Nat}, 1 ≤ k → Even m → 4 ≤ m → Solved (2 ^ k) m :=
  fun hk hm hm4 => even_two_pow_dimensions hk hm hm4

end TorusEven
