-- STATUS: conditional (endpoint assembled from open goals; becomes main-path when all goals close)
import TorusEven.D5Four
import TorusEven.D3
import TorusEven.D5

namespace TorusEven

/-- `D_5(m)` for every even `m ≥ 4`: the `m = 4` leaf plus E3. -/
theorem d5_even_uniform : evenClass.Uniform 5 :=
  d5_even_uniform_of_large d5_even_large

/-- Assembly along the odd dispatcher: seeds `5, 7` and a successor closure
(`d = 2, 3` are closed). -/
theorem even_modulus_tori_all_dimensions_of_successor
    (h7 : D7EvenGoal) (hSucc : EvenSuccessorGoal) :
    EvenModulusToriAllDimensionsGoal := by
  intro d m hd2 hm hm4
  exact evenClass.uniform_of_seeds_and_successor
    d3_even_uniform d5_even_uniform (fun h => h7 h.1 h.2)
    hSucc hd2 ⟨hm, hm4⟩

/-- Assembly along the manuscript: seed `5` and the collar route for odd `d ≥ 7`
(`d = 2, 3` are closed). -/
theorem even_modulus_tori_all_dimensions_of_collar
    (hOdd : EvenOddDegreeGoal) :
    EvenModulusToriAllDimensionsGoal := by
  intro d m hd2 hm hm4
  exact evenClass.uniform_of_seeds_and_odd_degree
    d3_even_uniform d5_even_uniform hOdd hd2 ⟨hm, hm4⟩

/-- Unconditional: `D_3(m)`, `D_5(m)`, `D_6(m)`, `D_9(m)`, `D_10(m)`, `D_15(m)` for every even
`m ≥ 4`. -/
theorem even_dimension_three {m : ℕ} (hm : Even m) (hm4 : 4 ≤ m) : Solved 3 m :=
  d3_even hm hm4

theorem even_dimension_six {m : ℕ} (hm : Even m) (hm4 : 4 ≤ m) : Solved 6 m :=
  evenClass.uniform_mul (a := 2) (b := 3) (by decide) (by decide)
    evenClass.uniform_two d3_even_uniform ⟨hm, hm4⟩

theorem even_dimension_nine {m : ℕ} (hm : Even m) (hm4 : 4 ≤ m) : Solved 9 m :=
  evenClass.uniform_mul (a := 3) (b := 3) (by decide) (by decide)
    d3_even_uniform d3_even_uniform ⟨hm, hm4⟩

theorem even_dimension_five {m : ℕ} (hm : Even m) (hm4 : 4 ≤ m) : Solved 5 m :=
  d5_even_uniform ⟨hm, hm4⟩

theorem even_dimension_ten {m : ℕ} (hm : Even m) (hm4 : 4 ≤ m) : Solved 10 m :=
  evenClass.uniform_mul (a := 2) (b := 5) (by decide) (by decide)
    evenClass.uniform_two d5_even_uniform ⟨hm, hm4⟩

theorem even_dimension_fifteen {m : ℕ} (hm : Even m) (hm4 : 4 ≤ m) : Solved 15 m :=
  evenClass.uniform_mul (a := 3) (b := 5) (by decide) (by decide)
    d3_even_uniform d5_even_uniform ⟨hm, hm4⟩

/-- Partial unconditional result: every power-of-two dimension at every even modulus. -/
theorem even_modulus_two_pow_dimensions :
    ∀ {k m : Nat}, 1 ≤ k → Even m → 4 ≤ m → Solved (2 ^ k) m :=
  fun hk hm hm4 => even_two_pow_dimensions hk hm hm4

end TorusEven
