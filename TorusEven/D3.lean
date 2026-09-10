-- STATUS: main-path
import TorusEven.D3.Four
import TorusEven.D3.RouteE

namespace TorusEven

/-- E2: `D_3(m)` for every even `m ≥ 4` (`m = 4` by the finite witness, `m ≥ 6` by Route E). -/
theorem d3_even : D3EvenGoal := by
  intro m hm h4
  by_cases h6 : 6 ≤ m
  · exact d3_even_of_six_le hm h6
  · have hm4 : m = 4 := by
      rcases hm with ⟨r, hr⟩
      omega
    subst hm4
    exact d3_even_four

theorem d3_even_uniform : evenClass.Uniform 3 := fun h => d3_even h.1 h.2

end TorusEven
