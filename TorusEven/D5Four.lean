-- STATUS: main-path (imports the D_5(4) leaf; the native leaf itself is D5Odd/EvenRouteEM4.lean)
import TorusEven.Goals
import D5Odd.EvenRouteEM4

namespace TorusEven

/-- `D_5(4)` in the shared interface.  The schedule is the Route-E `m = 4` table; the
manuscript's four-row schedule (`d5_m4_tours.json`) is kept as a second leaf in
`evidence/even_d5/` and is not yet a Lean certificate. -/
theorem d5_even_four : Solved 5 4 :=
  D5Odd.D5_even_m4_shared_cayley

/-- Combine the finite `m = 4` leaf with the parametric `m ≥ 6` goal. -/
theorem d5_even_uniform_of_large (h : D5EvenLargeGoal) : evenClass.Uniform 5 := by
  refine fun {m} hm => ?_
  rcases hm with ⟨heven, h4⟩
  by_cases h6 : 6 ≤ m
  · exact h heven h6
  · have hm4 : m = 4 := by
      rcases heven with ⟨r, hr⟩
      omega
    subst hm4
    exact d5_even_four

end TorusEven
