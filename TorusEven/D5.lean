-- STATUS: main-path (E3 assembly: D_5(m) for even m ≥ 6)
import TorusEven.Goals
import TorusEven.D5.Terminal3
import TorusEven.D5.Terminal4

/-!
# `D_5(m)` for even `m ≥ 6` (manuscript Theorem `thm:d5large`)

The five colour returns are single cycles (`ReturnFull` for colours `0, 2`; the terminal
splices `Terminal1/3/4` for colours `1, 3, 4`), every layer is a bijection, and the row rule
is Latin; `Chart.cayley_of_rootFlat` turns this into a Cayley Hamilton decomposition.
-/

namespace TorusEven
namespace D5

variable {m : ℕ} [NeZero m]

theorem fin5_cases (c : Fin 5) : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by
  fin_cases c <;> simp

theorem layerBijective (h6 : 6 ≤ m) (hm : Even m) : (schedule m).layerBijective := by
  intro t c
  obtain ⟨k, hk, rfl⟩ : ∃ k : ℕ, k < m ∧ ((k : ℕ) : ZMod m) = t :=
    ⟨t.val, t.val_lt, ZMod.natCast_zmod_val t⟩
  rcases fin5_cases c with rfl | rfl | rfl | rfl | rfl
  · rw [layer_eq_stage3_full h6 0 (Or.inl rfl) k hk]; exact stageLayer_bijective 0 3 k
  · by_cases hk2 : k = 2
    · subst hk2
      have h := actual1_two h6 hm
      unfold actual1 at h
      rw [h]
      exact (stageLayer_bijective 1 3 2).comp (Jplane_bijective 0
        (fun q hq => jmap0_inB h6 hm hq) (fun q q' hq hq' h => jmap0_inj h6 hm hq hq' h))
    · have h := actual1_eq h6 hm k hk hk2
      unfold actual1 at h
      rw [h]
      exact stageLayer_bijective 1 3 k
  · rw [layer_eq_stage3_full h6 2 (Or.inr rfl) k hk]; exact stageLayer_bijective 2 3 k
  · by_cases hk2 : k = 2
    · subst hk2
      have h := actual3_two h6 hm
      unfold actual3 at h
      rw [h]
      exact (stageLayer_bijective 3 3 2).comp (Jplane_bijective 1
        (fun q hq => jmap1_inB h6 hm hq) (fun q q' hq hq' h => jmap1_inj h6 hm hq hq' h))
    · have h := actual3_eq h6 hm k hk hk2
      unfold actual3 at h
      rw [h]
      exact stageLayer_bijective 3 3 k
  · by_cases hk2 : k = 2
    · subst hk2
      have h := actual4_two h6 hm
      unfold actual4 at h
      rw [h]
      exact (stageLayer_bijective 4 3 2).comp (Jplane_bijective 2
        (fun q hq => jmap2_inB h6 hm hq) (fun q q' hq hq' h => jmap2_inj h6 hm hq hq' h))
    · have h := actual4_eq h6 hm k hk hk2
      unfold actual4 at h
      rw [h]
      exact stageLayer_bijective 4 3 k

theorem returnsSingleCycle (h6 : 6 ≤ m) (hm : Even m) : (schedule m).returnsSingleCycle := by
  intro c
  rcases fin5_cases c with rfl | rfl | rfl | rfl | rfl
  · exact returnMap_single_cycle_c0 h6
  · exact returnMap_single_cycle_c1 h6 hm
  · exact returnMap_single_cycle_c2 h6
  · exact returnMap_single_cycle_c3 h6 hm
  · exact returnMap_single_cycle_c4 h6 hm

/-- `D_5(m)` has a Cayley Hamilton decomposition for every even `m ≥ 6`. -/
theorem cayley_of_even (h6 : 6 ≤ m) (hm : Even m) : Shared.CayleyHamiltonDecomposition 5 m :=
  Chart.cayley_of_rootFlat (schedule m) schedule_step rowLatin (layerBijective h6 hm)
    (returnsSingleCycle h6 hm)

end D5

/-- E3: manuscript Theorem `thm:d5large`. -/
theorem d5_even_large : D5EvenLargeGoal := by
  intro m hm h6
  haveI : NeZero m := ⟨by omega⟩
  exact D5.cayley_of_even h6 hm

end TorusEven
