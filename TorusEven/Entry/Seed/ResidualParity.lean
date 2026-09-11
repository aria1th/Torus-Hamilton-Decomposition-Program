-- STATUS: main-path
import TorusEven.Entry.Seed.ResidualComponents
import TorusEven.Entry.Seed.NonmatePairs

namespace TorusEven.Entry.Seed

open Collar Incidence

variable (p : ℕ) (hp : 2 ≤ p) {m : ℕ} [NeZero m] (hm : 4 ≤ m) (heven : Even m)

theorem residual_pair_same (hp4 : 4 ≤ p) (i : Fin (p - 2)) :
    residualComponent p hp hm heven (nonmatePairs p hp (i, false)).val =
      residualComponent p hp hm heven (nonmatePairs p hp (i, true)).val := by
  let l := (nonmatePairs p hp (i, false)).val
  let r := (nonmatePairs p hp (i, true)).val
  have hl := (mem_nonmates_iff p hp l).mp (nonmatePairs p hp (i, false)).property
  have hr := (mem_nonmates_iff p hp r).mp (nonmatePairs p hp (i, true)).property
  have h3 : p ≠ 3 := by omega
  by_cases he : p % 2 = 0
  · simp only [h3, if_false, he, if_true] at hl hr
    have hhalf : l.val < p ↔ r.val < p := by
      simp only [l, r, nonmatePairs_val, Bool.false_eq_true, if_false, if_true,
        Nat.add_zero, nonmateIndex, h3, he]
      split_ifs <;> omega
    by_cases ha : l.val < p
    · exact (residual_even_A p hp hm heven hp4 he l (by omega) ha).trans
        (residual_even_A p hp hm heven hp4 he r (by omega) (hhalf.mp ha)).symm
    · exact (residual_even_B p hp hm heven hp4 he l (by omega)).trans
        (residual_even_B p hp hm heven hp4 he r (by have := hhalf.not.mp ha; omega)).symm
  · simp only [h3, if_false, he] at hl hr
    exact (residual_odd_connected p hp hm heven hp4 he l (by omega)).trans
      (residual_odd_connected p hp hm heven hp4 he r (by omega)).symm

theorem residual_even : EvenOnComponents (matched p hp hm heven).residual
    (matched p hp hm heven).nonmates := by
  rw [matched_nonmates]
  apply evenOnComponents_of_pairs _ _ (nonmatePairs p hp)
  intro i
  by_cases hp4 : 4 ≤ p
  · exact residual_pair_same p hp hm heven hp4 i
  · have hs : p = 2 ∨ p = 3 := by omega
    rcases hs with rfl | rfl
    · exact Fin.elim0 i
    · have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
      subst i
      apply residual_same_nat 3 hp hm heven (0, 1)
      · change (4 : Shell.Color 3) ∈ residualNat 3 (by decide) (0, 1)
        decide
      · change (5 : Shell.Color 3) ∈ residualNat 3 (by decide) (0, 1)
        decide

include hm in
theorem exists_matchedSelection :
    ∃ J : (ZMod m × ZMod m) → ZMod m → Finset (Fin 4 ⊕ Shell.Color p),
      IsPinnedSelection (support p hp heven 0) ∅ J ∧
        ∀ hw t q, Sum.inl q ∈ J hw t ↔ xChart (hw, t) = anchor q := by
  obtain ⟨R, hR⟩ := (matched p hp hm heven).exists_selection hm (residual_even p hp hm heven)
  refine ⟨(matched p hp hm heven).pattern (R.row hm), ?_, ?_⟩
  · simpa only [funext (matched_fullSupport p hp hm heven)] using hR
  · intro hw t q
    rw [MatchedData.mem_pattern_left, ← anchor_coordinates hm q, xChart.injective.eq_iff]
    exact ⟨fun h => Prod.ext h.1 h.2, fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩

end TorusEven.Entry.Seed
