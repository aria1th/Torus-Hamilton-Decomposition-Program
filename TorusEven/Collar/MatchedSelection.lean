-- STATUS: main-path
import TorusEven.Collar.MatchedCarry
import TorusEven.Collar.MatchedCoherence
import TorusEven.Collar.PinnedSelection

namespace TorusEven.Collar.Incidence.MatchedData

variable {B Q Ω : Type*} [Fintype B] [Fintype Q] [Fintype Ω]
variable [DecidableEq Q] [DecidableEq Ω] {A : B → Finset Ω} {m : ℕ} [NeZero m]
variable (D : MatchedData (Q := Q) A m)

theorem exists_selection (hm : 4 ≤ m) (hEven : EvenOnComponents D.residual D.nonmates) :
    ∃ R : D.ResidualRows, IsPinnedSelection D.fullSupport ∅ (D.pattern (R.row hm)) := by
  classical
  obtain ⟨P, hodd, hzero⟩ := exists_directed_pairs_on D.residual D.nonmates hEven
  let R := D.rowsOfPairs P
  refine ⟨R, ⟨D.pattern_subset _ (R.row_subset hm),
    D.pattern_card _ (R.row_subset hm) (R.row_card hm), ?_, by simp,
    R.selected_coherent hm, R.complement_coherent hm⟩⟩
  intro x
  cases x with
  | inl q => exact Or.inl (by rw [D.active_card]; simp)
  | inr c =>
    have hcount : ((Finset.univ.filter (fun p : B × ZMod m =>
        Sum.inr c ∈ D.pattern (R.row hm) p.1 p.2)).card : ZMod m) =
        ∑ b, ∑ t : ZMod m, if Sum.inr c ∈ D.pattern (R.row hm) b t then 1 else 0 := by
      simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter,
        apply_ite, Nat.cast_zero, Fintype.sum_prod_type]
    rw [hcount, R.auxiliary_carry hm]
    by_cases hc : c ∈ D.mates
    · right
      have hz := hzero c (by simpa only [mem_nonmates, not_not] using hc)
      simp only [R, rowsOfPairs_pairs, hz, Int.cast_zero, hc, if_true, zero_sub]
    · rcases hodd c ((D.mem_nonmates c).mpr hc) with h | h
      · left
        simp only [R, rowsOfPairs_pairs, h, Int.cast_one, hc, if_false, sub_zero]
      · right
        simp only [R, rowsOfPairs_pairs, h, Int.cast_neg, Int.cast_one, hc, if_false, sub_zero]

end TorusEven.Collar.Incidence.MatchedData
