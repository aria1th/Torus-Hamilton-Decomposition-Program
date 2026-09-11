-- STATUS: main-path
import TorusEven.Collar.MatchedRows

namespace TorusEven.Collar.Incidence.MatchedData

variable {B Q Ω : Type*} [Fintype B] [Fintype Q] [DecidableEq Q] [DecidableEq Ω]
variable {A : B → Finset Ω} {m : ℕ} [NeZero m] (D : MatchedData (Q := Q) A m)

theorem pattern_sum (f : Q ⊕ Ω → ZMod m) (J : B → ZMod m → Finset Ω)
    (hJ : ∀ b t, J b t ⊆ D.residual b) :
    (∑ b, ∑ t : ZMod m, ∑ x ∈ D.pattern J b t, f x) =
      (∑ b, ∑ t : ZMod m, ∑ c ∈ J b t, f (.inr c)) +
        ∑ q, (f (.inl q) - f (.inr (D.mate q))) := by
  classical
  have hb (b : B) : (∑ t : ZMod m, ∑ x ∈ D.pattern J b t, f x) =
      (∑ t : ZMod m, ∑ c ∈ J b t, f (.inr c)) +
        (D.query b).elim 0 (fun q => f (.inl q) - f (.inr (D.mate q))) := by
    cases h : D.query b with
    | none => simp [pattern, h]
    | some q =>
      have ha (t : ZMod m) : Sum.inl q ∉ (J b t).map (Function.Embedding.inr : Ω ↪ Q ⊕ Ω) :=
        by simp
      have hc (t : ZMod m) : Sum.inr (D.mate q) ∉
          (J b t).map (Function.Embedding.inr : Ω ↪ Q ⊕ Ω) := by
        simpa using fun hx => D.mate_not_residual h (hJ b t hx)
      simp only [pattern, h, Option.elim_some]
      rw [sum_switchedRows f _ _ _ _ ha hc]
      simp [add_comm]
  simp only [hb, Finset.sum_add_distrib, D.sum_query]

omit [Fintype Q] in
theorem active_card (J : B → ZMod m → Finset Ω) (q : Q) :
    (Finset.univ.filter (fun p : B × ZMod m => Sum.inl q ∈ D.pattern J p.1 p.2)).card = 1 := by
  classical
  have h : Finset.univ.filter (fun p : B × ZMod m => Sum.inl q ∈ D.pattern J p.1 p.2) =
      {(D.anchor q, D.event q)} := by
    ext p
    simp [D.mem_pattern_left, Prod.ext_iff]
  rw [h, Finset.card_singleton]

omit [Fintype B] [DecidableEq Q] [NeZero m] in
theorem sum_mate_indicator (c : Ω) :
    (∑ q, if D.mate q = c then (1 : ZMod m) else 0) = if c ∈ D.mates then 1 else 0 := by
  classical
  have h := Finset.sum_map Finset.univ D.mate (fun x : Ω => if x = c then (1 : ZMod m) else 0)
  simpa only [mates, Finset.sum_ite_eq', Finset.mem_univ, if_true] using h.symm

namespace ResidualRows

variable {D} (R : D.ResidualRows) (hm : 4 ≤ m)

omit [Fintype Q] [DecidableEq Q] in
theorem auxiliary_sum (c : Ω) :
    (∑ b, ∑ t : ZMod m, ∑ x ∈ R.row hm b t, if x = c then (1 : ZMod m) else 0) =
      ((∑ b, (R.pairs b).divergence c : ℤ) : ZMod m) := by
  simp only [row, LocalPairs.sum_rows _ _ _ _ (R.filler_disjoint _), LocalPairs.divergence,
    Int.cast_sum, Int.cast_sub, apply_ite, Int.cast_one, Int.cast_zero]

theorem auxiliary_carry (c : Ω) :
    (∑ b, ∑ t : ZMod m, if Sum.inr c ∈ D.pattern (R.row hm) b t then (1 : ZMod m) else 0) =
      ((∑ b, (R.pairs b).divergence c : ℤ) : ZMod m) - if c ∈ D.mates then 1 else 0 := by
  classical
  have h := D.pattern_sum (fun x => if x = Sum.inr c then 1 else 0)
    (R.row hm) (R.row_subset hm)
  simp only [Sum.inr.injEq, Sum.inl_ne_inr, if_false, zero_sub] at h
  rw [R.auxiliary_sum hm, Finset.sum_neg_distrib, D.sum_mate_indicator] at h
  simpa only [Finset.sum_ite_eq', sub_eq_add_neg] using h

end ResidualRows
end TorusEven.Collar.Incidence.MatchedData
