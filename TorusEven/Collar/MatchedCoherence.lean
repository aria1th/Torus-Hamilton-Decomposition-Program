-- STATUS: main-path
import TorusEven.Collar.MatchedRows
import TorusEven.Collar.ComponentPairs

namespace TorusEven.Collar.Incidence.MatchedData.ResidualRows

variable {B Q Ω : Type*} [DecidableEq Ω] {A : B → Finset Ω} {m : ℕ}
variable {D : MatchedData (Q := Q) A m} (R : D.ResidualRows) (hm : 4 ≤ m)

theorem row_coherent_none {b : B} (h : D.query b = none) (hsize : 2 ≤ D.quota b) :
    Coherent (R.row hm b) := by
  let e := fourRanks hm (0 : ZMod m)
  apply (R.pairs b).coherent_row (R.event hm b) (R.fillers b) false (e 0) (e 1) (e 2)
    (e.injective.ne (by decide)) (e.injective.ne (by decide)) (e.injective.ne (by decide))
  · intro i
    simp only [event, h]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  · intro hn
    refine ⟨⟨⟨0, by omega⟩, ?_⟩, ⟨⟨1, by omega⟩, ?_⟩⟩ <;> simp [event, h, e]
  · rw [R.filler_card]
    exact hsize

variable [DecidableEq Q]

theorem selected_coherent (b : B) (hb : 2 ≤ (D.fullSupport b).card / 2) :
    Coherent (D.pattern (R.row hm) b) := by
  change Coherent (fun t => D.pattern (R.row hm) b t)
  cases h : D.query b with
  | none =>
    simp only [pattern, h]
    apply coherent_of_map_subset (R.row hm b) _ Sum.inr
      (fun _ x hx => Finset.mem_map.mpr ⟨x, hx, rfl⟩)
    apply R.row_coherent_none hm h
    simpa only [quota, h, Option.isSome_none, Bool.false_eq_true, if_false,
      Nat.sub_zero, card_fullSupport] using hb
  | some q =>
    simp only [pattern, h]
    apply coherent_switchedRow _ _ _ (fourRanks hm (D.event q) 3)
    · simpa only [fourRanks_zero] using (fourRanks hm (D.event q)).injective.ne
        (by decide : (3 : Fin 4) ≠ 0)
    · have he := congrArg (fun F : Finset Ω => F.map (Function.Embedding.inr : Ω ↪ Q ⊕ Ω))
        (R.row_baseline hm h)
      dsimp only at he
      rw [← he, Finset.inter_self, Finset.map_nonempty, ← Finset.card_pos, R.row_card]
      simp only [quota, h, Option.isSome_some, if_true]
      rw [card_fullSupport] at hb
      omega

theorem complement_coherent (b : B)
    (hb : 2 ≤ (D.fullSupport b).card - (D.fullSupport b).card / 2) :
    Coherent (fun t => D.fullSupport b \ D.pattern (R.row hm) b t) := by
  simp only [D.complement_pattern (R.row hm) (R.row_subset hm) b]
  cases h : D.query b with
  | none => exact coherent_insert _ _
  | some q =>
    apply coherent_switchedRow _ _ _ (fourRanks hm (D.event q) 3)
    · simpa only [fourRanks_zero] using (fourRanks hm (D.event q)).injective.ne
        (by decide : (3 : Fin 4) ≠ 0)
    · have he := congrArg
        (fun F : Finset Ω => (D.residual b \ F).map (Function.Embedding.inr : Ω ↪ Q ⊕ Ω))
        (R.row_baseline hm h)
      dsimp only at he
      rw [← he, Finset.inter_self, Finset.map_nonempty, ← Finset.card_pos,
        Finset.card_sdiff_of_subset (R.row_subset hm b (D.event q)), R.row_card, D.residual_card]
      simp only [quota, h, Option.isSome_some, if_true]
      rw [card_fullSupport] at hb
      omega

end TorusEven.Collar.Incidence.MatchedData.ResidualRows
