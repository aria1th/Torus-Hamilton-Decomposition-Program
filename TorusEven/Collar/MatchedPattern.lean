-- STATUS: main-path
import TorusEven.Collar.MatchedData

namespace TorusEven.Collar.Incidence.MatchedData

variable {B Q Ω : Type*} {A : B → Finset Ω} {m : ℕ}
variable (D : MatchedData (Q := Q) A m)

theorem sum_query [Fintype B] [Fintype Q] {M : Type*} [AddCommMonoid M] (f : Q → M) :
    (∑ b, (D.query b).elim 0 f) = ∑ q, f q := by
  classical
  have he (b : B) : (D.query b).elim 0 f = ∑ q, if D.anchor q = b then f q else 0 := by
    cases h : D.query b with
    | none => simp [(D.query_none b).mp h]
    | some q =>
      rw [← (D.query_some b q).mp h]
      simp [D.anchor.injective.eq_iff]
  simp only [he]
  rw [Finset.sum_comm]
  simp

variable [DecidableEq Q] [DecidableEq Ω]
variable (J : B → ZMod m → Finset Ω) (hJ : ∀ b t, J b t ⊆ D.residual b)
include hJ

theorem pattern_subset (b : B) (t : ZMod m) : D.pattern J b t ⊆ D.fullSupport b := by
  have hmapped : (J b t).map Function.Embedding.inr ⊆ D.fullSupport b := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_insert_of_mem (Finset.mem_map.mpr
      ⟨c, D.residual_subset b (hJ b t hc), rfl⟩)
  cases h : D.query b with
  | none => simpa only [pattern, h] using hmapped
  | some q =>
    simp only [pattern, h]
    apply switchedRow_subset _ _ _ _ _ _ hmapped
    · simp [fullSupport, D.active_of_query h]
    · simp [fullSupport, D.eligible_of_query h]

theorem pattern_card (hcard : ∀ b t, (J b t).card = D.quota b) (b : B) (t : ZMod m) :
    (D.pattern J b t).card = (D.fullSupport b).card / 2 := by
  rw [card_fullSupport]
  cases h : D.query b with
  | none => simp only [pattern, h, Finset.card_map, hcard, quota,
      Option.isSome_none, Bool.false_eq_true, if_false, Nat.sub_zero]
  | some q =>
    have hactive : Sum.inl q ∉ (J b t).map (Function.Embedding.inr : Ω ↪ Q ⊕ Ω) := by simp
    have hmate : Sum.inr (D.mate q) ∉ (J b t).map (Function.Embedding.inr : Ω ↪ Q ⊕ Ω) := by
      simpa using fun hc => D.mate_not_residual h (hJ b t hc)
    simp only [pattern, h]
    rw [card_switchedRow _ _ _ _ _ hactive hmate, Finset.card_map, hcard]
    simp only [quota, h, Option.isSome_some, if_true]
    have ha := Finset.card_pos.mpr ⟨D.mate q, D.eligible_of_query h⟩
    omega

omit J hJ in
theorem fullSupport_some {b : B} {q : Q} (h : D.query b = some q) :
    D.fullSupport b = insert (.inl q) (insert (.inr (D.mate q))
      ((D.residual b).map Function.Embedding.inr)) := by
  simp only [fullSupport, D.active_of_query h, residual, h]
  apply congrArg (fun S : Finset (Q ⊕ Ω) => insert (.inl q) S)
  calc
    (A b).map Function.Embedding.inr =
        (insert (D.mate q) ((A b).erase (D.mate q))).map Function.Embedding.inr :=
      congrArg (fun S : Finset Ω => S.map (Function.Embedding.inr : Ω ↪ Q ⊕ Ω))
        (Finset.insert_erase (D.eligible_of_query h)).symm
    _ = _ := Finset.map_insert _ _ _

theorem complement_pattern (b : B) (t : ZMod m) : D.fullSupport b \ D.pattern J b t =
    match D.query b with
    | none => insert (.inl (D.active b)) ((D.residual b \ J b t).map Function.Embedding.inr)
    | some q => switchedRow (.inr (D.mate q)) (.inl q) (D.event q) t
        ((D.residual b \ J b t).map Function.Embedding.inr) := by
  cases h : D.query b with
  | none =>
    ext x
    cases x <;> simp [fullSupport, pattern, residual, h]
  | some q =>
    rw [D.fullSupport_some h]
    simp only [pattern, h, Finset.map_sdiff]
    apply complement_switchedRow
    · simp
    · simp
    · simp [D.mate_not_residual h]
    · exact Finset.map_subset_map.mpr (hJ b t)

end TorusEven.Collar.Incidence.MatchedData
