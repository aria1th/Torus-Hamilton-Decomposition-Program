-- STATUS: main-path
import TorusEven.Collar.ReservedRows

namespace TorusEven.Collar.Incidence

variable {B Q Ω : Type*}

structure MatchedData (A : B → Finset Ω) (m : ℕ) where
  active : B → Q
  anchor : Q ↪ B
  mate : Q ↪ Ω
  event : Q → ZMod m
  active_anchor : ∀ q, active (anchor q) = q
  eligible : ∀ q, mate q ∈ A (anchor q)

namespace MatchedData

variable {A : B → Finset Ω} {m : ℕ} (D : MatchedData (Q := Q) A m)

noncomputable def query (b : B) : Option Q := by
  classical
  exact if h : ∃ q, D.anchor q = b then some h.choose else none

theorem query_some (b : B) (q : Q) : D.query b = some q ↔ D.anchor q = b := by
  classical
  unfold query
  split_ifs with h
  · rw [Option.some.injEq]
    constructor
    · intro he
      exact he ▸ h.choose_spec
    · intro he
      exact D.anchor.injective (h.choose_spec.trans he.symm)
  · simp only [false_iff]
    exact fun he => h ⟨q, he⟩

@[simp] theorem query_anchor (q : Q) : D.query (D.anchor q) = some q :=
  (D.query_some _ _).mpr rfl

theorem query_none (b : B) : D.query b = none ↔ ∀ q, D.anchor q ≠ b := by
  classical
  simp [query]

theorem active_of_query {b : B} {q : Q} (h : D.query b = some q) : D.active b = q := by
  rw [← (D.query_some b q).mp h, D.active_anchor]

theorem eligible_of_query {b : B} {q : Q} (h : D.query b = some q) : D.mate q ∈ A b := by
  rw [← (D.query_some b q).mp h]
  exact D.eligible q

def mates [Fintype Q] : Finset Ω := Finset.univ.map D.mate

@[simp] theorem mem_mates [Fintype Q] (x : Ω) : x ∈ D.mates ↔ ∃ q, D.mate q = x := by
  simp [mates]

variable [DecidableEq Ω]

def nonmates [Fintype Q] [Fintype Ω] : Finset Ω := Finset.univ \ D.mates

@[simp] theorem mem_nonmates [Fintype Q] [Fintype Ω] (x : Ω) :
    x ∈ D.nonmates ↔ x ∉ D.mates := by simp [nonmates]

noncomputable def residual (b : B) : Finset Ω :=
  match D.query b with
  | none => A b
  | some q => (A b).erase (D.mate q)

noncomputable def quota (b : B) : ℕ :=
  ((A b).card + 1) / 2 - if (D.query b).isSome then 1 else 0

theorem residual_subset (b : B) : D.residual b ⊆ A b := by
  unfold residual
  split
  · exact Finset.Subset.refl _
  · exact Finset.erase_subset _ _

theorem mate_not_residual {b : B} {q : Q} (h : D.query b = some q) :
    D.mate q ∉ D.residual b := by simp [residual, h]

theorem residual_card (b : B) :
    (D.residual b).card = (A b).card - if (D.query b).isSome then 1 else 0 := by
  cases h : D.query b with
  | none => simp [residual, h]
  | some q => simp [residual, h, Finset.card_erase_of_mem (D.eligible_of_query h)]

theorem quota_bounds (b : B) (P : LocalPairs (D.residual b)) :
    P.count ≤ D.quota b ∧ D.quota b + P.count ≤ (D.residual b).card := by
  have hc := P.count_le
  have hr := D.residual_card b
  unfold quota
  cases h : D.query b with
  | none =>
    simp only [h, Option.isSome_none, Bool.false_eq_true, if_false, Nat.sub_zero] at *
    omega
  | some q =>
    have ha := Finset.card_pos.mpr ⟨D.mate q, D.eligible_of_query h⟩
    simp only [h, Option.isSome_some, if_true] at *
    omega

variable [DecidableEq Q]

def fullSupport (b : B) : Finset (Q ⊕ Ω) :=
  insert (.inl (D.active b)) ((A b).map Function.Embedding.inr)

@[simp] theorem card_fullSupport (b : B) : (D.fullSupport b).card = (A b).card + 1 := by
  simp [fullSupport]

noncomputable def pattern (J : B → ZMod m → Finset Ω) (b : B) (t : ZMod m) : Finset (Q ⊕ Ω) :=
  match D.query b with
  | none => (J b t).map Function.Embedding.inr
  | some q => switchedRow (.inl q) (.inr (D.mate q)) (D.event q) t
      ((J b t).map Function.Embedding.inr)

theorem mem_pattern_left (J : B → ZMod m → Finset Ω) (b : B) (t : ZMod m) (q : Q) :
    Sum.inl q ∈ D.pattern J b t ↔ b = D.anchor q ∧ t = D.event q := by
  classical
  cases h : D.query b with
  | none =>
    have hb : b ≠ D.anchor q := ((D.query_none b).mp h q).symm
    simp [pattern, h, hb]
  | some r =>
    have hb := (D.query_some b r).mp h
    by_cases hr : q = r
    · subst r
      rw [← hb]
      by_cases ht : t = D.event q <;> simp [pattern, switchedRow, ht]
    · have hbq : b ≠ D.anchor q := by
        intro he
        exact hr (D.anchor.injective (he.symm.trans hb.symm))
      by_cases ht : t = D.event r <;> simp [pattern, h, switchedRow, ht, hr, hbq]

end MatchedData
end TorusEven.Collar.Incidence
