-- STATUS: main-path
import TorusEven.Collar.LocalPairs

namespace TorusEven.Collar.LocalPairs

variable {Ω R : Type*} [DecidableEq Ω] [DecidableEq R] {A : Finset Ω} (P : LocalPairs A)

def choice (event : Fin P.count → R) (side : Bool) (t : R) : Fin P.count ↪ Ω where
  toFun i := P.endpoint (i, if t = event i then !side else side)
  inj' _ _ h := congrArg Prod.fst (P.endpoint.injective h)

def chosen (event : Fin P.count → R) (side : Bool) (t : R) : Finset Ω :=
  Finset.univ.map (P.choice event side t)

def row (event : Fin P.count → R) (F : Finset Ω) (side : Bool) (t : R) : Finset Ω :=
  F ∪ P.chosen event side t

omit [DecidableEq Ω] in
theorem chosen_subset (event : Fin P.count → R) (side : Bool) (t : R) :
    P.chosen event side t ⊆ P.support := by
  rintro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
  exact P.mem_support.mpr ⟨_, rfl⟩

theorem row_subset (event : Fin P.count → R) (F : Finset Ω) (hF : F ⊆ A)
    (side : Bool) (t : R) : P.row event F side t ⊆ A :=
  Finset.union_subset hF ((P.chosen_subset event side t).trans P.support_subset)

theorem card_row (event : Fin P.count → R) (F : Finset Ω) (hF : Disjoint F P.support)
    (side : Bool) (t : R) : (P.row event F side t).card = F.card + P.count := by
  rw [row, Finset.card_union_of_disjoint (hF.mono_right (P.chosen_subset event side t))]
  simp [chosen]

theorem sum_row {M : Type*} [AddCommMonoid M] (f : Ω → M)
    (event : Fin P.count → R) (F : Finset Ω) (hF : Disjoint F P.support) (side : Bool) (t : R) :
    ∑ x ∈ P.row event F side t, f x =
      (∑ x ∈ F, f x) + ∑ i, f (P.endpoint (i, if t = event i then !side else side)) := by
  rw [row, Finset.sum_union (hF.mono_right (P.chosen_subset event side t)), chosen, Finset.sum_map]
  rfl

omit [DecidableEq Ω] in
@[simp] theorem endpoint_mem_chosen (event : Fin P.count → R) (side : Bool) (t : R)
    (i : Fin P.count) (b : Bool) :
    P.endpoint (i, b) ∈ P.chosen event side t ↔ b = if t = event i then !side else side := by
  simp [chosen, choice, P.endpoint.injective.eq_iff, eq_comm]

omit [DecidableEq Ω] in
theorem endpoint_not_mem_filler (F : Finset Ω) (hF : Disjoint F P.support)
    (p : Fin P.count × Bool) :
    P.endpoint p ∉ F := by
  intro h
  exact Finset.disjoint_left.mp hF h (P.mem_support.mpr ⟨p, rfl⟩)

theorem endpoint_mem_row (event : Fin P.count → R) (F : Finset Ω) (hF : Disjoint F P.support)
    (side : Bool) (t : R) (i : Fin P.count) (b : Bool) :
    P.endpoint (i, b) ∈ P.row event F side t ↔ b = if t = event i then !side else side := by
  simp [row, P.endpoint_not_mem_filler F hF]

theorem complement_row (event : Fin P.count → R) (F : Finset Ω)
    (hF : Disjoint F P.support) (side : Bool) (t : R) :
    A \ P.row event F side t = P.row event (A \ (P.support ∪ F)) (!side) t := by
  have hF' : Disjoint (A \ (P.support ∪ F)) P.support := by
    apply Finset.disjoint_left.mpr
    intro x hx hs
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_left _ hs)
  ext x
  by_cases hs : x ∈ P.support
  · obtain ⟨⟨i, b⟩, rfl⟩ := P.mem_support.mp hs
    simp only [Finset.mem_sdiff, P.mem_endpoint, true_and,
      P.endpoint_mem_row event F hF, P.endpoint_mem_row event _ hF']
    cases b <;> cases side <;> by_cases ht : t = event i <;> simp [ht]
  · have hc (side : Bool) : x ∉ P.chosen event side t := fun h => hs (P.chosen_subset _ _ _ h)
    simp [row, hc, hs]

theorem coherent_row (event : Fin P.count → R) (F : Finset Ω) (side : Bool)
    (r₀ r₁ r₂ : R) (h01 : r₀ ≠ r₁) (h20 : r₂ ≠ r₀) (h21 : r₂ ≠ r₁)
    (hevent : ∀ i, event i = r₀ ∨ event i = r₁)
    (hboth : 2 ≤ P.count → (∃ i, event i = r₀) ∧ ∃ i, event i = r₁)
    (hsize : 2 ≤ F.card + P.count) : Incidence.Coherent (P.row event F side) := by
  have hmeet (t : R) : ∃ x, x ∈ P.row event F side t ∧ x ∈ P.row event F side r₂ := by
    by_cases hF : F.Nonempty
    · obtain ⟨x, hx⟩ := hF
      exact ⟨x, Finset.mem_union_left _ hx, Finset.mem_union_left _ hx⟩
    · have hcard : F.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hF)
      obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hboth (by omega)
      have hsome : ∃ k, t ≠ event k := by
        by_cases h : t = r₀
        · exact ⟨j, by rw [hj, h]; exact h01⟩
        · exact ⟨i, by rwa [hi]⟩
      obtain ⟨k, hk⟩ := hsome
      have hbase : r₂ ≠ event k := by
        rcases hevent k with h | h
        · rw [h]; exact h20
        · rw [h]; exact h21
      refine ⟨P.endpoint (k, side), Finset.mem_union_right _ ?_, Finset.mem_union_right _ ?_⟩ <;>
        simp [hk, hbase]
  intro t s
  obtain ⟨x, hx, hx'⟩ := hmeet t
  obtain ⟨y, hy, hy'⟩ := hmeet s
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ ⟨x, hx, hx'⟩)
    (Relation.EqvGen.rel _ _ ⟨y, hy', hy⟩)

theorem sum_rows {m : ℕ} [NeZero m] (f : Ω → ZMod m)
    (event : Fin P.count → ZMod m) (F : Finset Ω) (hF : Disjoint F P.support) :
    (∑ t : ZMod m, ∑ x ∈ P.row event F false t, f x) =
      ∑ i, (f (P.endpoint (i, true)) - f (P.endpoint (i, false))) := by
  simp only [P.sum_row f event F hF, Finset.sum_add_distrib]
  have hconst : (∑ _ : ZMod m, ∑ x ∈ F, f x) = 0 := by
    simp [ZMod.card, nsmul_eq_mul]
  rw [hconst, zero_add, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hentry (t : ZMod m) : f (P.endpoint (i, if t = event i then !false else false)) =
      f (P.endpoint (i, false)) + if t = event i then
        f (P.endpoint (i, true)) - f (P.endpoint (i, false)) else 0 := by
    by_cases h : t = event i <;> simp [h]
  simp only [hentry, Finset.sum_add_distrib]
  simp [ZMod.card, nsmul_eq_mul]

end TorusEven.Collar.LocalPairs
