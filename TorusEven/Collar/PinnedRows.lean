-- STATUS: main-path
import TorusEven.Collar.PairRows

namespace TorusEven.Collar.LocalPairs

variable {Ω : Type*} [DecidableEq Ω] {A : Finset Ω} (P : LocalPairs A)

theorem exists_event_bits (active : Finset Ω) (hactive : (A ∩ active).card ≤ 1) :
    ∃ event : Fin P.count → Bool,
      (∀ p, P.endpoint p ∈ active → event p.1 = p.2) ∧
      (2 ≤ P.count → Function.Surjective event) := by
  classical
  by_cases h : ∃ p, P.endpoint p ∈ active
  · obtain ⟨⟨i, b⟩, hi⟩ := h
    let event : Fin P.count → Bool := fun j => if j = i then b else !b
    refine ⟨event, ?_, ?_⟩
    · intro p hp
      have heq : p = (i, b) := P.endpoint.injective
        (Finset.card_le_one.mp hactive _ (Finset.mem_inter.mpr ⟨P.mem_endpoint _, hp⟩)
          _ (Finset.mem_inter.mpr ⟨P.mem_endpoint _, hi⟩))
      simp [heq, event]
    · intro hn
      haveI : Nontrivial (Fin P.count) := Fintype.one_lt_card_iff_nontrivial.mp (by simpa using hn)
      obtain ⟨j, hj⟩ := exists_ne i
      intro c
      by_cases hc : c = b
      · exact ⟨i, by simp [event, hc]⟩
      · have hc' : c = !b := by cases c <;> cases b <;> simp_all
        exact ⟨j, by simp [event, hj, hc']⟩
  · refine ⟨fun i => decide (i.val ≠ 0), ?_, ?_⟩
    · intro p hp
      exact (h ⟨p, hp⟩).elim
    · intro hn c
      cases c
      · exact ⟨⟨0, by omega⟩, rfl⟩
      · exact ⟨⟨1, by omega⟩, rfl⟩

theorem exists_fillers (active : Finset Ω) (hactive : (A ∩ active).card ≤ 1) :
    ∃ F : Finset Ω, F ⊆ A ∧ Disjoint F P.support ∧ Disjoint F active ∧
      F.card + P.count = A.card / 2 := by
  have hp := P.count_le
  have hsmall : (active ∩ (A \ P.support)).card ≤ 1 := by
    apply (Finset.card_le_card ?_).trans hactive
    intro x hx
    exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_inter.mp hx).2).1,
      (Finset.mem_inter.mp hx).1⟩
  have havail : A.card / 2 - P.count ≤ ((A \ P.support) \ active).card := by
    rw [Finset.card_sdiff, Finset.card_sdiff_of_subset P.support_subset, P.card_support]
    omega
  obtain ⟨F, hF, hc⟩ := Finset.exists_subset_card_eq havail
  refine ⟨F, ?_, ?_, ?_, by omega⟩
  · intro x hx
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (hF hx)).1).1
  · apply Finset.disjoint_left.mpr
    intro x hx hs
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (hF hx)).1).2 hs
  · apply Finset.disjoint_left.mpr
    intro x hx ha
    exact (Finset.mem_sdiff.mp (hF hx)).2 ha

theorem row_pinned {R : Type*} [DecidableEq R] (r₀ r₁ : R) (hne : r₀ ≠ r₁)
    (active F : Finset Ω) (hF : Disjoint F active) (event : Fin P.count → Bool)
    (hpin : ∀ p, P.endpoint p ∈ active → event p.1 = p.2) :
    Disjoint (P.row (fun i => if event i then r₁ else r₀) F false r₀) active := by
  apply Finset.disjoint_left.mpr
  intro x hx ha
  rcases Finset.mem_union.mp hx with hf | hc
  · exact Finset.disjoint_left.mp hF hf ha
  · obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hc
    have h := hpin _ (hi ▸ ha)
    change event i = if r₀ = (if event i then r₁ else r₀) then !false else false at h
    cases he : event i <;> simp [he, hne] at h

end TorusEven.Collar.LocalPairs
