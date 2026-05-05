import Mathlib

namespace RoundComposite
namespace ActiveHall

open scoped BigOperators

/--
An active-incidence instance for the Hall-symboling layer.

At each base vertex `x`, exactly `T` colors are active.  A symboling will assign
the symbols `Fin T` bijectively to this active set.
-/
structure Incidence (T : Nat) (X C : Type*) [Fintype X] [Fintype C]
    [DecidableEq C] where
  active : X → Finset C
  active_card : ∀ x : X, (active x).card = T

namespace Incidence

def colorDegree {T : Nat} {X C : Type*} [Fintype X] [Fintype C]
    [DecidableEq X] [DecidableEq C] (I : Incidence T X C) (c : C) : Nat :=
  ((Finset.univ : Finset X).filter (fun x => c ∈ I.active x)).card

def choiceDegree {X C : Type*} [Fintype X] [DecidableEq X] [DecidableEq C]
    (choice : X → C) (c : C) : Nat :=
  ((Finset.univ : Finset X).filter (fun x => choice x = c)).card

def choiceDegreeOn {X C : Type*} [DecidableEq X] [DecidableEq C]
    (E : Finset X) (choice : X → C) (c : C) : Nat :=
  (E.filter (fun x => choice x = c)).card

theorem choiceDegreeOn_le_card {X C : Type*} [DecidableEq X] [DecidableEq C]
    (E : Finset X) (choice : X → C) (c : C) :
    choiceDegreeOn E choice c ≤ E.card := by
  unfold choiceDegreeOn
  exact Finset.card_filter_le E (fun x => choice x = c)

theorem choiceDegreeOn_mono_set {X C : Type*} [DecidableEq X] [DecidableEq C]
    {E₁ E₂ : Finset X} (hE : E₁ ⊆ E₂) (choice : X → C) (c : C) :
    choiceDegreeOn E₁ choice c ≤ choiceDegreeOn E₂ choice c := by
  unfold choiceDegreeOn
  exact Finset.card_le_card (by
    intro x hx
    exact Finset.mem_filter.mpr
      ⟨hE (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩)

theorem choiceDegreeOn_le_choiceDegree {X C : Type*}
    [Fintype X] [DecidableEq X] [DecidableEq C]
    (E : Finset X) (choice : X → C) (c : C) :
    choiceDegreeOn E choice c ≤ choiceDegree choice c := by
  unfold choiceDegreeOn choiceDegree
  exact Finset.card_le_card (by
    intro x hx
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ x, (Finset.mem_filter.mp hx).2⟩)

theorem choiceDegreeOn_univ {X C : Type*}
    [Fintype X] [DecidableEq X] [DecidableEq C]
    (choice : X → C) (c : C) :
    choiceDegreeOn (Finset.univ : Finset X) choice c =
      choiceDegree choice c := by
  rfl

def choiceHitCount {X C : Type*} [Fintype X] [DecidableEq X]
    [DecidableEq C] (choice : X → C) (U : Finset C) : Nat :=
  ((Finset.univ : Finset X).filter (fun x => choice x ∈ U)).card

def choiceHitCountOn {X C : Type*} [DecidableEq X] [DecidableEq C]
    (E : Finset X) (choice : X → C) (U : Finset C) : Nat :=
  (E.filter (fun x => choice x ∈ U)).card

theorem choiceHitCountOn_le_card {X C : Type*}
    [DecidableEq X] [DecidableEq C]
    (E : Finset X) (choice : X → C) (U : Finset C) :
    choiceHitCountOn E choice U ≤ E.card := by
  unfold choiceHitCountOn
  exact Finset.card_filter_le E (fun x => choice x ∈ U)

theorem choiceHitCountOn_mono_set {X C : Type*}
    [DecidableEq X] [DecidableEq C]
    {E₁ E₂ : Finset X} (hE : E₁ ⊆ E₂) (choice : X → C)
    (U : Finset C) :
    choiceHitCountOn E₁ choice U ≤ choiceHitCountOn E₂ choice U := by
  unfold choiceHitCountOn
  exact Finset.card_le_card (by
    intro x hx
    exact Finset.mem_filter.mpr
      ⟨hE (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩)

theorem choiceHitCountOn_mono_colors {X C : Type*}
    [DecidableEq X] [DecidableEq C]
    (E : Finset X) (choice : X → C) {U₁ U₂ : Finset C}
    (hU : U₁ ⊆ U₂) :
    choiceHitCountOn E choice U₁ ≤ choiceHitCountOn E choice U₂ := by
  unfold choiceHitCountOn
  exact Finset.card_le_card (by
    intro x hx
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hx).1, hU (Finset.mem_filter.mp hx).2⟩)

theorem choiceHitCountOn_le_choiceHitCount {X C : Type*}
    [Fintype X] [DecidableEq X] [DecidableEq C]
    (E : Finset X) (choice : X → C) (U : Finset C) :
    choiceHitCountOn E choice U ≤ choiceHitCount choice U := by
  unfold choiceHitCountOn choiceHitCount
  exact Finset.card_le_card (by
    intro x hx
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ x, (Finset.mem_filter.mp hx).2⟩)

theorem choiceHitCountOn_univ {X C : Type*}
    [Fintype X] [DecidableEq X] [DecidableEq C]
    (choice : X → C) (U : Finset C) :
    choiceHitCountOn (Finset.univ : Finset X) choice U =
      choiceHitCount choice U := by
  rfl

def lowCutSet {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence (T + 1) X C) (U : Finset C)
    (S : Finset (Fin T)) : Finset X :=
  (Finset.univ : Finset X).filter
    (fun x => (I.active x ∩ U).card ≤ S.card)

theorem lowCutSet_mono_symbols {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence (T + 1) X C) (U : Finset C)
    {S₁ S₂ : Finset (Fin T)} (hS : S₁.card ≤ S₂.card) :
    lowCutSet I U S₁ ⊆ lowCutSet I U S₂ := by
  intro x hx
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ x, (Finset.mem_filter.mp hx).2.trans hS⟩

theorem lowCutSet_mono_symbols_of_subset {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence (T + 1) X C) (U : Finset C)
    {S₁ S₂ : Finset (Fin T)} (hS : S₁ ⊆ S₂) :
    lowCutSet I U S₁ ⊆ lowCutSet I U S₂ :=
  lowCutSet_mono_symbols I U (Finset.card_le_card hS)

theorem lowCutSet_colors_empty {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence (T + 1) X C) (S : Finset (Fin T)) :
    lowCutSet I (∅ : Finset C) S = Finset.univ := by
  ext x
  simp [lowCutSet]

theorem lowCutSet_colors_univ {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence (T + 1) X C) (S : Finset (Fin T)) :
    lowCutSet I (Finset.univ : Finset C) S = ∅ := by
  classical
  ext x
  constructor
  · intro hx
    have hactive :
        (I.active x ∩ (Finset.univ : Finset C)).card = T + 1 := by
      simp [I.active_card x]
    have hS : S.card ≤ T := by
      simpa using Finset.card_le_univ S
    have hle : (I.active x ∩ (Finset.univ : Finset C)).card ≤ S.card :=
      (Finset.mem_filter.mp hx).2
    rw [hactive] at hle
    omega
  · simp

def choiceLowHitCount {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence (T + 1) X C) (choice : X → C)
    (U : Finset C) (S : Finset (Fin T)) : Nat :=
  ((Finset.univ : Finset X).filter
    (fun x => choice x ∈ U ∧ (I.active x ∩ U).card ≤ S.card)).card

theorem choiceLowHitCount_symbols_empty {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence (T + 1) X C) (choice : X → C)
    (hchoice : ∀ x : X, choice x ∈ I.active x) (U : Finset C) :
    choiceLowHitCount I choice U (∅ : Finset (Fin T)) = 0 := by
  classical
  rw [choiceLowHitCount, Finset.card_eq_zero]
  ext x
  constructor
  · intro hx
    rcases Finset.mem_filter.mp hx with ⟨_hxuniv, hU, hle⟩
    have hmem : choice x ∈ I.active x ∩ U := by
      simp [hchoice x, hU]
    have hpos : 0 < (I.active x ∩ U).card :=
      Finset.card_pos.mpr ⟨choice x, hmem⟩
    have hle0 : (I.active x ∩ U).card ≤ 0 := by
      simpa using hle
    omega
  · simp

theorem choiceLowHitCount_colors_empty {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence (T + 1) X C) (choice : X → C)
    (S : Finset (Fin T)) :
    choiceLowHitCount I choice (∅ : Finset C) S = 0 := by
  simp [choiceLowHitCount]

theorem choiceLowHitCount_colors_univ {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence (T + 1) X C) (choice : X → C)
    (S : Finset (Fin T)) :
    choiceLowHitCount I choice (Finset.univ : Finset C) S = 0 := by
  classical
  rw [choiceLowHitCount, Finset.card_eq_zero]
  ext x
  constructor
  · intro hx
    rcases Finset.mem_filter.mp hx with ⟨_hxuniv, _hchoiceU, hle⟩
    have hactive :
        (I.active x ∩ (Finset.univ : Finset C)).card = T + 1 := by
      simp [I.active_card x]
    have hS : S.card ≤ T := by
      simpa using Finset.card_le_univ S
    rw [hactive] at hle
    omega
  · simp

theorem choiceLowHitCount_le_choiceHitCount {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence (T + 1) X C) (choice : X → C)
    (U : Finset C) (S : Finset (Fin T)) :
    choiceLowHitCount I choice U S ≤ choiceHitCount choice U := by
  unfold choiceLowHitCount choiceHitCount
  exact Finset.card_le_card (by
    intro x hx
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2.1⟩)

theorem choiceLowHitCount_eq_choiceHitCountOn_lowCutSet
    {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence (T + 1) X C) (choice : X → C)
    (U : Finset C) (S : Finset (Fin T)) :
    choiceLowHitCount I choice U S =
      choiceHitCountOn (lowCutSet I U S) choice U := by
  unfold choiceLowHitCount choiceHitCountOn lowCutSet
  congr 1
  ext x
  simp [and_comm]

theorem sum_choiceDegreeOn_on {X C : Type*}
    [DecidableEq X] [DecidableEq C]
    (E : Finset X) (choice : X → C) (U : Finset C) :
    (∑ c ∈ U, choiceDegreeOn E choice c) =
      choiceHitCountOn E choice U := by
  classical
  unfold choiceDegreeOn choiceHitCountOn
  calc
    (∑ c ∈ U, (E.filter (fun x => choice x = c)).card)
        = ∑ c ∈ U, ∑ x ∈ E, if choice x = c then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro c _hc
            rw [Finset.card_filter]
    _ = ∑ x ∈ E, ∑ c ∈ U, if choice x = c then 1 else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ x ∈ E, if choice x ∈ U then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro x _hx
            by_cases hx : choice x ∈ U
            · rw [Finset.sum_eq_single (choice x)]
              · simp [hx]
              · intro c _hc hne
                have hneq : choice x ≠ c := by
                  intro h
                  exact hne h.symm
                simp [hneq]
              · intro hnot
                exact False.elim (hnot hx)
            · have hneq : ∀ c ∈ U, choice x ≠ c := by
                intro c hc h
                exact hx (by rw [h]; exact hc)
              rw [if_neg hx]
              apply Finset.sum_eq_zero
              intro c hc
              simp [hneq c hc]
    _ = (E.filter (fun x => choice x ∈ U)).card := by
            rw [Finset.card_filter]

theorem sum_choiceDegreeOn_on_le_card {X C : Type*}
    [DecidableEq X] [DecidableEq C]
    (E : Finset X) (choice : X → C) (U : Finset C) :
    (∑ c ∈ U, choiceDegreeOn E choice c) ≤ E.card := by
  rw [sum_choiceDegreeOn_on]
  exact choiceHitCountOn_le_card E choice U

theorem sum_choiceDegreeOn_on_le_choiceHitCount {X C : Type*}
    [Fintype X] [DecidableEq X] [DecidableEq C]
    (E : Finset X) (choice : X → C) (U : Finset C) :
    (∑ c ∈ U, choiceDegreeOn E choice c) ≤ choiceHitCount choice U := by
  rw [sum_choiceDegreeOn_on]
  exact choiceHitCountOn_le_choiceHitCount E choice U

theorem sum_choiceDegreeOn_on_le_sum_choiceDegree {X C : Type*}
    [Fintype X] [DecidableEq X] [DecidableEq C]
    (E : Finset X) (choice : X → C) (U : Finset C) :
    (∑ c ∈ U, choiceDegreeOn E choice c)
      ≤ ∑ c ∈ U, choiceDegree choice c := by
  exact Finset.sum_le_sum (by
    intro c _hc
    exact choiceDegreeOn_le_choiceDegree E choice c)

theorem sum_choiceDegreeOn_on_mono_set {X C : Type*}
    [DecidableEq X] [DecidableEq C]
    {E₁ E₂ : Finset X} (hE : E₁ ⊆ E₂) (choice : X → C)
    (U : Finset C) :
    (∑ c ∈ U, choiceDegreeOn E₁ choice c)
      ≤ ∑ c ∈ U, choiceDegreeOn E₂ choice c := by
  exact Finset.sum_le_sum (by
    intro c _hc
    exact choiceDegreeOn_mono_set hE choice c)

theorem sum_choiceDegreeOn_on_mono_colors {X C : Type*}
    [DecidableEq X] [DecidableEq C]
    (E : Finset X) (choice : X → C) {U₁ U₂ : Finset C}
    (hU : U₁ ⊆ U₂) :
    (∑ c ∈ U₁, choiceDegreeOn E choice c)
      ≤ ∑ c ∈ U₂, choiceDegreeOn E choice c := by
  exact Finset.sum_le_sum_of_subset hU

def tokenLoadOn {X C : Type*} [Fintype X] [Fintype C]
    [DecidableEq X] [DecidableEq C] {n : C → Nat}
    (f : (Sigma fun c : C => Fin (n c)) ≃ X)
    (E : Finset X) (U : Finset C) : Nat :=
  ((Finset.univ : Finset (Sigma fun c : C => Fin (n c))).filter
    (fun q => q.1 ∈ U ∧ f q ∈ E)).card

theorem tokenLoadOn_eq_choiceHitCountOn {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {n : C → Nat} (f : (Sigma fun c : C => Fin (n c)) ≃ X)
    (E : Finset X) (U : Finset C) :
    tokenLoadOn f E U =
      choiceHitCountOn E (fun x : X => (f.symm x).1) U := by
  classical
  unfold tokenLoadOn choiceHitCountOn
  calc
    ((Finset.univ : Finset (Sigma fun c : C => Fin (n c))).filter
        (fun q => q.1 ∈ U ∧ f q ∈ E)).card
        =
      ∑ q : Sigma fun c : C => Fin (n c),
        if q.1 ∈ U ∧ f q ∈ E then 1 else 0 := by
          rw [Finset.card_filter]
    _ =
      ∑ x : X, if (f.symm x).1 ∈ U ∧ x ∈ E then 1 else 0 := by
          exact (Fintype.sum_equiv f.symm
            (fun x : X =>
              if (f.symm x).1 ∈ U ∧ x ∈ E then (1 : Nat) else 0)
            (fun q : Sigma fun c : C => Fin (n c) =>
              if q.1 ∈ U ∧ f q ∈ E then (1 : Nat) else 0)
            (by intro x; simp)).symm
    _ =
      ∑ x ∈ E, if (f.symm x).1 ∈ U then 1 else 0 := by
          calc
            (∑ x : X, if (f.symm x).1 ∈ U ∧ x ∈ E
                then (1 : Nat) else 0)
                =
              ∑ x : X, if x ∈ E then
                (if (f.symm x).1 ∈ U then (1 : Nat) else 0) else 0 := by
                  apply Finset.sum_congr rfl
                  intro x _hx
                  by_cases hxE : x ∈ E <;>
                    by_cases hxU : (f.symm x).1 ∈ U <;> simp [hxE, hxU]
            _ =
              ∑ x ∈ E, if (f.symm x).1 ∈ U then 1 else 0 := by
                  rw [← Finset.sum_filter]
                  simp
    _ = (E.filter (fun x : X => (f.symm x).1 ∈ U)).card := by
          rw [Finset.card_filter]

theorem tokenLoadOn_eq_sum_choiceDegreeOn {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {n : C → Nat} (f : (Sigma fun c : C => Fin (n c)) ≃ X)
    (E : Finset X) (U : Finset C) :
    tokenLoadOn f E U =
      ∑ c ∈ U, choiceDegreeOn E (fun x : X => (f.symm x).1) c := by
  rw [tokenLoadOn_eq_choiceHitCountOn, ← sum_choiceDegreeOn_on]

theorem tokenLoadOn_le_card {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {n : C → Nat} (f : (Sigma fun c : C => Fin (n c)) ≃ X)
    (E : Finset X) (U : Finset C) :
    tokenLoadOn f E U ≤ E.card := by
  rw [tokenLoadOn_eq_choiceHitCountOn]
  exact choiceHitCountOn_le_card E (fun x : X => (f.symm x).1) U

theorem tokenLoadOn_mono_set {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {n : C → Nat} (f : (Sigma fun c : C => Fin (n c)) ≃ X)
    {E₁ E₂ : Finset X} (hE : E₁ ⊆ E₂) (U : Finset C) :
    tokenLoadOn f E₁ U ≤ tokenLoadOn f E₂ U := by
  rw [tokenLoadOn_eq_choiceHitCountOn, tokenLoadOn_eq_choiceHitCountOn]
  exact choiceHitCountOn_mono_set hE (fun x : X => (f.symm x).1) U

theorem tokenLoadOn_mono_colors {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {n : C → Nat} (f : (Sigma fun c : C => Fin (n c)) ≃ X)
    (E : Finset X) {U₁ U₂ : Finset C} (hU : U₁ ⊆ U₂) :
    tokenLoadOn f E U₁ ≤ tokenLoadOn f E U₂ := by
  rw [tokenLoadOn_eq_choiceHitCountOn, tokenLoadOn_eq_choiceHitCountOn]
  exact choiceHitCountOn_mono_colors E (fun x : X => (f.symm x).1) hU

theorem tokenLoadOn_set_empty {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {n : C → Nat} (f : (Sigma fun c : C => Fin (n c)) ≃ X)
    (U : Finset C) :
    tokenLoadOn f (∅ : Finset X) U = 0 := by
  simp [tokenLoadOn]

theorem tokenLoadOn_colors_empty {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {n : C → Nat} (f : (Sigma fun c : C => Fin (n c)) ≃ X)
    (E : Finset X) :
    tokenLoadOn f E (∅ : Finset C) = 0 := by
  simp [tokenLoadOn]

theorem tokenLoadOn_colors_univ {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {n : C → Nat} (f : (Sigma fun c : C => Fin (n c)) ≃ X)
    (E : Finset X) :
    tokenLoadOn f E (Finset.univ : Finset C) = E.card := by
  rw [tokenLoadOn_eq_choiceHitCountOn]
  simp [choiceHitCountOn]

theorem choiceLowHitCount_eq_sum_choiceDegreeOn_lowCutSet
    {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence (T + 1) X C) (choice : X → C)
    (U : Finset C) (S : Finset (Fin T)) :
    choiceLowHitCount I choice U S =
      ∑ c ∈ U, choiceDegreeOn (lowCutSet I U S) choice c := by
  rw [choiceLowHitCount_eq_choiceHitCountOn_lowCutSet,
    sum_choiceDegreeOn_on]

def cutCap {T : Nat} {X C : Type*} [Fintype X] [Fintype C]
    [DecidableEq X] [DecidableEq C] (I : Incidence T X C)
    (U : Finset C) (S : Finset (Fin T)) : Nat :=
  ∑ x : X, min ((I.active x ∩ U).card) S.card

def hitCount {T : Nat} {X C : Type*} [Fintype X] [Fintype C]
    [DecidableEq X] [DecidableEq C] (I : Incidence T X C)
    (U : Finset C) : Nat :=
  ((Finset.univ : Finset X).filter
    (fun x : X => (I.active x ∩ U).Nonempty)).card

theorem sum_colorDegree {T : Nat} {X C : Type*} [Fintype X] [Fintype C]
    [DecidableEq X] [DecidableEq C] (I : Incidence T X C) :
    (∑ c : C, I.colorDegree c) = T * Fintype.card X := by
  classical
  calc
    (∑ c : C, I.colorDegree c)
        = ∑ c : C, ∑ x : X, if c ∈ I.active x then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro c _hc
            rw [colorDegree, Finset.card_filter]
    _ = ∑ x : X, ∑ c : C, if c ∈ I.active x then 1 else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ x : X, (I.active x).card := by
            apply Finset.sum_congr rfl
            intro x _hx
            simp
    _ = ∑ _x : X, T := by
            apply Finset.sum_congr rfl
            intro x _hx
            exact I.active_card x
    _ = T * Fintype.card X := by
            simp [Finset.sum_const, Nat.mul_comm]

theorem eq_of_mem_of_active_card_one {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq C]
    (I : Incidence 1 X C) {x : X} {a b : C}
    (ha : a ∈ I.active x) (hb : b ∈ I.active x) :
    a = b := by
  have hcard : (I.active x).card ≤ 1 := by
    rw [I.active_card x]
  exact (Finset.card_le_one.mp hcard) a ha b hb

def eraseChoice {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq C]
    (I : Incidence (T + 1) X C) (choice : X → C)
    (hchoice : ∀ x : X, choice x ∈ I.active x) :
    Incidence T X C where
  active := fun x => (I.active x).erase (choice x)
  active_card := by
    intro x
    rw [Finset.card_erase_of_mem (hchoice x), I.active_card x]
    omega

@[simp] theorem eraseChoice_active {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq C]
    (I : Incidence (T + 1) X C) (choice : X → C)
    (hchoice : ∀ x : X, choice x ∈ I.active x) (x : X) :
    (I.eraseChoice choice hchoice).active x =
      (I.active x).erase (choice x) :=
  rfl

theorem mem_eraseChoice_active {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq C]
    (I : Incidence (T + 1) X C) (choice : X → C)
    (hchoice : ∀ x : X, choice x ∈ I.active x)
    {x : X} {c : C} :
    c ∈ (I.eraseChoice choice hchoice).active x ↔
      c ∈ I.active x ∧ c ≠ choice x := by
  simp [eraseChoice, and_comm]

theorem eraseChoice_active_inter_card_add_indicator
    {T : Nat} {X C : Type*} [Fintype X] [Fintype C] [DecidableEq C]
    (I : Incidence (T + 1) X C) (choice : X → C)
    (hchoice : ∀ x : X, choice x ∈ I.active x)
    (x : X) (U : Finset C) :
    ((I.eraseChoice choice hchoice).active x ∩ U).card
        + (if choice x ∈ U then 1 else 0)
      = (I.active x ∩ U).card := by
  classical
  have hEq :
      (I.active x).erase (choice x) ∩ U =
        (I.active x ∩ U).erase (choice x) := by
    ext c
    by_cases hc : c = choice x <;> simp [hc]
  by_cases hU : choice x ∈ U
  · have hmem : choice x ∈ I.active x ∩ U := by
      simp [hchoice x, hU]
    have hpos : 0 < (I.active x ∩ U).card :=
      Finset.card_pos.mpr ⟨choice x, hmem⟩
    rw [eraseChoice_active, hEq, Finset.card_erase_of_mem hmem]
    simp [hU]
    omega
  · have hnotmem : choice x ∉ I.active x ∩ U := by
      simp [hU]
    rw [eraseChoice_active, hEq, Finset.erase_eq_of_notMem hnotmem]
    simp [hU]

theorem eraseChoice_colorDegree_add_choiceDegree
    {T : Nat} {X C : Type*} [Fintype X] [Fintype C]
    [DecidableEq X] [DecidableEq C]
    (I : Incidence (T + 1) X C) (choice : X → C)
    (hchoice : ∀ x : X, choice x ∈ I.active x) (c : C) :
    (I.eraseChoice choice hchoice).colorDegree c
      + choiceDegree choice c = I.colorDegree c := by
  classical
  let B : Finset X := (Finset.univ : Finset X).filter
    (fun x => c ∈ (I.eraseChoice choice hchoice).active x)
  let D : Finset X := (Finset.univ : Finset X).filter
    (fun x => choice x = c)
  let A : Finset X := (Finset.univ : Finset X).filter
    (fun x => c ∈ I.active x)
  have hdisj : Disjoint B D := by
    rw [Finset.disjoint_left]
    intro x hxB hxD
    have hxB' : c ≠ choice x ∧ c ∈ I.active x := by
      simpa [B] using hxB
    have hxD' : choice x = c := by
      simpa [D] using hxD
    exact hxB'.1 hxD'.symm
  have hUnion : B ∪ D = A := by
    ext x
    by_cases hxD : choice x = c
    · have hcx : c ∈ I.active x := by
        rw [← hxD]
        exact hchoice x
      simp [A, B, D, hxD, hcx]
    · by_cases hcx : c ∈ I.active x
      · have hxne : c ≠ choice x := by
          intro h
          exact hxD h.symm
        simp [A, B, D, hcx, hxD, hxne]
      · simp [A, B, D, hcx, hxD]
  change B.card + D.card = A.card
  rw [← hUnion, Finset.card_union_of_disjoint hdisj]

theorem sum_choiceDegree_on {X C : Type*}
    [Fintype X] [DecidableEq X] [DecidableEq C]
    (choice : X → C) (U : Finset C) :
    (∑ c ∈ U, choiceDegree choice c) = choiceHitCount choice U := by
  classical
  unfold choiceDegree choiceHitCount
  calc
    (∑ c ∈ U, ((Finset.univ : Finset X).filter
        (fun x => choice x = c)).card)
        = ∑ c ∈ U, ∑ x : X, if choice x = c then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro c _hc
            rw [Finset.card_filter]
    _ = ∑ x : X, ∑ c ∈ U, if choice x = c then 1 else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ x : X, if choice x ∈ U then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro x _hx
            by_cases hx : choice x ∈ U
            · rw [Finset.sum_eq_single (choice x)]
              · simp [hx]
              · intro c _hc hne
                have hneq : choice x ≠ c := by
                  intro h
                  exact hne h.symm
                simp [hneq]
              · intro hnot
                exact False.elim (hnot hx)
            · have hneq : ∀ c ∈ U, choice x ≠ c := by
                intro c hc h
                exact hx (by rw [h]; exact hc)
              rw [if_neg hx]
              apply Finset.sum_eq_zero
              intro c hc
              simp [hneq c hc]
    _ = ((Finset.univ : Finset X).filter
        (fun x => choice x ∈ U)).card := by
            rw [Finset.card_filter]

theorem sum_colorDegree_on {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (U : Finset C) :
    (∑ c ∈ U, I.colorDegree c)
      = ∑ x : X, (I.active x ∩ U).card := by
  classical
  calc
    (∑ c ∈ U, I.colorDegree c)
        = ∑ c ∈ U, ∑ x : X, if c ∈ I.active x then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro c _hc
            rw [colorDegree, Finset.card_filter]
    _ = ∑ x : X, ∑ c ∈ U, if c ∈ I.active x then 1 else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ x : X, (I.active x ∩ U).card := by
            apply Finset.sum_congr rfl
            intro x _hx
            have hfilter :
                U.filter (fun c : C => c ∈ I.active x) = I.active x ∩ U := by
              ext c
              simp [and_comm]
            rw [← hfilter]
            exact (Finset.card_filter (fun c : C => c ∈ I.active x) U).symm

theorem sum_colorDegree_on_le_hitCount_mul {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (U : Finset C) :
    (∑ c ∈ U, I.colorDegree c) ≤ T * I.hitCount U := by
  classical
  rw [I.sum_colorDegree_on U]
  calc
    (∑ x : X, (I.active x ∩ U).card)
        ≤ ∑ x : X,
            (if (I.active x ∩ U).Nonempty then T else 0) := by
          apply Finset.sum_le_sum
          intro x _hx
          by_cases hhit : (I.active x ∩ U).Nonempty
          · have hcard :
                (I.active x ∩ U).card ≤ (I.active x).card :=
              Finset.card_le_card (by
                intro c hc
                exact (Finset.mem_inter.mp hc).1)
            rw [I.active_card x] at hcard
            simpa [hhit] using hcard
          · have hzero : (I.active x ∩ U).card = 0 := by
              rw [Finset.card_eq_zero]
              exact Finset.not_nonempty_iff_eq_empty.mp hhit
            simp [hhit, hzero]
    _ = T * I.hitCount U := by
          rw [hitCount, Finset.card_filter]
          calc
            (∑ x : X,
              (if (I.active x ∩ U).Nonempty then T else 0))
                =
              ∑ x : X,
                T * (if (I.active x ∩ U).Nonempty then 1 else 0) := by
                  apply Finset.sum_congr rfl
                  intro x _hx
                  by_cases hhit : (I.active x ∩ U).Nonempty <;>
                    simp [hhit]
            _ = T *
                (∑ x : X,
                  (if (I.active x ∩ U).Nonempty then 1 else 0)) := by
                  rw [Finset.mul_sum]

theorem scaled_bary_point_le_cutCap_point
    {T a s : Nat} (haT : a ≤ T) (hsT : s ≤ T) :
    s * a ≤ T * min a s := by
  by_cases has : a ≤ s
  · rw [min_eq_left has]
    exact Nat.mul_le_mul_right a hsT
  · have hsa : s ≤ a := Nat.le_of_not_ge has
    rw [min_eq_right hsa]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right s haT

theorem scaled_bary_point_add_mixed_le_cutCap_point
    {T a s : Nat} (haT : a ≤ T) (hsT : s ≤ T) :
    s * a + (if 0 < a ∧ a < T then min s (T - s) else 0)
      ≤ T * min a s := by
  by_cases hmix : 0 < a ∧ a < T
  · have hapos : 0 < a := hmix.1
    have haLt : a < T := hmix.2
    by_cases has : a ≤ s
    · rw [if_pos hmix, min_eq_left has]
      have hmin_le_sub : min s (T - s) ≤ T - s := Nat.min_le_right _ _
      have hsub_le_mul : T - s ≤ (T - s) * a :=
        Nat.le_mul_of_pos_right (T - s) hapos
      calc
        s * a + min s (T - s)
            ≤ s * a + (T - s) * a := by
                exact Nat.add_le_add_left
                  (hmin_le_sub.trans hsub_le_mul) (s * a)
        _ = T * a := by
                rw [← Nat.add_mul, Nat.add_sub_of_le hsT]
    · have hsa : s ≤ a := Nat.le_of_not_ge has
      rw [if_pos hmix, min_eq_right hsa]
      have hmin_le_s : min s (T - s) ≤ s := Nat.min_le_left _ _
      have hsub_pos : 0 < T - a := Nat.sub_pos_of_lt haLt
      have hs_le_mul : s ≤ s * (T - a) :=
        Nat.le_mul_of_pos_right s hsub_pos
      calc
        s * a + min s (T - s)
            ≤ s * a + s * (T - a) := by
                exact Nat.add_le_add_left
                  (hmin_le_s.trans hs_le_mul) (s * a)
        _ = T * s := by
                rw [← Nat.mul_add, Nat.add_sub_of_le haT]
                exact Nat.mul_comm s T
  · simp [hmix, scaled_bary_point_le_cutCap_point haT hsT]

def mixedCount {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (U : Finset C) : Nat :=
  ∑ x : X,
    if 0 < (I.active x ∩ U).card ∧ (I.active x ∩ U).card < T
    then 1 else 0

theorem mixedCount_eq_card_filter {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (U : Finset C) :
    I.mixedCount U =
      ((Finset.univ : Finset X).filter
        (fun x =>
          0 < (I.active x ∩ U).card ∧
            (I.active x ∩ U).card < T)).card := by
  rw [mixedCount, Finset.card_filter]

theorem mixedCount_le_hitCount {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (U : Finset C) :
    I.mixedCount U ≤ I.hitCount U := by
  classical
  rw [I.mixedCount_eq_card_filter U]
  unfold hitCount
  apply Finset.card_le_card
  intro x hx
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ x,
      Finset.card_pos.mp (Finset.mem_filter.mp hx).2.1⟩

theorem mixedCount_le_hitCount_compl {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (U : Finset C) :
    I.mixedCount U ≤ I.hitCount Uᶜ := by
  classical
  rw [I.mixedCount_eq_card_filter U]
  unfold hitCount
  apply Finset.card_le_card
  intro x hx
  rcases (Finset.mem_filter.mp hx).2 with ⟨_hpos, hlt⟩
  have hnotSubset : ¬ I.active x ⊆ U := by
    intro hsubset
    have heq : I.active x ∩ U = I.active x := by
      ext c
      constructor
      · intro hc
        exact (Finset.mem_inter.mp hc).1
      · intro hc
        exact Finset.mem_inter.mpr ⟨hc, hsubset hc⟩
    have hcard :
        (I.active x ∩ U).card = T := by
      rw [heq, I.active_card x]
    omega
  rw [Finset.not_subset] at hnotSubset
  rcases hnotSubset with ⟨c, hcActive, hcNotU⟩
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ x, ?_⟩
  exact ⟨c, Finset.mem_inter.mpr
    ⟨hcActive, Finset.mem_compl.mpr hcNotU⟩⟩

theorem mixedCount_eq_card_filter_hit_and_compl
    {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (U : Finset C) :
    I.mixedCount U =
      ((Finset.univ : Finset X).filter
        (fun x =>
          (I.active x ∩ U).Nonempty ∧
            (I.active x ∩ Uᶜ).Nonempty)).card := by
  classical
  rw [I.mixedCount_eq_card_filter U]
  apply congrArg Finset.card
  ext x
  constructor
  · intro hx
    rcases (Finset.mem_filter.mp hx).2 with ⟨hpos, hlt⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ x, ?_⟩
    have hhit : (I.active x ∩ U).Nonempty := Finset.card_pos.mp hpos
    have hnotSubset : ¬ I.active x ⊆ U := by
      intro hsubset
      have heq : I.active x ∩ U = I.active x := by
        ext c
        constructor
        · intro hc
          exact (Finset.mem_inter.mp hc).1
        · intro hc
          exact Finset.mem_inter.mpr ⟨hc, hsubset hc⟩
      have hcard :
          (I.active x ∩ U).card = T := by
        rw [heq, I.active_card x]
      omega
    rw [Finset.not_subset] at hnotSubset
    rcases hnotSubset with ⟨c, hcActive, hcNotU⟩
    exact ⟨hhit, ⟨c, Finset.mem_inter.mpr
      ⟨hcActive, Finset.mem_compl.mpr hcNotU⟩⟩⟩
  · intro hx
    rcases (Finset.mem_filter.mp hx).2 with ⟨hhit, hcompl⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ x, ?_⟩
    have hpos : 0 < (I.active x ∩ U).card := hhit.card_pos
    rcases hcompl with ⟨c, hc⟩
    have hproper : (I.active x ∩ U).card < T := by
      have hnotmem : c ∉ I.active x ∩ U := by
        intro hcu
        exact (Finset.mem_compl.mp (Finset.mem_inter.mp hc).2)
          (Finset.mem_inter.mp hcu).2
      have hsub : I.active x ∩ U ⊆ I.active x := by
        intro d hd
        exact (Finset.mem_inter.mp hd).1
      have hlt_active :
          (I.active x ∩ U).card < (I.active x).card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
          ⟨hsub, by
            intro heq
            exact hnotmem (by
              rw [heq]
              exact (Finset.mem_inter.mp hc).1)⟩)
      simpa [I.active_card x] using hlt_active
    exact ⟨hpos, hproper⟩

theorem mixedCount_compl {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (U : Finset C) :
    I.mixedCount Uᶜ = I.mixedCount U := by
  classical
  rw [I.mixedCount_eq_card_filter_hit_and_compl Uᶜ,
    I.mixedCount_eq_card_filter_hit_and_compl U]
  apply congrArg Finset.card
  ext x
  simp [and_comm]

theorem scaled_bary_cutMass_le_cutCap {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (U : Finset C) (S : Finset (Fin T)) :
    S.card * (∑ c ∈ U, I.colorDegree c) ≤ T * I.cutCap U S := by
  classical
  rw [I.sum_colorDegree_on U]
  unfold cutCap
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _hx
  have haT : (I.active x ∩ U).card ≤ T := by
    have hsub : I.active x ∩ U ⊆ I.active x := by
      intro c hc
      exact (Finset.mem_inter.mp hc).1
    have hcard := Finset.card_le_card hsub
    simpa [I.active_card x] using hcard
  have hsT : S.card ≤ T := by
    simpa [Fintype.card_fin] using Finset.card_le_univ S
  exact scaled_bary_point_le_cutCap_point
    (T := T) (a := (I.active x ∩ U).card) (s := S.card)
    haT hsT

theorem scaled_bary_cutMass_add_mixed_le_cutCap {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (U : Finset C) (S : Finset (Fin T)) :
    S.card * (∑ c ∈ U, I.colorDegree c) +
        I.mixedCount U * min S.card (T - S.card)
      ≤ T * I.cutCap U S := by
  classical
  rw [I.sum_colorDegree_on U]
  unfold cutCap mixedCount
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _hx
  have haT : (I.active x ∩ U).card ≤ T := by
    have hsub : I.active x ∩ U ⊆ I.active x := by
      intro c hc
      exact (Finset.mem_inter.mp hc).1
    have hcard := Finset.card_le_card hsub
    simpa [I.active_card x] using hcard
  have hsT : S.card ≤ T := by
    simpa [Fintype.card_fin] using Finset.card_le_univ S
  by_cases hmix :
      0 < (I.active x ∩ U).card ∧ (I.active x ∩ U).card < T
  · simpa [hmix] using
      scaled_bary_point_add_mixed_le_cutCap_point
        (T := T) (a := (I.active x ∩ U).card) (s := S.card)
        haT hsT
  · simpa [hmix] using
      scaled_bary_point_add_mixed_le_cutCap_point
        (T := T) (a := (I.active x ∩ U).card) (s := S.card)
        haT hsT

theorem cutCap_symbols_univ {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (U : Finset C) :
    I.cutCap U (Finset.univ : Finset (Fin T))
      = ∑ x : X, (I.active x ∩ U).card := by
  classical
  unfold cutCap
  apply Finset.sum_congr rfl
  intro x _hx
  rw [min_eq_left]
  have hle : (I.active x ∩ U).card ≤ (I.active x).card := by
    exact Finset.card_le_card (by
      intro c hc
      exact (Finset.mem_inter.mp hc).1)
  rw [I.active_card x] at hle
  simpa using hle

theorem cutCap_colors_univ {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (S : Finset (Fin T)) :
    I.cutCap (Finset.univ : Finset C) S = S.card * Fintype.card X := by
  classical
  have hS : S.card ≤ T := by
    simpa using Finset.card_le_univ S
  calc
    I.cutCap (Finset.univ : Finset C) S
        = ∑ _x : X, S.card := by
            unfold cutCap
            apply Finset.sum_congr rfl
            intro x _hx
            have hactive : (I.active x ∩ (Finset.univ : Finset C)).card = T := by
              simp [I.active_card x]
            rw [hactive, min_eq_right hS]
    _ = S.card * Fintype.card X := by
            simp [Finset.sum_const, Nat.mul_comm]

theorem cutCap_colors_empty {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (S : Finset (Fin T)) :
    I.cutCap (∅ : Finset C) S = 0 := by
  simp [cutCap]

theorem cutCap_symbols_empty {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (U : Finset C) :
    I.cutCap U (∅ : Finset (Fin T)) = 0 := by
  simp [cutCap]

theorem cutCap_symbol_singleton {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (U : Finset C) (σ : Fin T) :
    I.cutCap U ({σ} : Finset (Fin T)) = I.hitCount U := by
  classical
  calc
    I.cutCap U ({σ} : Finset (Fin T))
        = ∑ x : X,
            if (I.active x ∩ U).Nonempty then 1 else 0 := by
            unfold cutCap
            apply Finset.sum_congr rfl
            intro x _hx
            by_cases hhit : (I.active x ∩ U).Nonempty
            · have hcard : 1 ≤ (I.active x ∩ U).card :=
                hhit.card_pos
              rw [Finset.card_singleton, min_eq_right hcard]
              simp [hhit]
            · have hcard : (I.active x ∩ U).card = 0 := by
                rw [Finset.card_eq_zero]
                exact Finset.not_nonempty_iff_eq_empty.mp hhit
              simp [hhit, hcard]
    _ = I.hitCount U := by
            rw [hitCount, Finset.card_filter]

theorem cutCap_mono {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) {U₁ U₂ : Finset C} {S₁ S₂ : Finset (Fin T)}
    (hU : U₁ ⊆ U₂) (hS : S₁ ⊆ S₂) :
    I.cutCap U₁ S₁ ≤ I.cutCap U₂ S₂ := by
  unfold cutCap
  apply Finset.sum_le_sum
  intro x _hx
  exact min_le_min
    (Finset.card_le_card (Finset.inter_subset_inter_left hU))
    (Finset.card_le_card hS)

theorem cutCap_mono_colors {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) {U₁ U₂ : Finset C} (hU : U₁ ⊆ U₂)
    (S : Finset (Fin T)) :
    I.cutCap U₁ S ≤ I.cutCap U₂ S :=
  I.cutCap_mono hU (fun _ h => h)

theorem cutCap_mono_symbols {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (U : Finset C) {S₁ S₂ : Finset (Fin T)}
    (hS : S₁ ⊆ S₂) :
    I.cutCap U S₁ ≤ I.cutCap U S₂ :=
  I.cutCap_mono (fun _ h => h) hS

theorem card_image_castSucc {T : Nat} (S : Finset (Fin T)) :
    (S.image (Fin.castSucc : Fin T → Fin (T + 1))).card = S.card := by
  exact Finset.card_image_of_injective _ (Fin.castSucc_injective T)

theorem last_notMem_image_castSucc {T : Nat} (S : Finset (Fin T)) :
    Fin.last T ∉ S.image (Fin.castSucc : Fin T → Fin (T + 1)) := by
  intro h
  rcases Finset.mem_image.mp h with ⟨σ, _hσ, hlast⟩
  exact Fin.castSucc_ne_last σ hlast

theorem card_image_castSucc_insert_last {T : Nat}
    (S : Finset (Fin T)) :
    (insert (Fin.last T)
        (S.image (Fin.castSucc : Fin T → Fin (T + 1)))).card =
      S.card + 1 := by
  rw [Finset.card_insert_of_notMem (last_notMem_image_castSucc S),
    card_image_castSucc]

theorem cutCap_image_castSucc {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence (T + 1) X C) (U : Finset C)
    (S : Finset (Fin T)) :
    I.cutCap U (S.image (Fin.castSucc : Fin T → Fin (T + 1))) =
      ∑ x : X, min ((I.active x ∩ U).card) S.card := by
  unfold cutCap
  rw [card_image_castSucc]

theorem cutCap_image_castSucc_pair {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence (T + 1) X C) (U : Finset C)
    {σ τ : Fin T} (hστ : σ ≠ τ) :
    I.cutCap U
        (({σ, τ} : Finset (Fin T)).image
          (Fin.castSucc : Fin T → Fin (T + 1))) =
      ∑ x : X, min ((I.active x ∩ U).card) 2 := by
  rw [I.cutCap_image_castSucc U ({σ, τ} : Finset (Fin T))]
  simp [Finset.card_pair hστ]

theorem cutCap_image_castSucc_insert_last {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence (T + 1) X C) (U : Finset C)
    (S : Finset (Fin T)) :
    I.cutCap U
        (insert (Fin.last T)
          (S.image (Fin.castSucc : Fin T → Fin (T + 1)))) =
      ∑ x : X, min ((I.active x ∩ U).card) (S.card + 1) := by
  unfold cutCap
  rw [card_image_castSucc_insert_last]

theorem eraseChoice_min_card_add_indicator_le_min_succ
    {T : Nat} {X C : Type*} [Fintype X] [Fintype C]
    [DecidableEq C]
    (I : Incidence (T + 1) X C) (choice : X → C)
    (hchoice : ∀ x : X, choice x ∈ I.active x)
    (x : X) (U : Finset C) (S : Finset (Fin T)) :
    min (((I.eraseChoice choice hchoice).active x ∩ U).card) S.card
        + (if choice x ∈ U then 1 else 0)
      ≤ min ((I.active x ∩ U).card) (S.card + 1) := by
  classical
  have hEq :=
    I.eraseChoice_active_inter_card_add_indicator choice hchoice x U
  by_cases hU : choice x ∈ U
  · let a := ((I.eraseChoice choice hchoice).active x ∩ U).card
    let A := (I.active x ∩ U).card
    have hEq' : a + 1 = A := by
      simpa [a, A, hU] using hEq
    simp only [hU, if_true]
    change min a S.card + 1 ≤ min A (S.card + 1)
    rw [← hEq']
    have hmin :
        min (a + 1) (S.card + 1) = min a S.card + 1 := by
      simp [Nat.succ_eq_add_one, Nat.succ_min_succ]
    rw [hmin]
  · let a := ((I.eraseChoice choice hchoice).active x ∩ U).card
    let A := (I.active x ∩ U).card
    have hEq' : a = A := by
      simp [a, A, hU]
    simp only [hU, if_false, add_zero]
    change min a S.card ≤ min A (S.card + 1)
    rw [← hEq']
    exact min_le_min le_rfl (Nat.le_succ S.card)

theorem min_card_le_eraseChoice_min_card_add_indicator
    {T : Nat} {X C : Type*} [Fintype X] [Fintype C]
    [DecidableEq C]
    (I : Incidence (T + 1) X C) (choice : X → C)
    (hchoice : ∀ x : X, choice x ∈ I.active x)
    (x : X) (U : Finset C) (S : Finset (Fin T)) :
    min ((I.active x ∩ U).card) S.card
      ≤ min (((I.eraseChoice choice hchoice).active x ∩ U).card) S.card
          + (if choice x ∈ U then 1 else 0) := by
  classical
  have hEq :=
    I.eraseChoice_active_inter_card_add_indicator choice hchoice x U
  by_cases hU : choice x ∈ U
  · let a := ((I.eraseChoice choice hchoice).active x ∩ U).card
    let A := (I.active x ∩ U).card
    have hEq' : a + 1 = A := by
      simpa [a, A, hU] using hEq
    simp only [hU, if_true]
    change min A S.card ≤ min a S.card + 1
    rw [← hEq']
    let s := S.card
    change min (a + 1) s ≤ min a s + 1
    by_cases hlt : a < s
    · have ha : a ≤ s := Nat.le_of_lt hlt
      have has : a + 1 ≤ s := Nat.succ_le_of_lt hlt
      rw [min_eq_left has, min_eq_left ha]
    · have hs : s ≤ a := Nat.le_of_not_gt hlt
      have hs' : s ≤ a + 1 := hs.trans (Nat.le_succ a)
      rw [min_eq_right hs', min_eq_right hs]
      omega
  · let a := ((I.eraseChoice choice hchoice).active x ∩ U).card
    let A := (I.active x ∩ U).card
    have hEq' : a = A := by
      simp [a, A, hU]
    simp only [hU, if_false, add_zero]
    change min A S.card ≤ min a S.card
    rw [← hEq']

theorem eraseChoice_cutCap_add_choiceHitCount_le_cutCap_image_castSucc_insert_last
    {T : Nat} {X C : Type*} [Fintype X] [Fintype C]
    [DecidableEq X] [DecidableEq C]
    (I : Incidence (T + 1) X C) (choice : X → C)
    (hchoice : ∀ x : X, choice x ∈ I.active x)
    (U : Finset C) (S : Finset (Fin T)) :
    (I.eraseChoice choice hchoice).cutCap U S
        + choiceHitCount choice U
      ≤ I.cutCap U
          (insert (Fin.last T)
            (S.image (Fin.castSucc : Fin T → Fin (T + 1)))) := by
  classical
  rw [cutCap_image_castSucc_insert_last]
  unfold cutCap choiceHitCount
  rw [Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _hx
  exact I.eraseChoice_min_card_add_indicator_le_min_succ choice hchoice x U S

theorem cutCap_image_castSucc_le_eraseChoice_cutCap_add_choiceHitCount
    {T : Nat} {X C : Type*} [Fintype X] [Fintype C]
    [DecidableEq X] [DecidableEq C]
    (I : Incidence (T + 1) X C) (choice : X → C)
    (hchoice : ∀ x : X, choice x ∈ I.active x)
    (U : Finset C) (S : Finset (Fin T)) :
    I.cutCap U (S.image (Fin.castSucc : Fin T → Fin (T + 1)))
      ≤ (I.eraseChoice choice hchoice).cutCap U S
          + choiceHitCount choice U := by
  classical
  rw [cutCap_image_castSucc]
  unfold cutCap choiceHitCount
  rw [Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _hx
  exact I.min_card_le_eraseChoice_min_card_add_indicator choice hchoice x U S

theorem min_card_eq_eraseChoice_min_card_add_lowHitIndicator
    {T : Nat} {X C : Type*} [Fintype X] [Fintype C]
    [DecidableEq C]
    (I : Incidence (T + 1) X C) (choice : X → C)
    (hchoice : ∀ x : X, choice x ∈ I.active x)
    (x : X) (U : Finset C) (S : Finset (Fin T)) :
    min ((I.active x ∩ U).card) S.card =
      min (((I.eraseChoice choice hchoice).active x ∩ U).card) S.card
        + (if choice x ∈ U ∧ (I.active x ∩ U).card ≤ S.card then 1 else 0) := by
  classical
  have hEq :=
    I.eraseChoice_active_inter_card_add_indicator choice hchoice x U
  by_cases hU : choice x ∈ U
  · let a := ((I.eraseChoice choice hchoice).active x ∩ U).card
    let A := (I.active x ∩ U).card
    have hEq' : a + 1 = A := by
      simpa [a, A, hU] using hEq
    change min A S.card =
      min a S.card + (if choice x ∈ U ∧ A ≤ S.card then 1 else 0)
    rw [← hEq']
    by_cases hle : a + 1 ≤ S.card
    · have ha : a ≤ S.card := (Nat.le_succ a).trans hle
      rw [min_eq_left hle, min_eq_left ha]
      simp [hU, hle]
    · have hs_lt : S.card < a + 1 := Nat.lt_of_not_ge hle
      have hs : S.card ≤ a := Nat.lt_succ_iff.mp hs_lt
      have hs' : S.card ≤ a + 1 := Nat.le_of_lt hs_lt
      rw [min_eq_right hs', min_eq_right hs]
      simp [hU, hle]
  · let a := ((I.eraseChoice choice hchoice).active x ∩ U).card
    let A := (I.active x ∩ U).card
    have hEq' : a = A := by
      simp [a, A, hU]
    change min A S.card =
      min a S.card + (if choice x ∈ U ∧ A ≤ S.card then 1 else 0)
    rw [← hEq']
    simp [hU]

theorem cutCap_image_castSucc_eq_eraseChoice_cutCap_add_choiceLowHitCount
    {T : Nat} {X C : Type*} [Fintype X] [Fintype C]
    [DecidableEq X] [DecidableEq C]
    (I : Incidence (T + 1) X C) (choice : X → C)
    (hchoice : ∀ x : X, choice x ∈ I.active x)
    (U : Finset C) (S : Finset (Fin T)) :
    I.cutCap U (S.image (Fin.castSucc : Fin T → Fin (T + 1))) =
      (I.eraseChoice choice hchoice).cutCap U S
        + choiceLowHitCount I choice U S := by
  classical
  rw [cutCap_image_castSucc]
  unfold cutCap choiceLowHitCount
  rw [Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _hx
  exact I.min_card_eq_eraseChoice_min_card_add_lowHitIndicator
    choice hchoice x U S

theorem exists_injective_token_matching_of_hall
    {T : Nat} {X C Q : Type*} [Fintype X] [Fintype C]
    [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (colorOf : Q → C)
    (hHall : ∀ A : Finset Q, A.card ≤ I.hitCount (A.image colorOf)) :
    ∃ f : Q → X, Function.Injective f ∧
      ∀ q : Q, colorOf q ∈ I.active (f q) := by
  classical
  rw [← Fintype.all_card_le_filter_rel_iff_exists_injective
    (r := fun q x => colorOf q ∈ I.active x)]
  intro A
  have hfilter :
      ({x : X | ∃ q ∈ A, colorOf q ∈ I.active x} : Finset X)
        =
      (Finset.univ.filter
        (fun x : X => (I.active x ∩ A.image colorOf).Nonempty)) := by
    ext x
    simp [Finset.Nonempty, and_comm]
  rw [hfilter]
  exact hHall A

set_option linter.unusedFintypeInType false in
theorem exists_choiceDegree_bijective_token_matching
    {X C : Type*} [Fintype X] [Fintype C]
    [DecidableEq X] [DecidableEq C]
    (choice : X → C) (n : C → Nat)
    (hdegree : ∀ c : C, choiceDegree choice c = n c) :
    ∃ f : (Sigma fun c : C => Fin (n c)) ≃ X,
      ∀ q : Sigma fun c : C => Fin (n c), q.1 = choice (f q) := by
  classical
  have hInjective :
      ∃ f : (Sigma fun c : C => Fin (n c)) → X,
        Function.Injective f ∧
          ∀ q : Sigma fun c : C => Fin (n c), q.1 = choice (f q) := by
    rw [← Fintype.all_card_le_filter_rel_iff_exists_injective
      (r := fun (q : Sigma fun c : C => Fin (n c)) (x : X) =>
        q.1 = choice x)]
    intro A
    let U : Finset C :=
      A.image (fun q : Sigma fun c : C => Fin (n c) => q.1)
    have hsubset :
        A ⊆ U.sigma
          (fun c : C => (Finset.univ : Finset (Fin (n c)))) := by
      intro q hq
      exact Finset.mem_sigma.mpr
        ⟨Finset.mem_image_of_mem
          (fun q : Sigma fun c : C => Fin (n c) => q.1) hq,
          Finset.mem_univ q.2⟩
    have hcardA :
        A.card ≤
          (U.sigma
            (fun c : C => (Finset.univ : Finset (Fin (n c))))).card :=
      Finset.card_le_card hsubset
    have hcardSigma :
        (U.sigma
            (fun c : C => (Finset.univ : Finset (Fin (n c))))).card =
          ∑ c ∈ U, n c := by
      rw [Finset.card_sigma]
      simp
    have hsum :
        (∑ c ∈ U, n c) = choiceHitCount choice U := by
      calc
        (∑ c ∈ U, n c)
            = ∑ c ∈ U, choiceDegree choice c := by
                apply Finset.sum_congr rfl
                intro c _hc
                rw [hdegree c]
        _ = choiceHitCount choice U :=
                sum_choiceDegree_on choice U
    have hfilter :
        ({x : X | ∃ q ∈ A, q.1 = choice x} : Finset X)
          =
        (Finset.univ.filter (fun x : X => choice x ∈ U)) := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_filter.mp hx with ⟨_hxuniv, q, hqA, hq⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ x, by
            rw [← hq]
            exact Finset.mem_image_of_mem
              (fun q : Sigma fun c : C => Fin (n c) => q.1) hqA⟩
      · intro hx
        have hU : choice x ∈ U := (Finset.mem_filter.mp hx).2
        rcases Finset.mem_image.mp hU with ⟨q, hqA, hq⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ x, q, hqA, by rw [hq]⟩
    rw [hfilter]
    exact hcardA.trans (by rw [hcardSigma, hsum, choiceHitCount])
  rcases hInjective with ⟨f, hfInj, hfRel⟩
  have hcard :
      Fintype.card (Sigma fun c : C => Fin (n c)) = Fintype.card X := by
    rw [Fintype.card_sigma]
    calc
      (∑ c : C, Fintype.card (Fin (n c)))
          = ∑ c : C, n c := by simp
      _ = ∑ c : C, choiceDegree choice c := by
            apply Finset.sum_congr rfl
            intro c _hc
            rw [hdegree c]
      _ = ∑ c ∈ (Finset.univ : Finset C), choiceDegree choice c := by
            simp
      _ = choiceHitCount choice (Finset.univ : Finset C) :=
            sum_choiceDegree_on choice (Finset.univ : Finset C)
      _ = Fintype.card X := by
            unfold choiceHitCount
            simp
  have hfBij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hfInj, hcard⟩
  exact ⟨Equiv.ofBijective f hfBij, hfRel⟩

end Incidence

/-- A nonnegative count matrix with the row and column sums forced by incidence. -/
structure CountMatrix {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) where
  val : C → Fin T → Nat
  row_sum : ∀ c : C, (∑ σ : Fin T, val c σ) = I.colorDegree c
  col_sum : ∀ σ : Fin T, (∑ c : C, val c σ) = Fintype.card X

/-- Desired residues for active symbol counts. -/
structure ResidueSpec (m T : Nat) (C : Type*) [Fintype C] where
  target : C → Fin T → ZMod m

namespace ResidueSpec

def RowCompatible {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (R : ResidueSpec m T C) : Prop :=
  ∀ c : C, (I.colorDegree c : ZMod m) = ∑ σ : Fin T, R.target c σ

def ColCompatible {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (_I : Incidence T X C) (R : ResidueSpec m T C) : Prop :=
  ∀ σ : Fin T, (Fintype.card X : ZMod m) = ∑ c : C, R.target c σ

end ResidueSpec

def balancedUnitResidueLength : Nat → Nat
  | 0 => 3
  | k + 1 => balancedUnitResidueLength k + 2

theorem balancedUnitResidueLength_eq :
    ∀ k : Nat, balancedUnitResidueLength k = 2 * k + 3
  | 0 => by simp [balancedUnitResidueLength]
  | k + 1 => by
      rw [balancedUnitResidueLength]
      rw [balancedUnitResidueLength_eq k]
      omega

noncomputable def balancedUnitResiduesAux (m : Nat) :
    (k : Nat) → Fin (balancedUnitResidueLength k) → ZMod m
  | 0 => fun i => if i.val = 0 then 1 else if i.val = 1 then 1 else -2
  | k + 1 => fun i =>
      if h : i.val < balancedUnitResidueLength k then
        balancedUnitResiduesAux m k ⟨i.val, h⟩
      else if i.val = balancedUnitResidueLength k then
        1
      else
        -1

theorem balancedUnitResiduesAux_sum_zero {m : Nat} :
    ∀ k : Nat,
      (∑ i : Fin (balancedUnitResidueLength k),
        balancedUnitResiduesAux m k i) = 0
  | 0 => by
      change (∑ i : Fin 3, balancedUnitResiduesAux m 0 i) = 0
      rw [Fin.sum_univ_three]
      simp [balancedUnitResiduesAux, balancedUnitResidueLength]
      ring
  | k + 1 => by
      change (∑ i : Fin (balancedUnitResidueLength k + 2),
        balancedUnitResiduesAux m (k + 1) i) = 0
      rw [Fin.sum_univ_castSucc]
      have hcast :
          (∑ i : Fin (balancedUnitResidueLength k + 1),
              balancedUnitResiduesAux m (k + 1) i.castSucc)
            =
          (∑ i : Fin (balancedUnitResidueLength k),
              balancedUnitResiduesAux m k i) + 1 := by
        rw [Fin.sum_univ_castSucc]
        congr 1
        · apply Finset.sum_congr rfl
          intro i _hi
          simp [balancedUnitResiduesAux, i.isLt]
        · simp [balancedUnitResiduesAux]
      have hlast :
          balancedUnitResiduesAux m (k + 1)
              (Fin.last (balancedUnitResidueLength k + 1)) = -1 := by
        simp [balancedUnitResiduesAux]
      rw [hcast, hlast, balancedUnitResiduesAux_sum_zero k]
      ring

theorem balancedUnitResiduesAux_isUnit {m : Nat} (hmodd : Odd m) :
    ∀ k : Nat, ∀ i : Fin (balancedUnitResidueLength k),
      IsUnit (balancedUnitResiduesAux m k i)
  | 0, i => by
      fin_cases i <;> simp [balancedUnitResiduesAux]
      simpa using
        (IsUnit.neg (ZMod.isUnit_iff_coprime 2 m |>.2 hmodd.coprime_two_left))
  | k + 1, i => by
      by_cases h : i.val < balancedUnitResidueLength k
      · simpa [balancedUnitResiduesAux, h] using
          balancedUnitResiduesAux_isUnit hmodd k ⟨i.val, h⟩
      · by_cases hi : i.val = balancedUnitResidueLength k
        · simp [balancedUnitResiduesAux, hi]
        · simp [balancedUnitResiduesAux, h, hi]

noncomputable def balancedUnitResidues (m k : Nat) :
    Fin (2 * k + 3) → ZMod m :=
  fun i =>
    balancedUnitResiduesAux m k
      (Fin.cast (balancedUnitResidueLength_eq k).symm i)

theorem balancedUnitResidues_sum_zero {m k : Nat} :
    (∑ i : Fin (2 * k + 3), balancedUnitResidues m k i) = 0 := by
  unfold balancedUnitResidues
  let e : Fin (2 * k + 3) ≃ Fin (balancedUnitResidueLength k) :=
    finCongr (balancedUnitResidueLength_eq k).symm
  calc
    (∑ i : Fin (2 * k + 3), balancedUnitResiduesAux m k (e i))
        = ∑ j : Fin (balancedUnitResidueLength k),
            balancedUnitResiduesAux m k j := by
            exact Fintype.sum_equiv e
              (fun i : Fin (2 * k + 3) =>
                balancedUnitResiduesAux m k (e i))
              (fun j : Fin (balancedUnitResidueLength k) =>
                balancedUnitResiduesAux m k j)
              (by intro i; rfl)
    _ = 0 := balancedUnitResiduesAux_sum_zero k

theorem balancedUnitResidues_isUnit {m k : Nat} (hmodd : Odd m)
    (i : Fin (2 * k + 3)) :
    IsUnit (balancedUnitResidues m k i) := by
  unfold balancedUnitResidues
  exact balancedUnitResiduesAux_isUnit hmodd k
    (Fin.cast (balancedUnitResidueLength_eq k).symm i)

theorem exists_balanced_unit_residues_fin {d m : Nat}
    (hdodd : Odd d) (hd3 : 3 ≤ d) (hmodd : Odd m) :
    ∃ u : Fin d → ZMod m,
      (∑ i : Fin d, u i) = 0 ∧ ∀ i : Fin d, IsUnit (u i) := by
  rcases hdodd with ⟨a, rfl⟩
  have ha1 : 1 ≤ a := by omega
  let k := a - 1
  have hdim : 2 * k + 3 = 2 * a + 1 := by
    simp [k]
    omega
  let e : Fin (2 * a + 1) ≃ Fin (2 * k + 3) := finCongr hdim.symm
  refine ⟨fun i => balancedUnitResidues m k (e i), ?_, ?_⟩
  · calc
      (∑ i : Fin (2 * a + 1), balancedUnitResidues m k (e i))
          = ∑ j : Fin (2 * k + 3), balancedUnitResidues m k j := by
              exact Fintype.sum_equiv e
                (fun i : Fin (2 * a + 1) => balancedUnitResidues m k (e i))
                (fun j : Fin (2 * k + 3) => balancedUnitResidues m k j)
                (by intro i; rfl)
      _ = 0 := balancedUnitResidues_sum_zero
  · intro i
    exact balancedUnitResidues_isUnit hmodd (e i)

theorem zmod_natCast_pow_eq_zero_of_pos {m n : Nat} (hn : 0 < n) :
    ((m ^ n : Nat) : ZMod m) = 0 := by
  rcases n with _ | n
  · omega
  · simp [pow_succ]

theorem zmod_natCast_mul_pow_eq_zero_of_pos {m n a : Nat} (hn : 0 < n) :
    ((a * m ^ n : Nat) : ZMod m) = 0 := by
  rw [Nat.cast_mul, zmod_natCast_pow_eq_zero_of_pos hn, mul_zero]

theorem zmod_natCast_pow_mul_eq_zero_of_pos {m n a : Nat} (hn : 0 < n) :
    ((m ^ n * a : Nat) : ZMod m) = 0 := by
  rw [Nat.cast_mul, zmod_natCast_pow_eq_zero_of_pos hn, zero_mul]

noncomputable def universalUnitResidueSpec (m d n : Nat)
    (u : Fin d → ZMod m) : ResidueSpec m (n + 2) (Fin d) where
  target := fun c σ =>
    if σ.val = 0 then u c else if σ.val = 1 then -u c else 0

theorem universalUnitResidueSpec_row_sum {m d n : Nat}
    (u : Fin d → ZMod m) (c : Fin d) :
    (∑ σ : Fin (n + 2),
      (universalUnitResidueSpec m d n u).target c σ) = 0 := by
  induction n with
  | zero =>
      rw [Fin.sum_univ_two]
      simp [universalUnitResidueSpec]
  | succ n ih =>
      change (∑ σ : Fin ((n + 2) + 1),
        (universalUnitResidueSpec m d (n + 1) u).target c σ) = 0
      rw [Fin.sum_univ_castSucc]
      have hcast :
          (∑ i : Fin (n + 2),
            (universalUnitResidueSpec m d (n + 1) u).target c i.castSucc)
          =
          (∑ i : Fin (n + 2),
            (universalUnitResidueSpec m d n u).target c i) := by
        apply Finset.sum_congr rfl
        intro i _hi
        by_cases h0 : i.val = 0
        · simp [universalUnitResidueSpec, h0]
        · by_cases h1 : i.val = 1
          · simp [universalUnitResidueSpec, h1]
          · simp [universalUnitResidueSpec, h1]
      have hlast :
          (universalUnitResidueSpec m d (n + 1) u).target c
            (Fin.last (n + 2)) = 0 := by
        simp [universalUnitResidueSpec]
      rw [hcast, hlast, ih]
      simp

theorem universalUnitResidueSpec_col_sum {m d n : Nat}
    {u : Fin d → ZMod m} (hu : (∑ c : Fin d, u c) = 0)
    (σ : Fin (n + 2)) :
    (∑ c : Fin d, (universalUnitResidueSpec m d n u).target c σ) = 0 := by
  by_cases hs0 : σ = 0
  · subst σ
    simp [universalUnitResidueSpec, hu]
  · by_cases hs1 : σ = 1
    · subst σ
      simp [universalUnitResidueSpec, hu]
    · have h1 : σ.val ≠ 1 := by
        intro hval
        exact hs1 (Fin.ext hval)
      simp [universalUnitResidueSpec, hs0, h1]

theorem universalUnitResidueSpec_rowCompatible
    {m d n : Nat} {X : Type*} [Fintype X] [DecidableEq X]
    (I : Incidence (n + 2) X (Fin d)) (u : Fin d → ZMod m)
    (hColor : ∀ c : Fin d, (I.colorDegree c : ZMod m) = 0) :
    (universalUnitResidueSpec m d n u).RowCompatible I := by
  intro c
  rw [hColor c, universalUnitResidueSpec_row_sum]

theorem universalUnitResidueSpec_colCompatible
    {m d n : Nat} {X : Type*} [Fintype X] [DecidableEq X]
    (I : Incidence (n + 2) X (Fin d)) {u : Fin d → ZMod m}
    (hu : (∑ c : Fin d, u c) = 0)
    (hX : (Fintype.card X : ZMod m) = 0) :
    (universalUnitResidueSpec m d n u).ColCompatible I := by
  intro σ
  rw [hX, universalUnitResidueSpec_col_sum hu σ]

theorem universalUnitResidueSpec_zero_isUnit {m d n : Nat}
    {u : Fin d → ZMod m} (huUnit : ∀ c : Fin d, IsUnit (u c))
    (c : Fin d) :
    IsUnit ((universalUnitResidueSpec m d n u).target c 0) := by
  simpa [universalUnitResidueSpec] using huUnit c

theorem universalUnitResidueSpec_numeric_sub_delta_isUnit {m d n : Nat}
    {u : Fin d → ZMod m} (huUnit : ∀ c : Fin d, IsUnit (u c))
    (c : Fin d) {σ : Fin (n + 2)} (hσ : 2 ≤ σ.val) :
    IsUnit ((universalUnitResidueSpec m d n u).target c σ -
      (universalUnitResidueSpec m d n u).target c 1) := by
  have hs0 : σ ≠ 0 := by
    intro h
    have hval : σ.val = 0 := by
      simpa using congrArg Fin.val h
    omega
  have h1 : σ.val ≠ 1 := by omega
  simpa [universalUnitResidueSpec, hs0, h1] using huUnit c

theorem exists_universalUnitResidueSpec_compatible_primitive
    {m d n : Nat} {X : Type*} [Fintype X] [DecidableEq X]
    (I : Incidence (n + 2) X (Fin d))
    (hdodd : Odd d) (hd3 : 3 ≤ d) (hmodd : Odd m)
    (hColor : ∀ c : Fin d, (I.colorDegree c : ZMod m) = 0)
    (hX : (Fintype.card X : ZMod m) = 0) :
    ∃ R : ResidueSpec m (n + 2) (Fin d),
      R.RowCompatible I ∧ R.ColCompatible I ∧
      (∀ c : Fin d, IsUnit (R.target c 0)) ∧
      (∀ c : Fin d, ∀ σ : Fin (n + 2), 2 ≤ σ.val →
        IsUnit (R.target c σ - R.target c 1)) := by
  rcases exists_balanced_unit_residues_fin hdodd hd3 hmodd with
    ⟨u, huSum, huUnit⟩
  refine ⟨universalUnitResidueSpec m d n u, ?_, ?_, ?_, ?_⟩
  · exact universalUnitResidueSpec_rowCompatible I u hColor
  · exact universalUnitResidueSpec_colCompatible I huSum hX
  · exact universalUnitResidueSpec_zero_isUnit huUnit
  · intro c σ hσ
    exact universalUnitResidueSpec_numeric_sub_delta_isUnit huUnit c hσ

noncomputable def universalUnitResidueSpecOfTwoLe (m d T : Nat)
    (u : Fin d → ZMod m) : ResidueSpec m T (Fin d) where
  target := fun c σ =>
    if σ.val = 0 then u c else if σ.val = 1 then -u c else 0

theorem universalUnitResidueSpecOfTwoLe_row_sum {m d T : Nat}
    (hT : 2 ≤ T) (u : Fin d → ZMod m) (c : Fin d) :
    (∑ σ : Fin T,
      (universalUnitResidueSpecOfTwoLe m d T u).target c σ) = 0 := by
  rcases T with _ | T
  · omega
  rcases T with _ | T
  · omega
  simpa [universalUnitResidueSpecOfTwoLe, universalUnitResidueSpec] using
    (universalUnitResidueSpec_row_sum (m := m) (d := d) (n := T) u c)

theorem universalUnitResidueSpecOfTwoLe_col_sum {m d T : Nat}
    (hT : 2 ≤ T) {u : Fin d → ZMod m}
    (hu : (∑ c : Fin d, u c) = 0) (σ : Fin T) :
    (∑ c : Fin d,
      (universalUnitResidueSpecOfTwoLe m d T u).target c σ) = 0 := by
  rcases T with _ | T
  · omega
  rcases T with _ | T
  · omega
  simpa [universalUnitResidueSpecOfTwoLe, universalUnitResidueSpec] using
    (universalUnitResidueSpec_col_sum
      (m := m) (d := d) (n := T) (u := u) hu σ)

theorem universalUnitResidueSpecOfTwoLe_rowCompatible
    {m d T : Nat} {X : Type*} [Fintype X] [DecidableEq X]
    (hT : 2 ≤ T) (I : Incidence T X (Fin d)) (u : Fin d → ZMod m)
    (hColor : ∀ c : Fin d, (I.colorDegree c : ZMod m) = 0) :
    (universalUnitResidueSpecOfTwoLe m d T u).RowCompatible I := by
  intro c
  rw [hColor c, universalUnitResidueSpecOfTwoLe_row_sum hT u c]

theorem universalUnitResidueSpecOfTwoLe_colCompatible
    {m d T : Nat} {X : Type*} [Fintype X] [DecidableEq X]
    (hT : 2 ≤ T) (I : Incidence T X (Fin d))
    {u : Fin d → ZMod m} (hu : (∑ c : Fin d, u c) = 0)
    (hX : (Fintype.card X : ZMod m) = 0) :
    (universalUnitResidueSpecOfTwoLe m d T u).ColCompatible I := by
  intro σ
  rw [hX, universalUnitResidueSpecOfTwoLe_col_sum hT hu σ]

theorem universalUnitResidueSpecOfTwoLe_zero_isUnit {m d T : Nat}
    (hT : 2 ≤ T)
    {u : Fin d → ZMod m} (huUnit : ∀ c : Fin d, IsUnit (u c))
    (c : Fin d) :
    IsUnit
      ((universalUnitResidueSpecOfTwoLe m d T u).target c
        ⟨0, by omega⟩) := by
  simpa [universalUnitResidueSpecOfTwoLe] using huUnit c

theorem universalUnitResidueSpecOfTwoLe_numeric_sub_delta_isUnit
    {m d T : Nat} {u : Fin d → ZMod m}
    (hT : 2 ≤ T)
    (huUnit : ∀ c : Fin d, IsUnit (u c))
    (c : Fin d) {σ : Fin T} (hσ : 2 ≤ σ.val) :
    IsUnit ((universalUnitResidueSpecOfTwoLe m d T u).target c σ -
      (universalUnitResidueSpecOfTwoLe m d T u).target c
        ⟨1, by omega⟩) := by
  have hs0 : σ.val ≠ 0 := by omega
  have h1 : σ.val ≠ 1 := by omega
  simpa [universalUnitResidueSpecOfTwoLe, hs0, h1] using huUnit c

theorem exists_universalUnitResidueSpecOfTwoLe_compatible_primitive
    {m d T : Nat} {X : Type*} [Fintype X] [DecidableEq X]
    (hT : 2 ≤ T) (I : Incidence T X (Fin d))
    (hdodd : Odd d) (hd3 : 3 ≤ d) (hmodd : Odd m)
    (hColor : ∀ c : Fin d, (I.colorDegree c : ZMod m) = 0)
    (hX : (Fintype.card X : ZMod m) = 0) :
    ∃ R : ResidueSpec m T (Fin d),
      R.RowCompatible I ∧ R.ColCompatible I ∧
      (∀ c : Fin d, IsUnit (R.target c ⟨0, by omega⟩)) ∧
      (∀ c : Fin d, ∀ σ : Fin T, 2 ≤ σ.val →
        IsUnit (R.target c σ - R.target c ⟨1, by omega⟩)) := by
  rcases exists_balanced_unit_residues_fin hdodd hd3 hmodd with
    ⟨u, huSum, huUnit⟩
  refine ⟨universalUnitResidueSpecOfTwoLe m d T u, ?_, ?_, ?_, ?_⟩
  · exact universalUnitResidueSpecOfTwoLe_rowCompatible hT I u hColor
  · exact universalUnitResidueSpecOfTwoLe_colCompatible hT I huSum hX
  · exact universalUnitResidueSpecOfTwoLe_zero_isUnit hT huUnit
  · intro c σ hσ
    exact universalUnitResidueSpecOfTwoLe_numeric_sub_delta_isUnit
      hT huUnit c hσ

/--
Finite transportation for natural row and column marginals.

This is the quotient-transport core used by residue rounding: once the row and
column residual quotas have the same total, a nonnegative matrix with those
marginals exists.
-/
theorem exists_nat_matrix_with_marginals
    {α β : Type*} [Fintype α] [Fintype β]
    (row : α → Nat) (col : β → Nat)
    (h : (∑ a : α, row a) = ∑ b : β, col b) :
    ∃ k : α → β → Nat,
      (∀ a : α, (∑ b : β, k a b) = row a) ∧
      (∀ b : β, (∑ a : α, k a b) = col b) := by
  classical
  let RowTok := Sigma fun a : α => Fin (row a)
  let ColTok := Sigma fun b : β => Fin (col b)
  have hcard : Fintype.card RowTok = Fintype.card ColTok := by
    simp [RowTok, ColTok, Fintype.card_sigma, h]
  let e : RowTok ≃ ColTok := Fintype.equivOfCardEq hcard
  let k : α → β → Nat := fun a b =>
    Fintype.card {i : Fin (row a) // (e ⟨a, i⟩).1 = b}
  refine ⟨k, ?_, ?_⟩
  · intro a
    have hcongr :
        Fintype.card (Sigma fun b : β =>
            {i : Fin (row a) // (e ⟨a, i⟩).1 = b}) =
          Fintype.card (Fin (row a)) := by
      refine Fintype.card_congr ?_
      exact {
        toFun := fun q => q.2.1
        invFun := fun i => ⟨(e ⟨a, i⟩).1, ⟨i, rfl⟩⟩
        left_inv := by
          intro q
          rcases q with ⟨b, i, hb⟩
          dsimp
          cases hb
          rfl
        right_inv := by
          intro i
          rfl }
    calc
      (∑ b : β, k a b)
          = Fintype.card (Sigma fun b : β =>
              {i : Fin (row a) // (e ⟨a, i⟩).1 = b}) := by
              simp [k, Fintype.card_sigma]
      _ = row a := by simpa using hcongr
  · intro b
    have hpre :
        Fintype.card (Sigma fun a : α =>
            {i : Fin (row a) // (e ⟨a, i⟩).1 = b}) =
          Fintype.card {q : RowTok // (e q).1 = b} := by
      refine Fintype.card_congr ?_
      exact {
        toFun := fun q => ⟨⟨q.1, q.2.1⟩, q.2.2⟩
        invFun := fun q => ⟨q.1.1, ⟨q.1.2, q.2⟩⟩
        left_inv := by intro q; rfl
        right_inv := by intro q; rfl }
    have hmap :
        Fintype.card {q : RowTok // (e q).1 = b} =
          Fintype.card {q : ColTok // q.1 = b} := by
      refine Fintype.card_congr ?_
      exact {
        toFun := fun q => ⟨e q.1, q.2⟩
        invFun := fun q => ⟨e.symm q.1, by
          have hq := e.apply_symm_apply q.1
          have hf : (e (e.symm q.1)).1 = q.1.1 :=
            congrArg (fun r : ColTok => r.1) hq
          exact hf.trans q.2⟩
        left_inv := by
          intro q
          apply Subtype.ext
          exact e.symm_apply_apply q.1
        right_inv := by
          intro q
          apply Subtype.ext
          exact e.apply_symm_apply q.1 }
    have hcolcard :
        Fintype.card {q : ColTok // q.1 = b} = Fintype.card (Fin (col b)) := by
      refine Fintype.card_congr ?_
      exact {
        toFun := fun q =>
          ⟨q.1.2.val, by
            have hlt := q.1.2.isLt
            simpa [q.2] using hlt⟩
        invFun := fun j => ⟨⟨b, j⟩, rfl⟩
        left_inv := by
          intro q
          rcases q with ⟨q, hq⟩
          rcases q with ⟨b', j⟩
          dsimp
          cases hq
          rfl
        right_inv := by
          intro j
          rfl }
    calc
      (∑ a : α, k a b)
          = Fintype.card (Sigma fun a : α =>
              {i : Fin (row a) // (e ⟨a, i⟩).1 = b}) := by
              simp [k, Fintype.card_sigma]
      _ = col b := by simpa using hpre.trans (hmap.trans hcolcard)

namespace CountMatrix

def cutMass {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I)
    (U : Finset C) (S : Finset (Fin T)) : Nat :=
  ∑ c ∈ U, ∑ σ ∈ S, M.val c σ

def HallCuts {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I) : Prop :=
  ∀ U : Finset C, ∀ S : Finset (Fin T),
    M.cutMass U S ≤ I.cutCap U S

def cutSlack {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I)
    (U : Finset C) (S : Finset (Fin T)) : Nat :=
  I.cutCap U S - M.cutMass U S

def HasResidues {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I)
    (R : ResidueSpec m T C) : Prop :=
  ∀ c σ, (M.val c σ : ZMod m) = R.target c σ

theorem exists_with_residueQuotients
    {m T : Nat} [NeZero m] {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C}
    (r : C → Fin T → Nat)
    (hr : ∀ c σ, ((r c σ : Nat) : ZMod m) = R.target c σ)
    (hrowLe : ∀ c : C, (∑ σ : Fin T, r c σ) ≤ I.colorDegree c)
    (hcolLe : ∀ σ : Fin T, (∑ c : C, r c σ) ≤ Fintype.card X)
    (hrowDiv : ∀ c : C,
      m * ((I.colorDegree c - ∑ σ : Fin T, r c σ) / m) =
        I.colorDegree c - ∑ σ : Fin T, r c σ)
    (hcolDiv : ∀ σ : Fin T,
      m * ((Fintype.card X - ∑ c : C, r c σ) / m) =
        Fintype.card X - ∑ c : C, r c σ)
    (hTotal :
      (∑ c : C, (I.colorDegree c - ∑ σ : Fin T, r c σ) / m) =
        ∑ σ : Fin T, (Fintype.card X - ∑ c : C, r c σ) / m) :
    ∃ M : CountMatrix I, M.HasResidues R := by
  classical
  let rowQ : C → Nat := fun c =>
    (I.colorDegree c - ∑ σ : Fin T, r c σ) / m
  let colQ : Fin T → Nat := fun σ =>
    (Fintype.card X - ∑ c : C, r c σ) / m
  rcases exists_nat_matrix_with_marginals rowQ colQ
      (by simpa [rowQ, colQ] using hTotal) with
    ⟨K, hKrow, hKcol⟩
  let val : C → Fin T → Nat := fun c σ => r c σ + m * K c σ
  refine ⟨{ val := val, row_sum := ?_, col_sum := ?_ }, ?_⟩
  · intro c
    have hsum : (∑ σ : Fin T, val c σ) =
        (∑ σ : Fin T, r c σ) + m * rowQ c := by
      calc
        (∑ σ : Fin T, val c σ)
            = (∑ σ : Fin T, (r c σ + m * K c σ)) := rfl
        _ = (∑ σ : Fin T, r c σ) + ∑ σ : Fin T, m * K c σ := by
            rw [Finset.sum_add_distrib]
        _ = (∑ σ : Fin T, r c σ) + m * (∑ σ : Fin T, K c σ) := by
            rw [← Finset.mul_sum]
        _ = (∑ σ : Fin T, r c σ) + m * rowQ c := by
            rw [hKrow c]
    rw [hsum]
    have hdiv : m * rowQ c = I.colorDegree c - ∑ σ : Fin T, r c σ := by
      simpa [rowQ] using hrowDiv c
    rw [hdiv]
    exact Nat.add_sub_of_le (hrowLe c)
  · intro σ
    have hsum : (∑ c : C, val c σ) =
        (∑ c : C, r c σ) + m * colQ σ := by
      calc
        (∑ c : C, val c σ)
            = (∑ c : C, (r c σ + m * K c σ)) := rfl
        _ = (∑ c : C, r c σ) + ∑ c : C, m * K c σ := by
            rw [Finset.sum_add_distrib]
        _ = (∑ c : C, r c σ) + m * (∑ c : C, K c σ) := by
            rw [← Finset.mul_sum]
        _ = (∑ c : C, r c σ) + m * colQ σ := by
            rw [hKcol σ]
    rw [hsum]
    have hdiv : m * colQ σ = Fintype.card X - ∑ c : C, r c σ := by
      simpa [colQ] using hcolDiv σ
    rw [hdiv]
    exact Nat.add_sub_of_le (hcolLe σ)
  · intro c σ
    simp [val, hr]

theorem exists_with_residueVals
    {m T : Nat} [NeZero m] {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (R : ResidueSpec m T C)
    (hrow : R.RowCompatible I) (hcol : R.ColCompatible I)
    (hrowLe : ∀ c : C,
      (∑ σ : Fin T, (R.target c σ).val) ≤ I.colorDegree c)
    (hcolLe : ∀ σ : Fin T,
      (∑ c : C, (R.target c σ).val) ≤ Fintype.card X) :
    ∃ M : CountMatrix I, M.HasResidues R := by
  classical
  let r : C → Fin T → Nat := fun c σ => (R.target c σ).val
  have hr : ∀ c σ, ((r c σ : Nat) : ZMod m) = R.target c σ := by
    intro c σ
    simp [r]
  have hrowDiv : ∀ c : C,
      m * ((I.colorDegree c - ∑ σ : Fin T, r c σ) / m) =
        I.colorDegree c - ∑ σ : Fin T, r c σ := by
    intro c
    have hsumCast : (((∑ σ : Fin T, r c σ) : Nat) : ZMod m) =
        ∑ σ : Fin T, R.target c σ := by
      simp [r]
    have hdiff :
        (((I.colorDegree c - ∑ σ : Fin T, r c σ) : Nat) : ZMod m) =
          0 := by
      rw [Nat.cast_sub (hrowLe c), hrow c, hsumCast, sub_self]
    have hdvd : m ∣ I.colorDegree c - ∑ σ : Fin T, r c σ :=
      (ZMod.natCast_eq_zero_iff
        (I.colorDegree c - ∑ σ : Fin T, r c σ) m).mp hdiff
    simpa [Nat.mul_comm] using Nat.div_mul_cancel hdvd
  have hcolDiv : ∀ σ : Fin T,
      m * ((Fintype.card X - ∑ c : C, r c σ) / m) =
        Fintype.card X - ∑ c : C, r c σ := by
    intro σ
    have hsumCast : (((∑ c : C, r c σ) : Nat) : ZMod m) =
        ∑ c : C, R.target c σ := by
      simp [r]
    have hdiff :
        (((Fintype.card X - ∑ c : C, r c σ) : Nat) : ZMod m) =
          0 := by
      rw [Nat.cast_sub (hcolLe σ), hcol σ, hsumCast, sub_self]
    have hdvd : m ∣ Fintype.card X - ∑ c : C, r c σ :=
      (ZMod.natCast_eq_zero_iff
        (Fintype.card X - ∑ c : C, r c σ) m).mp hdiff
    simpa [Nat.mul_comm] using Nat.div_mul_cancel hdvd
  have hTotal :
      (∑ c : C, (I.colorDegree c - ∑ σ : Fin T, r c σ) / m) =
        ∑ σ : Fin T, (Fintype.card X - ∑ c : C, r c σ) / m := by
    have hmulRow :
        m * (∑ c : C,
            (I.colorDegree c - ∑ σ : Fin T, r c σ) / m) =
          ∑ c : C, (I.colorDegree c - ∑ σ : Fin T, r c σ) := by
      calc
        m * (∑ c : C,
            (I.colorDegree c - ∑ σ : Fin T, r c σ) / m)
            =
          ∑ c : C,
            m * ((I.colorDegree c - ∑ σ : Fin T, r c σ) / m) := by
              rw [Finset.mul_sum]
        _ = ∑ c : C, (I.colorDegree c - ∑ σ : Fin T, r c σ) := by
              apply Finset.sum_congr rfl
              intro c _hc
              exact hrowDiv c
    have hmulCol :
        m * (∑ σ : Fin T,
            (Fintype.card X - ∑ c : C, r c σ) / m) =
          ∑ σ : Fin T, (Fintype.card X - ∑ c : C, r c σ) := by
      calc
        m * (∑ σ : Fin T,
            (Fintype.card X - ∑ c : C, r c σ) / m)
            =
          ∑ σ : Fin T,
            m * ((Fintype.card X - ∑ c : C, r c σ) / m) := by
              rw [Finset.mul_sum]
        _ = ∑ σ : Fin T, (Fintype.card X - ∑ c : C, r c σ) := by
              apply Finset.sum_congr rfl
              intro σ _hσ
              exact hcolDiv σ
    have hdiffEq :
        (∑ c : C, (I.colorDegree c - ∑ σ : Fin T, r c σ)) =
          ∑ σ : Fin T, (Fintype.card X - ∑ c : C, r c σ) := by
      calc
        (∑ c : C, (I.colorDegree c - ∑ σ : Fin T, r c σ))
            = (∑ c : C, I.colorDegree c) -
                ∑ c : C, ∑ σ : Fin T, r c σ := by
                simpa using
                  (Finset.sum_tsub_distrib (s := (Finset.univ : Finset C))
                    (f := fun c : C => I.colorDegree c)
                    (g := fun c : C => ∑ σ : Fin T, r c σ)
                    (by intro c _hc; exact hrowLe c))
        _ = T * Fintype.card X -
                ∑ c : C, ∑ σ : Fin T, r c σ := by
                rw [I.sum_colorDegree]
        _ = (∑ σ : Fin T, Fintype.card X) -
                ∑ σ : Fin T, ∑ c : C, r c σ := by
                rw [Finset.sum_comm]
                simp [Finset.sum_const]
        _ = ∑ σ : Fin T, (Fintype.card X - ∑ c : C, r c σ) := by
                simpa using
                  (Finset.sum_tsub_distrib
                    (s := (Finset.univ : Finset (Fin T)))
                    (f := fun _σ : Fin T => Fintype.card X)
                    (g := fun σ : Fin T => ∑ c : C, r c σ)
                    (by intro σ _hσ; exact hcolLe σ)).symm
    have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
    exact Nat.eq_of_mul_eq_mul_left hmpos
      (by rw [hmulRow, hmulCol, hdiffEq])
  exact exists_with_residueQuotients r hr hrowLe hcolLe hrowDiv hcolDiv
    hTotal

theorem exists_with_residues_of_largeMargin
    {m T : Nat} [NeZero m] {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (hTpos : 0 < T)
    (hLarge : ∀ c : C, m * Fintype.card C * T < I.colorDegree c)
    (R : ResidueSpec m T C)
    (hrow : R.RowCompatible I) (hcol : R.ColCompatible I) :
    ∃ M : CountMatrix I, M.HasResidues R := by
  classical
  refine exists_with_residueVals I R hrow hcol ?_ ?_
  · intro c
    have hvalLe :
        ∀ σ ∈ (Finset.univ : Finset (Fin T)),
          (R.target c σ).val ≤ m - 1 := by
      intro σ _hσ
      have hlt := ZMod.val_lt (R.target c σ)
      omega
    have hsumBound :=
      Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin T))
        (fun σ : Fin T => (R.target c σ).val) (m - 1) hvalLe
    have hsumBound' :
        (∑ σ : Fin T, (R.target c σ).val) ≤ T * (m - 1) := by
      simpa [Fintype.card_fin, nsmul_eq_mul, Nat.mul_comm] using hsumBound
    have hcardCpos : 0 < Fintype.card C :=
      Fintype.card_pos_iff.mpr ⟨c⟩
    have hscale : T * (m - 1) ≤ m * Fintype.card C * T := by
      calc
        T * (m - 1) ≤ T * m :=
          Nat.mul_le_mul_left T (Nat.sub_le m 1)
        _ = m * T := Nat.mul_comm T m
        _ ≤ (m * Fintype.card C) * T :=
          Nat.mul_le_mul_right T (Nat.le_mul_of_pos_right m hcardCpos)
        _ = m * Fintype.card C * T := rfl
    exact hsumBound'.trans (hscale.trans (Nat.le_of_lt (hLarge c)))
  · intro σ
    by_cases hC : Nonempty C
    · rcases hC with ⟨c0⟩
      have hvalLe :
          ∀ c ∈ (Finset.univ : Finset C),
            (R.target c σ).val ≤ m - 1 := by
        intro c _hc
        have hlt := ZMod.val_lt (R.target c σ)
        omega
      have hsumBound :=
        Finset.sum_le_card_nsmul (Finset.univ : Finset C)
          (fun c : C => (R.target c σ).val) (m - 1) hvalLe
      have hsumBound' :
          (∑ c : C, (R.target c σ).val) ≤
            Fintype.card C * (m - 1) := by
        simpa [nsmul_eq_mul, Nat.mul_comm] using hsumBound
      have hdegreeLe : I.colorDegree c0 ≤ Fintype.card X := by
        unfold Incidence.colorDegree
        exact Finset.card_filter_le (Finset.univ : Finset X)
          (fun x : X => c0 ∈ I.active x)
      have hcap : Fintype.card C * (m - 1) ≤ Fintype.card X := by
        have hlargeX : m * Fintype.card C * T < Fintype.card X :=
          (hLarge c0).trans_le hdegreeLe
        have hscale : Fintype.card C * (m - 1) ≤ m * Fintype.card C * T := by
          calc
            Fintype.card C * (m - 1) ≤ Fintype.card C * m :=
              Nat.mul_le_mul_left (Fintype.card C) (Nat.sub_le m 1)
            _ = m * Fintype.card C := Nat.mul_comm (Fintype.card C) m
            _ ≤ (m * Fintype.card C) * T :=
              Nat.le_mul_of_pos_right (m * Fintype.card C) hTpos
            _ = m * Fintype.card C * T := rfl
        exact hscale.trans (Nat.le_of_lt hlargeX)
      exact hsumBound'.trans hcap
    · haveI : IsEmpty C := not_nonempty_iff.mp hC
      simp

theorem cutMass_symbols_univ {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I) (U : Finset C) :
    M.cutMass U (Finset.univ : Finset (Fin T))
      = ∑ c ∈ U, I.colorDegree c := by
  classical
  calc
    M.cutMass U (Finset.univ : Finset (Fin T))
        = ∑ c ∈ U, ∑ σ : Fin T, M.val c σ := by
            rfl
    _ = ∑ c ∈ U, I.colorDegree c := by
            apply Finset.sum_congr rfl
            intro c _hc
            exact M.row_sum c

theorem cutMass_add_le_iff_le_cutSlack {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I)
    (U : Finset C) (S : Finset (Fin T))
    (hHall : M.cutMass U S ≤ I.cutCap U S) (k : Nat) :
    M.cutMass U S + k ≤ I.cutCap U S ↔ k ≤ M.cutSlack U S := by
  unfold cutSlack
  omega

theorem cutMass_colors_univ {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I) (S : Finset (Fin T)) :
    M.cutMass (Finset.univ : Finset C) S = S.card * Fintype.card X := by
  classical
  calc
    M.cutMass (Finset.univ : Finset C) S
        = ∑ σ ∈ S, ∑ c : C, M.val c σ := by
            unfold cutMass
            rw [Finset.sum_comm]
    _ = ∑ _σ ∈ S, Fintype.card X := by
            apply Finset.sum_congr rfl
            intro σ _hσ
            exact M.col_sum σ
    _ = S.card * Fintype.card X := by
            simp [Finset.sum_const]

theorem cutMass_symbols_univ_eq_cutCap {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I) (U : Finset C) :
    M.cutMass U (Finset.univ : Finset (Fin T))
      = I.cutCap U (Finset.univ : Finset (Fin T)) := by
  rw [M.cutMass_symbols_univ U, I.cutCap_symbols_univ U,
    I.sum_colorDegree_on U]

theorem cutMass_colors_univ_eq_cutCap {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I) (S : Finset (Fin T)) :
    M.cutMass (Finset.univ : Finset C) S
      = I.cutCap (Finset.univ : Finset C) S := by
  rw [M.cutMass_colors_univ S, I.cutCap_colors_univ S]

theorem cutMass_colors_empty {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I) (S : Finset (Fin T)) :
    M.cutMass (∅ : Finset C) S = 0 := by
  simp [cutMass]

theorem cutMass_symbols_empty {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I) (U : Finset C) :
    M.cutMass U (∅ : Finset (Fin T)) = 0 := by
  simp [cutMass]

theorem cutMass_symbol_singleton {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I)
    (U : Finset C) (σ : Fin T) :
    M.cutMass U ({σ} : Finset (Fin T)) = ∑ c ∈ U, M.val c σ := by
  simp [cutMass]

theorem cutSlack_symbol_singleton {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I)
    (U : Finset C) (σ : Fin T) :
    M.cutSlack U ({σ} : Finset (Fin T)) =
      I.hitCount U - ∑ c ∈ U, M.val c σ := by
  rw [cutSlack, M.cutMass_symbol_singleton U σ,
    I.cutCap_symbol_singleton U σ]

theorem cutSlack_image_castSucc_singleton {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence (T + 1) X C} (M : CountMatrix I)
    (U : Finset C) (σ : Fin T) :
    M.cutSlack U
        (({σ} : Finset (Fin T)).image
          (Fin.castSucc : Fin T → Fin (T + 1))) =
      I.hitCount U - ∑ c ∈ U, M.val c (Fin.castSucc σ) := by
  simpa using M.cutSlack_symbol_singleton U (Fin.castSucc σ)

theorem cutMass_image_castSucc {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence (T + 1) X C} (M : CountMatrix I)
    (U : Finset C) (S : Finset (Fin T)) :
    M.cutMass U (S.image (Fin.castSucc : Fin T → Fin (T + 1))) =
      ∑ c ∈ U, ∑ σ ∈ S, M.val c (Fin.castSucc σ) := by
  classical
  unfold cutMass
  apply Finset.sum_congr rfl
  intro c _hc
  rw [Finset.sum_image]
  intro σ hσ τ hτ hEq
  exact Fin.ext (by simpa using congrArg Fin.val hEq)

theorem cutSlack_image_castSucc {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence (T + 1) X C} (M : CountMatrix I)
    (U : Finset C) (S : Finset (Fin T)) :
    M.cutSlack U (S.image (Fin.castSucc : Fin T → Fin (T + 1))) =
      (∑ x : X, min ((I.active x ∩ U).card) S.card)
        - ∑ c ∈ U, ∑ σ ∈ S, M.val c (Fin.castSucc σ) := by
  rw [cutSlack, M.cutMass_image_castSucc U S,
    I.cutCap_image_castSucc U S]

theorem cutMass_pair {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I)
    (U : Finset C) {σ τ : Fin T} (hστ : σ ≠ τ) :
    M.cutMass U ({σ, τ} : Finset (Fin T)) =
      ∑ c ∈ U, (M.val c σ + M.val c τ) := by
  classical
  unfold cutMass
  apply Finset.sum_congr rfl
  intro c _hc
  rw [Finset.sum_pair hστ]

theorem cutMass_image_castSucc_pair {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence (T + 1) X C} (M : CountMatrix I)
    (U : Finset C) {σ τ : Fin T} (hστ : σ ≠ τ) :
    M.cutMass U
        (({σ, τ} : Finset (Fin T)).image
          (Fin.castSucc : Fin T → Fin (T + 1))) =
      ∑ c ∈ U, (M.val c (Fin.castSucc σ) +
        M.val c (Fin.castSucc τ)) := by
  classical
  have hcast : Fin.castSucc σ ≠ Fin.castSucc τ := by
    intro h
    exact hστ (Fin.ext (by simpa using congrArg Fin.val h))
  have himage :
      (({σ, τ} : Finset (Fin T)).image
          (Fin.castSucc : Fin T → Fin (T + 1))) =
        ({Fin.castSucc σ, Fin.castSucc τ} : Finset (Fin (T + 1))) := by
    ext ρ
    simp
  rw [himage]
  exact M.cutMass_pair U hcast

theorem cutSlack_image_castSucc_pair {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence (T + 1) X C} (M : CountMatrix I)
    (U : Finset C) {σ τ : Fin T} (hστ : σ ≠ τ) :
    M.cutSlack U
        (({σ, τ} : Finset (Fin T)).image
          (Fin.castSucc : Fin T → Fin (T + 1))) =
      I.cutCap U
          (({σ, τ} : Finset (Fin T)).image
            (Fin.castSucc : Fin T → Fin (T + 1)))
        - ∑ c ∈ U, (M.val c (Fin.castSucc σ) +
          M.val c (Fin.castSucc τ)) := by
  rw [cutSlack, M.cutMass_image_castSucc_pair U hστ]

theorem cutSlack_image_castSucc_pair_eq_min_two {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence (T + 1) X C} (M : CountMatrix I)
    (U : Finset C) {σ τ : Fin T} (hστ : σ ≠ τ) :
    M.cutSlack U
        (({σ, τ} : Finset (Fin T)).image
          (Fin.castSucc : Fin T → Fin (T + 1))) =
      (∑ x : X, min ((I.active x ∩ U).card) 2)
        - ∑ c ∈ U, (M.val c (Fin.castSucc σ) +
          M.val c (Fin.castSucc τ)) := by
  rw [M.cutSlack_image_castSucc_pair U hστ,
    I.cutCap_image_castSucc_pair U hστ]

theorem cutMass_colors_empty_eq_cutCap {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I) (S : Finset (Fin T)) :
    M.cutMass (∅ : Finset C) S = I.cutCap (∅ : Finset C) S := by
  rw [M.cutMass_colors_empty S, I.cutCap_colors_empty S]

theorem cutMass_symbols_empty_eq_cutCap {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I) (U : Finset C) :
    M.cutMass U (∅ : Finset (Fin T)) = I.cutCap U (∅ : Finset (Fin T)) := by
  rw [M.cutMass_symbols_empty U, I.cutCap_symbols_empty U]

theorem cutMass_mono {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I)
    {U₁ U₂ : Finset C} {S₁ S₂ : Finset (Fin T)}
    (hU : U₁ ⊆ U₂) (hS : S₁ ⊆ S₂) :
    M.cutMass U₁ S₁ ≤ M.cutMass U₂ S₂ := by
  unfold cutMass
  have hcolor :
      (∑ c ∈ U₁, ∑ σ ∈ S₁, M.val c σ)
        ≤ ∑ c ∈ U₂, ∑ σ ∈ S₁, M.val c σ :=
    Finset.sum_le_sum_of_subset hU
  have hsymbol :
      (∑ c ∈ U₂, ∑ σ ∈ S₁, M.val c σ)
        ≤ ∑ c ∈ U₂, ∑ σ ∈ S₂, M.val c σ := by
    apply Finset.sum_le_sum
    intro c _hc
    exact Finset.sum_le_sum_of_subset hS
  exact hcolor.trans hsymbol

theorem cutMass_mono_colors {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I)
    {U₁ U₂ : Finset C} (hU : U₁ ⊆ U₂) (S : Finset (Fin T)) :
    M.cutMass U₁ S ≤ M.cutMass U₂ S :=
  M.cutMass_mono hU (fun _ h => h)

theorem cutMass_mono_symbols {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I)
    (U : Finset C) {S₁ S₂ : Finset (Fin T)} (hS : S₁ ⊆ S₂) :
    M.cutMass U S₁ ≤ M.cutMass U S₂ :=
  M.cutMass_mono (fun _ h => h) hS

theorem hallCuts_of_nontrivial {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I)
    (hCuts :
      ∀ U : Finset C, ∀ S : Finset (Fin T),
        U.Nonempty → U ≠ (Finset.univ : Finset C) →
        S.Nonempty → S ≠ (Finset.univ : Finset (Fin T)) →
        M.cutMass U S ≤ I.cutCap U S) :
    M.HallCuts := by
  intro U S
  by_cases hUempty : U = ∅
  · subst U
    rw [M.cutMass_colors_empty_eq_cutCap S]
  by_cases hSempty : S = ∅
  · subst S
    rw [M.cutMass_symbols_empty_eq_cutCap U]
  by_cases hUuniv : U = (Finset.univ : Finset C)
  · subst U
    rw [M.cutMass_colors_univ_eq_cutCap S]
  by_cases hSuniv : S = (Finset.univ : Finset (Fin T))
  · subst S
    rw [M.cutMass_symbols_univ_eq_cutCap U]
  exact hCuts U S
    (Finset.nonempty_iff_ne_empty.mpr hUempty) hUuniv
    (Finset.nonempty_iff_ne_empty.mpr hSempty) hSuniv

theorem hallCuts_iff_nontrivial {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I) :
    M.HallCuts ↔
      ∀ U : Finset C, ∀ S : Finset (Fin T),
        U.Nonempty → U ≠ (Finset.univ : Finset C) →
        S.Nonempty → S ≠ (Finset.univ : Finset (Fin T)) →
        M.cutMass U S ≤ I.cutCap U S := by
  constructor
  · intro hCuts U S _hUne _hUuniv _hSne _hSuniv
    exact hCuts U S
  · exact M.hallCuts_of_nontrivial

theorem hallCuts_of_scaled_bary_error_le_mixed {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I) (hTpos : 0 < T)
    (hScaled :
      ∀ U : Finset C, ∀ S : Finset (Fin T),
        T * M.cutMass U S ≤
          S.card * (∑ c ∈ U, I.colorDegree c) +
            I.mixedCount U * min S.card (T - S.card)) :
    M.HallCuts := by
  intro U S
  have hmul :
      T * M.cutMass U S ≤ T * I.cutCap U S :=
    (hScaled U S).trans
      (I.scaled_bary_cutMass_add_mixed_le_cutCap U S)
  exact Nat.le_of_mul_le_mul_left hmul hTpos

theorem hallCuts_of_nontrivial_scaled_bary_error_le_mixed
    {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I) (hTpos : 0 < T)
    (hScaled :
      ∀ U : Finset C, ∀ S : Finset (Fin T),
        U.Nonempty → U ≠ (Finset.univ : Finset C) →
        S.Nonempty → S ≠ (Finset.univ : Finset (Fin T)) →
          T * M.cutMass U S ≤
            S.card * (∑ c ∈ U, I.colorDegree c) +
              I.mixedCount U * min S.card (T - S.card)) :
    M.HallCuts := by
  apply M.hallCuts_of_nontrivial
  intro U S hUne hUuniv hSne hSuniv
  have hmul :
      T * M.cutMass U S ≤ T * I.cutCap U S :=
    (hScaled U S hUne hUuniv hSne hSuniv).trans
      (I.scaled_bary_cutMass_add_mixed_le_cutCap U S)
  exact Nat.le_of_mul_le_mul_left hmul hTpos

theorem hallCuts_one {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence 1 X C} (M : CountMatrix I) :
    M.HallCuts := by
  classical
  apply M.hallCuts_of_nontrivial
  intro U S _hUne _hUuniv hSne hSuniv
  have hS : S = (Finset.univ : Finset (Fin 1)) := by
    rcases hSne with ⟨σ, hσ⟩
    fin_cases σ
    ext τ
    fin_cases τ
    constructor
    · intro _h
      simp
    · intro _h
      simpa using hσ
  exact False.elim (hSuniv hS)

theorem finset_fin_two_nonempty_proper_eq_singleton
    (S : Finset (Fin 2)) (hSne : S.Nonempty)
    (hSuniv : S ≠ (Finset.univ : Finset (Fin 2))) :
    ∃ σ : Fin 2, S = {σ} := by
  classical
  by_cases h0 : (0 : Fin 2) ∈ S
  · by_cases h1 : (1 : Fin 2) ∈ S
    · have hS : S = (Finset.univ : Finset (Fin 2)) := by
        ext σ
        fin_cases σ <;> simp [h0, h1]
      exact False.elim (hSuniv hS)
    · exact ⟨0, by
        ext σ
        fin_cases σ <;> simp [h0, h1]⟩
  · rcases hSne with ⟨σ, hσ⟩
    fin_cases σ
    · exact False.elim (h0 hσ)
    · have h1 : (1 : Fin 2) ∈ S := by
        simpa using hσ
      exact ⟨1, by
        ext τ
        fin_cases τ <;> simp [h0, h1]⟩

theorem hallCuts_two_of_singleSymbol {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence 2 X C} (M : CountMatrix I)
    (hSingle : ∀ U : Finset C, ∀ σ : Fin 2,
      (∑ c ∈ U, M.val c σ) ≤ I.hitCount U) :
    M.HallCuts := by
  classical
  apply M.hallCuts_of_nontrivial
  intro U S _hUne _hUuniv hSne hSuniv
  rcases finset_fin_two_nonempty_proper_eq_singleton S hSne hSuniv with
    ⟨σ, rfl⟩
  rw [M.cutMass_symbol_singleton U σ, I.cutCap_symbol_singleton U σ]
  exact hSingle U σ

theorem hallCuts_two_iff_singleSymbol {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence 2 X C} (M : CountMatrix I) :
    M.HallCuts ↔
      ∀ U : Finset C, ∀ σ : Fin 2,
        (∑ c ∈ U, M.val c σ) ≤ I.hitCount U :=
  ⟨fun hHall U σ => by
      rw [← M.cutMass_symbol_singleton U σ, ← I.cutCap_symbol_singleton U σ]
      exact hHall U ({σ} : Finset (Fin 2)),
    M.hallCuts_two_of_singleSymbol⟩

theorem singleSymbol_hall {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I)
    (hHall : M.HallCuts) (U : Finset C) (σ : Fin T) :
    (∑ c ∈ U, M.val c σ) ≤ I.hitCount U := by
  rw [← M.cutMass_symbol_singleton U σ, ← I.cutCap_symbol_singleton U σ]
  exact hHall U ({σ} : Finset (Fin T))

theorem exists_singleSymbol_token_matching {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I)
    (hHall : M.HallCuts) (σ : Fin T) :
    ∃ f : (Sigma fun c : C => Fin (M.val c σ)) → X,
      Function.Injective f ∧
      ∀ q : Sigma fun c : C => Fin (M.val c σ),
        q.1 ∈ I.active (f q) := by
  classical
  apply I.exists_injective_token_matching_of_hall
    (colorOf := fun q : Sigma fun c : C => Fin (M.val c σ) => q.1)
  intro A
  let U : Finset C :=
    A.image (fun q : Sigma fun c : C => Fin (M.val c σ) => q.1)
  have hsubset :
      A ⊆ U.sigma
        (fun c : C => (Finset.univ : Finset (Fin (M.val c σ)))) := by
    intro q hq
    exact Finset.mem_sigma.mpr
      ⟨Finset.mem_image_of_mem
        (fun q : Sigma fun c : C => Fin (M.val c σ) => q.1) hq,
        Finset.mem_univ q.2⟩
  have hcardA :
      A.card ≤
        (U.sigma
          (fun c : C => (Finset.univ : Finset (Fin (M.val c σ))))).card :=
    Finset.card_le_card hsubset
  have hcardSigma :
      (U.sigma
          (fun c : C => (Finset.univ : Finset (Fin (M.val c σ))))).card
        = ∑ c ∈ U, M.val c σ := by
    rw [Finset.card_sigma]
    simp
  rw [hcardSigma] at hcardA
  exact hcardA.trans (M.singleSymbol_hall hHall U σ)

theorem exists_singleSymbol_bijective_token_matching
    {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I)
    (hHall : M.HallCuts) (σ : Fin T) :
    ∃ f : (Sigma fun c : C => Fin (M.val c σ)) ≃ X,
      ∀ q : Sigma fun c : C => Fin (M.val c σ),
        q.1 ∈ I.active (f q) := by
  classical
  rcases M.exists_singleSymbol_token_matching hHall σ with
    ⟨f, hfInj, hfActive⟩
  have hcard :
      Fintype.card (Sigma fun c : C => Fin (M.val c σ))
        = Fintype.card X := by
    rw [Fintype.card_sigma]
    simpa using M.col_sum σ
  have hfBij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hfInj, hcard⟩
  exact ⟨Equiv.ofBijective f hfBij, hfActive⟩

theorem choiceDegree_of_bijective_token_matching
    {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I) (σ : Fin T)
    (f : (Sigma fun c : C => Fin (M.val c σ)) ≃ X) (c : C) :
    Incidence.choiceDegree (fun x : X => (f.symm x).1) c =
      M.val c σ := by
  classical
  unfold Incidence.choiceDegree
  calc
    ((Finset.univ : Finset X).filter
        (fun x => (f.symm x).1 = c)).card
        = ∑ x : X, if (f.symm x).1 = c then 1 else 0 := by
            rw [Finset.card_filter]
    _ = ∑ q : Sigma fun c : C => Fin (M.val c σ),
          if q.1 = c then 1 else 0 := by
            exact Fintype.sum_equiv f.symm
              (fun x : X => if (f.symm x).1 = c then (1 : Nat) else 0)
              (fun q : Sigma fun c : C => Fin (M.val c σ) =>
                if q.1 = c then (1 : Nat) else 0)
              (by intro x; simp)
    _ = M.val c σ := by
            rw [Fintype.sum_sigma]
            calc
              (∑ x : C, ∑ q : Fin (M.val x σ),
                  if x = c then (1 : Nat) else 0)
                  = ∑ x : C, if x = c then M.val x σ else 0 := by
                      apply Finset.sum_congr rfl
                      intro x _hx
                      by_cases hxc : x = c <;> simp [hxc]
              _ = M.val c σ := by
                      simp

structure ColumnFilling {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I) where
  color : X → Fin T → C
  active : ∀ x : X, ∀ σ : Fin T, color x σ ∈ I.active x
  count_eq :
    ∀ c : C, ∀ σ : Fin T,
      Incidence.choiceDegree (fun x : X => color x σ) c = M.val c σ

theorem exists_columnFilling_of_hallCuts
    {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I)
    (hHall : M.HallCuts) :
    Nonempty M.ColumnFilling := by
  classical
  have hmatch :
      ∀ σ : Fin T,
        ∃ f : (Sigma fun c : C => Fin (M.val c σ)) ≃ X,
          ∀ q : Sigma fun c : C => Fin (M.val c σ),
            q.1 ∈ I.active (f q) := by
    intro σ
    exact M.exists_singleSymbol_bijective_token_matching hHall σ
  choose f hfActive using hmatch
  exact ⟨{
    color := fun x σ => ((f σ).symm x).1
    active := by
      intro x σ
      simpa using hfActive σ ((f σ).symm x)
    count_eq := by
      intro c σ
      exact M.choiceDegree_of_bijective_token_matching σ (f σ) c
  }⟩

theorem eraseChoice_colorDegree_add_val_of_bijective_token_matching
    {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence (T + 1) X C} (M : CountMatrix I) (σ : Fin (T + 1))
    (f : (Sigma fun c : C => Fin (M.val c σ)) ≃ X)
    (hfActive :
      ∀ q : Sigma fun c : C => Fin (M.val c σ), q.1 ∈ I.active (f q))
    (c : C) :
    let choice : X → C := fun x => (f.symm x).1
    let hchoice : ∀ x : X, choice x ∈ I.active x := by
      intro x
      simpa [choice] using hfActive (f.symm x)
    (I.eraseChoice choice hchoice).colorDegree c + M.val c σ =
      I.colorDegree c := by
  intro choice hchoice
  rw [← M.choiceDegree_of_bijective_token_matching σ f c]
  exact I.eraseChoice_colorDegree_add_choiceDegree choice hchoice c

def eraseLastCountMatrix
    {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence (T + 1) X C} (M : CountMatrix I)
    (choice : X → C) (hchoice : ∀ x : X, choice x ∈ I.active x)
    (hdegree :
      ∀ c : C, Incidence.choiceDegree choice c = M.val c (Fin.last T)) :
    CountMatrix (I.eraseChoice choice hchoice) where
  val := fun c σ => M.val c σ.castSucc
  row_sum := by
    intro c
    have hrow := M.row_sum c
    rw [Fin.sum_univ_castSucc] at hrow
    have herase := I.eraseChoice_colorDegree_add_choiceDegree choice hchoice c
    rw [hdegree c] at herase
    omega
  col_sum := by
    intro σ
    exact M.col_sum σ.castSucc

theorem eraseLastCountMatrix_cutMass
    {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence (T + 1) X C} (M : CountMatrix I)
    (choice : X → C) (hchoice : ∀ x : X, choice x ∈ I.active x)
    (hdegree :
      ∀ c : C, Incidence.choiceDegree choice c = M.val c (Fin.last T))
    (U : Finset C) (S : Finset (Fin T)) :
    (M.eraseLastCountMatrix choice hchoice hdegree).cutMass U S =
      M.cutMass U (S.image Fin.castSucc) := by
  classical
  unfold cutMass eraseLastCountMatrix
  apply Finset.sum_congr rfl
  intro c _hc
  rw [Finset.sum_image]
  intro a _ha b _hb hab
  exact Fin.castSucc_injective T hab

theorem cutMass_last_eq_choiceHitCount
    {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence (T + 1) X C} (M : CountMatrix I)
    (choice : X → C)
    (hdegree :
      ∀ c : C, Incidence.choiceDegree choice c = M.val c (Fin.last T))
    (U : Finset C) :
    M.cutMass U ({Fin.last T} : Finset (Fin (T + 1))) =
      Incidence.choiceHitCount choice U := by
  rw [M.cutMass_symbol_singleton U (Fin.last T)]
  calc
    (∑ c ∈ U, M.val c (Fin.last T))
        = ∑ c ∈ U, Incidence.choiceDegree choice c := by
            apply Finset.sum_congr rfl
            intro c _hc
            rw [hdegree c]
    _ = Incidence.choiceHitCount choice U :=
            Incidence.sum_choiceDegree_on choice U

theorem cutMass_image_castSucc_insert_last_eq_eraseLast_add_choiceHitCount
    {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence (T + 1) X C} (M : CountMatrix I)
    (choice : X → C) (hchoice : ∀ x : X, choice x ∈ I.active x)
    (hdegree :
      ∀ c : C, Incidence.choiceDegree choice c = M.val c (Fin.last T))
    (U : Finset C) (S : Finset (Fin T)) :
    M.cutMass U
        (insert (Fin.last T)
          (S.image (Fin.castSucc : Fin T → Fin (T + 1)))) =
      (M.eraseLastCountMatrix choice hchoice hdegree).cutMass U S
        + Incidence.choiceHitCount choice U := by
  classical
  have hlast :
      Fin.last T ∉ S.image (Fin.castSucc : Fin T → Fin (T + 1)) :=
    Incidence.last_notMem_image_castSucc S
  have hlastMass :
      (∑ c ∈ U, M.val c (Fin.last T)) =
        Incidence.choiceHitCount choice U := by
    simpa [cutMass] using
      (M.cutMass_last_eq_choiceHitCount choice hdegree U)
  rw [M.eraseLastCountMatrix_cutMass choice hchoice hdegree U S]
  unfold cutMass
  calc
    (∑ c ∈ U,
        ∑ σ ∈ insert (Fin.last T)
          (S.image (Fin.castSucc : Fin T → Fin (T + 1))),
          M.val c σ)
        =
      ∑ c ∈ U,
        (M.val c (Fin.last T) +
          ∑ σ ∈ S.image (Fin.castSucc : Fin T → Fin (T + 1)),
            M.val c σ) := by
          apply Finset.sum_congr rfl
          intro c _hc
          rw [Finset.sum_insert hlast]
    _ =
      (∑ c ∈ U,
        ∑ σ ∈ S.image (Fin.castSucc : Fin T → Fin (T + 1)),
          M.val c σ)
        + ∑ c ∈ U, M.val c (Fin.last T) := by
          rw [Finset.sum_add_distrib]
          omega
    _ =
      (∑ c ∈ U,
        ∑ σ ∈ S.image (Fin.castSucc : Fin T → Fin (T + 1)),
          M.val c σ)
        + Incidence.choiceHitCount choice U := by
          rw [hlastMass]

theorem eraseLastCountMatrix_hallCuts_of_cutCap_insert_le
    {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence (T + 1) X C} (M : CountMatrix I)
    (choice : X → C) (hchoice : ∀ x : X, choice x ∈ I.active x)
    (hdegree :
      ∀ c : C, Incidence.choiceDegree choice c = M.val c (Fin.last T))
    (hHall : M.HallCuts)
    (hCover :
      ∀ U : Finset C, ∀ S : Finset (Fin T),
        I.cutCap U
            (insert (Fin.last T)
              (S.image (Fin.castSucc : Fin T → Fin (T + 1))))
          ≤ (I.eraseChoice choice hchoice).cutCap U S
              + Incidence.choiceHitCount choice U) :
    (M.eraseLastCountMatrix choice hchoice hdegree).HallCuts := by
  classical
  intro U S
  let M' := M.eraseLastCountMatrix choice hchoice hdegree
  let hit := Incidence.choiceHitCount choice U
  have hMass :
      M.cutMass U
          (insert (Fin.last T)
            (S.image (Fin.castSucc : Fin T → Fin (T + 1)))) =
        M'.cutMass U S + hit := by
    simpa [M', hit] using
      M.cutMass_image_castSucc_insert_last_eq_eraseLast_add_choiceHitCount
        choice hchoice hdegree U S
  have hStep :
      M'.cutMass U S + hit
        ≤ (I.eraseChoice choice hchoice).cutCap U S + hit := by
    rw [← hMass]
    exact (hHall U
      (insert (Fin.last T)
        (S.image (Fin.castSucc : Fin T → Fin (T + 1))))).trans
      (hCover U S)
  change M'.cutMass U S ≤ (I.eraseChoice choice hchoice).cutCap U S
  omega

theorem eraseLastCountMatrix_hallCuts_of_cutCap_slack
    {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence (T + 1) X C} (M : CountMatrix I)
    (choice : X → C) (hchoice : ∀ x : X, choice x ∈ I.active x)
    (hdegree :
      ∀ c : C, Incidence.choiceDegree choice c = M.val c (Fin.last T))
    (hSlack :
      ∀ U : Finset C, ∀ S : Finset (Fin T),
        M.cutMass U (S.image (Fin.castSucc : Fin T → Fin (T + 1)))
            + Incidence.choiceLowHitCount I choice U S
          ≤ I.cutCap U
              (S.image (Fin.castSucc : Fin T → Fin (T + 1)))) :
    (M.eraseLastCountMatrix choice hchoice hdegree).HallCuts := by
  classical
  intro U S
  let M' := M.eraseLastCountMatrix choice hchoice hdegree
  let low := Incidence.choiceLowHitCount I choice U S
  have hMass :
      M'.cutMass U S =
        M.cutMass U (S.image (Fin.castSucc : Fin T → Fin (T + 1))) := by
    simpa [M'] using M.eraseLastCountMatrix_cutMass choice hchoice hdegree U S
  have hCap :
      I.cutCap U (S.image (Fin.castSucc : Fin T → Fin (T + 1))) =
        (I.eraseChoice choice hchoice).cutCap U S + low := by
    simpa [low] using
      I.cutCap_image_castSucc_eq_eraseChoice_cutCap_add_choiceLowHitCount
        choice hchoice U S
  have hStep :
      M'.cutMass U S + low
        ≤ (I.eraseChoice choice hchoice).cutCap U S + low := by
    rw [hMass, ← hCap]
    exact hSlack U S
  change M'.cutMass U S ≤ (I.eraseChoice choice hchoice).cutCap U S
  omega

theorem choiceLowHitCount_univ_le_cutSlack_image_castSucc
    {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence (T + 1) X C} (M : CountMatrix I)
    (choice : X → C) (hchoice : ∀ x : X, choice x ∈ I.active x)
    (hdegree :
      ∀ c : C, Incidence.choiceDegree choice c = M.val c (Fin.last T))
    (hHall : M.HallCuts) (U : Finset C) :
    Incidence.choiceLowHitCount I choice U
        (Finset.univ : Finset (Fin T))
      ≤ M.cutSlack U
          ((Finset.univ : Finset (Fin T)).image
            (Fin.castSucc : Fin T → Fin (T + 1))) := by
  classical
  let S : Finset (Fin T) := Finset.univ
  let M' := M.eraseLastCountMatrix choice hchoice hdegree
  let I' := I.eraseChoice choice hchoice
  let low := Incidence.choiceLowHitCount I choice U S
  have hHallUS :
      M.cutMass U (S.image (Fin.castSucc : Fin T → Fin (T + 1)))
        ≤ I.cutCap U (S.image (Fin.castSucc : Fin T → Fin (T + 1))) :=
    hHall U (S.image (Fin.castSucc : Fin T → Fin (T + 1)))
  have hMass :
      M'.cutMass U S =
        M.cutMass U (S.image (Fin.castSucc : Fin T → Fin (T + 1))) := by
    simpa [M', S] using
      M.eraseLastCountMatrix_cutMass choice hchoice hdegree U
        (Finset.univ : Finset (Fin T))
  have hUniv :
      M'.cutMass U S = I'.cutCap U S := by
    simpa [M', I', S] using
      M'.cutMass_symbols_univ_eq_cutCap U
  have hCap :
      I.cutCap U (S.image (Fin.castSucc : Fin T → Fin (T + 1))) =
        I'.cutCap U S + low := by
    simpa [I', S, low] using
      I.cutCap_image_castSucc_eq_eraseChoice_cutCap_add_choiceLowHitCount
        choice hchoice U (Finset.univ : Finset (Fin T))
  have hAdd :
      M.cutMass U (S.image (Fin.castSucc : Fin T → Fin (T + 1))) + low
        ≤ I.cutCap U (S.image (Fin.castSucc : Fin T → Fin (T + 1))) := by
    rw [← hMass, hUniv, hCap]
  exact
    ((M.cutMass_add_le_iff_le_cutSlack U
      (S.image (Fin.castSucc : Fin T → Fin (T + 1))) hHallUS low).1
      hAdd)

theorem eraseLastCountMatrix_hallCuts_two_of_singleton_cutCap_slack
    {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence 3 X C} (M : CountMatrix I)
    (choice : X → C) (hchoice : ∀ x : X, choice x ∈ I.active x)
    (hdegree :
      ∀ c : C, Incidence.choiceDegree choice c = M.val c (Fin.last 2))
    (hSlack : ∀ U : Finset C, ∀ σ : Fin 2,
      M.cutMass U
          (({σ} : Finset (Fin 2)).image
            (Fin.castSucc : Fin 2 → Fin 3))
        + Incidence.choiceLowHitCount I choice U ({σ} : Finset (Fin 2))
          ≤ I.cutCap U
              (({σ} : Finset (Fin 2)).image
                (Fin.castSucc : Fin 2 → Fin 3))) :
    (M.eraseLastCountMatrix choice hchoice hdegree).HallCuts := by
  classical
  apply CountMatrix.hallCuts_two_of_singleSymbol
  intro U σ
  let M' := M.eraseLastCountMatrix choice hchoice hdegree
  let I' := I.eraseChoice choice hchoice
  let low := Incidence.choiceLowHitCount I choice U ({σ} : Finset (Fin 2))
  have hMass :
      M'.cutMass U ({σ} : Finset (Fin 2)) =
        M.cutMass U
          (({σ} : Finset (Fin 2)).image
            (Fin.castSucc : Fin 2 → Fin 3)) := by
    simpa [M'] using
      M.eraseLastCountMatrix_cutMass choice hchoice hdegree U
        ({σ} : Finset (Fin 2))
  have hCap :
      I.cutCap U
          (({σ} : Finset (Fin 2)).image
            (Fin.castSucc : Fin 2 → Fin 3)) =
        I'.cutCap U ({σ} : Finset (Fin 2)) + low := by
    simpa [I', low] using
      I.cutCap_image_castSucc_eq_eraseChoice_cutCap_add_choiceLowHitCount
        choice hchoice U ({σ} : Finset (Fin 2))
  rw [← M'.cutMass_symbol_singleton U σ,
    ← I'.cutCap_symbol_singleton U σ]
  have h := hSlack U σ
  rw [← hMass, hCap] at h
  omega

theorem eraseLastHallCuts_two_of_singleton_selection
    {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence 3 X C) (M : CountMatrix I)
    (_hHall : M.HallCuts)
    (hSelect :
      ∃ f : (Sigma fun c : C => Fin (M.val c (Fin.last 2))) ≃ X,
        (∀ q : Sigma fun c : C => Fin (M.val c (Fin.last 2)),
            q.1 ∈ I.active (f q)) ∧
          let choice : X → C := fun x => (f.symm x).1
          ∀ U : Finset C, ∀ σ : Fin 2,
            M.cutMass U
                (({σ} : Finset (Fin 2)).image
                  (Fin.castSucc : Fin 2 → Fin 3))
              + Incidence.choiceLowHitCount I choice U
                  ({σ} : Finset (Fin 2))
                ≤ I.cutCap U
                    (({σ} : Finset (Fin 2)).image
                      (Fin.castSucc : Fin 2 → Fin 3))) :
    ∃ f : (Sigma fun c : C => Fin (M.val c (Fin.last 2))) ≃ X,
      ∃ hfActive :
        ∀ q : Sigma fun c : C => Fin (M.val c (Fin.last 2)),
          q.1 ∈ I.active (f q),
        let choice : X → C := fun x => (f.symm x).1
        let hchoice : ∀ x : X, choice x ∈ I.active x := by
          intro x
          have h := hfActive (f.symm x)
          rw [f.apply_symm_apply] at h
          simpa [choice] using h
        let hdegree :
            ∀ c : C,
              Incidence.choiceDegree choice c = M.val c (Fin.last 2) :=
          fun c => M.choiceDegree_of_bijective_token_matching
            (Fin.last 2) f c
        (M.eraseLastCountMatrix choice hchoice hdegree).HallCuts := by
  classical
  rcases hSelect with ⟨f, hfActive, hSlack⟩
  refine ⟨f, hfActive, ?_⟩
  let choice : X → C := fun x => (f.symm x).1
  have hchoice : ∀ x : X, choice x ∈ I.active x := by
    intro x
    have h := hfActive (f.symm x)
    rw [f.apply_symm_apply] at h
    simpa [choice] using h
  have hdegree :
      ∀ c : C, Incidence.choiceDegree choice c = M.val c (Fin.last 2) :=
    fun c => M.choiceDegree_of_bijective_token_matching (Fin.last 2) f c
  change (M.eraseLastCountMatrix choice hchoice hdegree).HallCuts
  exact M.eraseLastCountMatrix_hallCuts_two_of_singleton_cutCap_slack
    choice hchoice hdegree hSlack

theorem eraseLastHallCuts_two_of_singleton_cutSlack_selection
    {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence 3 X C) (M : CountMatrix I)
    (hHall : M.HallCuts)
    (hSelect :
      ∃ f : (Sigma fun c : C => Fin (M.val c (Fin.last 2))) ≃ X,
        (∀ q : Sigma fun c : C => Fin (M.val c (Fin.last 2)),
            q.1 ∈ I.active (f q)) ∧
          let choice : X → C := fun x => (f.symm x).1
          ∀ U : Finset C, ∀ σ : Fin 2,
            Incidence.choiceLowHitCount I choice U
                ({σ} : Finset (Fin 2))
              ≤ M.cutSlack U
                  (({σ} : Finset (Fin 2)).image
                    (Fin.castSucc : Fin 2 → Fin 3))) :
    ∃ f : (Sigma fun c : C => Fin (M.val c (Fin.last 2))) ≃ X,
      ∃ hfActive :
        ∀ q : Sigma fun c : C => Fin (M.val c (Fin.last 2)),
          q.1 ∈ I.active (f q),
        let choice : X → C := fun x => (f.symm x).1
        let hchoice : ∀ x : X, choice x ∈ I.active x := by
          intro x
          have h := hfActive (f.symm x)
          rw [f.apply_symm_apply] at h
          simpa [choice] using h
        let hdegree :
            ∀ c : C,
              Incidence.choiceDegree choice c = M.val c (Fin.last 2) :=
          fun c => M.choiceDegree_of_bijective_token_matching
            (Fin.last 2) f c
        (M.eraseLastCountMatrix choice hchoice hdegree).HallCuts := by
  classical
  have hSelectAdd :
      ∃ f : (Sigma fun c : C => Fin (M.val c (Fin.last 2))) ≃ X,
        (∀ q : Sigma fun c : C => Fin (M.val c (Fin.last 2)),
            q.1 ∈ I.active (f q)) ∧
          let choice : X → C := fun x => (f.symm x).1
          ∀ U : Finset C, ∀ σ : Fin 2,
            M.cutMass U
                (({σ} : Finset (Fin 2)).image
                  (Fin.castSucc : Fin 2 → Fin 3))
              + Incidence.choiceLowHitCount I choice U
                  ({σ} : Finset (Fin 2))
                ≤ I.cutCap U
                    (({σ} : Finset (Fin 2)).image
                      (Fin.castSucc : Fin 2 → Fin 3)) := by
    rcases hSelect with ⟨f, hfActive, hSlack⟩
    refine ⟨f, hfActive, ?_⟩
    dsimp only
    intro U σ
    let S : Finset (Fin 3) :=
      ({σ} : Finset (Fin 2)).image (Fin.castSucc : Fin 2 → Fin 3)
    have hHallUS : M.cutMass U S ≤ I.cutCap U S := hHall U S
    exact
      ((M.cutMass_add_le_iff_le_cutSlack U S hHallUS
        (Incidence.choiceLowHitCount I (fun x : X => (f.symm x).1)
          U ({σ} : Finset (Fin 2)))).2 (hSlack U σ))
  exact M.eraseLastHallCuts_two_of_singleton_selection I hHall hSelectAdd

theorem eraseLastCountMatrix_hallCuts_of_cutSlack
    {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence (T + 1) X C} (M : CountMatrix I)
    (choice : X → C) (hchoice : ∀ x : X, choice x ∈ I.active x)
    (hdegree :
      ∀ c : C, Incidence.choiceDegree choice c = M.val c (Fin.last T))
    (hHall : M.HallCuts)
    (hSlack :
      ∀ U : Finset C, ∀ S : Finset (Fin T),
        Incidence.choiceLowHitCount I choice U S
          ≤ M.cutSlack U (S.image (Fin.castSucc : Fin T → Fin (T + 1)))) :
    (M.eraseLastCountMatrix choice hchoice hdegree).HallCuts := by
  classical
  apply M.eraseLastCountMatrix_hallCuts_of_cutCap_slack choice hchoice hdegree
  intro U S
  have hHallUS :
      M.cutMass U (S.image (Fin.castSucc : Fin T → Fin (T + 1))) ≤
        I.cutCap U (S.image (Fin.castSucc : Fin T → Fin (T + 1))) :=
    hHall U (S.image (Fin.castSucc : Fin T → Fin (T + 1)))
  exact ((M.cutMass_add_le_iff_le_cutSlack U
    (S.image (Fin.castSucc : Fin T → Fin (T + 1))) hHallUS
    (Incidence.choiceLowHitCount I choice U S)).2 (hSlack U S))

theorem rowCompatible_of_hasResidues {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I)
    {R : ResidueSpec m T C} (hres : M.HasResidues R) :
    R.RowCompatible I := by
  intro c
  calc
    (I.colorDegree c : ZMod m)
        = ((∑ σ : Fin T, M.val c σ : Nat) : ZMod m) := by
            rw [M.row_sum c]
    _ = ∑ σ : Fin T, (M.val c σ : ZMod m) := by
            simp
    _ = ∑ σ : Fin T, R.target c σ := by
            apply Finset.sum_congr rfl
            intro σ _hσ
            exact hres c σ

theorem colCompatible_of_hasResidues {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I)
    {R : ResidueSpec m T C} (hres : M.HasResidues R) :
    R.ColCompatible I := by
  intro σ
  calc
    (Fintype.card X : ZMod m)
        = ((∑ c : C, M.val c σ : Nat) : ZMod m) := by
            rw [M.col_sum σ]
    _ = ∑ c : C, (M.val c σ : ZMod m) := by
            simp
    _ = ∑ c : C, R.target c σ := by
            apply Finset.sum_congr rfl
            intro c _hc
            exact hres c σ

end CountMatrix

def FeasibleWithResidues {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (R : ResidueSpec m T C) : Prop :=
  ∃ M : CountMatrix I, M.HallCuts ∧ M.HasResidues R

namespace FeasibleWithResidues

theorem rowCompatible {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C}
    (hFeasible : FeasibleWithResidues I R) :
    R.RowCompatible I := by
  rcases hFeasible with ⟨M, _hHall, hResidues⟩
  exact M.rowCompatible_of_hasResidues hResidues

theorem colCompatible {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C}
    (hFeasible : FeasibleWithResidues I R) :
    R.ColCompatible I := by
  rcases hFeasible with ⟨M, _hHall, hResidues⟩
  exact M.colCompatible_of_hasResidues hResidues

theorem compatible {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C}
    (hFeasible : FeasibleWithResidues I R) :
    R.RowCompatible I ∧ R.ColCompatible I :=
  ⟨hFeasible.rowCompatible, hFeasible.colCompatible⟩

end FeasibleWithResidues

/-- A symboling assigns each active set bijectively to the `T` active symbols. -/
structure Symboling {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq C]
    (I : Incidence T X C) where
  equiv : ∀ x : X, Fin T ≃ {c : C // c ∈ I.active x}

namespace Symboling

noncomputable def ofIncidence {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq C]
    (I : Incidence T X C) : Symboling I where
  equiv := fun x =>
    Fintype.equivOfCardEq (by
      rw [Fintype.card_fin, Fintype.card_subtype]
      simpa using (I.active_card x).symm)

theorem exists_of_incidence {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq C]
    (I : Incidence T X C) : ∃ _ : Symboling I, True :=
  ⟨ofIncidence I, trivial⟩

def color {T : Nat} {X C : Type*} [Fintype X] [Fintype C]
    [DecidableEq C] {I : Incidence T X C} (Φ : Symboling I)
    (x : X) (σ : Fin T) : C :=
  (Φ.equiv x σ).1

theorem color_mem_active {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    (x : X) (σ : Fin T) :
    Φ.color x σ ∈ I.active x :=
  (Φ.equiv x σ).2

/--
Swap two active symbols at one base vertex.

This is the local move used by the v7.5 coactive-site reservoir proof: it
changes only one local bijection `Fin T ≃ I.active x` and preserves every
other active-set bijection verbatim.
-/
noncomputable def swapAt {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    (x₀ : X) (σ τ : Fin T) : Symboling I where
  equiv := fun x =>
    if h : x = x₀ then by
      subst x
      exact (Equiv.swap σ τ).trans (Φ.equiv x₀)
    else
      Φ.equiv x

@[simp] theorem swapAt_color_self {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    (x₀ : X) (σ τ ρ : Fin T) :
    (Φ.swapAt x₀ σ τ).color x₀ ρ =
      Φ.color x₀ ((Equiv.swap σ τ) ρ) := by
  simp [swapAt, color]

@[simp] theorem swapAt_color_ne {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    {x₀ x : X} (h : x ≠ x₀) (σ τ ρ : Fin T) :
    (Φ.swapAt x₀ σ τ).color x ρ = Φ.color x ρ := by
  simp [swapAt, color, h]

@[simp] theorem swapAt_color_left {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    (x₀ : X) (σ τ : Fin T) :
    (Φ.swapAt x₀ σ τ).color x₀ σ = Φ.color x₀ τ := by
  simp

@[simp] theorem swapAt_color_right {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    (x₀ : X) (σ τ : Fin T) :
    (Φ.swapAt x₀ σ τ).color x₀ τ = Φ.color x₀ σ := by
  simp

noncomputable def permuteAt {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    (x₀ : X) (π : Equiv.Perm (Fin T)) : Symboling I where
  equiv := fun x =>
    if h : x = x₀ then by
      subst x
      exact π.trans (Φ.equiv x₀)
    else
      Φ.equiv x

@[simp] theorem permuteAt_color_self {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    (x₀ : X) (π : Equiv.Perm (Fin T)) (ρ : Fin T) :
    (Φ.permuteAt x₀ π).color x₀ ρ = Φ.color x₀ (π ρ) := by
  simp [permuteAt, color]

@[simp] theorem permuteAt_color_ne {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    {x₀ x : X} (h : x ≠ x₀) (π : Equiv.Perm (Fin T)) (ρ : Fin T) :
    (Φ.permuteAt x₀ π).color x ρ = Φ.color x ρ := by
  simp [permuteAt, color, h]

def count {T : Nat} {X C : Type*} [Fintype X] [Fintype C]
    [DecidableEq X] [DecidableEq C] {I : Incidence T X C}
    (Φ : Symboling I) (c : C) (σ : Fin T) : Nat :=
  ∑ x : X, if Φ.color x σ = c then 1 else 0

theorem swapAt_count_of_ne {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    (x₀ : X) (σ τ ρ : Fin T) (c : C)
    (hρσ : ρ ≠ σ) (hρτ : ρ ≠ τ) :
    (Φ.swapAt x₀ σ τ).count c ρ = Φ.count c ρ := by
  classical
  unfold count
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases hx : x = x₀
  · subst x
    have hswap : (Equiv.swap σ τ) ρ = ρ :=
      Equiv.swap_apply_of_ne_of_ne hρσ hρτ
    simp [hswap]
  · simp [swapAt_color_ne Φ hx σ τ ρ]

theorem swapAt_count_zmod {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    (x₀ : X) (σ τ ρ : Fin T) (c : C) :
    ((Φ.swapAt x₀ σ τ).count c ρ : ZMod m) =
      (Φ.count c ρ : ZMod m)
        - (if Φ.color x₀ ρ = c then 1 else 0)
        + (if Φ.color x₀ ((Equiv.swap σ τ) ρ) = c then 1 else 0) := by
  classical
  unfold count
  let f : X → Nat := fun x => if Φ.color x ρ = c then 1 else 0
  let g : X → Nat :=
    fun x => if (Φ.swapAt x₀ σ τ).color x ρ = c then 1 else 0
  have hfg :
      ∀ x : X, x ∈ ((Finset.univ : Finset X).erase x₀) → g x = f x := by
    intro x hx
    exact by
      have hxne : x ≠ x₀ := Finset.ne_of_mem_erase hx
      simp [f, g, swapAt_color_ne Φ hxne σ τ ρ]
  have hsum_erase :
      ((Finset.univ : Finset X).erase x₀).sum g =
        ((Finset.univ : Finset X).erase x₀).sum f := by
    apply Finset.sum_congr rfl
    intro x hx
    exact hfg x hx
  rw [show
      (∑ x : X,
        if (Φ.swapAt x₀ σ τ).color x ρ = c then 1 else 0) =
        ∑ x : X, g x by rfl]
  rw [show
      (∑ x : X, if Φ.color x ρ = c then 1 else 0) =
        ∑ x : X, f x by rfl]
  rw [← Finset.sum_erase_add (Finset.univ : Finset X) g (Finset.mem_univ x₀),
    hsum_erase,
    ← Finset.sum_erase_add (Finset.univ : Finset X) f (Finset.mem_univ x₀)]
  simp [f, g, add_comm]

theorem swapAt_count_left_zmod {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    (x₀ : X) (σ τ : Fin T) (c : C) :
    ((Φ.swapAt x₀ σ τ).count c σ : ZMod m) =
      (Φ.count c σ : ZMod m)
        - (if Φ.color x₀ σ = c then 1 else 0)
        + (if Φ.color x₀ τ = c then 1 else 0) := by
  simpa using
    (Φ.swapAt_count_zmod (m := m) x₀ σ τ σ c)

theorem swapAt_count_right_zmod {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    (x₀ : X) (σ τ : Fin T) (c : C) :
    ((Φ.swapAt x₀ σ τ).count c τ : ZMod m) =
      (Φ.count c τ : ZMod m)
        - (if Φ.color x₀ τ = c then 1 else 0)
        + (if Φ.color x₀ σ = c then 1 else 0) := by
  simpa [add_comm] using
    (Φ.swapAt_count_zmod (m := m) x₀ σ τ τ c)

theorem permuteAt_count_zmod {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    (x₀ : X) (π : Equiv.Perm (Fin T)) (ρ : Fin T) (c : C) :
    ((Φ.permuteAt x₀ π).count c ρ : ZMod m) =
      (Φ.count c ρ : ZMod m)
        - (if Φ.color x₀ ρ = c then 1 else 0)
        + (if Φ.color x₀ (π ρ) = c then 1 else 0) := by
  classical
  unfold count
  let f : X → Nat := fun x => if Φ.color x ρ = c then 1 else 0
  let g : X → Nat :=
    fun x => if (Φ.permuteAt x₀ π).color x ρ = c then 1 else 0
  have hfg :
      ∀ x : X, x ∈ ((Finset.univ : Finset X).erase x₀) → g x = f x := by
    intro x hx
    exact by
      have hxne : x ≠ x₀ := Finset.ne_of_mem_erase hx
      simp [f, g, permuteAt_color_ne Φ hxne π ρ]
  have hsum_erase :
      ((Finset.univ : Finset X).erase x₀).sum g =
        ((Finset.univ : Finset X).erase x₀).sum f := by
    apply Finset.sum_congr rfl
    intro x hx
    exact hfg x hx
  rw [show
      (∑ x : X,
        if (Φ.permuteAt x₀ π).color x ρ = c then 1 else 0) =
        ∑ x : X, g x by rfl]
  rw [show
      (∑ x : X, if Φ.color x ρ = c then 1 else 0) =
        ∑ x : X, f x by rfl]
  rw [← Finset.sum_erase_add (Finset.univ : Finset X) g (Finset.mem_univ x₀),
    hsum_erase,
    ← Finset.sum_erase_add (Finset.univ : Finset X) f (Finset.mem_univ x₀)]
  simp [f, g, add_comm]

noncomputable def swapResidueSpec {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    (R : ResidueSpec m T C) (x₀ : X) (σ τ : Fin T) :
    ResidueSpec m T C where
  target := fun c ρ =>
    R.target c ρ
      - (if Φ.color x₀ ρ = c then 1 else 0)
      + (if Φ.color x₀ ((Equiv.swap σ τ) ρ) = c then 1 else 0)

@[simp] theorem swapResidueSpec_target {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    (R : ResidueSpec m T C) (x₀ : X) (σ τ ρ : Fin T) (c : C) :
    (Φ.swapResidueSpec R x₀ σ τ).target c ρ =
      R.target c ρ
        - (if Φ.color x₀ ρ = c then 1 else 0)
        + (if Φ.color x₀ ((Equiv.swap σ τ) ρ) = c then 1 else 0) := by
  rfl

/--
Rank-one residue delta for one local symbol trade.

If the symbols `σ` and `τ` are swapped at one active vertex, the color currently
at `σ` loses one count in column `σ` and gains one in column `τ`, while the
color currently at `τ` makes the opposite move.  This is the Lean form of the
local symbol-trade lemma used by the v7.6 residue scheduling proof.
-/
theorem swapResidueSpec_target_eq_add_localTradeDelta {m T : Nat}
    {X C : Type*} [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    (R : ResidueSpec m T C) (x₀ : X) {σ τ ρ : Fin T} (hστ : σ ≠ τ)
    (c : C) :
    (Φ.swapResidueSpec R x₀ σ τ).target c ρ =
      R.target c ρ
        + (if Φ.color x₀ σ = c then
            (if ρ = τ then (1 : ZMod m)
             else if ρ = σ then -1 else 0)
          else 0)
        + (if Φ.color x₀ τ = c then
            (if ρ = σ then (1 : ZMod m)
             else if ρ = τ then -1 else 0)
          else 0) := by
  by_cases hρσ : ρ = σ
  · subst ρ
    by_cases hσc : Φ.color x₀ σ = c
    · by_cases hτc : Φ.color x₀ τ = c
      · simp [hστ, hσc, hτc, sub_eq_add_neg]
      · simp [hστ, hσc, hτc, sub_eq_add_neg]
    · by_cases hτc : Φ.color x₀ τ = c
      · simp [hσc, hτc, sub_eq_add_neg]
      · simp [hσc, hτc, sub_eq_add_neg]
  · by_cases hρτ : ρ = τ
    · subst ρ
      by_cases hσc : Φ.color x₀ σ = c
      · by_cases hτc : Φ.color x₀ τ = c
        · simp [hρσ, hσc, hτc, sub_eq_add_neg]
        · simp [hσc, hτc, sub_eq_add_neg]
      · by_cases hτc : Φ.color x₀ τ = c
        · simp [hρσ, hσc, hτc, sub_eq_add_neg]
        · simp [hσc, hτc, sub_eq_add_neg]
    · have hswap : (Equiv.swap σ τ) ρ = ρ :=
        Equiv.swap_apply_of_ne_of_ne hρσ hρτ
      simp [hρσ, hρτ, hswap]

theorem swapResidueSpec_target_eq_add_zeroTradeDelta {m T : Nat}
    [NeZero T] {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    (R : ResidueSpec m T C) (x₀ : X) {τ ρ : Fin T} (hτ : τ ≠ 0)
    {c₀ β : C} (hc₀ : Φ.color x₀ 0 = c₀) (hβ : Φ.color x₀ τ = β)
    (c : C) :
    (Φ.swapResidueSpec R x₀ 0 τ).target c ρ =
      R.target c ρ
        + (if c₀ = c then
            (if ρ = τ then (1 : ZMod m)
             else if ρ = 0 then -1 else 0)
          else 0)
        + (if β = c then
            (if ρ = 0 then (1 : ZMod m)
             else if ρ = τ then -1 else 0)
          else 0) := by
  have h0τ : (0 : Fin T) ≠ τ := by
    intro h
    exact hτ h.symm
  simpa [hc₀, hβ] using
    (Φ.swapResidueSpec_target_eq_add_localTradeDelta R x₀
      (σ := (0 : Fin T)) (τ := τ) (ρ := ρ) h0τ c)

theorem swapResidueSpec_rowCompatible {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    {R : ResidueSpec m T C} {x₀ : X} {σ τ : Fin T}
    (hRow : R.RowCompatible I) :
    (Φ.swapResidueSpec R x₀ σ τ).RowCompatible I := by
  intro c
  rw [hRow c]
  symm
  have hperm :
      (∑ ρ : Fin T,
        (if Φ.color x₀ ((Equiv.swap σ τ) ρ) = c then (1 : ZMod m) else 0)) =
        ∑ ρ : Fin T,
          (if Φ.color x₀ ρ = c then (1 : ZMod m) else 0) := by
    simpa using
      (Equiv.sum_comp (Equiv.swap σ τ)
        (fun ρ : Fin T =>
          if Φ.color x₀ ρ = c then (1 : ZMod m) else 0))
  calc
    (∑ ρ : Fin T, (Φ.swapResidueSpec R x₀ σ τ).target c ρ)
        = ∑ ρ : Fin T,
            (R.target c ρ
              - (if Φ.color x₀ ρ = c then (1 : ZMod m) else 0)
              + (if Φ.color x₀ ((Equiv.swap σ τ) ρ) = c then 1 else 0)) := by
            rfl
    _ = (∑ ρ : Fin T, R.target c ρ)
          - (∑ ρ : Fin T,
              if Φ.color x₀ ρ = c then (1 : ZMod m) else 0)
          + (∑ ρ : Fin T,
              if Φ.color x₀ ((Equiv.swap σ τ) ρ) = c then
                (1 : ZMod m)
              else 0) := by
            simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = ∑ ρ : Fin T, R.target c ρ := by
            rw [hperm]
            abel

theorem swapResidueSpec_colCompatible {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    {R : ResidueSpec m T C} {x₀ : X} {σ τ : Fin T}
    (hCol : R.ColCompatible I) :
    (Φ.swapResidueSpec R x₀ σ τ).ColCompatible I := by
  intro ρ
  rw [hCol ρ]
  symm
  have hOld :
      (∑ c : C, if Φ.color x₀ ρ = c then (1 : ZMod m) else 0) = 1 := by
    simp
  have hNew :
      (∑ c : C,
        if Φ.color x₀ ((Equiv.swap σ τ) ρ) = c then
          (1 : ZMod m)
        else 0) = 1 := by
    simp
  calc
    (∑ c : C, (Φ.swapResidueSpec R x₀ σ τ).target c ρ)
        = ∑ c : C,
            (R.target c ρ
              - (if Φ.color x₀ ρ = c then (1 : ZMod m) else 0)
              + (if Φ.color x₀ ((Equiv.swap σ τ) ρ) = c then 1 else 0)) := by
            rfl
    _ = (∑ c : C, R.target c ρ)
          - (∑ c : C,
              if Φ.color x₀ ρ = c then (1 : ZMod m) else 0)
          + (∑ c : C,
              if Φ.color x₀ ((Equiv.swap σ τ) ρ) = c then
                (1 : ZMod m)
              else 0) := by
            simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = ∑ c : C, R.target c ρ := by
            rw [hOld, hNew]
            abel

noncomputable def permuteResidueSpec {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    (R : ResidueSpec m T C) (x₀ : X) (π : Equiv.Perm (Fin T)) :
    ResidueSpec m T C where
  target := fun c ρ =>
    R.target c ρ
      - (if Φ.color x₀ ρ = c then 1 else 0)
      + (if Φ.color x₀ (π ρ) = c then 1 else 0)

@[simp] theorem permuteResidueSpec_target {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    (R : ResidueSpec m T C) (x₀ : X) (π : Equiv.Perm (Fin T))
    (ρ : Fin T) (c : C) :
    (Φ.permuteResidueSpec R x₀ π).target c ρ =
      R.target c ρ
        - (if Φ.color x₀ ρ = c then 1 else 0)
        + (if Φ.color x₀ (π ρ) = c then 1 else 0) := by
  rfl

theorem permuteResidueSpec_rowCompatible {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    {R : ResidueSpec m T C} {x₀ : X} {π : Equiv.Perm (Fin T)}
    (hRow : R.RowCompatible I) :
    (Φ.permuteResidueSpec R x₀ π).RowCompatible I := by
  intro c
  rw [hRow c]
  symm
  have hperm :
      (∑ ρ : Fin T,
        (if Φ.color x₀ (π ρ) = c then (1 : ZMod m) else 0)) =
        ∑ ρ : Fin T,
          (if Φ.color x₀ ρ = c then (1 : ZMod m) else 0) := by
    simpa using
      (Equiv.sum_comp π
        (fun ρ : Fin T =>
          if Φ.color x₀ ρ = c then (1 : ZMod m) else 0))
  calc
    (∑ ρ : Fin T, (Φ.permuteResidueSpec R x₀ π).target c ρ)
        = ∑ ρ : Fin T,
            (R.target c ρ
              - (if Φ.color x₀ ρ = c then (1 : ZMod m) else 0)
              + (if Φ.color x₀ (π ρ) = c then 1 else 0)) := by
            rfl
    _ = (∑ ρ : Fin T, R.target c ρ)
          - (∑ ρ : Fin T,
              if Φ.color x₀ ρ = c then (1 : ZMod m) else 0)
          + (∑ ρ : Fin T,
              if Φ.color x₀ (π ρ) = c then (1 : ZMod m) else 0) := by
            simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = ∑ ρ : Fin T, R.target c ρ := by
            rw [hperm]
            abel

theorem permuteResidueSpec_colCompatible {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    {R : ResidueSpec m T C} {x₀ : X} {π : Equiv.Perm (Fin T)}
    (hCol : R.ColCompatible I) :
    (Φ.permuteResidueSpec R x₀ π).ColCompatible I := by
  intro ρ
  rw [hCol ρ]
  symm
  have hOld :
      (∑ c : C, if Φ.color x₀ ρ = c then (1 : ZMod m) else 0) = 1 := by
    simp
  have hNew :
      (∑ c : C,
        if Φ.color x₀ (π ρ) = c then (1 : ZMod m) else 0) = 1 := by
    simp
  calc
    (∑ c : C, (Φ.permuteResidueSpec R x₀ π).target c ρ)
        = ∑ c : C,
            (R.target c ρ
              - (if Φ.color x₀ ρ = c then (1 : ZMod m) else 0)
              + (if Φ.color x₀ (π ρ) = c then 1 else 0)) := by
            rfl
    _ = (∑ c : C, R.target c ρ)
          - (∑ c : C,
              if Φ.color x₀ ρ = c then (1 : ZMod m) else 0)
          + (∑ c : C,
              if Φ.color x₀ (π ρ) = c then (1 : ZMod m) else 0) := by
            simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = ∑ c : C, R.target c ρ := by
            rw [hOld, hNew]
            abel

theorem count_eq_choiceDegree {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I) (c : C) (σ : Fin T) :
    Φ.count c σ = Incidence.choiceDegree (fun x : X => Φ.color x σ) c := by
  classical
  unfold count Incidence.choiceDegree
  rw [Finset.card_filter]

def symbolsIn {T : Nat} {X C : Type*} [Fintype X] [Fintype C]
    [DecidableEq C] {I : Incidence T X C}
    (Φ : Symboling I) (x : X) (U : Finset C) (S : Finset (Fin T)) :
    Finset (Fin T) :=
  S.filter (fun σ => Φ.color x σ ∈ U)

theorem sum_color_eq_indicator {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    (x : X) (c : C) :
    (∑ σ : Fin T, if Φ.color x σ = c then (1 : Nat) else 0)
      = if c ∈ I.active x then 1 else 0 := by
  classical
  by_cases hc : c ∈ I.active x
  · let σ0 : Fin T := (Φ.equiv x).symm ⟨c, hc⟩
    have hσ0 : Φ.color x σ0 = c := by
      exact congrArg Subtype.val ((Φ.equiv x).apply_symm_apply ⟨c, hc⟩)
    rw [Finset.sum_eq_single σ0]
    · simp [hσ0, hc]
    · intro σ _hσ hne
      have hneq : Φ.color x σ ≠ c := by
        intro hcol
        have hsub : Φ.equiv x σ = ⟨c, hc⟩ := by
          exact Subtype.ext hcol
        have hσeq : σ = σ0 := by
          simpa [σ0] using congrArg (Φ.equiv x).symm hsub
        exact hne hσeq
      simp [hneq]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ σ0))
  · have hneq : ∀ σ : Fin T, Φ.color x σ ≠ c := by
      intro σ hcol
      have hmem : Φ.color x σ ∈ I.active x := (Φ.equiv x σ).2
      exact hc (by
        rw [← hcol]
        exact hmem)
    simp [hc, hneq]

theorem sum_color_column_eq_one {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    (x : X) (σ : Fin T) :
    (∑ c : C, if Φ.color x σ = c then (1 : Nat) else 0) = 1 := by
  classical
  rw [Finset.sum_eq_single (Φ.color x σ)]
  · simp
  · intro c _hc hne
    have hneq : Φ.color x σ ≠ c := by
      intro h
      exact hne h.symm
    simp [hneq]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ (Φ.color x σ)))

theorem count_row_sum {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I) :
    ∀ c : C, (∑ σ : Fin T, Φ.count c σ) = I.colorDegree c := by
  classical
  intro c
  calc
    (∑ σ : Fin T, Φ.count c σ)
        = ∑ σ : Fin T, ∑ x : X,
            if Φ.color x σ = c then (1 : Nat) else 0 := by
            simp [count]
    _ = ∑ x : X, ∑ σ : Fin T,
            if Φ.color x σ = c then (1 : Nat) else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ x : X, if c ∈ I.active x then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro x _hx
            exact Φ.sum_color_eq_indicator x c
    _ = I.colorDegree c := by
            rw [Incidence.colorDegree, Finset.card_filter]

theorem count_col_sum {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I) :
    ∀ σ : Fin T, (∑ c : C, Φ.count c σ) = Fintype.card X := by
  classical
  intro σ
  calc
    (∑ c : C, Φ.count c σ)
        = ∑ c : C, ∑ x : X,
            if Φ.color x σ = c then (1 : Nat) else 0 := by
            simp [count]
    _ = ∑ x : X, ∑ c : C,
            if Φ.color x σ = c then (1 : Nat) else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ _x : X, 1 := by
            apply Finset.sum_congr rfl
            intro x _hx
            exact Φ.sum_color_column_eq_one x σ
    _ = Fintype.card X := by
            simp

theorem local_cut_count_eq_symbolsIn_card {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    (x : X) (U : Finset C) (S : Finset (Fin T)) :
    (∑ c ∈ U, ∑ σ ∈ S,
        if Φ.color x σ = c then (1 : Nat) else 0)
      = (Φ.symbolsIn x U S).card := by
  classical
  calc
    (∑ c ∈ U, ∑ σ ∈ S,
        if Φ.color x σ = c then (1 : Nat) else 0)
        = ∑ σ ∈ S, ∑ c ∈ U,
            if Φ.color x σ = c then (1 : Nat) else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ σ ∈ S, if Φ.color x σ ∈ U then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro σ _hσ
            by_cases hmem : Φ.color x σ ∈ U
            · rw [Finset.sum_eq_single (Φ.color x σ)]
              · simp [hmem]
              · intro c _hc hne
                have hneq : Φ.color x σ ≠ c := by
                  intro h
                  exact hne h.symm
                simp [hneq]
              · intro hnot
                exact False.elim (hnot hmem)
            · have hneq : ∀ c ∈ U, Φ.color x σ ≠ c := by
                intro c hc h
                exact hmem (by rw [h]; exact hc)
              simp [hmem]
    _ = (Φ.symbolsIn x U S).card := by
            rw [symbolsIn]
            exact (Finset.card_filter (fun σ => Φ.color x σ ∈ U) S).symm

theorem symbolsIn_card_le_S {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    (x : X) (U : Finset C) (S : Finset (Fin T)) :
    (Φ.symbolsIn x U S).card ≤ S.card :=
  Finset.card_filter_le S (fun σ => Φ.color x σ ∈ U)

theorem symbolsIn_card_le_active_inter {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    (x : X) (U : Finset C) (S : Finset (Fin T)) :
    (Φ.symbolsIn x U S).card ≤ (I.active x ∩ U).card := by
  classical
  let imageSet : Finset C := (Φ.symbolsIn x U S).image (Φ.color x)
  have hcardImage :
      imageSet.card = (Φ.symbolsIn x U S).card := by
    apply Finset.card_image_of_injOn
    intro σ hσ τ hτ hcolor
    have hsub : Φ.equiv x σ = Φ.equiv x τ := by
      exact Subtype.ext hcolor
    exact (Φ.equiv x).injective hsub
  have hsubset : imageSet ⊆ I.active x ∩ U := by
    intro c hc
    rcases Finset.mem_image.mp hc with ⟨σ, hσ, rfl⟩
    have hactive : Φ.color x σ ∈ I.active x := (Φ.equiv x σ).2
    have hU : Φ.color x σ ∈ U := by
      exact (Finset.mem_filter.mp hσ).2
    exact Finset.mem_inter.mpr ⟨hactive, hU⟩
  calc
    (Φ.symbolsIn x U S).card = imageSet.card := hcardImage.symm
    _ ≤ (I.active x ∩ U).card := Finset.card_le_card hsubset

theorem local_cut_count_le_cap {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    (x : X) (U : Finset C) (S : Finset (Fin T)) :
    (∑ c ∈ U, ∑ σ ∈ S,
        if Φ.color x σ = c then (1 : Nat) else 0)
      ≤ min ((I.active x ∩ U).card) S.card := by
  rw [Φ.local_cut_count_eq_symbolsIn_card x U S]
  exact le_min (Φ.symbolsIn_card_le_active_inter x U S)
    (Φ.symbolsIn_card_le_S x U S)

theorem local_castSucc_cut_count_add_last_low_indicator_le_cap
    {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq C]
    {I : Incidence (T + 1) X C} (Φ : Symboling I)
    (x : X) (U : Finset C) (S : Finset (Fin T)) :
    (∑ c ∈ U,
        ∑ σ ∈ S.image (Fin.castSucc : Fin T → Fin (T + 1)),
          if Φ.color x σ = c then (1 : Nat) else 0)
      + (if Φ.color x (Fin.last T) ∈ U ∧
            (I.active x ∩ U).card ≤ S.card then 1 else 0)
      ≤ min ((I.active x ∩ U).card) S.card := by
  classical
  let S' : Finset (Fin (T + 1)) :=
    S.image (Fin.castSucc : Fin T → Fin (T + 1))
  let lower := (Φ.symbolsIn x U S').card
  let a := (I.active x ∩ U).card
  let s := S.card
  have hcount :
      (∑ c ∈ U, ∑ σ ∈ S',
          if Φ.color x σ = c then (1 : Nat) else 0) = lower := by
    simpa [lower] using Φ.local_cut_count_eq_symbolsIn_card x U S'
  have hlowerA : lower ≤ a := by
    simpa [lower, a] using Φ.symbolsIn_card_le_active_inter x U S'
  have hlowerS : lower ≤ s := by
    have h := Φ.symbolsIn_card_le_S x U S'
    have hS' : S'.card = s := by
      simp [S', s, Incidence.card_image_castSucc]
    simpa [lower, hS'] using h
  have hlastNot : Fin.last T ∉ S' := by
    simp [S', Incidence.last_notMem_image_castSucc S]
  have hinsertA :
      (Φ.symbolsIn x U (insert (Fin.last T) S')).card ≤ a := by
    simpa [a] using
      Φ.symbolsIn_card_le_active_inter x U (insert (Fin.last T) S')
  have hlastInsert :
      Φ.color x (Fin.last T) ∈ U →
        lower + 1 ≤ a := by
    intro hlastU
    have hcard :
        (Φ.symbolsIn x U (insert (Fin.last T) S')).card = lower + 1 := by
      have hfilter :
          (insert (Fin.last T) S').filter
              (fun σ => Φ.color x σ ∈ U)
            =
          insert (Fin.last T)
            (S'.filter (fun σ => Φ.color x σ ∈ U)) := by
        ext σ
        by_cases hσ : σ = Fin.last T <;> simp [hσ, hlastU]
      rw [symbolsIn, hfilter]
      rw [Finset.card_insert_of_notMem]
      · simp [lower, symbolsIn]
      · intro hmem
        exact hlastNot (Finset.mem_filter.mp hmem).1
    omega
  rw [hcount]
  by_cases hlastU : Φ.color x (Fin.last T) ∈ U
  · by_cases hle : a ≤ s
    · have hlow : lower + 1 ≤ a := hlastInsert hlastU
      change lower +
          (if Φ.color x (Fin.last T) ∈ U ∧ a ≤ s then 1 else 0)
        ≤ min a s
      rw [if_pos ⟨hlastU, hle⟩, min_eq_left hle]
      exact hlow
    · have hslea : s ≤ a := Nat.le_of_not_ge hle
      change lower +
          (if Φ.color x (Fin.last T) ∈ U ∧ a ≤ s then 1 else 0)
        ≤ min a s
      rw [if_neg (by intro h; exact hle h.2), min_eq_right hslea]
      exact hlowerS
  · change lower +
        (if Φ.color x (Fin.last T) ∈ U ∧ a ≤ s then 1 else 0)
      ≤ min a s
    rw [if_neg (by intro h; exact hlastU h.1)]
    exact le_min hlowerA hlowerS

def toCountMatrix {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I) : CountMatrix I where
  val := Φ.count
  row_sum := Φ.count_row_sum
  col_sum := Φ.count_col_sum

def Realizes {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I) (M : C → Fin T → Nat) : Prop :=
  ∀ c σ, Φ.count c σ = M c σ

def toColumnFilling {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I) (M : CountMatrix I)
    (hReal : Φ.Realizes M.val) : M.ColumnFilling where
  color := Φ.color
  active := fun x σ => Φ.color_mem_active x σ
  count_eq := by
    intro c σ
    rw [← Φ.count_eq_choiceDegree c σ, hReal c σ]

def HasResidues {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    (R : ResidueSpec m T C) : Prop :=
  ∀ c σ, (Φ.count c σ : ZMod m) = R.target c σ

def residueSpec {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I) :
    ResidueSpec m T C where
  target := fun c σ => (Φ.count c σ : ZMod m)

@[simp] theorem residueSpec_target {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I) (c : C) (σ : Fin T) :
    (Φ.residueSpec (m := m)).target c σ =
      (Φ.count c σ : ZMod m) := by
  rfl

theorem hasResidues_residueSpec {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I) :
    Φ.HasResidues (Φ.residueSpec (m := m)) := by
  intro c σ
  rfl

theorem residueSpec_rowCompatible {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I) :
    (Φ.residueSpec (m := m)).RowCompatible I := by
  intro c
  change (I.colorDegree c : ZMod m) =
    ∑ σ : Fin T, (Φ.count c σ : ZMod m)
  rw [← Nat.cast_sum, Φ.count_row_sum c]

theorem residueSpec_colCompatible {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I) :
    (Φ.residueSpec (m := m)).ColCompatible I := by
  intro σ
  change (Fintype.card X : ZMod m) =
    ∑ c : C, (Φ.count c σ : ZMod m)
  rw [← Nat.cast_sum, Φ.count_col_sum σ]

theorem swapAt_hasResidues {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {Φ : Symboling I}
    {R : ResidueSpec m T C} {x₀ : X} {σ τ : Fin T}
    (hResidues : Φ.HasResidues R) :
    (Φ.swapAt x₀ σ τ).HasResidues (Φ.swapResidueSpec R x₀ σ τ) := by
  intro c ρ
  rw [Φ.swapAt_count_zmod (m := m) x₀ σ τ ρ c, hResidues c ρ]
  rfl

theorem permuteAt_hasResidues {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {Φ : Symboling I}
    {R : ResidueSpec m T C} {x₀ : X} {π : Equiv.Perm (Fin T)}
    (hResidues : Φ.HasResidues R) :
    (Φ.permuteAt x₀ π).HasResidues
      (Φ.permuteResidueSpec R x₀ π) := by
  intro c ρ
  rw [Φ.permuteAt_count_zmod (m := m) x₀ π ρ c, hResidues c ρ]
  rfl

/-- One scheduled local swap in the active-symbol trade list. -/
structure SwapMove (X : Type*) (T : Nat) where
  vertex : X
  left : Fin T
  right : Fin T

/--
One scheduled paper-style trade swapping the zero symbol with a target symbol.

The v7.6 reservoir proof only uses local trades of the form `0 ↔ τ`.
This structure records that smaller datum before it is expanded to a generic
`SwapMove`.
-/
structure ZeroSwapMove (X : Type*) (T : Nat) where
  vertex : X
  right : Fin T

structure NonzeroZeroSwapMove (X : Type*) (T : Nat) where
  vertex : X
  right : Fin T
  right_ne_zero : right.val ≠ 0

namespace ZeroSwapMove

def toSwapMove {X : Type*} {T : Nat} (hTpos : 0 < T)
    (move : ZeroSwapMove X T) : SwapMove X T where
  vertex := move.vertex
  left := ⟨0, hTpos⟩
  right := move.right

end ZeroSwapMove

namespace NonzeroZeroSwapMove

theorem right_ne_zero_fin {X : Type*} {T : Nat} [NeZero T]
    (move : NonzeroZeroSwapMove X T) : move.right ≠ 0 := by
  intro h
  have hval : move.right.val = 0 := by
    simp [h]
  exact move.right_ne_zero hval

def toZeroSwapMove {X : Type*} {T : Nat}
    (move : NonzeroZeroSwapMove X T) : ZeroSwapMove X T where
  vertex := move.vertex
  right := move.right

@[simp] theorem toZeroSwapMove_vertex {X : Type*} {T : Nat}
    (move : NonzeroZeroSwapMove X T) :
    move.toZeroSwapMove.vertex = move.vertex := rfl

@[simp] theorem toZeroSwapMove_right {X : Type*} {T : Nat}
    (move : NonzeroZeroSwapMove X T) :
    move.toZeroSwapMove.right = move.right := rfl

end NonzeroZeroSwapMove

def zeroSwapMoves {X : Type*} {T : Nat} (hTpos : 0 < T)
    (moves : List (ZeroSwapMove X T)) : List (SwapMove X T) :=
  moves.map (ZeroSwapMove.toSwapMove hTpos)

def nonzeroZeroSwapMoves {X : Type*} {T : Nat} (hTpos : 0 < T)
    (moves : List (NonzeroZeroSwapMove X T)) : List (SwapMove X T) :=
  zeroSwapMoves hTpos (moves.map NonzeroZeroSwapMove.toZeroSwapMove)

noncomputable def applySwapMoves {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I) :
    List (SwapMove X T) → Symboling I
  | [] => Φ
  | move :: moves =>
      (Φ.swapAt move.vertex move.left move.right).applySwapMoves moves

noncomputable def applySwapResidueSpecs {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    (R : ResidueSpec m T C) :
    List (SwapMove X T) → ResidueSpec m T C
  | [] => R
  | move :: moves =>
      (Φ.swapAt move.vertex move.left move.right).applySwapResidueSpecs
        (Φ.swapResidueSpec R move.vertex move.left move.right) moves

def swapMoveDelta {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    (move : SwapMove X T) (c : C) (ρ : Fin T) : ZMod m :=
  - (if Φ.color move.vertex ρ = c then 1 else 0)
    + (if Φ.color move.vertex ((Equiv.swap move.left move.right) ρ) = c then
        1
      else
        0)

def localTradeDelta {m T : Nat} {C : Type*} [DecidableEq C]
    (leftColor rightColor c : C) (left right ρ : Fin T) : ZMod m :=
  (if leftColor = c then
      (if ρ = right then (1 : ZMod m)
       else if ρ = left then -1 else 0)
    else 0)
    + (if rightColor = c then
      (if ρ = left then (1 : ZMod m)
       else if ρ = right then -1 else 0)
    else 0)

theorem swapMoveDelta_eq_localTradeDelta {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    (move : SwapMove X T) (hSymbols : move.left ≠ move.right)
    {leftColor rightColor : C}
    (hLeft : Φ.color move.vertex move.left = leftColor)
    (hRight : Φ.color move.vertex move.right = rightColor)
    (c : C) (ρ : Fin T) :
    Φ.swapMoveDelta (m := m) move c ρ =
      localTradeDelta (m := m) leftColor rightColor c
        move.left move.right ρ := by
  classical
  let R0 : ResidueSpec m T C := { target := fun _ _ => 0 }
  have h :=
    Φ.swapResidueSpec_target_eq_add_localTradeDelta
      R0 move.vertex (σ := move.left) (τ := move.right) (ρ := ρ)
      hSymbols c
  simpa [swapResidueSpec, swapMoveDelta, localTradeDelta, R0,
    hLeft, hRight, sub_eq_add_neg] using h

def swapDeltaSum {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I) :
    List (SwapMove X T) → C → Fin T → ZMod m
  | [], _, _ => 0
  | move :: moves, c, ρ =>
      Φ.swapMoveDelta move c ρ + Φ.swapDeltaSum moves c ρ

theorem swapMoveDelta_swapAt_of_vertex_ne {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    {x₀ : X} {σ τ : Fin T} {move : SwapMove X T}
    (hvertex : move.vertex ≠ x₀) (c : C) (ρ : Fin T) :
    (Φ.swapAt x₀ σ τ).swapMoveDelta (m := m) move c ρ =
      Φ.swapMoveDelta (m := m) move c ρ := by
  simp [swapMoveDelta, swapAt_color_ne Φ hvertex σ τ]

theorem swapDeltaSum_swapAt_of_forall_vertex_ne {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    {x₀ : X} {σ τ : Fin T}
    (moves : List (SwapMove X T))
    (hvertex : ∀ move, move ∈ moves → move.vertex ≠ x₀)
    (c : C) (ρ : Fin T) :
    (Φ.swapAt x₀ σ τ).swapDeltaSum (m := m) moves c ρ =
      Φ.swapDeltaSum (m := m) moves c ρ := by
  induction moves with
  | nil =>
      simp [swapDeltaSum]
  | cons move moves ih =>
      have hmove : move.vertex ≠ x₀ := hvertex move (by simp)
      have hmoves : ∀ move', move' ∈ moves → move'.vertex ≠ x₀ := by
        intro move' hmem
        exact hvertex move' (by simp [hmem])
      simp [swapDeltaSum,
        Φ.swapMoveDelta_swapAt_of_vertex_ne (m := m) hmove c ρ,
        ih hmoves]

theorem applySwapResidueSpecs_target_eq_add_swapDeltaSum_of_pairwise_vertex
    {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    {R : ResidueSpec m T C} {moves : List (SwapMove X T)}
    (hPairwise : moves.Pairwise (fun move₁ move₂ => move₁.vertex ≠ move₂.vertex))
    (c : C) (ρ : Fin T) :
    (Φ.applySwapResidueSpecs R moves).target c ρ =
      R.target c ρ + Φ.swapDeltaSum (m := m) moves c ρ := by
  induction moves generalizing Φ R with
  | nil =>
      simp [applySwapResidueSpecs, swapDeltaSum]
  | cons move moves ih =>
      rcases List.pairwise_cons.mp hPairwise with ⟨hHead, hTail⟩
      have hNoHead :
          ∀ move', move' ∈ moves → move'.vertex ≠ move.vertex := by
        intro move' hmem hEq
        exact hHead move' hmem hEq.symm
      have hTailDelta :
          (Φ.swapAt move.vertex move.left move.right).swapDeltaSum
              (m := m) moves c ρ =
            Φ.swapDeltaSum (m := m) moves c ρ :=
        Φ.swapDeltaSum_swapAt_of_forall_vertex_ne
          (m := m) moves hNoHead c ρ
      calc
        (Φ.applySwapResidueSpecs R (move :: moves)).target c ρ
            =
              (Φ.swapResidueSpec R move.vertex move.left move.right).target c ρ
                +
              (Φ.swapAt move.vertex move.left move.right).swapDeltaSum
                (m := m) moves c ρ := by
                simpa [applySwapResidueSpecs] using
                  ih (Φ := Φ.swapAt move.vertex move.left move.right)
                    (R := Φ.swapResidueSpec R move.vertex move.left move.right)
                    hTail
        _ =
              R.target c ρ + Φ.swapMoveDelta (m := m) move c ρ
                +
              (Φ.swapAt move.vertex move.left move.right).swapDeltaSum
                (m := m) moves c ρ := by
                simp [swapResidueSpec, swapMoveDelta, sub_eq_add_neg,
                  add_assoc]
        _ =
              R.target c ρ +
                (Φ.swapMoveDelta (m := m) move c ρ +
                  Φ.swapDeltaSum (m := m) moves c ρ) := by
                rw [hTailDelta]
                abel
        _ = R.target c ρ +
              Φ.swapDeltaSum (m := m) (move :: moves) c ρ := by
                rfl

theorem applySwapMoves_hasResidues {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {Φ : Symboling I}
    {R : ResidueSpec m T C} (hResidues : Φ.HasResidues R)
    (moves : List (SwapMove X T)) :
    (Φ.applySwapMoves moves).HasResidues
      (Φ.applySwapResidueSpecs R moves) := by
  induction moves generalizing Φ R with
  | nil =>
      simpa [applySwapMoves, applySwapResidueSpecs] using hResidues
  | cons move moves ih =>
      simpa [applySwapMoves, applySwapResidueSpecs] using
        ih (Φ.swapAt_hasResidues hResidues)

theorem applySwapResidueSpecs_rowCompatible {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    {R : ResidueSpec m T C} (hRow : R.RowCompatible I)
    (moves : List (SwapMove X T)) :
    (Φ.applySwapResidueSpecs R moves).RowCompatible I := by
  induction moves generalizing Φ R with
  | nil =>
      simpa [applySwapResidueSpecs] using hRow
  | cons move moves ih =>
      simpa [applySwapResidueSpecs] using
        ih (Φ := Φ.swapAt move.vertex move.left move.right)
          (R := Φ.swapResidueSpec R move.vertex move.left move.right)
          (Φ.swapResidueSpec_rowCompatible hRow)

theorem applySwapResidueSpecs_colCompatible {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I)
    {R : ResidueSpec m T C} (hCol : R.ColCompatible I)
    (moves : List (SwapMove X T)) :
    (Φ.applySwapResidueSpecs R moves).ColCompatible I := by
  induction moves generalizing Φ R with
  | nil =>
      simpa [applySwapResidueSpecs] using hCol
  | cons move moves ih =>
      simpa [applySwapResidueSpecs] using
        ih (Φ := Φ.swapAt move.vertex move.left move.right)
          (R := Φ.swapResidueSpec R move.vertex move.left move.right)
          (Φ.swapResidueSpec_colCompatible hCol)

theorem hasResidues_of_realizes {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {Φ : Symboling I} {M : CountMatrix I}
    {R : ResidueSpec m T C}
    (hreal : Φ.Realizes M.val) (hres : M.HasResidues R) :
    Φ.HasResidues R := by
  intro c σ
  rw [hreal c σ]
  exact hres c σ

theorem toCountMatrix_hallCuts {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I) :
    (Φ.toCountMatrix).HallCuts := by
  classical
  intro U S
  calc
    (Φ.toCountMatrix).cutMass U S
        = ∑ x : X, ∑ c ∈ U, ∑ σ ∈ S,
            if Φ.color x σ = c then (1 : Nat) else 0 := by
            change (∑ c ∈ U, ∑ σ ∈ S, ∑ x : X,
                if Φ.color x σ = c then (1 : Nat) else 0)
              = ∑ x : X, ∑ c ∈ U, ∑ σ ∈ S,
                if Φ.color x σ = c then (1 : Nat) else 0
            calc
              (∑ c ∈ U, ∑ σ ∈ S, ∑ x : X,
                  if Φ.color x σ = c then (1 : Nat) else 0)
                  = ∑ c ∈ U, ∑ x : X, ∑ σ ∈ S,
                      if Φ.color x σ = c then (1 : Nat) else 0 := by
                      apply Finset.sum_congr rfl
                      intro c _hc
                      rw [Finset.sum_comm]
              _ = ∑ x : X, ∑ c ∈ U, ∑ σ ∈ S,
                    if Φ.color x σ = c then (1 : Nat) else 0 := by
                    rw [Finset.sum_comm]
    _ ≤ ∑ x : X, min ((I.active x ∩ U).card) S.card := by
            apply Finset.sum_le_sum
            intro x _hx
            exact Φ.local_cut_count_le_cap x U S
    _ = I.cutCap U S := by
            rfl

theorem cutMass_eq_sum_local_of_realizes {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (Φ : Symboling I) (M : CountMatrix I)
    (hReal : Φ.Realizes M.val) (U : Finset C) (S : Finset (Fin T)) :
    M.cutMass U S =
      ∑ x : X, ∑ c ∈ U, ∑ σ ∈ S,
        if Φ.color x σ = c then (1 : Nat) else 0 := by
  classical
  calc
    M.cutMass U S
        = ∑ c ∈ U, ∑ σ ∈ S, Φ.count c σ := by
            unfold CountMatrix.cutMass
            apply Finset.sum_congr rfl
            intro c _hc
            apply Finset.sum_congr rfl
            intro σ _hσ
            exact (hReal c σ).symm
    _ = ∑ c ∈ U, ∑ σ ∈ S, ∑ x : X,
          if Φ.color x σ = c then (1 : Nat) else 0 := by
            simp [count]
    _ = ∑ c ∈ U, ∑ x : X, ∑ σ ∈ S,
          if Φ.color x σ = c then (1 : Nat) else 0 := by
            apply Finset.sum_congr rfl
            intro c _hc
            rw [Finset.sum_comm]
    _ = ∑ x : X, ∑ c ∈ U, ∑ σ ∈ S,
          if Φ.color x σ = c then (1 : Nat) else 0 := by
            rw [Finset.sum_comm]

theorem cutMass_image_castSucc_add_choiceLowHitCount_le_cutCap_of_realizes
    {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence (T + 1) X C} (Φ : Symboling I)
    (M : CountMatrix I) (hReal : Φ.Realizes M.val)
    (U : Finset C) (S : Finset (Fin T)) :
    M.cutMass U (S.image (Fin.castSucc : Fin T → Fin (T + 1)))
        + Incidence.choiceLowHitCount I
          (fun x : X => Φ.color x (Fin.last T)) U S
      ≤ I.cutCap U (S.image (Fin.castSucc : Fin T → Fin (T + 1))) := by
  classical
  rw [Φ.cutMass_eq_sum_local_of_realizes M hReal U
    (S.image (Fin.castSucc : Fin T → Fin (T + 1)))]
  unfold Incidence.choiceLowHitCount
  rw [Finset.card_filter, ← Finset.sum_add_distrib,
    Incidence.cutCap_image_castSucc]
  apply Finset.sum_le_sum
  intro x _hx
  exact Φ.local_castSucc_cut_count_add_last_low_indicator_le_cap x U S

noncomputable def extendLast {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq C]
    {I : Incidence (T + 1) X C} (choice : X → C)
    (hchoice : ∀ x : X, choice x ∈ I.active x)
    (Φ : Symboling (I.eraseChoice choice hchoice)) :
    Symboling I where
  equiv := fun x => {
    toFun := Fin.lastCases
      ⟨choice x, hchoice x⟩
      (fun σ =>
        ⟨Φ.color x σ,
          ((I.mem_eraseChoice_active choice hchoice).1
            (Φ.equiv x σ).2).1⟩)
    invFun := fun c =>
      if h : c.1 = choice x then
        Fin.last T
      else
        Fin.castSucc ((Φ.equiv x).symm
          ⟨c.1, (I.mem_eraseChoice_active choice hchoice).2 ⟨c.2, h⟩⟩)
    left_inv := by
      intro σ
      rcases Fin.eq_castSucc_or_eq_last σ with ⟨τ, rfl⟩ | rfl
      · have hne : (Φ.color x τ) ≠ choice x := by
          exact ((I.mem_eraseChoice_active choice hchoice).1
            (Φ.equiv x τ).2).2
        have hne' : ((Φ.equiv x τ).1) ≠ choice x := hne
        simp only [Fin.lastCases_castSucc]
        rw [dif_neg hne]
        simpa [Symboling.color] using (Φ.equiv x).symm_apply_apply τ
      · simp
    right_inv := by
      intro c
      by_cases h : c.1 = choice x
      · apply Subtype.ext
        simp [h]
      · apply Subtype.ext
        have hmem :
            c.1 ∈ (I.eraseChoice choice hchoice).active x :=
          (I.mem_eraseChoice_active choice hchoice).2 ⟨c.2, h⟩
        simp only [dif_neg h, Fin.lastCases_castSucc]
        simpa [Symboling.color] using congrArg Subtype.val
          ((Φ.equiv x).apply_symm_apply ⟨c.1, hmem⟩)
  }

@[simp] theorem extendLast_color_last {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq C]
    {I : Incidence (T + 1) X C} (choice : X → C)
    (hchoice : ∀ x : X, choice x ∈ I.active x)
    (Φ : Symboling (I.eraseChoice choice hchoice)) (x : X) :
    (Φ.extendLast choice hchoice).color x (Fin.last T) = choice x := by
  simp [extendLast, Symboling.color]

@[simp] theorem extendLast_color_castSucc {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq C]
    {I : Incidence (T + 1) X C} (choice : X → C)
    (hchoice : ∀ x : X, choice x ∈ I.active x)
    (Φ : Symboling (I.eraseChoice choice hchoice))
    (x : X) (σ : Fin T) :
    (Φ.extendLast choice hchoice).color x σ.castSucc = Φ.color x σ := by
  simp [extendLast, Symboling.color]

theorem extendLast_count_last {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence (T + 1) X C} (choice : X → C)
    (hchoice : ∀ x : X, choice x ∈ I.active x)
    (Φ : Symboling (I.eraseChoice choice hchoice)) (c : C) :
    (Φ.extendLast choice hchoice).count c (Fin.last T) =
      Incidence.choiceDegree choice c := by
  classical
  unfold Symboling.count Incidence.choiceDegree
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro x _hx
  simp

theorem extendLast_count_castSucc {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence (T + 1) X C} (choice : X → C)
    (hchoice : ∀ x : X, choice x ∈ I.active x)
    (Φ : Symboling (I.eraseChoice choice hchoice))
    (c : C) (σ : Fin T) :
    (Φ.extendLast choice hchoice).count c σ.castSucc = Φ.count c σ := by
  classical
  unfold Symboling.count
  apply Finset.sum_congr rfl
  intro x _hx
  simp

theorem extendLast_realizes_eraseLastCountMatrix
    {T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence (T + 1) X C} (M : CountMatrix I)
    (choice : X → C) (hchoice : ∀ x : X, choice x ∈ I.active x)
    (hdegree :
      ∀ c : C, Incidence.choiceDegree choice c = M.val c (Fin.last T))
    (Φ : Symboling (I.eraseChoice choice hchoice))
    (hReal :
      Φ.Realizes (M.eraseLastCountMatrix choice hchoice hdegree).val) :
    (Φ.extendLast choice hchoice).Realizes M.val := by
  intro c σ
  rcases Fin.eq_castSucc_or_eq_last σ with ⟨τ, rfl⟩ | rfl
  · rw [Φ.extendLast_count_castSucc choice hchoice c τ]
    exact hReal c τ
  · rw [Φ.extendLast_count_last choice hchoice c]
    exact hdegree c

end Symboling

def SymbolingWithResidues {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (R : ResidueSpec m T C) : Prop :=
  ∃ Φ : Symboling I, Φ.HasResidues R

theorem symbolingWithResidues_of_swapAt_hasResidues
    {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {Φ : Symboling I}
    {R : ResidueSpec m T C} (hResidues : Φ.HasResidues R)
    (x₀ : X) (σ τ : Fin T) :
    SymbolingWithResidues I (Φ.swapResidueSpec R x₀ σ τ) :=
  ⟨Φ.swapAt x₀ σ τ, Φ.swapAt_hasResidues hResidues⟩

theorem symbolingWithResidues_of_permuteAt_hasResidues
    {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {Φ : Symboling I}
    {R : ResidueSpec m T C} (hResidues : Φ.HasResidues R)
    (x₀ : X) (π : Equiv.Perm (Fin T)) :
    SymbolingWithResidues I (Φ.permuteResidueSpec R x₀ π) :=
  ⟨Φ.permuteAt x₀ π, Φ.permuteAt_hasResidues hResidues⟩

universe uX uC

namespace FiniteHoffman

def edgeLeftDegree {C E : Type*} [Fintype E] [DecidableEq E]
    [DecidableEq C] (left : E → C) (c : C) : Nat :=
  ((Finset.univ : Finset E).filter (fun e => left e = c)).card

def edgeRightDegree {T : Nat} {E : Type*} [Fintype E] [DecidableEq E]
    (right : E → Fin T) (σ : Fin T) : Nat :=
  ((Finset.univ : Finset E).filter (fun e => right e = σ)).card

def edgeRectCount {T : Nat} {C E : Type*} [Fintype E] [DecidableEq E]
    [DecidableEq C] (left : E → C) (right : E → Fin T)
    (U : Finset C) (S : Finset (Fin T)) : Nat :=
  ((Finset.univ : Finset E).filter
    (fun e => left e ∈ U ∧ right e ∈ S)).card

def edgePairCount {T : Nat} {C E : Type*} [Fintype E] [DecidableEq E]
    [DecidableEq C] (left : E → C) (right : E → Fin T)
    (c : C) (σ : Fin T) : Nat :=
  ((Finset.univ : Finset E).filter
    (fun e => left e = c ∧ right e = σ)).card

def activeDegree {X C : Type*} [Fintype X] [DecidableEq X]
    [DecidableEq C] (active : X → Finset C) (c : C) : Nat :=
  ((Finset.univ : Finset X).filter (fun x => c ∈ active x)).card

/--
Finite Hoffman/de Werra compatible edge-colouring theorem.

`A k` and `B k` are the left and right vertices where colour `k` is allowed.
The conclusion colours each copied edge by a colour compatible with both
endpoints, using every colour exactly once at each of its allowed vertices.
-/
def CompatibleDeWerraGoal : Prop :=
  ∀ {L : Type uC} {R : Type} {K : Type uX} {E : Type uC}
    [Fintype L] [Fintype R] [Fintype K] [Fintype E]
    [DecidableEq L] [DecidableEq R] [DecidableEq K] [DecidableEq E],
    ∀ (left : E → L) (right : E → R)
      (A : K → Finset L) (B : K → Finset R),
      (∀ k : K, (A k).card = (B k).card) →
      (∀ l : L,
        ((Finset.univ : Finset E).filter (fun e => left e = l)).card =
          ((Finset.univ : Finset K).filter (fun k => l ∈ A k)).card) →
      (∀ r : R,
        ((Finset.univ : Finset E).filter (fun e => right e = r)).card =
          ((Finset.univ : Finset K).filter (fun k => r ∈ B k)).card) →
      (∀ U : Finset L, ∀ V : Finset R,
        ((Finset.univ : Finset E).filter
          (fun e => left e ∈ U ∧ right e ∈ V)).card
          ≤ ∑ k : K, min ((A k ∩ U).card) ((B k ∩ V).card)) →
      ∃ κ : E → K,
        (∀ e : E, left e ∈ A (κ e) ∧ right e ∈ B (κ e)) ∧
        (∀ l : L, ∀ k : K, l ∈ A k →
          ∃! e : E, left e = l ∧ κ e = k) ∧
        (∀ r : R, ∀ k : K, r ∈ B k →
          ∃! e : E, right e = r ∧ κ e = k)

/--
The most standard copied-edge colouring form: colour every copied edge by an
`x`, respecting active left endpoints, with uniqueness over every `(x, sigma)`
and every active `(x, c)`.
-/
def RawExactEdgeColoringGoal : Prop :=
  ∀ {T : Nat} {X : Type uX} {C : Type uC} {E : Type uC}
    [Fintype X] [Fintype C] [Fintype E]
    [DecidableEq X] [DecidableEq C] [DecidableEq E],
    ∀ (left : E → C) (right : E → Fin T) (active : X → Finset C),
      (∀ x : X, (active x).card = T) →
      (∀ c : C, edgeLeftDegree left c = activeDegree active c) →
      (∀ σ : Fin T, edgeRightDegree right σ = Fintype.card X) →
      (∀ U : Finset C, ∀ S : Finset (Fin T),
        edgeRectCount left right U S
          ≤ ∑ x : X, min ((active x ∩ U).card) S.card) →
      ∃ κ : E → X,
        (∀ e : E, left e ∈ active (κ e)) ∧
        (∀ x : X, ∀ σ : Fin T,
          ∃! e : E, κ e = x ∧ right e = σ) ∧
        (∀ x : X, ∀ c : C, c ∈ active x →
          ∃! e : E, κ e = x ∧ left e = c)

theorem rawExactEdgeColoringGoal_of_compatibleDeWerra
    (hDW : CompatibleDeWerraGoal.{uX, uC}) :
    RawExactEdgeColoringGoal.{uX, uC} := by
  classical
  intro T X C E _instX _instC _instE _decX _decC _decE
    left right active hActive hLeft hRight hRect
  let B : X → Finset (Fin T) := fun _ => Finset.univ
  have hcardDW : ∀ x : X, (active x).card = (B x).card := by
    intro x
    simpa [B] using hActive x
  have hleftDW :
      ∀ c : C,
        ((Finset.univ : Finset E).filter (fun e => left e = c)).card =
          ((Finset.univ : Finset X).filter (fun x => c ∈ active x)).card := by
    intro c
    simpa [edgeLeftDegree, activeDegree] using hLeft c
  have hrightDW :
      ∀ σ : Fin T,
        ((Finset.univ : Finset E).filter (fun e => right e = σ)).card =
          ((Finset.univ : Finset X).filter (fun x => σ ∈ B x)).card := by
    intro σ
    simpa [edgeRightDegree, B] using hRight σ
  have hrectDW :
      ∀ U : Finset C, ∀ S : Finset (Fin T),
        ((Finset.univ : Finset E).filter
          (fun e => left e ∈ U ∧ right e ∈ S)).card
          ≤ ∑ x : X, min ((active x ∩ U).card) ((B x ∩ S).card) := by
    intro U S
    simpa [edgeRectCount, B] using hRect U S
  rcases hDW (left := left) (right := right)
      (A := active) (B := B)
      hcardDW hleftDW hrightDW hrectDW with
    ⟨κ, hκ, hL, hR⟩
  refine ⟨κ, ?_, ?_, ?_⟩
  · intro e
    exact (hκ e).1
  · intro x σ
    rcases hR σ x (by simp [B]) with ⟨e, he, huniq⟩
    refine ⟨e, ⟨he.2, he.1⟩, ?_⟩
    intro y hy
    exact huniq y ⟨hy.2, hy.1⟩
  · intro x c hc
    rcases hL c x hc with ⟨e, he, huniq⟩
    refine ⟨e, ⟨he.2, he.1⟩, ?_⟩
    intro y hy
    exact huniq y ⟨hy.2, hy.1⟩

/--
External finite Hoffman/de Werra edge-colouring theorem in copied-edge form.

The copied edges `E` have endpoints `C` and `Fin T`.  A local ordering assigns,
for each colour-copy `x`, the symbols `Fin T` bijectively to the active left
endpoints.  The rectangle condition is the Hoffman cut condition.
-/
def ExactEdgeColoringGoal : Prop :=
  ∀ {T : Nat} {X : Type uX} {C : Type uC} {E : Type uC}
    [Fintype X] [Fintype C] [Fintype E]
    [DecidableEq X] [DecidableEq C] [DecidableEq E],
    ∀ (left : E → C) (right : E → Fin T) (active : X → Finset C),
      (∀ x : X, (active x).card = T) →
      (∀ c : C, edgeLeftDegree left c = activeDegree active c) →
      (∀ σ : Fin T, edgeRightDegree right σ = Fintype.card X) →
      (∀ U : Finset C, ∀ S : Finset (Fin T),
        edgeRectCount left right U S
          ≤ ∑ x : X, min ((active x ∩ U).card) S.card) →
      ∃ e : (∀ x : X, Fin T ≃ {c : C // c ∈ active x}),
        ∀ c : C, ∀ σ : Fin T,
          Incidence.choiceDegree (fun x : X => ((e x) σ).1) c =
            edgePairCount left right c σ

noncomputable def rightEdge {T : Nat} {X E : Type*}
    (right : E → Fin T) (κ : E → X)
    (hRight : ∀ x : X, ∀ σ : Fin T,
      ∃! e : E, κ e = x ∧ right e = σ)
    (x : X) (σ : Fin T) : E :=
  Classical.choose ((hRight x σ).exists)

theorem rightEdge_spec {T : Nat} {X E : Type*}
    (right : E → Fin T) (κ : E → X)
    (hRight : ∀ x : X, ∀ σ : Fin T,
      ∃! e : E, κ e = x ∧ right e = σ)
    (x : X) (σ : Fin T) :
    κ (rightEdge right κ hRight x σ) = x ∧
      right (rightEdge right κ hRight x σ) = σ :=
  Classical.choose_spec ((hRight x σ).exists)

noncomputable def leftEdge {X C E : Type*}
    (left : E → C) (active : X → Finset C) (κ : E → X)
    (hLeft : ∀ x : X, ∀ c : C, c ∈ active x →
      ∃! e : E, κ e = x ∧ left e = c)
    (x : X) (c : {c : C // c ∈ active x}) : E :=
  Classical.choose ((hLeft x c.1 c.2).exists)

theorem leftEdge_spec {X C E : Type*}
    (left : E → C) (active : X → Finset C) (κ : E → X)
    (hLeft : ∀ x : X, ∀ c : C, c ∈ active x →
      ∃! e : E, κ e = x ∧ left e = c)
    (x : X) (c : {c : C // c ∈ active x}) :
    κ (leftEdge left active κ hLeft x c) = x ∧
      left (leftEdge left active κ hLeft x c) = c.1 :=
  Classical.choose_spec ((hLeft x c.1 c.2).exists)

noncomputable def localEquivOfRawExactColoring {T : Nat} {X C E : Type*}
    [DecidableEq C]
    (left : E → C) (right : E → Fin T) (active : X → Finset C)
    (κ : E → X)
    (hAvail : ∀ e : E, left e ∈ active (κ e))
    (hRight : ∀ x : X, ∀ σ : Fin T,
      ∃! e : E, κ e = x ∧ right e = σ)
    (hLeft : ∀ x : X, ∀ c : C, c ∈ active x →
      ∃! e : E, κ e = x ∧ left e = c)
    (x : X) :
    Fin T ≃ {c : C // c ∈ active x} where
  toFun := fun σ =>
    let e := rightEdge right κ hRight x σ
    ⟨left e, by
      have he := rightEdge_spec right κ hRight x σ
      have hmem := hAvail e
      rw [he.1] at hmem
      exact hmem⟩
  invFun := fun c =>
    right (leftEdge left active κ hLeft x c)
  left_inv := by
    intro σ
    dsimp
    let eR := rightEdge right κ hRight x σ
    have hR := rightEdge_spec right κ hRight x σ
    have hAct : left eR ∈ active x := by
      have hmem := hAvail eR
      rw [hR.1] at hmem
      exact hmem
    let csub : {c : C // c ∈ active x} := ⟨left eR, hAct⟩
    let eL := leftEdge left active κ hLeft x csub
    have hL := leftEdge_spec left active κ hLeft x csub
    have heq : eL = eR := by
      exact (hLeft x csub.1 csub.2).unique hL ⟨hR.1, rfl⟩
    change right eL = σ
    rw [heq]
    exact hR.2
  right_inv := by
    intro csub
    dsimp
    let eL := leftEdge left active κ hLeft x csub
    have hL := leftEdge_spec left active κ hLeft x csub
    let σ := right eL
    have hR := rightEdge_spec right κ hRight x σ
    have heq : rightEdge right κ hRight x σ = eL := by
      exact (hRight x σ).unique hR ⟨hL.1, rfl⟩
    apply Subtype.ext
    change left (rightEdge right κ hRight x σ) = csub.1
    rw [heq]
    exact hL.2

theorem choiceDegree_localEquivOfRawExactColoring
    {T : Nat} {X : Type uX} {C : Type uC} {E : Type uC}
    [Fintype X] [Fintype E] [DecidableEq X] [DecidableEq C] [DecidableEq E]
    (left : E → C) (right : E → Fin T) (active : X → Finset C)
    (κ : E → X)
    (hAvail : ∀ e : E, left e ∈ active (κ e))
    (hRight : ∀ x : X, ∀ σ : Fin T,
      ∃! e : E, κ e = x ∧ right e = σ)
    (hLeft : ∀ x : X, ∀ c : C, c ∈ active x →
      ∃! e : E, κ e = x ∧ left e = c)
    (c : C) (σ : Fin T) :
    Incidence.choiceDegree
        (fun x : X =>
          ((localEquivOfRawExactColoring
            left right active κ hAvail hRight hLeft x) σ).1) c =
      edgePairCount left right c σ := by
  classical
  rw [Incidence.choiceDegree, edgePairCount]
  rw [← Fintype.card_subtype
    (fun x : X =>
      ((localEquivOfRawExactColoring
        left right active κ hAvail hRight hLeft x) σ).1 = c)]
  rw [← Fintype.card_subtype
    (fun e : E => left e = c ∧ right e = σ)]
  let f :
      {x : X //
        ((localEquivOfRawExactColoring
          left right active κ hAvail hRight hLeft x) σ).1 = c} ≃
        {e : E // left e = c ∧ right e = σ} :=
    { toFun := fun x =>
        ⟨rightEdge right κ hRight x.1 σ, by
          have hx := x.2
          have hR := rightEdge_spec right κ hRight x.1 σ
          have hleft :
              left (rightEdge right κ hRight x.1 σ) = c := by
            simpa [localEquivOfRawExactColoring] using hx
          exact ⟨hleft, hR.2⟩⟩
      invFun := fun e =>
        ⟨κ e.1, by
          have hR := rightEdge_spec right κ hRight (κ e.1) σ
          have heq :
              rightEdge right κ hRight (κ e.1) σ = e.1 := by
            exact (hRight (κ e.1) σ).unique hR ⟨rfl, e.2.2⟩
          change
            left (rightEdge right κ hRight (κ e.1) σ) = c
          rw [heq]
          exact e.2.1⟩
      left_inv := by
        intro x
        apply Subtype.ext
        have hR := rightEdge_spec right κ hRight x.1 σ
        exact hR.1
      right_inv := by
        intro e
        apply Subtype.ext
        have hR := rightEdge_spec right κ hRight (κ e.1) σ
        exact (hRight (κ e.1) σ).unique hR ⟨rfl, e.2.2⟩ }
  exact Fintype.card_congr f

theorem exactEdgeColoringGoal_of_raw
    (hRaw : RawExactEdgeColoringGoal.{uX, uC}) :
    ExactEdgeColoringGoal.{uX, uC} := by
  classical
  intro T X C E _instX _instC _instE _decX _decC _decE
    left right active hAct hLeftDeg hRightDeg hRect
  rcases hRaw left right active hAct hLeftDeg hRightDeg hRect with
    ⟨κ, hAvail, hRight, hLeft⟩
  refine ⟨fun x =>
    localEquivOfRawExactColoring left right active κ hAvail hRight hLeft x,
    ?_⟩
  intro c σ
  exact choiceDegree_localEquivOfRawExactColoring
    left right active κ hAvail hRight hLeft c σ

theorem exactEdgeColoringGoal_of_compatibleDeWerra
    (hDW : CompatibleDeWerraGoal.{uX, uC}) :
    ExactEdgeColoringGoal.{uX, uC} :=
  exactEdgeColoringGoal_of_raw
    (rawExactEdgeColoringGoal_of_compatibleDeWerra hDW)

end FiniteHoffman

abbrev DemandToken {T : Nat} {C : Type uC}
    (m : C → Fin T → Nat) : Type uC :=
  Sigma fun c : C => Sigma fun σ : Fin T => Fin (m c σ)

namespace DemandToken

def color {T : Nat} {C : Type uC} {m : C → Fin T → Nat}
    (q : DemandToken m) : C :=
  q.1

def sym {T : Nat} {C : Type uC} {m : C → Fin T → Nat}
    (q : DemandToken m) : Fin T :=
  q.2.1

theorem edgeLeftDegree_color {T : Nat} {C : Type uC}
    [Fintype C] [DecidableEq C] (m : C → Fin T → Nat) (c : C) :
    FiniteHoffman.edgeLeftDegree
        (fun q : DemandToken m => color q) c =
      ∑ σ : Fin T, m c σ := by
  classical
  rw [FiniteHoffman.edgeLeftDegree, Finset.card_filter]
  change
    (∑ q : DemandToken m, if q.1 = c then 1 else 0) =
      ∑ σ : Fin T, m c σ
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single c]
  · simp
  · intro b _hb hbc
    simp [hbc]
  · intro hc
    exact False.elim (hc (Finset.mem_univ c))

theorem edgeRightDegree_sym {T : Nat} {C : Type uC}
    [Fintype C] [DecidableEq C] (m : C → Fin T → Nat) (σ : Fin T) :
    FiniteHoffman.edgeRightDegree
        (fun q : DemandToken m => sym q) σ =
      ∑ c : C, m c σ := by
  classical
  rw [FiniteHoffman.edgeRightDegree, Finset.card_filter]
  change
    (∑ q : DemandToken m, if q.2.1 = σ then 1 else 0) =
      ∑ c : C, m c σ
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c _hc
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single σ]
  · simp
  · intro τ _hτ hτσ
    simp [hτσ]
  · intro hσ
    exact False.elim (hσ (Finset.mem_univ σ))

theorem edgeRectCount_color_sym {T : Nat} {C : Type uC}
    [Fintype C] [DecidableEq C] (m : C → Fin T → Nat)
    (U : Finset C) (S : Finset (Fin T)) :
    FiniteHoffman.edgeRectCount
        (fun q : DemandToken m => color q)
        (fun q : DemandToken m => sym q) U S =
      ∑ c ∈ U, ∑ σ ∈ S, m c σ := by
  classical
  rw [FiniteHoffman.edgeRectCount]
  rw [← Fintype.card_subtype
    (fun q : DemandToken m => color q ∈ U ∧ sym q ∈ S)]
  let e :
      {q : DemandToken m // color q ∈ U ∧ sym q ∈ S} ≃
        Sigma fun c : {c : C // c ∈ U} =>
          Sigma fun σ : {σ : Fin T // σ ∈ S} => Fin (m c.1 σ.1) :=
    { toFun := fun q =>
        ⟨⟨q.1.1, q.2.1⟩, ⟨⟨q.1.2.1, q.2.2⟩, q.1.2.2⟩⟩
      invFun := fun q =>
        ⟨⟨q.1.1, ⟨q.2.1.1, q.2.2⟩⟩, ⟨q.1.2, q.2.1.2⟩⟩
      left_inv := by
        intro q
        rcases q with ⟨⟨c, σ, j⟩, hU, hS⟩
        rfl
      right_inv := by
        intro q
        rcases q with ⟨⟨c, hU⟩, ⟨⟨σ, hS⟩, j⟩⟩
        rfl }
  calc
    Fintype.card {q : DemandToken m // color q ∈ U ∧ sym q ∈ S}
        =
        Fintype.card
          (Sigma fun c : {c : C // c ∈ U} =>
            Sigma fun σ : {σ : Fin T // σ ∈ S} => Fin (m c.1 σ.1)) :=
          Fintype.card_congr e
    _ = ∑ c : {c : C // c ∈ U},
          ∑ σ : {σ : Fin T // σ ∈ S}, m c.1 σ.1 := by
          simp [Fintype.card_sigma]
    _ = ∑ c ∈ U, ∑ σ ∈ S, m c σ := by
          change
            (∑ c ∈ U.attach, ∑ σ ∈ S.attach, m c.1 σ.1) =
              ∑ c ∈ U, ∑ σ ∈ S, m c σ
          rw [Finset.sum_attach U
            (fun c : C => ∑ σ ∈ S.attach, m c σ.1)]
          apply Finset.sum_congr rfl
          intro c _hc
          rw [Finset.sum_attach S (fun σ : Fin T => m c σ)]

theorem edgePairCount_color_sym {T : Nat} {C : Type uC}
    [Fintype C] [DecidableEq C] (m : C → Fin T → Nat)
    (c : C) (σ : Fin T) :
    FiniteHoffman.edgePairCount
        (fun q : DemandToken m => color q)
        (fun q : DemandToken m => sym q) c σ =
      m c σ := by
  classical
  rw [FiniteHoffman.edgePairCount, Finset.card_filter]
  change
    (∑ q : DemandToken m,
      if q.1 = c ∧ q.2.1 = σ then 1 else 0) =
      m c σ
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single c]
  · rw [Fintype.sum_sigma]
    rw [Finset.sum_eq_single σ]
    · simp
    · intro τ _hτ hτσ
      simp [hτσ]
    · intro hσ
      exact False.elim (hσ (Finset.mem_univ σ))
  · intro b _hb hbc
    simp [hbc]
  · intro hc
    exact False.elim (hc (Finset.mem_univ c))

end DemandToken

/--
The Hoffman/Hall realization theorem needed by the active branch.

This is intentionally isolated from rounding and residue arithmetic: once a
count matrix has the forced row/column sums and Hall cuts, it can be realized by
a symboling.
-/
def HallRealizationGoal : Prop :=
  ∀ {T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C],
    ∀ (I : Incidence T X C) (M : CountMatrix I),
      M.HallCuts →
      ∃ Φ : Symboling I, Φ.Realizes M.val

def HoffmanOrderedSDRGoal : Prop :=
  ∀ {T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C],
    ∀ (I : Incidence T X C) (m : C → Fin T → Nat),
      (∀ c : C, (∑ σ : Fin T, m c σ) = I.colorDegree c) →
      (∀ σ : Fin T, (∑ c : C, m c σ) = Fintype.card X) →
      (∀ U : Finset C, ∀ S : Finset (Fin T),
        (∑ c ∈ U, ∑ σ ∈ S, m c σ) ≤ I.cutCap U S) →
      ∃ e : (∀ x : X, Fin T ≃ {c : C // c ∈ I.active x}),
        ∀ c : C, ∀ σ : Fin T,
          Incidence.choiceDegree (fun x : X => ((e x) σ).1) c = m c σ

theorem hoffmanOrderedSDRGoal_of_exactEdgeColoring
    (hEdge : FiniteHoffman.ExactEdgeColoringGoal.{uX, uC}) :
    HoffmanOrderedSDRGoal.{uX, uC} := by
  classical
  intro T X C _instX _instC _decX _decC I m hrow hcol hcut
  let E : Type uC := DemandToken m
  let left : E → C := fun q => DemandToken.color q
  let right : E → Fin T := fun q => DemandToken.sym q
  have hAct : ∀ x : X, (I.active x).card = T := by
    intro x
    exact I.active_card x
  have hLeft :
      ∀ c : C,
        FiniteHoffman.edgeLeftDegree left c =
          FiniteHoffman.activeDegree I.active c := by
    intro c
    rw [DemandToken.edgeLeftDegree_color]
    simpa [left, FiniteHoffman.activeDegree, Incidence.colorDegree]
      using hrow c
  have hRight :
      ∀ σ : Fin T,
        FiniteHoffman.edgeRightDegree right σ = Fintype.card X := by
    intro σ
    rw [DemandToken.edgeRightDegree_sym]
    simpa [right] using hcol σ
  have hRect :
      ∀ U : Finset C, ∀ S : Finset (Fin T),
        FiniteHoffman.edgeRectCount left right U S
          ≤ ∑ x : X, min ((I.active x ∩ U).card) S.card := by
    intro U S
    rw [DemandToken.edgeRectCount_color_sym]
    simpa [left, right, Incidence.cutCap] using hcut U S
  rcases hEdge left right I.active hAct hLeft hRight hRect with ⟨e, he⟩
  refine ⟨e, ?_⟩
  intro c σ
  calc
    Incidence.choiceDegree (fun x : X => ((e x) σ).1) c
        = FiniteHoffman.edgePairCount left right c σ := he c σ
    _ = m c σ := by
        rw [DemandToken.edgePairCount_color_sym]

theorem hallRealizationGoal_of_hoffmanOrderedSDR
    (hHoffman : HoffmanOrderedSDRGoal.{uX, uC}) :
    HallRealizationGoal.{uX, uC} := by
  classical
  intro T X C _instX _instC _decX _decC I M hHall
  rcases hHoffman I M.val M.row_sum M.col_sum (by
      intro U S
      simpa [CountMatrix.cutMass] using hHall U S) with
    ⟨e, he⟩
  let Φ : Symboling I := { equiv := e }
  refine ⟨Φ, ?_⟩
  intro c σ
  rw [Φ.count_eq_choiceDegree c σ]
  exact he c σ

theorem hallRealizationGoal_of_exactEdgeColoring
    (hEdge : FiniteHoffman.ExactEdgeColoringGoal.{uX, uC}) :
    HallRealizationGoal.{uX, uC} :=
  hallRealizationGoal_of_hoffmanOrderedSDR
    (hoffmanOrderedSDRGoal_of_exactEdgeColoring hEdge)

theorem hoffmanOrderedSDRGoal_of_hallRealization
    (hRealize : HallRealizationGoal.{uX, uC}) :
    HoffmanOrderedSDRGoal.{uX, uC} := by
  classical
  intro T X C _instX _instC _decX _decC I m hrow hcol hcut
  let M : CountMatrix I := {
    val := m
    row_sum := hrow
    col_sum := hcol
  }
  have hHall : M.HallCuts := by
    intro U S
    change (∑ c ∈ U, ∑ σ ∈ S, m c σ) ≤ I.cutCap U S
    exact hcut U S
  rcases hRealize I M hHall with ⟨Φ, hReal⟩
  refine ⟨Φ.equiv, ?_⟩
  intro c σ
  change Incidence.choiceDegree (fun x : X => Φ.color x σ) c = m c σ
  rw [← Φ.count_eq_choiceDegree c σ]
  exact hReal c σ

theorem hallRealizationGoal_iff_hoffmanOrderedSDRGoal :
    HallRealizationGoal.{uX, uC} ↔ HoffmanOrderedSDRGoal.{uX, uC} :=
  ⟨hoffmanOrderedSDRGoal_of_hallRealization,
    hallRealizationGoal_of_hoffmanOrderedSDR⟩

def ColumnFillingUpgradeGoal : Prop :=
  ∀ {T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C],
    ∀ (I : Incidence T X C) (M : CountMatrix I),
      M.HallCuts →
      M.ColumnFilling →
      ∃ Φ : Symboling I, Φ.Realizes M.val

theorem hallRealizationGoal_of_columnFillingUpgrade
    (hUpgrade : ColumnFillingUpgradeGoal.{uX, uC}) :
    HallRealizationGoal.{uX, uC} := by
  intro T X C _instX _instC _decX _decC I M hHall
  rcases M.exists_columnFilling_of_hallCuts hHall with ⟨F⟩
  exact hUpgrade I M hHall F

theorem columnFillingUpgradeGoal_of_hallRealization
    (hRealize : HallRealizationGoal.{uX, uC}) :
    ColumnFillingUpgradeGoal.{uX, uC} := by
  intro T X C _instX _instC _decX _decC I M hHall _F
  exact hRealize I M hHall

theorem hallRealizationGoal_iff_columnFillingUpgradeGoal :
    HallRealizationGoal.{uX, uC} ↔ ColumnFillingUpgradeGoal.{uX, uC} :=
  ⟨columnFillingUpgradeGoal_of_hallRealization,
    hallRealizationGoal_of_columnFillingUpgrade⟩

def EraseLastHallCutsGoal : Prop :=
  ∀ {T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C],
    ∀ (I : Incidence (T + 1) X C) (M : CountMatrix I),
      M.HallCuts →
      ∃ f : (Sigma fun c : C => Fin (M.val c (Fin.last T))) ≃ X,
        ∃ hfActive :
          ∀ q : Sigma fun c : C => Fin (M.val c (Fin.last T)),
            q.1 ∈ I.active (f q),
          let choice : X → C := fun x => (f.symm x).1
          let hchoice : ∀ x : X, choice x ∈ I.active x := by
            intro x
            simpa [choice] using hfActive (f.symm x)
          let hdegree :
              ∀ c : C,
                Incidence.choiceDegree choice c = M.val c (Fin.last T) :=
            fun c => M.choiceDegree_of_bijective_token_matching (Fin.last T) f c
          (M.eraseLastCountMatrix choice hchoice hdegree).HallCuts

def EraseLastHallCutsSelectionGoal : Prop :=
  ∀ {T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C],
    ∀ (I : Incidence (T + 1) X C) (M : CountMatrix I),
      M.HallCuts →
      ∃ f : (Sigma fun c : C => Fin (M.val c (Fin.last T))) ≃ X,
        ∃ hfActive :
          ∀ q : Sigma fun c : C => Fin (M.val c (Fin.last T)),
            q.1 ∈ I.active (f q),
          let choice : X → C := fun x => (f.symm x).1
          let hchoice : ∀ x : X, choice x ∈ I.active x := by
            intro x
            simpa [choice] using hfActive (f.symm x)
          ∀ U : Finset C, ∀ S : Finset (Fin T),
            M.cutMass U (S.image (Fin.castSucc : Fin T → Fin (T + 1)))
                + Incidence.choiceLowHitCount I choice U S
              ≤ I.cutCap U
                  (S.image (Fin.castSucc : Fin T → Fin (T + 1)))

def EraseLastHallCutsChoiceGoal : Prop :=
  ∀ {T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C],
    ∀ (I : Incidence (T + 1) X C) (M : CountMatrix I),
      M.HallCuts →
      ∃ choice : X → C,
        ∃ _hchoice : ∀ x : X, choice x ∈ I.active x,
          (∀ c : C, Incidence.choiceDegree choice c = M.val c (Fin.last T)) ∧
            ∀ U : Finset C, ∀ S : Finset (Fin T),
              M.cutMass U (S.image (Fin.castSucc : Fin T → Fin (T + 1)))
                  + Incidence.choiceLowHitCount I choice U S
                ≤ I.cutCap U
                    (S.image (Fin.castSucc : Fin T → Fin (T + 1)))

def EraseLastHallCutsSlackChoiceGoal : Prop :=
  ∀ {T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C],
    ∀ (I : Incidence (T + 1) X C) (M : CountMatrix I),
      M.HallCuts →
      ∃ choice : X → C,
        ∃ _hchoice : ∀ x : X, choice x ∈ I.active x,
          (∀ c : C, Incidence.choiceDegree choice c = M.val c (Fin.last T)) ∧
            ∀ U : Finset C, ∀ S : Finset (Fin T),
              Incidence.choiceLowHitCount I choice U S
                ≤ M.cutSlack U
                    (S.image (Fin.castSucc : Fin T → Fin (T + 1)))

def EraseLastHallCutsNontrivialSlackChoiceGoal : Prop :=
  ∀ {T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C],
    ∀ (I : Incidence (T + 1) X C) (M : CountMatrix I),
      M.HallCuts →
      ∃ choice : X → C,
        ∃ _hchoice : ∀ x : X, choice x ∈ I.active x,
          (∀ c : C, Incidence.choiceDegree choice c = M.val c (Fin.last T)) ∧
            ∀ U : Finset C, ∀ S : Finset (Fin T),
              U.Nonempty → U ≠ (Finset.univ : Finset C) → S.Nonempty →
                Incidence.choiceLowHitCount I choice U S
                  ≤ M.cutSlack U
                      (S.image (Fin.castSucc : Fin T → Fin (T + 1)))

def EraseLastHallCutsLinearChoiceGoal : Prop :=
  ∀ {T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C],
    ∀ (I : Incidence (T + 1) X C) (M : CountMatrix I),
      M.HallCuts →
      ∃ choice : X → C,
        ∃ _hchoice : ∀ x : X, choice x ∈ I.active x,
          (∀ c : C, Incidence.choiceDegree choice c = M.val c (Fin.last T)) ∧
            ∀ U : Finset C, ∀ S : Finset (Fin T),
              U.Nonempty → U ≠ (Finset.univ : Finset C) → S.Nonempty →
                (∑ c ∈ U,
                  Incidence.choiceDegreeOn (Incidence.lowCutSet I U S)
                    choice c)
                  ≤ M.cutSlack U
                      (S.image (Fin.castSucc : Fin T → Fin (T + 1)))

def EraseLastHallCutsTokenLinearChoiceGoal : Prop :=
  ∀ {T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C],
    ∀ (I : Incidence (T + 1) X C) (M : CountMatrix I),
      M.HallCuts →
      ∃ f : (Sigma fun c : C => Fin (M.val c (Fin.last T))) ≃ X,
        (∀ q : Sigma fun c : C => Fin (M.val c (Fin.last T)),
            q.1 ∈ I.active (f q)) ∧
          ∀ U : Finset C, ∀ S : Finset (Fin T),
            U.Nonempty → U ≠ (Finset.univ : Finset C) → S.Nonempty →
              Incidence.tokenLoadOn f (Incidence.lowCutSet I U S) U
                ≤ M.cutSlack U
                    (S.image (Fin.castSucc : Fin T → Fin (T + 1)))

def EraseLastHallCutsProperTokenLinearChoiceGoal : Prop :=
  ∀ {T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C],
    ∀ (I : Incidence (T + 1) X C) (M : CountMatrix I),
      M.HallCuts →
      ∃ f : (Sigma fun c : C => Fin (M.val c (Fin.last T))) ≃ X,
        (∀ q : Sigma fun c : C => Fin (M.val c (Fin.last T)),
            q.1 ∈ I.active (f q)) ∧
          ∀ U : Finset C, ∀ S : Finset (Fin T),
            U.Nonempty → U ≠ (Finset.univ : Finset C) →
              S.Nonempty → S ≠ (Finset.univ : Finset (Fin T)) →
                Incidence.tokenLoadOn f (Incidence.lowCutSet I U S) U
                  ≤ M.cutSlack U
                      (S.image (Fin.castSucc : Fin T → Fin (T + 1)))

def EraseLastHallCutsProperTokenQuotaSelectionGoal : Prop :=
  ∀ {T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C],
    ∀ (I : Incidence (T + 1) X C) (M : CountMatrix I),
      M.HallCuts →
      ∃ f : (Sigma fun c : C => Fin (M.val c (Fin.last T))) ≃ X,
        (∀ q : Sigma fun c : C => Fin (M.val c (Fin.last T)),
            q.1 ∈ I.active (f q)) ∧
          ∀ U : Finset C, ∀ S : Finset (Fin T),
            U.Nonempty → U ≠ (Finset.univ : Finset C) →
              S.Nonempty → S ≠ (Finset.univ : Finset (Fin T)) →
                Incidence.tokenLoadOn f (Incidence.lowCutSet I U S) U
                  ≤ (∑ x : X, min ((I.active x ∩ U).card) S.card)
                      - ∑ c ∈ U, ∑ σ ∈ S, M.val c (Fin.castSucc σ)

theorem eraseLastHallCutsProperTokenLinearChoiceGoal_of_quota
    (hQuota :
      EraseLastHallCutsProperTokenQuotaSelectionGoal.{uX, uC}) :
    EraseLastHallCutsProperTokenLinearChoiceGoal.{uX, uC} := by
  classical
  intro T X C _instX _instC _decX _decC I M hHall
  rcases hQuota I M hHall with ⟨f, hfActive, hQuotaCuts⟩
  refine ⟨f, hfActive, ?_⟩
  intro U S hUne hUuniv hSne hSuniv
  rw [M.cutSlack_image_castSucc U S]
  exact hQuotaCuts U S hUne hUuniv hSne hSuniv

theorem eraseLastHallCutsTokenLinearChoiceGoal_of_hallRealization
    (hRealize : HallRealizationGoal.{uX, uC}) :
    EraseLastHallCutsTokenLinearChoiceGoal.{uX, uC} := by
  classical
  intro T X C _instX _instC _decX _decC I M hHall
  rcases hRealize I M hHall with ⟨Φ, hReal⟩
  let choice : X → C := fun x => Φ.color x (Fin.last T)
  have hchoice : ∀ x : X, choice x ∈ I.active x := by
    intro x
    exact Φ.color_mem_active x (Fin.last T)
  have hdegree :
      ∀ c : C, Incidence.choiceDegree choice c = M.val c (Fin.last T) := by
    intro c
    rw [← Φ.count_eq_choiceDegree c (Fin.last T), hReal c (Fin.last T)]
  rcases Incidence.exists_choiceDegree_bijective_token_matching
      choice (fun c : C => M.val c (Fin.last T)) hdegree with
    ⟨f, hfChoice⟩
  refine ⟨f, ?_, ?_⟩
  · intro q
    rw [hfChoice q]
    exact hchoice (f q)
  · have hchoiceEq : (fun x : X => (f.symm x).1) = choice := by
      funext x
      have h := hfChoice (f.symm x)
      simpa using h
    intro U S _hUne _hUuniv _hSne
    have hHallUS :
        M.cutMass U (S.image (Fin.castSucc : Fin T → Fin (T + 1))) ≤
          I.cutCap U (S.image (Fin.castSucc : Fin T → Fin (T + 1))) :=
      hHall U (S.image (Fin.castSucc : Fin T → Fin (T + 1)))
    have hAdd :
        M.cutMass U (S.image (Fin.castSucc : Fin T → Fin (T + 1)))
            + Incidence.choiceLowHitCount I choice U S
          ≤ I.cutCap U
              (S.image (Fin.castSucc : Fin T → Fin (T + 1))) := by
      simpa [choice] using
        Φ.cutMass_image_castSucc_add_choiceLowHitCount_le_cutCap_of_realizes
          M hReal U S
    have hLow :
        Incidence.choiceLowHitCount I choice U S
          ≤ M.cutSlack U
              (S.image (Fin.castSucc : Fin T → Fin (T + 1))) :=
      ((M.cutMass_add_le_iff_le_cutSlack U
        (S.image (Fin.castSucc : Fin T → Fin (T + 1))) hHallUS
        (Incidence.choiceLowHitCount I choice U S)).1 hAdd)
    rw [Incidence.tokenLoadOn_eq_choiceHitCountOn, hchoiceEq,
      ← Incidence.choiceLowHitCount_eq_choiceHitCountOn_lowCutSet]
    exact hLow

theorem eraseLastHallCutsProperTokenQuotaSelection_of_realizes
    {T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence (T + 1) X C} (M : CountMatrix I)
    (hHall : M.HallCuts) (Φ : Symboling I) (hReal : Φ.Realizes M.val) :
    ∃ f : (Sigma fun c : C => Fin (M.val c (Fin.last T))) ≃ X,
      (∀ q : Sigma fun c : C => Fin (M.val c (Fin.last T)),
          q.1 ∈ I.active (f q)) ∧
        ∀ U : Finset C, ∀ S : Finset (Fin T),
          U.Nonempty → U ≠ (Finset.univ : Finset C) →
            S.Nonempty → S ≠ (Finset.univ : Finset (Fin T)) →
              Incidence.tokenLoadOn f (Incidence.lowCutSet I U S) U
                ≤ (∑ x : X, min ((I.active x ∩ U).card) S.card)
                    - ∑ c ∈ U, ∑ σ ∈ S, M.val c (Fin.castSucc σ) := by
  classical
  let choice : X → C := fun x => Φ.color x (Fin.last T)
  have hchoice : ∀ x : X, choice x ∈ I.active x := by
    intro x
    exact Φ.color_mem_active x (Fin.last T)
  have hdegree :
      ∀ c : C, Incidence.choiceDegree choice c = M.val c (Fin.last T) := by
    intro c
    rw [← Φ.count_eq_choiceDegree c (Fin.last T), hReal c (Fin.last T)]
  rcases Incidence.exists_choiceDegree_bijective_token_matching
      choice (fun c : C => M.val c (Fin.last T)) hdegree with
    ⟨f, hfChoice⟩
  refine ⟨f, ?_, ?_⟩
  · intro q
    rw [hfChoice q]
    exact hchoice (f q)
  · have hchoiceEq : (fun x : X => (f.symm x).1) = choice := by
      funext x
      have h := hfChoice (f.symm x)
      simpa using h
    intro U S _hUne _hUuniv _hSne _hSuniv
    have hHallUS :
        M.cutMass U (S.image (Fin.castSucc : Fin T → Fin (T + 1))) ≤
          I.cutCap U (S.image (Fin.castSucc : Fin T → Fin (T + 1))) :=
      hHall U (S.image (Fin.castSucc : Fin T → Fin (T + 1)))
    have hAdd :
        M.cutMass U (S.image (Fin.castSucc : Fin T → Fin (T + 1)))
            + Incidence.choiceLowHitCount I choice U S
          ≤ I.cutCap U
              (S.image (Fin.castSucc : Fin T → Fin (T + 1))) := by
      simpa [choice] using
        Φ.cutMass_image_castSucc_add_choiceLowHitCount_le_cutCap_of_realizes
          M hReal U S
    have hLow :
        Incidence.choiceLowHitCount I choice U S
          ≤ M.cutSlack U
              (S.image (Fin.castSucc : Fin T → Fin (T + 1))) :=
      ((M.cutMass_add_le_iff_le_cutSlack U
        (S.image (Fin.castSucc : Fin T → Fin (T + 1))) hHallUS
        (Incidence.choiceLowHitCount I choice U S)).1 hAdd)
    rw [← M.cutSlack_image_castSucc U S]
    rw [Incidence.tokenLoadOn_eq_choiceHitCountOn, hchoiceEq,
      ← Incidence.choiceLowHitCount_eq_choiceHitCountOn_lowCutSet]
    exact hLow

theorem eraseLastHallCutsTokenLinearChoiceGoal_of_proper
    (hProper : EraseLastHallCutsProperTokenLinearChoiceGoal.{uX, uC}) :
    EraseLastHallCutsTokenLinearChoiceGoal.{uX, uC} := by
  classical
  intro T X C _instX _instC _decX _decC I M hHall
  rcases hProper I M hHall with ⟨f, hfActive, hSlackProper⟩
  let choice : X → C := fun x : X => (f.symm x).1
  have hchoice : ∀ x : X, choice x ∈ I.active x := by
    intro x
    have h := hfActive (f.symm x)
    rw [f.apply_symm_apply] at h
    simpa [choice] using h
  have hdegree :
      ∀ c : C, Incidence.choiceDegree choice c = M.val c (Fin.last T) :=
    fun c => M.choiceDegree_of_bijective_token_matching (Fin.last T) f c
  refine ⟨f, hfActive, ?_⟩
  intro U S hUne hUuniv hSne
  by_cases hSuniv : S = (Finset.univ : Finset (Fin T))
  · subst S
    have hlow :
        Incidence.choiceLowHitCount I choice U
            (Finset.univ : Finset (Fin T))
          ≤ M.cutSlack U
              ((Finset.univ : Finset (Fin T)).image
                (Fin.castSucc : Fin T → Fin (T + 1))) :=
      M.choiceLowHitCount_univ_le_cutSlack_image_castSucc
        choice hchoice hdegree hHall U
    have hload :
        Incidence.tokenLoadOn f
            (Incidence.lowCutSet I U (Finset.univ : Finset (Fin T))) U =
          Incidence.choiceLowHitCount I choice U
            (Finset.univ : Finset (Fin T)) := by
      rw [Incidence.choiceLowHitCount_eq_choiceHitCountOn_lowCutSet,
        ← Incidence.tokenLoadOn_eq_choiceHitCountOn]
    rw [hload]
    exact hlow
  · exact hSlackProper U S hUne hUuniv hSne hSuniv

theorem eraseLastHallCutsTokenLinearChoiceGoal_of_exactEdgeColoring
    (hEdge : FiniteHoffman.ExactEdgeColoringGoal.{uX, uC}) :
    EraseLastHallCutsTokenLinearChoiceGoal.{uX, uC} :=
  eraseLastHallCutsTokenLinearChoiceGoal_of_hallRealization
    (hallRealizationGoal_of_exactEdgeColoring hEdge)

theorem eraseLastHallCutsTokenLinearChoiceGoal_of_selection
    (hSelect : EraseLastHallCutsSelectionGoal.{uX, uC}) :
    EraseLastHallCutsTokenLinearChoiceGoal.{uX, uC} := by
  classical
  intro T X C _instX _instC _decX _decC I M hHall
  rcases hSelect I M hHall with ⟨f, hfActive, hCover⟩
  let choice : X → C := fun x : X => (f.symm x).1
  refine ⟨f, hfActive, ?_⟩
  intro U S _hUne _hUuniv _hSne
  have hHallUS :
      M.cutMass U (S.image (Fin.castSucc : Fin T → Fin (T + 1))) ≤
        I.cutCap U (S.image (Fin.castSucc : Fin T → Fin (T + 1))) :=
    hHall U (S.image (Fin.castSucc : Fin T → Fin (T + 1)))
  have hLow :
      Incidence.choiceLowHitCount I choice U S
        ≤ M.cutSlack U
            (S.image (Fin.castSucc : Fin T → Fin (T + 1))) :=
    ((M.cutMass_add_le_iff_le_cutSlack U
      (S.image (Fin.castSucc : Fin T → Fin (T + 1))) hHallUS
      (Incidence.choiceLowHitCount I choice U S)).1 (by
        simpa [choice] using hCover U S))
  rw [Incidence.tokenLoadOn_eq_choiceHitCountOn]
  change
    Incidence.choiceHitCountOn (Incidence.lowCutSet I U S)
        (fun x : X => (f.symm x).1) U
      ≤ M.cutSlack U
          (S.image (Fin.castSucc : Fin T → Fin (T + 1)))
  rw [← Incidence.choiceLowHitCount_eq_choiceHitCountOn_lowCutSet]
  exact hLow

theorem eraseLastHallCutsLinearChoiceGoal_of_tokenLinear
    (hToken : EraseLastHallCutsTokenLinearChoiceGoal.{uX, uC}) :
    EraseLastHallCutsLinearChoiceGoal.{uX, uC} := by
  classical
  intro T X C _instX _instC _decX _decC I M hHall
  rcases hToken I M hHall with ⟨f, hfActive, hSlack⟩
  let choice : X → C := fun x => (f.symm x).1
  have hchoice : ∀ x : X, choice x ∈ I.active x := by
    intro x
    have h := hfActive (f.symm x)
    rw [f.apply_symm_apply] at h
    simpa [choice] using h
  have hdegree :
      ∀ c : C,
        Incidence.choiceDegree choice c = M.val c (Fin.last T) :=
    fun c => M.choiceDegree_of_bijective_token_matching (Fin.last T) f c
  refine ⟨choice, hchoice, hdegree, ?_⟩
  intro U S hUne hUuniv hSne
  simpa [choice, Incidence.tokenLoadOn_eq_sum_choiceDegreeOn f
      (Incidence.lowCutSet I U S) U] using
    hSlack U S hUne hUuniv hSne

theorem eraseLastHallCutsNontrivialSlackChoiceGoal_of_linear
    (hLinear : EraseLastHallCutsLinearChoiceGoal.{uX, uC}) :
    EraseLastHallCutsNontrivialSlackChoiceGoal.{uX, uC} := by
  classical
  intro T X C _instX _instC _decX _decC I M hHall
  rcases hLinear I M hHall with ⟨choice, hchoice, hdegree, hSlack⟩
  refine ⟨choice, hchoice, hdegree, ?_⟩
  intro U S hUne hUuniv hSne
  rw [Incidence.choiceLowHitCount_eq_sum_choiceDegreeOn_lowCutSet]
  exact hSlack U S hUne hUuniv hSne

theorem eraseLastHallCutsSlackChoiceGoal_of_nontrivial
    (hNontriv : EraseLastHallCutsNontrivialSlackChoiceGoal.{uX, uC}) :
    EraseLastHallCutsSlackChoiceGoal.{uX, uC} := by
  classical
  intro T X C _instX _instC _decX _decC I M hHall
  rcases hNontriv I M hHall with ⟨choice, hchoice, hdegree, hSlack⟩
  refine ⟨choice, hchoice, hdegree, ?_⟩
  intro U S
  by_cases hUempty : U = ∅
  · subst U
    rw [Incidence.choiceLowHitCount_colors_empty]
    exact Nat.zero_le _
  by_cases hUuniv : U = (Finset.univ : Finset C)
  · subst U
    rw [Incidence.choiceLowHitCount_colors_univ]
    exact Nat.zero_le _
  by_cases hSempty : S = ∅
  · subst S
    rw [Incidence.choiceLowHitCount_symbols_empty I choice hchoice]
    exact Nat.zero_le _
  exact hSlack U S
    (Finset.nonempty_iff_ne_empty.mpr hUempty) hUuniv
    (Finset.nonempty_iff_ne_empty.mpr hSempty)

theorem eraseLastHallCutsChoiceGoal_of_slackChoice
    (hSlackChoice : EraseLastHallCutsSlackChoiceGoal.{uX, uC}) :
    EraseLastHallCutsChoiceGoal.{uX, uC} := by
  classical
  intro T X C _instX _instC _decX _decC I M hHall
  rcases hSlackChoice I M hHall with ⟨choice, hchoice, hdegree, hSlack⟩
  refine ⟨choice, hchoice, hdegree, ?_⟩
  intro U S
  have hHallUS :
      M.cutMass U (S.image (Fin.castSucc : Fin T → Fin (T + 1))) ≤
        I.cutCap U (S.image (Fin.castSucc : Fin T → Fin (T + 1))) :=
    hHall U (S.image (Fin.castSucc : Fin T → Fin (T + 1)))
  exact ((M.cutMass_add_le_iff_le_cutSlack U
    (S.image (Fin.castSucc : Fin T → Fin (T + 1))) hHallUS
    (Incidence.choiceLowHitCount I choice U S)).2 (hSlack U S))

theorem eraseLastHallCutsSelectionGoal_of_choice
    (hChoice : EraseLastHallCutsChoiceGoal.{uX, uC}) :
    EraseLastHallCutsSelectionGoal.{uX, uC} := by
  classical
  intro T X C _instX _instC _decX _decC I M hHall
  rcases hChoice I M hHall with ⟨choice, hchoice, hdegree, hSlack⟩
  rcases Incidence.exists_choiceDegree_bijective_token_matching
      choice (fun c : C => M.val c (Fin.last T)) hdegree with
    ⟨f, hfChoice⟩
  refine ⟨f, ?_, ?_⟩
  · intro q
    rw [hfChoice q]
    exact hchoice (f q)
  · dsimp only
    have hchoiceEq : (fun x : X => (f.symm x).1) = choice := by
      funext x
      have h := hfChoice (f.symm x)
      simpa using h
    intro U S
    simpa [hchoiceEq] using hSlack U S

theorem eraseLastHallCutsGoal_of_selection
    (hSelect : EraseLastHallCutsSelectionGoal.{uX, uC}) :
    EraseLastHallCutsGoal.{uX, uC} := by
  classical
  intro T X C _instX _instC _decX _decC I M hHall
  rcases hSelect I M hHall with ⟨f, hfActive, hCover⟩
  let choice : X → C := fun x => (f.symm x).1
  have hchoice : ∀ x : X, choice x ∈ I.active x := by
    intro x
    have h := hfActive (f.symm x)
    rw [f.apply_symm_apply] at h
    simpa [choice] using h
  have hdegree :
      ∀ c : C,
        Incidence.choiceDegree choice c = M.val c (Fin.last T) :=
    fun c => M.choiceDegree_of_bijective_token_matching (Fin.last T) f c
  refine ⟨f, hfActive, ?_⟩
  change (M.eraseLastCountMatrix choice hchoice hdegree).HallCuts
  exact M.eraseLastCountMatrix_hallCuts_of_cutCap_slack
    choice hchoice hdegree hCover

theorem eraseLastHallCutsGoal_of_choice
    (hChoice : EraseLastHallCutsChoiceGoal.{uX, uC}) :
    EraseLastHallCutsGoal.{uX, uC} :=
  eraseLastHallCutsGoal_of_selection
    (eraseLastHallCutsSelectionGoal_of_choice hChoice)

theorem eraseLastHallCutsGoal_of_slackChoice
    (hSlackChoice : EraseLastHallCutsSlackChoiceGoal.{uX, uC}) :
    EraseLastHallCutsGoal.{uX, uC} :=
  eraseLastHallCutsGoal_of_choice
    (eraseLastHallCutsChoiceGoal_of_slackChoice hSlackChoice)

theorem eraseLastHallCutsGoal_of_nontrivialSlackChoice
    (hNontriv : EraseLastHallCutsNontrivialSlackChoiceGoal.{uX, uC}) :
    EraseLastHallCutsGoal.{uX, uC} :=
  eraseLastHallCutsGoal_of_slackChoice
    (eraseLastHallCutsSlackChoiceGoal_of_nontrivial hNontriv)

theorem eraseLastHallCutsGoal_of_linearChoice
    (hLinear : EraseLastHallCutsLinearChoiceGoal.{uX, uC}) :
    EraseLastHallCutsGoal.{uX, uC} :=
  eraseLastHallCutsGoal_of_nontrivialSlackChoice
    (eraseLastHallCutsNontrivialSlackChoiceGoal_of_linear hLinear)

theorem eraseLastHallCutsGoal_of_tokenLinearChoice
    (hToken : EraseLastHallCutsTokenLinearChoiceGoal.{uX, uC}) :
    EraseLastHallCutsGoal.{uX, uC} :=
  eraseLastHallCutsGoal_of_linearChoice
    (eraseLastHallCutsLinearChoiceGoal_of_tokenLinear hToken)

theorem eraseLastHallCutsGoal_of_properTokenLinearChoice
    (hProper : EraseLastHallCutsProperTokenLinearChoiceGoal.{uX, uC}) :
    EraseLastHallCutsGoal.{uX, uC} :=
  eraseLastHallCutsGoal_of_tokenLinearChoice
    (eraseLastHallCutsTokenLinearChoiceGoal_of_proper hProper)

theorem eraseLastHallCutsChoice_zero {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence 1 X C) (M : CountMatrix I)
    (hHall : M.HallCuts) :
    ∃ choice : X → C,
      ∃ _hchoice : ∀ x : X, choice x ∈ I.active x,
        (∀ c : C, Incidence.choiceDegree choice c = M.val c (Fin.last 0)) ∧
          ∀ U : Finset C, ∀ S : Finset (Fin 0),
            M.cutMass U (S.image (Fin.castSucc : Fin 0 → Fin (0 + 1)))
                + Incidence.choiceLowHitCount I choice U S
              ≤ I.cutCap U
                  (S.image (Fin.castSucc : Fin 0 → Fin (0 + 1))) := by
  classical
  rcases M.exists_singleSymbol_bijective_token_matching hHall (Fin.last 0) with
    ⟨f, hfActive⟩
  let choice : X → C := fun x => (f.symm x).1
  have hchoice : ∀ x : X, choice x ∈ I.active x := by
    intro x
    have h := hfActive (f.symm x)
    rw [f.apply_symm_apply] at h
    simpa [choice] using h
  have hdegree :
      ∀ c : C, Incidence.choiceDegree choice c = M.val c (Fin.last 0) :=
    fun c => M.choiceDegree_of_bijective_token_matching (Fin.last 0) f c
  refine ⟨choice, hchoice, hdegree, ?_⟩
  intro U S
  have hS : S = ∅ := by
    ext σ
    exact Fin.elim0 σ
  subst S
  rw [Incidence.choiceLowHitCount_symbols_empty I choice hchoice U]
  simp [M.cutMass_symbols_empty_eq_cutCap U]

theorem eraseLastHallCutsSlackChoice_zero {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence 1 X C) (M : CountMatrix I)
    (hHall : M.HallCuts) :
    ∃ choice : X → C,
      ∃ _hchoice : ∀ x : X, choice x ∈ I.active x,
        (∀ c : C, Incidence.choiceDegree choice c = M.val c (Fin.last 0)) ∧
          ∀ U : Finset C, ∀ S : Finset (Fin 0),
            Incidence.choiceLowHitCount I choice U S
              ≤ M.cutSlack U
                  (S.image (Fin.castSucc : Fin 0 → Fin (0 + 1))) := by
  classical
  rcases M.exists_singleSymbol_bijective_token_matching hHall (Fin.last 0) with
    ⟨f, hfActive⟩
  let choice : X → C := fun x => (f.symm x).1
  have hchoice : ∀ x : X, choice x ∈ I.active x := by
    intro x
    have h := hfActive (f.symm x)
    rw [f.apply_symm_apply] at h
    simpa [choice] using h
  have hdegree :
      ∀ c : C, Incidence.choiceDegree choice c = M.val c (Fin.last 0) :=
    fun c => M.choiceDegree_of_bijective_token_matching (Fin.last 0) f c
  refine ⟨choice, hchoice, hdegree, ?_⟩
  intro U S
  have hS : S = ∅ := by
    ext σ
    exact Fin.elim0 σ
  subst S
  rw [Incidence.choiceLowHitCount_symbols_empty I choice hchoice U]
  exact Nat.zero_le _

theorem eraseLastHallCutsNontrivialSlackChoice_zero
    {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence 1 X C) (M : CountMatrix I)
    (hHall : M.HallCuts) :
    ∃ choice : X → C,
      ∃ _hchoice : ∀ x : X, choice x ∈ I.active x,
        (∀ c : C, Incidence.choiceDegree choice c = M.val c (Fin.last 0)) ∧
          ∀ U : Finset C, ∀ S : Finset (Fin 0),
            U.Nonempty → U ≠ (Finset.univ : Finset C) → S.Nonempty →
              Incidence.choiceLowHitCount I choice U S
                ≤ M.cutSlack U
                    (S.image (Fin.castSucc : Fin 0 → Fin (0 + 1))) := by
  classical
  rcases M.exists_singleSymbol_bijective_token_matching hHall (Fin.last 0) with
    ⟨f, hfActive⟩
  let choice : X → C := fun x => (f.symm x).1
  have hchoice : ∀ x : X, choice x ∈ I.active x := by
    intro x
    have h := hfActive (f.symm x)
    rw [f.apply_symm_apply] at h
    simpa [choice] using h
  have hdegree :
      ∀ c : C, Incidence.choiceDegree choice c = M.val c (Fin.last 0) :=
    fun c => M.choiceDegree_of_bijective_token_matching (Fin.last 0) f c
  refine ⟨choice, hchoice, hdegree, ?_⟩
  intro U S _hUne _hUuniv hSne
  rcases hSne with ⟨σ, _hσ⟩
  exact Fin.elim0 σ

theorem eraseLastHallCutsLinearChoice_zero
    {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence 1 X C) (M : CountMatrix I)
    (hHall : M.HallCuts) :
    ∃ choice : X → C,
      ∃ _hchoice : ∀ x : X, choice x ∈ I.active x,
        (∀ c : C, Incidence.choiceDegree choice c = M.val c (Fin.last 0)) ∧
          ∀ U : Finset C, ∀ S : Finset (Fin 0),
            U.Nonempty → U ≠ (Finset.univ : Finset C) → S.Nonempty →
              (∑ c ∈ U,
                Incidence.choiceDegreeOn (Incidence.lowCutSet I U S)
                  choice c)
                ≤ M.cutSlack U
                    (S.image (Fin.castSucc : Fin 0 → Fin (0 + 1))) := by
  classical
  rcases M.exists_singleSymbol_bijective_token_matching hHall (Fin.last 0) with
    ⟨f, hfActive⟩
  let choice : X → C := fun x => (f.symm x).1
  have hchoice : ∀ x : X, choice x ∈ I.active x := by
    intro x
    have h := hfActive (f.symm x)
    rw [f.apply_symm_apply] at h
    simpa [choice] using h
  have hdegree :
      ∀ c : C, Incidence.choiceDegree choice c = M.val c (Fin.last 0) :=
    fun c => M.choiceDegree_of_bijective_token_matching (Fin.last 0) f c
  refine ⟨choice, hchoice, hdegree, ?_⟩
  intro U S _hUne _hUuniv hSne
  rcases hSne with ⟨σ, _hσ⟩
  exact Fin.elim0 σ

theorem eraseLastHallCutsTokenLinearChoice_zero
    {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence 1 X C) (M : CountMatrix I)
    (hHall : M.HallCuts) :
    ∃ f : (Sigma fun c : C => Fin (M.val c (Fin.last 0))) ≃ X,
      (∀ q : Sigma fun c : C => Fin (M.val c (Fin.last 0)),
          q.1 ∈ I.active (f q)) ∧
        ∀ U : Finset C, ∀ S : Finset (Fin 0),
          U.Nonempty → U ≠ (Finset.univ : Finset C) → S.Nonempty →
            Incidence.tokenLoadOn f (Incidence.lowCutSet I U S) U
              ≤ M.cutSlack U
                  (S.image (Fin.castSucc : Fin 0 → Fin (0 + 1))) := by
  classical
  rcases M.exists_singleSymbol_bijective_token_matching hHall (Fin.last 0) with
    ⟨f, hfActive⟩
  refine ⟨f, hfActive, ?_⟩
  intro U S _hUne _hUuniv hSne
  rcases hSne with ⟨σ, _hσ⟩
  exact Fin.elim0 σ

theorem eraseLastHallCuts_zero {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence 1 X C) (M : CountMatrix I)
    (hHall : M.HallCuts) :
    ∃ f : (Sigma fun c : C => Fin (M.val c (Fin.last 0))) ≃ X,
      ∃ hfActive :
        ∀ q : Sigma fun c : C => Fin (M.val c (Fin.last 0)),
          q.1 ∈ I.active (f q),
        let choice : X → C := fun x => (f.symm x).1
        let hchoice : ∀ x : X, choice x ∈ I.active x := by
          intro x
          have h := hfActive (f.symm x)
          rw [f.apply_symm_apply] at h
          simpa [choice] using h
        let hdegree :
            ∀ c : C,
              Incidence.choiceDegree choice c = M.val c (Fin.last 0) :=
          fun c => M.choiceDegree_of_bijective_token_matching (Fin.last 0) f c
        (M.eraseLastCountMatrix choice hchoice hdegree).HallCuts := by
  classical
  rcases M.exists_singleSymbol_bijective_token_matching hHall (Fin.last 0) with
    ⟨f, hfActive⟩
  let choice : X → C := fun x => (f.symm x).1
  have hchoice : ∀ x : X, choice x ∈ I.active x := by
    intro x
    have h := hfActive (f.symm x)
    rw [f.apply_symm_apply] at h
    simpa [choice] using h
  have hdegree :
      ∀ c : C, Incidence.choiceDegree choice c = M.val c (Fin.last 0) :=
    fun c => M.choiceDegree_of_bijective_token_matching (Fin.last 0) f c
  refine ⟨f, hfActive, ?_⟩
  change (M.eraseLastCountMatrix choice hchoice hdegree).HallCuts
  intro U S
  have hS : S = ∅ := by
    ext σ
    exact Fin.elim0 σ
  subst S
  rw [CountMatrix.cutMass_symbols_empty_eq_cutCap]

theorem eraseLastHallCuts_one {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence 2 X C) (M : CountMatrix I)
    (hHall : M.HallCuts) :
    ∃ f : (Sigma fun c : C => Fin (M.val c (Fin.last 1))) ≃ X,
      ∃ hfActive :
        ∀ q : Sigma fun c : C => Fin (M.val c (Fin.last 1)),
          q.1 ∈ I.active (f q),
        let choice : X → C := fun x => (f.symm x).1
        let hchoice : ∀ x : X, choice x ∈ I.active x := by
          intro x
          have h := hfActive (f.symm x)
          rw [f.apply_symm_apply] at h
          simpa [choice] using h
        let hdegree :
            ∀ c : C,
              Incidence.choiceDegree choice c = M.val c (Fin.last 1) :=
          fun c => M.choiceDegree_of_bijective_token_matching (Fin.last 1) f c
        (M.eraseLastCountMatrix choice hchoice hdegree).HallCuts := by
  classical
  rcases M.exists_singleSymbol_bijective_token_matching hHall (Fin.last 1) with
    ⟨f, hfActive⟩
  refine ⟨f, hfActive, ?_⟩
  let choice : X → C := fun x => (f.symm x).1
  have hchoice : ∀ x : X, choice x ∈ I.active x := by
    intro x
    have h := hfActive (f.symm x)
    rw [f.apply_symm_apply] at h
    simpa [choice] using h
  have hdegree :
      ∀ c : C, Incidence.choiceDegree choice c = M.val c (Fin.last 1) :=
    fun c => M.choiceDegree_of_bijective_token_matching (Fin.last 1) f c
  change (M.eraseLastCountMatrix choice hchoice hdegree).HallCuts
  exact CountMatrix.hallCuts_one (M.eraseLastCountMatrix choice hchoice hdegree)

theorem eraseLastHallCutsProperTokenQuotaSelection_zero
    {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence 1 X C) (M : CountMatrix I)
    (hHall : M.HallCuts) :
    ∃ f : (Sigma fun c : C => Fin (M.val c (Fin.last 0))) ≃ X,
      (∀ q : Sigma fun c : C => Fin (M.val c (Fin.last 0)),
          q.1 ∈ I.active (f q)) ∧
        ∀ U : Finset C, ∀ S : Finset (Fin 0),
          U.Nonempty → U ≠ (Finset.univ : Finset C) →
            S.Nonempty → S ≠ (Finset.univ : Finset (Fin 0)) →
              Incidence.tokenLoadOn f (Incidence.lowCutSet I U S) U
                ≤ (∑ x : X, min ((I.active x ∩ U).card) S.card)
                    - ∑ c ∈ U, ∑ σ ∈ S, M.val c (Fin.castSucc σ) := by
  classical
  rcases M.exists_singleSymbol_bijective_token_matching hHall (Fin.last 0) with
    ⟨f, hfActive⟩
  refine ⟨f, hfActive, ?_⟩
  intro _U S _hUne _hUuniv hSne _hSuniv
  rcases hSne with ⟨σ, _hσ⟩
  exact Fin.elim0 σ

theorem eraseLastHallCutsProperTokenQuotaSelection_one
    {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence 2 X C) (M : CountMatrix I)
    (hHall : M.HallCuts) :
    ∃ f : (Sigma fun c : C => Fin (M.val c (Fin.last 1))) ≃ X,
      (∀ q : Sigma fun c : C => Fin (M.val c (Fin.last 1)),
          q.1 ∈ I.active (f q)) ∧
        ∀ U : Finset C, ∀ S : Finset (Fin 1),
          U.Nonempty → U ≠ (Finset.univ : Finset C) →
            S.Nonempty → S ≠ (Finset.univ : Finset (Fin 1)) →
              Incidence.tokenLoadOn f (Incidence.lowCutSet I U S) U
                ≤ (∑ x : X, min ((I.active x ∩ U).card) S.card)
                    - ∑ c ∈ U, ∑ σ ∈ S, M.val c (Fin.castSucc σ) := by
  classical
  rcases M.exists_singleSymbol_bijective_token_matching hHall (Fin.last 1) with
    ⟨f, hfActive⟩
  refine ⟨f, hfActive, ?_⟩
  intro _U S _hUne _hUuniv hSne hSuniv
  have h0 : (0 : Fin 1) ∈ S := by
    rcases hSne with ⟨σ, hσ⟩
    fin_cases σ
    exact hσ
  have hS : S = (Finset.univ : Finset (Fin 1)) := by
    ext σ
    constructor
    · intro _h
      fin_cases σ
      exact Finset.mem_univ _
    · intro _h
      fin_cases σ
      exact h0
  exact False.elim (hSuniv hS)

theorem eraseLastHallCutsProperTokenQuotaSelection_of_T_le_one
    {T : Nat} (hT : T ≤ 1)
    {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence (T + 1) X C) (M : CountMatrix I)
    (hHall : M.HallCuts) :
    ∃ f : (Sigma fun c : C => Fin (M.val c (Fin.last T))) ≃ X,
      (∀ q : Sigma fun c : C => Fin (M.val c (Fin.last T)),
          q.1 ∈ I.active (f q)) ∧
        ∀ U : Finset C, ∀ S : Finset (Fin T),
          U.Nonempty → U ≠ (Finset.univ : Finset C) →
            S.Nonempty → S ≠ (Finset.univ : Finset (Fin T)) →
              Incidence.tokenLoadOn f (Incidence.lowCutSet I U S) U
                ≤ (∑ x : X, min ((I.active x ∩ U).card) S.card)
                    - ∑ c ∈ U, ∑ σ ∈ S, M.val c (Fin.castSucc σ) := by
  interval_cases T
  · exact eraseLastHallCutsProperTokenQuotaSelection_zero I M hHall
  · exact eraseLastHallCutsProperTokenQuotaSelection_one I M hHall

theorem hallRealization_zero {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence 0 X C) (M : CountMatrix I) :
    ∃ Φ : Symboling I, Φ.Realizes M.val := by
  classical
  refine ⟨{
    equiv := fun x => ?_
  }, ?_⟩
  · refine {
      toFun := fun σ => Fin.elim0 σ
      invFun := fun c => ?_
      left_inv := fun σ => Fin.elim0 σ
      right_inv := fun c => ?_
    }
    · have hEmpty : I.active x = ∅ :=
        Finset.card_eq_zero.mp (I.active_card x)
      exact False.elim (by
        have hc : c.1 ∈ (∅ : Finset C) := by
          simpa [hEmpty] using c.2
        simp at hc)
    · have hEmpty : I.active x = ∅ :=
        Finset.card_eq_zero.mp (I.active_card x)
      exact False.elim (by
        have hc : c.1 ∈ (∅ : Finset C) := by
          simpa [hEmpty] using c.2
        simp at hc)
  · intro c σ
    exact Fin.elim0 σ

theorem hallRealization_one {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence 1 X C) (M : CountMatrix I)
    (hHall : M.HallCuts) :
    ∃ Φ : Symboling I, Φ.Realizes M.val := by
  classical
  rcases M.exists_singleSymbol_bijective_token_matching hHall (0 : Fin 1) with
    ⟨f, hfActive⟩
  let chosen : X → C := fun x => (f.symm x).1
  have hChosenActive : ∀ x : X, chosen x ∈ I.active x := by
    intro x
    simpa [chosen] using hfActive (f.symm x)
  let Φ : Symboling I := {
    equiv := fun x => {
      toFun := fun _σ => ⟨chosen x, hChosenActive x⟩
      invFun := fun _c => 0
      left_inv := by
        intro σ
        fin_cases σ
        rfl
      right_inv := by
        intro c
        apply Subtype.ext
        exact I.eq_of_mem_of_active_card_one (hChosenActive x) c.2
    }
  }
  refine ⟨Φ, ?_⟩
  intro c σ
  fin_cases σ
  calc
    Φ.count c 0
        = ∑ x : X, if chosen x = c then 1 else 0 := by
            unfold Symboling.count
            apply Finset.sum_congr rfl
            intro x _hx
            simp [Symboling.color, Φ, chosen]
    _ = ∑ q : Sigma fun c : C => Fin (M.val c (0 : Fin 1)),
          if q.1 = c then 1 else 0 := by
            exact Fintype.sum_equiv f.symm
              (fun x : X => if chosen x = c then (1 : Nat) else 0)
              (fun q : Sigma fun c : C => Fin (M.val c (0 : Fin 1)) =>
                if q.1 = c then (1 : Nat) else 0)
              (by
                intro x
                simp [chosen])
    _ = M.val c 0 := by
            rw [Fintype.sum_sigma]
            calc
              (∑ x : C, ∑ q : Fin (M.val x (0 : Fin 1)),
                  if x = c then (1 : Nat) else 0)
                  = ∑ x : C, if x = c then M.val x 0 else 0 := by
                      apply Finset.sum_congr rfl
                      intro x _hx
                      by_cases hxc : x = c <;> simp [hxc]
              _ = M.val c 0 := by
                      simp

theorem hallRealization_succ_of_eraseLastHallCuts
    {T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence (T + 1) X C) (M : CountMatrix I)
    (hErase :
      ∃ f : (Sigma fun c : C => Fin (M.val c (Fin.last T))) ≃ X,
        ∃ hfActive :
          ∀ q : Sigma fun c : C => Fin (M.val c (Fin.last T)),
            q.1 ∈ I.active (f q),
          let choice : X → C := fun x => (f.symm x).1
          let hchoice : ∀ x : X, choice x ∈ I.active x := by
            intro x
            have h := hfActive (f.symm x)
            rw [f.apply_symm_apply] at h
            simpa [choice] using h
          let hdegree :
              ∀ c : C,
                Incidence.choiceDegree choice c = M.val c (Fin.last T) :=
            fun c => M.choiceDegree_of_bijective_token_matching
              (Fin.last T) f c
          (M.eraseLastCountMatrix choice hchoice hdegree).HallCuts)
    (hLower :
      ∀ (I' : Incidence T X C) (M' : CountMatrix I'),
        M'.HallCuts → ∃ Φ : Symboling I', Φ.Realizes M'.val) :
    ∃ Φ : Symboling I, Φ.Realizes M.val := by
  classical
  rcases hErase with ⟨f, hfActive, hReducedHall⟩
  let choice : X → C := fun x => (f.symm x).1
  have hchoice : ∀ x : X, choice x ∈ I.active x := by
    intro x
    simpa [choice] using hfActive (f.symm x)
  have hdegree :
      ∀ c : C,
        Incidence.choiceDegree choice c = M.val c (Fin.last T) :=
    fun c => M.choiceDegree_of_bijective_token_matching
      (Fin.last T) f c
  rcases hLower (I.eraseChoice choice hchoice)
      (M.eraseLastCountMatrix choice hchoice hdegree)
      hReducedHall with ⟨Φ, hReal⟩
  exact ⟨Φ.extendLast choice hchoice,
    Φ.extendLast_realizes_eraseLastCountMatrix M choice hchoice hdegree hReal⟩

theorem hallRealization_two {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence 2 X C) (M : CountMatrix I)
    (hHall : M.HallCuts) :
    ∃ Φ : Symboling I, Φ.Realizes M.val := by
  classical
  exact hallRealization_succ_of_eraseLastHallCuts I M
    (eraseLastHallCuts_one I M hHall)
    (fun I' M' hHall' => hallRealization_one I' M' hHall')

def EraseLastHallCutsTwoSingletonSelectionGoal : Prop :=
  ∀ {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C],
    ∀ (I : Incidence 3 X C) (M : CountMatrix I),
      M.HallCuts →
      ∃ f : (Sigma fun c : C => Fin (M.val c (Fin.last 2))) ≃ X,
        (∀ q : Sigma fun c : C => Fin (M.val c (Fin.last 2)),
            q.1 ∈ I.active (f q)) ∧
          let choice : X → C := fun x => (f.symm x).1
          ∀ U : Finset C, ∀ σ : Fin 2,
            M.cutMass U
                (({σ} : Finset (Fin 2)).image
                  (Fin.castSucc : Fin 2 → Fin 3))
              + Incidence.choiceLowHitCount I choice U
                  ({σ} : Finset (Fin 2))
                ≤ I.cutCap U
                    (({σ} : Finset (Fin 2)).image
                      (Fin.castSucc : Fin 2 → Fin 3))

def EraseLastHallCutsTwoSingletonCutSlackSelectionGoal : Prop :=
  ∀ {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C],
    ∀ (I : Incidence 3 X C) (M : CountMatrix I),
      M.HallCuts →
      ∃ f : (Sigma fun c : C => Fin (M.val c (Fin.last 2))) ≃ X,
        (∀ q : Sigma fun c : C => Fin (M.val c (Fin.last 2)),
            q.1 ∈ I.active (f q)) ∧
          let choice : X → C := fun x => (f.symm x).1
          ∀ U : Finset C, ∀ σ : Fin 2,
            Incidence.choiceLowHitCount I choice U
                ({σ} : Finset (Fin 2))
              ≤ M.cutSlack U
                  (({σ} : Finset (Fin 2)).image
                    (Fin.castSucc : Fin 2 → Fin 3))

def EraseLastHallCutsTwoSingletonTokenCutSlackSelectionGoal : Prop :=
  ∀ {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C],
    ∀ (I : Incidence 3 X C) (M : CountMatrix I),
      M.HallCuts →
      ∃ f : (Sigma fun c : C => Fin (M.val c (Fin.last 2))) ≃ X,
        (∀ q : Sigma fun c : C => Fin (M.val c (Fin.last 2)),
            q.1 ∈ I.active (f q)) ∧
          ∀ U : Finset C, ∀ σ : Fin 2,
            Incidence.tokenLoadOn f
                (Incidence.lowCutSet I U ({σ} : Finset (Fin 2))) U
              ≤ M.cutSlack U
                  (({σ} : Finset (Fin 2)).image
                    (Fin.castSucc : Fin 2 → Fin 3))

def EraseLastHallCutsTwoSingletonProperTokenCutSlackSelectionGoal : Prop :=
  ∀ {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C],
    ∀ (I : Incidence 3 X C) (M : CountMatrix I),
      M.HallCuts →
      ∃ f : (Sigma fun c : C => Fin (M.val c (Fin.last 2))) ≃ X,
        (∀ q : Sigma fun c : C => Fin (M.val c (Fin.last 2)),
            q.1 ∈ I.active (f q)) ∧
          ∀ U : Finset C, ∀ σ : Fin 2,
            U.Nonempty → U ≠ (Finset.univ : Finset C) →
              Incidence.tokenLoadOn f
                  (Incidence.lowCutSet I U ({σ} : Finset (Fin 2))) U
                ≤ M.cutSlack U
                    (({σ} : Finset (Fin 2)).image
                      (Fin.castSucc : Fin 2 → Fin 3))

def EraseLastHallCutsTwoSingletonProperTokenQuotaSelectionGoal : Prop :=
  ∀ {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C],
    ∀ (I : Incidence 3 X C) (M : CountMatrix I),
      M.HallCuts →
      ∃ f : (Sigma fun c : C => Fin (M.val c (Fin.last 2))) ≃ X,
        (∀ q : Sigma fun c : C => Fin (M.val c (Fin.last 2)),
            q.1 ∈ I.active (f q)) ∧
          ∀ U : Finset C, ∀ σ : Fin 2,
            U.Nonempty → U ≠ (Finset.univ : Finset C) →
              Incidence.tokenLoadOn f
                  (Incidence.lowCutSet I U ({σ} : Finset (Fin 2))) U
                ≤ I.hitCount U - ∑ c ∈ U, M.val c (Fin.castSucc σ)

lemma finset_fin_two_eq_singleton_of_mem_of_ne_univ
    (S : Finset (Fin 2)) {σ : Fin 2} (hσ : σ ∈ S)
    (hS : S ≠ (Finset.univ : Finset (Fin 2))) :
    S = {σ} := by
  ext τ
  constructor
  · intro hτ
    by_cases hτσ : τ = σ
    · simp [hτσ]
    · exfalso
      have hUniv : S = (Finset.univ : Finset (Fin 2)) := by
        ext ρ
        constructor
        · intro _
          simp
        · intro _
          fin_cases σ <;> fin_cases τ <;> fin_cases ρ <;>
            simp_all
      exact hS hUniv
  · intro hτ
    rw [Finset.mem_singleton] at hτ
    rw [hτ]
    exact hσ

theorem eraseLastHallCutsTwoSingletonProperTokenQuotaSelection_of_realizes
    {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence 3 X C} (M : CountMatrix I)
    (hHall : M.HallCuts) (Φ : Symboling I) (hReal : Φ.Realizes M.val) :
    ∃ f : (Sigma fun c : C => Fin (M.val c (Fin.last 2))) ≃ X,
      (∀ q : Sigma fun c : C => Fin (M.val c (Fin.last 2)),
          q.1 ∈ I.active (f q)) ∧
        ∀ U : Finset C, ∀ σ : Fin 2,
          U.Nonempty → U ≠ (Finset.univ : Finset C) →
            Incidence.tokenLoadOn f
                (Incidence.lowCutSet I U ({σ} : Finset (Fin 2))) U
              ≤ I.hitCount U - ∑ c ∈ U, M.val c (Fin.castSucc σ) := by
  classical
  rcases eraseLastHallCutsProperTokenQuotaSelection_of_realizes
      (T := 2) M hHall Φ hReal with
    ⟨f, hfActive, hQuota⟩
  refine ⟨f, hfActive, ?_⟩
  intro U σ hUne hUuniv
  have hSingletonProper : ({σ} : Finset (Fin 2)) ≠ Finset.univ := by
    intro h
    have hcard := congrArg Finset.card h
    simp at hcard
  have h :=
    hQuota U ({σ} : Finset (Fin 2)) hUne hUuniv
      (Finset.singleton_nonempty σ) hSingletonProper
  rw [← M.cutSlack_image_castSucc U ({σ} : Finset (Fin 2)),
    M.cutSlack_image_castSucc_singleton U σ] at h
  exact h

theorem eraseLastHallCutsProperTokenQuotaSelection_two_of_twoSingletonProperTokenQuota
    (hTwo :
      EraseLastHallCutsTwoSingletonProperTokenQuotaSelectionGoal.{uX, uC})
    {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence 3 X C) (M : CountMatrix I)
    (hHall : M.HallCuts) :
    ∃ f : (Sigma fun c : C => Fin (M.val c (Fin.last 2))) ≃ X,
      (∀ q : Sigma fun c : C => Fin (M.val c (Fin.last 2)),
          q.1 ∈ I.active (f q)) ∧
        ∀ U : Finset C, ∀ S : Finset (Fin 2),
          U.Nonempty → U ≠ (Finset.univ : Finset C) →
            S.Nonempty → S ≠ (Finset.univ : Finset (Fin 2)) →
              Incidence.tokenLoadOn f (Incidence.lowCutSet I U S) U
                ≤ (∑ x : X, min ((I.active x ∩ U).card) S.card)
                    - ∑ c ∈ U, ∑ σ ∈ S, M.val c (Fin.castSucc σ) := by
  classical
  rcases hTwo I M hHall with ⟨f, hfActive, hSingleton⟩
  refine ⟨f, hfActive, ?_⟩
  intro U S hUne hUuniv hSne hSuniv
  rcases hSne with ⟨σ, hσ⟩
  have hS : S = {σ} :=
    finset_fin_two_eq_singleton_of_mem_of_ne_univ S hσ hSuniv
  rw [← M.cutSlack_image_castSucc U S, hS,
    M.cutSlack_image_castSucc_singleton U σ]
  exact hSingleton U σ hUne hUuniv

theorem eraseLastHallCutsProperTokenQuotaSelection_of_T_le_two
    (hTwo :
      EraseLastHallCutsTwoSingletonProperTokenQuotaSelectionGoal.{uX, uC})
    {T : Nat} (hT : T ≤ 2)
    {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence (T + 1) X C) (M : CountMatrix I)
    (hHall : M.HallCuts) :
    ∃ f : (Sigma fun c : C => Fin (M.val c (Fin.last T))) ≃ X,
      (∀ q : Sigma fun c : C => Fin (M.val c (Fin.last T)),
          q.1 ∈ I.active (f q)) ∧
        ∀ U : Finset C, ∀ S : Finset (Fin T),
          U.Nonempty → U ≠ (Finset.univ : Finset C) →
            S.Nonempty → S ≠ (Finset.univ : Finset (Fin T)) →
              Incidence.tokenLoadOn f (Incidence.lowCutSet I U S) U
                ≤ (∑ x : X, min ((I.active x ∩ U).card) S.card)
                    - ∑ c ∈ U, ∑ σ ∈ S, M.val c (Fin.castSucc σ) := by
  interval_cases T
  · exact eraseLastHallCutsProperTokenQuotaSelection_zero I M hHall
  · exact eraseLastHallCutsProperTokenQuotaSelection_one I M hHall
  · exact eraseLastHallCutsProperTokenQuotaSelection_two_of_twoSingletonProperTokenQuota
      hTwo I M hHall

theorem eraseLastHallCutsTwoSingletonProperTokenCutSlackSelectionGoal_of_quota
    (hQuota :
      EraseLastHallCutsTwoSingletonProperTokenQuotaSelectionGoal.{uX, uC}) :
    EraseLastHallCutsTwoSingletonProperTokenCutSlackSelectionGoal.{uX, uC} := by
  classical
  intro X C _instX _instC _decX _decC I M hHall
  rcases hQuota I M hHall with ⟨f, hfActive, hLoad⟩
  refine ⟨f, hfActive, ?_⟩
  intro U σ hUne hUuniv
  rw [M.cutSlack_image_castSucc_singleton U σ]
  exact hLoad U σ hUne hUuniv

theorem eraseLastHallCutsTwoSingletonTokenCutSlackSelectionGoal_of_proper
    (hProper :
      EraseLastHallCutsTwoSingletonProperTokenCutSlackSelectionGoal.{uX, uC}) :
    EraseLastHallCutsTwoSingletonTokenCutSlackSelectionGoal.{uX, uC} := by
  classical
  intro X C _instX _instC _decX _decC I M hHall
  rcases hProper I M hHall with ⟨f, hfActive, hLoadProper⟩
  refine ⟨f, hfActive, ?_⟩
  intro U σ
  by_cases hUempty : U = ∅
  · subst U
    rw [Incidence.tokenLoadOn_colors_empty]
    exact Nat.zero_le _
  by_cases hUuniv : U = (Finset.univ : Finset C)
  · subst U
    rw [Incidence.lowCutSet_colors_univ, Incidence.tokenLoadOn_set_empty]
    exact Nat.zero_le _
  exact hLoadProper U σ
    (Finset.nonempty_iff_ne_empty.mpr hUempty) hUuniv

theorem eraseLastHallCutsTwoSingletonCutSlackSelectionGoal_of_token
    (hToken :
      EraseLastHallCutsTwoSingletonTokenCutSlackSelectionGoal.{uX, uC}) :
    EraseLastHallCutsTwoSingletonCutSlackSelectionGoal.{uX, uC} := by
  classical
  intro X C _instX _instC _decX _decC I M hHall
  rcases hToken I M hHall with ⟨f, hfActive, hLoad⟩
  refine ⟨f, hfActive, ?_⟩
  dsimp only
  intro U σ
  rw [Incidence.choiceLowHitCount_eq_choiceHitCountOn_lowCutSet,
    ← Incidence.tokenLoadOn_eq_choiceHitCountOn]
  exact hLoad U σ

theorem eraseLastHallCutsTwoSingletonSelectionGoal_of_cutSlack
    (hSelect : EraseLastHallCutsTwoSingletonCutSlackSelectionGoal.{uX, uC}) :
    EraseLastHallCutsTwoSingletonSelectionGoal.{uX, uC} := by
  classical
  intro X C _instX _instC _decX _decC I M hHall
  rcases hSelect I M hHall with ⟨f, hfActive, hSlack⟩
  refine ⟨f, hfActive, ?_⟩
  dsimp only
  intro U σ
  let S : Finset (Fin 3) :=
    ({σ} : Finset (Fin 2)).image (Fin.castSucc : Fin 2 → Fin 3)
  have hHallUS : M.cutMass U S ≤ I.cutCap U S := hHall U S
  exact
    ((M.cutMass_add_le_iff_le_cutSlack U S hHallUS
      (Incidence.choiceLowHitCount I (fun x : X => (f.symm x).1)
        U ({σ} : Finset (Fin 2)))).2 (hSlack U σ))

theorem hallRealization_three_of_singletonSelection
    (hSelect : EraseLastHallCutsTwoSingletonSelectionGoal.{uX, uC})
    {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence 3 X C) (M : CountMatrix I)
    (hHall : M.HallCuts) :
    ∃ Φ : Symboling I, Φ.Realizes M.val := by
  classical
  exact hallRealization_succ_of_eraseLastHallCuts I M
    (CountMatrix.eraseLastHallCuts_two_of_singleton_selection
      I M hHall (hSelect I M hHall))
    (fun I' M' hHall' => hallRealization_two I' M' hHall')

theorem hallRealization_three_of_singletonCutSlackSelection
    (hSelect : EraseLastHallCutsTwoSingletonCutSlackSelectionGoal.{uX, uC})
    {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence 3 X C) (M : CountMatrix I)
    (hHall : M.HallCuts) :
    ∃ Φ : Symboling I, Φ.Realizes M.val :=
  hallRealization_three_of_singletonSelection
    (eraseLastHallCutsTwoSingletonSelectionGoal_of_cutSlack hSelect)
    I M hHall

theorem hallRealization_three_of_singletonTokenCutSlackSelection
    (hToken :
      EraseLastHallCutsTwoSingletonTokenCutSlackSelectionGoal.{uX, uC})
    {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence 3 X C) (M : CountMatrix I)
    (hHall : M.HallCuts) :
    ∃ Φ : Symboling I, Φ.Realizes M.val :=
  hallRealization_three_of_singletonCutSlackSelection
    (eraseLastHallCutsTwoSingletonCutSlackSelectionGoal_of_token hToken)
    I M hHall

theorem hallRealization_three_of_singletonProperTokenCutSlackSelection
    (hProper :
      EraseLastHallCutsTwoSingletonProperTokenCutSlackSelectionGoal.{uX, uC})
    {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence 3 X C) (M : CountMatrix I)
    (hHall : M.HallCuts) :
    ∃ Φ : Symboling I, Φ.Realizes M.val :=
  hallRealization_three_of_singletonTokenCutSlackSelection
    (eraseLastHallCutsTwoSingletonTokenCutSlackSelectionGoal_of_proper
      hProper)
    I M hHall

theorem hallRealization_three_of_singletonProperTokenQuotaSelection
    (hQuota :
      EraseLastHallCutsTwoSingletonProperTokenQuotaSelectionGoal.{uX, uC})
    {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence 3 X C) (M : CountMatrix I)
    (hHall : M.HallCuts) :
    ∃ Φ : Symboling I, Φ.Realizes M.val :=
  hallRealization_three_of_singletonProperTokenCutSlackSelection
    (eraseLastHallCutsTwoSingletonProperTokenCutSlackSelectionGoal_of_quota
      hQuota)
    I M hHall

theorem hallRealization_of_T_le_two
    {T : Nat} (hT : T ≤ 2)
    {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (M : CountMatrix I)
    (hHall : M.HallCuts) :
    ∃ Φ : Symboling I, Φ.Realizes M.val := by
  interval_cases T
  · exact hallRealization_zero I M
  · exact hallRealization_one I M hHall
  · exact hallRealization_two I M hHall

theorem hallRealization_of_T_le_three_of_singletonSelection
    (hSelect : EraseLastHallCutsTwoSingletonSelectionGoal.{uX, uC})
    {T : Nat} (hT : T ≤ 3)
    {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (M : CountMatrix I)
    (hHall : M.HallCuts) :
    ∃ Φ : Symboling I, Φ.Realizes M.val := by
  interval_cases T
  · exact hallRealization_zero I M
  · exact hallRealization_one I M hHall
  · exact hallRealization_two I M hHall
  · exact hallRealization_three_of_singletonSelection hSelect I M hHall

theorem hallRealization_of_T_le_three_of_singletonCutSlackSelection
    (hSelect : EraseLastHallCutsTwoSingletonCutSlackSelectionGoal.{uX, uC})
    {T : Nat} (hT : T ≤ 3)
    {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (M : CountMatrix I)
    (hHall : M.HallCuts) :
    ∃ Φ : Symboling I, Φ.Realizes M.val :=
  hallRealization_of_T_le_three_of_singletonSelection
    (eraseLastHallCutsTwoSingletonSelectionGoal_of_cutSlack hSelect)
    hT I M hHall

theorem hallRealization_of_T_le_three_of_singletonTokenCutSlackSelection
    (hToken : EraseLastHallCutsTwoSingletonTokenCutSlackSelectionGoal.{uX, uC})
    {T : Nat} (hT : T ≤ 3)
    {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (M : CountMatrix I)
    (hHall : M.HallCuts) :
    ∃ Φ : Symboling I, Φ.Realizes M.val :=
  hallRealization_of_T_le_three_of_singletonCutSlackSelection
    (eraseLastHallCutsTwoSingletonCutSlackSelectionGoal_of_token hToken)
    hT I M hHall

theorem hallRealization_of_T_le_three_of_singletonProperTokenCutSlackSelection
    (hProper :
      EraseLastHallCutsTwoSingletonProperTokenCutSlackSelectionGoal.{uX, uC})
    {T : Nat} (hT : T ≤ 3)
    {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (M : CountMatrix I)
    (hHall : M.HallCuts) :
    ∃ Φ : Symboling I, Φ.Realizes M.val :=
  hallRealization_of_T_le_three_of_singletonTokenCutSlackSelection
    (eraseLastHallCutsTwoSingletonTokenCutSlackSelectionGoal_of_proper
      hProper)
    hT I M hHall

theorem hallRealization_of_T_le_three_of_singletonProperTokenQuotaSelection
    (hQuota :
      EraseLastHallCutsTwoSingletonProperTokenQuotaSelectionGoal.{uX, uC})
    {T : Nat} (hT : T ≤ 3)
    {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence T X C) (M : CountMatrix I)
    (hHall : M.HallCuts) :
    ∃ Φ : Symboling I, Φ.Realizes M.val :=
  hallRealization_of_T_le_three_of_singletonProperTokenCutSlackSelection
    (eraseLastHallCutsTwoSingletonProperTokenCutSlackSelectionGoal_of_quota
      hQuota)
    hT I M hHall

theorem hallRealization_succ_of_eraseLastHallCuts_and_lower_T_le_three
    (hToken : EraseLastHallCutsTwoSingletonTokenCutSlackSelectionGoal.{uX, uC})
    {T : Nat} (hT : T ≤ 3)
    {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence (T + 1) X C) (M : CountMatrix I)
    (hErase :
      ∃ f : (Sigma fun c : C => Fin (M.val c (Fin.last T))) ≃ X,
        ∃ hfActive :
          ∀ q : Sigma fun c : C => Fin (M.val c (Fin.last T)),
            q.1 ∈ I.active (f q),
          let choice : X → C := fun x => (f.symm x).1
          let hchoice : ∀ x : X, choice x ∈ I.active x := by
            intro x
            have h := hfActive (f.symm x)
            rw [f.apply_symm_apply] at h
            simpa [choice] using h
          let hdegree :
              ∀ c : C,
                Incidence.choiceDegree choice c = M.val c (Fin.last T) :=
            fun c => M.choiceDegree_of_bijective_token_matching
              (Fin.last T) f c
          (M.eraseLastCountMatrix choice hchoice hdegree).HallCuts) :
    ∃ Φ : Symboling I, Φ.Realizes M.val :=
  hallRealization_succ_of_eraseLastHallCuts I M hErase
    (fun I' M' hHall' =>
      hallRealization_of_T_le_three_of_singletonTokenCutSlackSelection
        hToken hT I' M' hHall')

theorem hallRealization_four_of_eraseLastHallCuts_and_singletonTokenCutSlackSelection
    (hToken : EraseLastHallCutsTwoSingletonTokenCutSlackSelectionGoal.{uX, uC})
    {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence 4 X C) (M : CountMatrix I)
    (hErase :
      ∃ f : (Sigma fun c : C => Fin (M.val c (Fin.last 3))) ≃ X,
        ∃ hfActive :
          ∀ q : Sigma fun c : C => Fin (M.val c (Fin.last 3)),
            q.1 ∈ I.active (f q),
          let choice : X → C := fun x => (f.symm x).1
          let hchoice : ∀ x : X, choice x ∈ I.active x := by
            intro x
            have h := hfActive (f.symm x)
            rw [f.apply_symm_apply] at h
            simpa [choice] using h
          let hdegree :
              ∀ c : C,
                Incidence.choiceDegree choice c = M.val c (Fin.last 3) :=
            fun c => M.choiceDegree_of_bijective_token_matching
              (Fin.last 3) f c
          (M.eraseLastCountMatrix choice hchoice hdegree).HallCuts) :
    ∃ Φ : Symboling I, Φ.Realizes M.val :=
  hallRealization_succ_of_eraseLastHallCuts_and_lower_T_le_three
    hToken (by omega : 3 ≤ 3) I M hErase

def EraseLastHallCutsFourGoal : Prop :=
  ∀ {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C],
    ∀ (I : Incidence 4 X C) (M : CountMatrix I),
      M.HallCuts →
      ∃ f : (Sigma fun c : C => Fin (M.val c (Fin.last 3))) ≃ X,
        ∃ hfActive :
          ∀ q : Sigma fun c : C => Fin (M.val c (Fin.last 3)),
            q.1 ∈ I.active (f q),
          let choice : X → C := fun x => (f.symm x).1
          let hchoice : ∀ x : X, choice x ∈ I.active x := by
            intro x
            have h := hfActive (f.symm x)
            rw [f.apply_symm_apply] at h
            simpa [choice] using h
          let hdegree :
              ∀ c : C,
                Incidence.choiceDegree choice c = M.val c (Fin.last 3) :=
            fun c => M.choiceDegree_of_bijective_token_matching
              (Fin.last 3) f c
          (M.eraseLastCountMatrix choice hchoice hdegree).HallCuts

def EraseLastHallCutsFourTokenCutSlackSelectionGoal : Prop :=
  ∀ {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C],
    ∀ (I : Incidence 4 X C) (M : CountMatrix I),
      M.HallCuts →
      ∃ f : (Sigma fun c : C => Fin (M.val c (Fin.last 3))) ≃ X,
        (∀ q : Sigma fun c : C => Fin (M.val c (Fin.last 3)),
            q.1 ∈ I.active (f q)) ∧
          ∀ U : Finset C, ∀ S : Finset (Fin 3),
            U.Nonempty → U ≠ (Finset.univ : Finset C) → S.Nonempty →
              Incidence.tokenLoadOn f (Incidence.lowCutSet I U S) U
                ≤ M.cutSlack U
                    (S.image (Fin.castSucc : Fin 3 → Fin 4))

def EraseLastHallCutsFourSmallTokenCutSlackSelectionGoal : Prop :=
  ∀ {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C],
    ∀ (I : Incidence 4 X C) (M : CountMatrix I),
      M.HallCuts →
      ∃ f : (Sigma fun c : C => Fin (M.val c (Fin.last 3))) ≃ X,
        (∀ q : Sigma fun c : C => Fin (M.val c (Fin.last 3)),
            q.1 ∈ I.active (f q)) ∧
          ∀ U : Finset C, ∀ S : Finset (Fin 3),
            U.Nonempty → U ≠ (Finset.univ : Finset C) →
              S.Nonempty → S.card ≤ 2 →
                Incidence.tokenLoadOn f (Incidence.lowCutSet I U S) U
                  ≤ M.cutSlack U
                      (S.image (Fin.castSucc : Fin 3 → Fin 4))

def EraseLastHallCutsFourSingletonPairTokenCutSlackSelectionGoal : Prop :=
  ∀ {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C],
    ∀ (I : Incidence 4 X C) (M : CountMatrix I),
      M.HallCuts →
      ∃ f : (Sigma fun c : C => Fin (M.val c (Fin.last 3))) ≃ X,
        (∀ q : Sigma fun c : C => Fin (M.val c (Fin.last 3)),
            q.1 ∈ I.active (f q)) ∧
          (∀ U : Finset C, ∀ σ : Fin 3,
            U.Nonempty → U ≠ (Finset.univ : Finset C) →
              Incidence.tokenLoadOn f
                  (Incidence.lowCutSet I U ({σ} : Finset (Fin 3))) U
                ≤ M.cutSlack U
                    (({σ} : Finset (Fin 3)).image
                      (Fin.castSucc : Fin 3 → Fin 4))) ∧
          (∀ U : Finset C, ∀ σ τ : Fin 3, σ ≠ τ →
            U.Nonempty → U ≠ (Finset.univ : Finset C) →
              Incidence.tokenLoadOn f
                  (Incidence.lowCutSet I U ({σ, τ} : Finset (Fin 3))) U
                ≤ M.cutSlack U
                    (({σ, τ} : Finset (Fin 3)).image
                      (Fin.castSucc : Fin 3 → Fin 4)))

def EraseLastHallCutsFourSingletonPairTokenQuotaSelectionGoal : Prop :=
  ∀ {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C],
    ∀ (I : Incidence 4 X C) (M : CountMatrix I),
      M.HallCuts →
      ∃ f : (Sigma fun c : C => Fin (M.val c (Fin.last 3))) ≃ X,
        (∀ q : Sigma fun c : C => Fin (M.val c (Fin.last 3)),
            q.1 ∈ I.active (f q)) ∧
          (∀ U : Finset C, ∀ σ : Fin 3,
            U.Nonempty → U ≠ (Finset.univ : Finset C) →
              Incidence.tokenLoadOn f
                  (Incidence.lowCutSet I U ({σ} : Finset (Fin 3))) U
                ≤ I.hitCount U - ∑ c ∈ U, M.val c (Fin.castSucc σ)) ∧
          (∀ U : Finset C, ∀ σ τ : Fin 3, σ ≠ τ →
            U.Nonempty → U ≠ (Finset.univ : Finset C) →
              Incidence.tokenLoadOn f
                  (Incidence.lowCutSet I U ({σ, τ} : Finset (Fin 3))) U
                ≤ (∑ x : X, min ((I.active x ∩ U).card) 2)
                    - ∑ c ∈ U,
                        (M.val c (Fin.castSucc σ) +
                          M.val c (Fin.castSucc τ)))

theorem eraseLastHallCutsFourSingletonPairTokenCutSlackSelectionGoal_of_quota
    (hQuota :
      EraseLastHallCutsFourSingletonPairTokenQuotaSelectionGoal.{uX, uC}) :
    EraseLastHallCutsFourSingletonPairTokenCutSlackSelectionGoal.{uX, uC} := by
  classical
  intro X C _instX _instC _decX _decC I M hHall
  rcases hQuota I M hHall with ⟨f, hfActive, hSingleton, hPair⟩
  refine ⟨f, hfActive, ?_, ?_⟩
  · intro U σ hUne hUuniv
    rw [M.cutSlack_image_castSucc_singleton U σ]
    exact hSingleton U σ hUne hUuniv
  · intro U σ τ hστ hUne hUuniv
    rw [M.cutSlack_image_castSucc_pair_eq_min_two U hστ]
    exact hPair U σ τ hστ hUne hUuniv

theorem eraseLastHallCutsFourSmallTokenCutSlackSelectionGoal_of_singletonPair
    (hSP :
      EraseLastHallCutsFourSingletonPairTokenCutSlackSelectionGoal.{uX, uC}) :
    EraseLastHallCutsFourSmallTokenCutSlackSelectionGoal.{uX, uC} := by
  classical
  intro X C _instX _instC _decX _decC I M hHall
  rcases hSP I M hHall with ⟨f, hfActive, hSingleton, hPair⟩
  refine ⟨f, hfActive, ?_⟩
  intro U S hUne hUuniv hSne hScard
  have hSpos : 0 < S.card := hSne.card_pos
  have hcases : S.card = 1 ∨ S.card = 2 := by omega
  rcases hcases with hSone | hStwo
  · rcases Finset.card_eq_one.mp hSone with ⟨σ, rfl⟩
    exact hSingleton U σ hUne hUuniv
  · rcases Finset.card_eq_two.mp hStwo with ⟨σ, τ, hστ, rfl⟩
    exact hPair U σ τ hστ hUne hUuniv

theorem eraseLastHallCutsFourTokenCutSlackSelectionGoal_of_small
    (hSmall :
      EraseLastHallCutsFourSmallTokenCutSlackSelectionGoal.{uX, uC}) :
    EraseLastHallCutsFourTokenCutSlackSelectionGoal.{uX, uC} := by
  classical
  intro X C _instX _instC _decX _decC I M hHall
  rcases hSmall I M hHall with ⟨f, hfActive, hSlackSmall⟩
  refine ⟨f, hfActive, ?_⟩
  intro U S hUne hUuniv hSne
  by_cases hSsmall : S.card ≤ 2
  · exact hSlackSmall U S hUne hUuniv hSne hSsmall
  · have hScard_le : S.card ≤ 3 := by
      simpa [Fintype.card_fin] using Finset.card_le_univ S
    have hScard : S.card = 3 := by omega
    have hSuniv : S = (Finset.univ : Finset (Fin 3)) := by
      exact Finset.eq_univ_of_card S (by
        simpa [Fintype.card_fin] using hScard)
    subst S
    let choice : X → C := fun x => (f.symm x).1
    have hchoice : ∀ x : X, choice x ∈ I.active x := by
      intro x
      have h := hfActive (f.symm x)
      rw [f.apply_symm_apply] at h
      simpa [choice] using h
    have hdegree :
        ∀ c : C, Incidence.choiceDegree choice c = M.val c (Fin.last 3) :=
      fun c => M.choiceDegree_of_bijective_token_matching (Fin.last 3) f c
    have hlow :
        Incidence.choiceLowHitCount I choice U
            (Finset.univ : Finset (Fin 3))
          ≤ M.cutSlack U
              ((Finset.univ : Finset (Fin 3)).image
                (Fin.castSucc : Fin 3 → Fin 4)) :=
      M.choiceLowHitCount_univ_le_cutSlack_image_castSucc
        choice hchoice hdegree hHall U
    have hload :
        Incidence.tokenLoadOn f
            (Incidence.lowCutSet I U (Finset.univ : Finset (Fin 3))) U =
          Incidence.choiceLowHitCount I choice U
            (Finset.univ : Finset (Fin 3)) := by
      rw [Incidence.choiceLowHitCount_eq_choiceHitCountOn_lowCutSet,
        ← Incidence.tokenLoadOn_eq_choiceHitCountOn]
    rw [hload]
    exact hlow

theorem eraseLastHallCutsFourGoal_of_tokenCutSlackSelection
    (hToken : EraseLastHallCutsFourTokenCutSlackSelectionGoal.{uX, uC}) :
    EraseLastHallCutsFourGoal.{uX, uC} := by
  classical
  intro X C _instX _instC _decX _decC I M hHall
  rcases hToken I M hHall with ⟨f, hfActive, hSlack⟩
  let choice : X → C := fun x => (f.symm x).1
  have hchoice : ∀ x : X, choice x ∈ I.active x := by
    intro x
    have h := hfActive (f.symm x)
    rw [f.apply_symm_apply] at h
    simpa [choice] using h
  have hdegree :
      ∀ c : C, Incidence.choiceDegree choice c = M.val c (Fin.last 3) :=
    fun c => M.choiceDegree_of_bijective_token_matching (Fin.last 3) f c
  refine ⟨f, hfActive, ?_⟩
  dsimp only
  change (M.eraseLastCountMatrix choice hchoice hdegree).HallCuts
  apply M.eraseLastCountMatrix_hallCuts_of_cutSlack choice hchoice hdegree hHall
  intro U S
  by_cases hUempty : U = ∅
  · subst U
    rw [Incidence.choiceLowHitCount_colors_empty]
    exact Nat.zero_le _
  by_cases hUuniv : U = (Finset.univ : Finset C)
  · subst U
    rw [Incidence.choiceLowHitCount_colors_univ]
    exact Nat.zero_le _
  by_cases hSempty : S = ∅
  · subst S
    rw [Incidence.choiceLowHitCount_symbols_empty I choice hchoice U]
    exact Nat.zero_le _
  have hlow :
      Incidence.choiceLowHitCount I choice U S
        =
      Incidence.tokenLoadOn f (Incidence.lowCutSet I U S) U := by
    rw [Incidence.choiceLowHitCount_eq_choiceHitCountOn_lowCutSet,
      ← Incidence.tokenLoadOn_eq_choiceHitCountOn]
  rw [hlow]
  exact hSlack U S
    (Finset.nonempty_iff_ne_empty.mpr hUempty) hUuniv
    (Finset.nonempty_iff_ne_empty.mpr hSempty)

theorem hallRealization_four_of_eraseLastHallCutsFourGoal
    (hFour : EraseLastHallCutsFourGoal.{uX, uC})
    (hToken : EraseLastHallCutsTwoSingletonTokenCutSlackSelectionGoal.{uX, uC})
    {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence 4 X C) (M : CountMatrix I)
    (hHall : M.HallCuts) :
    ∃ Φ : Symboling I, Φ.Realizes M.val :=
  hallRealization_four_of_eraseLastHallCuts_and_singletonTokenCutSlackSelection
    hToken I M (hFour I M hHall)

theorem hallRealization_four_of_fourTokenCutSlackSelection
    (hFourToken :
      EraseLastHallCutsFourTokenCutSlackSelectionGoal.{uX, uC})
    (hToken : EraseLastHallCutsTwoSingletonTokenCutSlackSelectionGoal.{uX, uC})
    {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence 4 X C) (M : CountMatrix I)
    (hHall : M.HallCuts) :
    ∃ Φ : Symboling I, Φ.Realizes M.val :=
  hallRealization_four_of_eraseLastHallCutsFourGoal
    (eraseLastHallCutsFourGoal_of_tokenCutSlackSelection hFourToken)
    hToken I M hHall

theorem hallRealization_four_of_fourSmallTokenCutSlackSelection
    (hFourSmall :
      EraseLastHallCutsFourSmallTokenCutSlackSelectionGoal.{uX, uC})
    (hToken : EraseLastHallCutsTwoSingletonTokenCutSlackSelectionGoal.{uX, uC})
    {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence 4 X C) (M : CountMatrix I)
    (hHall : M.HallCuts) :
    ∃ Φ : Symboling I, Φ.Realizes M.val :=
  hallRealization_four_of_fourTokenCutSlackSelection
    (eraseLastHallCutsFourTokenCutSlackSelectionGoal_of_small hFourSmall)
    hToken I M hHall

theorem hallRealization_four_of_fourSingletonPairTokenCutSlackSelection
    (hFourSP :
      EraseLastHallCutsFourSingletonPairTokenCutSlackSelectionGoal.{uX, uC})
    (hToken : EraseLastHallCutsTwoSingletonTokenCutSlackSelectionGoal.{uX, uC})
    {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence 4 X C) (M : CountMatrix I)
    (hHall : M.HallCuts) :
    ∃ Φ : Symboling I, Φ.Realizes M.val :=
  hallRealization_four_of_fourSmallTokenCutSlackSelection
    (eraseLastHallCutsFourSmallTokenCutSlackSelectionGoal_of_singletonPair
      hFourSP)
    hToken I M hHall

theorem hallRealization_four_of_fourSingletonPairTokenQuotaSelection
    (hFourQuota :
      EraseLastHallCutsFourSingletonPairTokenQuotaSelectionGoal.{uX, uC})
    (hToken : EraseLastHallCutsTwoSingletonTokenCutSlackSelectionGoal.{uX, uC})
    {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    (I : Incidence 4 X C) (M : CountMatrix I)
    (hHall : M.HallCuts) :
    ∃ Φ : Symboling I, Φ.Realizes M.val :=
  hallRealization_four_of_fourSingletonPairTokenCutSlackSelection
    (eraseLastHallCutsFourSingletonPairTokenCutSlackSelectionGoal_of_quota
      hFourQuota)
    hToken I M hHall

theorem hallRealizationGoal_of_eraseLastHallCuts
    (hErase : EraseLastHallCutsGoal.{uX, uC}) :
    HallRealizationGoal.{uX, uC} := by
  intro T
  induction T with
  | zero =>
      intro X C _instX _instC _decX _decC I M _hHall
      exact hallRealization_zero I M
  | succ T ih =>
      intro X C _instX _instC _decX _decC I M hHall
      exact hallRealization_succ_of_eraseLastHallCuts I M
        (hErase I M hHall) ih

theorem hallRealizationGoal_of_eraseLastHallCutsSelection
    (hSelect : EraseLastHallCutsSelectionGoal.{uX, uC}) :
    HallRealizationGoal.{uX, uC} :=
  hallRealizationGoal_of_eraseLastHallCuts
    (eraseLastHallCutsGoal_of_selection hSelect)

theorem hallRealizationGoal_of_eraseLastHallCutsChoice
    (hChoice : EraseLastHallCutsChoiceGoal.{uX, uC}) :
    HallRealizationGoal.{uX, uC} :=
  hallRealizationGoal_of_eraseLastHallCuts
    (eraseLastHallCutsGoal_of_choice hChoice)

theorem hallRealizationGoal_of_eraseLastHallCutsSlackChoice
    (hSlackChoice : EraseLastHallCutsSlackChoiceGoal.{uX, uC}) :
    HallRealizationGoal.{uX, uC} :=
  hallRealizationGoal_of_eraseLastHallCutsChoice
    (eraseLastHallCutsChoiceGoal_of_slackChoice hSlackChoice)

theorem hallRealizationGoal_of_eraseLastHallCutsNontrivialSlackChoice
    (hNontriv : EraseLastHallCutsNontrivialSlackChoiceGoal.{uX, uC}) :
    HallRealizationGoal.{uX, uC} :=
  hallRealizationGoal_of_eraseLastHallCutsSlackChoice
    (eraseLastHallCutsSlackChoiceGoal_of_nontrivial hNontriv)

theorem hallRealizationGoal_of_eraseLastHallCutsLinearChoice
    (hLinear : EraseLastHallCutsLinearChoiceGoal.{uX, uC}) :
    HallRealizationGoal.{uX, uC} :=
  hallRealizationGoal_of_eraseLastHallCutsNontrivialSlackChoice
    (eraseLastHallCutsNontrivialSlackChoiceGoal_of_linear hLinear)

theorem hallRealizationGoal_of_eraseLastHallCutsTokenLinearChoice
    (hToken : EraseLastHallCutsTokenLinearChoiceGoal.{uX, uC}) :
    HallRealizationGoal.{uX, uC} :=
  hallRealizationGoal_of_eraseLastHallCutsLinearChoice
    (eraseLastHallCutsLinearChoiceGoal_of_tokenLinear hToken)

theorem hallRealizationGoal_of_eraseLastHallCutsProperTokenLinearChoice
    (hProper : EraseLastHallCutsProperTokenLinearChoiceGoal.{uX, uC}) :
    HallRealizationGoal.{uX, uC} :=
  hallRealizationGoal_of_eraseLastHallCutsTokenLinearChoice
    (eraseLastHallCutsTokenLinearChoiceGoal_of_proper hProper)

theorem eraseLastHallCutsProperTokenQuotaSelectionGoal_of_hallRealization
    (hRealize : HallRealizationGoal.{uX, uC}) :
    EraseLastHallCutsProperTokenQuotaSelectionGoal.{uX, uC} := by
  classical
  intro T X C _instX _instC _decX _decC I M hHall
  rcases eraseLastHallCutsTokenLinearChoiceGoal_of_hallRealization
      hRealize I M hHall with
    ⟨f, hfActive, hSlack⟩
  refine ⟨f, hfActive, ?_⟩
  intro U S hUne hUuniv hSne _hSuniv
  rw [← M.cutSlack_image_castSucc U S]
  exact hSlack U S hUne hUuniv hSne

theorem hallRealizationGoal_of_eraseLastHallCutsProperTokenQuotaSelection
    (hQuota : EraseLastHallCutsProperTokenQuotaSelectionGoal.{uX, uC}) :
    HallRealizationGoal.{uX, uC} :=
  hallRealizationGoal_of_eraseLastHallCutsProperTokenLinearChoice
    (eraseLastHallCutsProperTokenLinearChoiceGoal_of_quota hQuota)

theorem hallRealizationGoal_iff_eraseLastHallCutsTokenLinearChoiceGoal :
    HallRealizationGoal.{uX, uC} ↔
      EraseLastHallCutsTokenLinearChoiceGoal.{uX, uC} :=
  ⟨eraseLastHallCutsTokenLinearChoiceGoal_of_hallRealization,
    hallRealizationGoal_of_eraseLastHallCutsTokenLinearChoice⟩

theorem hallRealizationGoal_iff_eraseLastHallCutsProperTokenLinearChoiceGoal :
    HallRealizationGoal.{uX, uC} ↔
      EraseLastHallCutsProperTokenLinearChoiceGoal.{uX, uC} := by
  constructor
  · intro hRealize
    have hToken : EraseLastHallCutsTokenLinearChoiceGoal.{uX, uC} :=
      eraseLastHallCutsTokenLinearChoiceGoal_of_hallRealization hRealize
    intro T X C _instX _instC _decX _decC I M hHall
    rcases hToken I M hHall with ⟨f, hfActive, hSlack⟩
    exact ⟨f, hfActive, fun U S hUne hUuniv hSne _hSuniv =>
      hSlack U S hUne hUuniv hSne⟩
  · exact hallRealizationGoal_of_eraseLastHallCutsProperTokenLinearChoice

theorem hallRealizationGoal_iff_eraseLastHallCutsProperTokenQuotaSelectionGoal :
    HallRealizationGoal.{uX, uC} ↔
      EraseLastHallCutsProperTokenQuotaSelectionGoal.{uX, uC} :=
  ⟨eraseLastHallCutsProperTokenQuotaSelectionGoal_of_hallRealization,
    hallRealizationGoal_of_eraseLastHallCutsProperTokenQuotaSelection⟩

theorem hallRealizationGoal_iff_eraseLastHallCutsGoal :
    HallRealizationGoal.{uX, uC} ↔
      EraseLastHallCutsGoal.{uX, uC} :=
  ⟨fun hRealize =>
      eraseLastHallCutsGoal_of_tokenLinearChoice
        (eraseLastHallCutsTokenLinearChoiceGoal_of_hallRealization hRealize),
    hallRealizationGoal_of_eraseLastHallCuts⟩

theorem hallRealizationGoal_iff_eraseLastHallCutsSelectionGoal :
    HallRealizationGoal.{uX, uC} ↔
      EraseLastHallCutsSelectionGoal.{uX, uC} :=
  ⟨fun hRealize =>
      eraseLastHallCutsSelectionGoal_of_choice
        (eraseLastHallCutsChoiceGoal_of_slackChoice
          (eraseLastHallCutsSlackChoiceGoal_of_nontrivial
            (eraseLastHallCutsNontrivialSlackChoiceGoal_of_linear
              (eraseLastHallCutsLinearChoiceGoal_of_tokenLinear
                (eraseLastHallCutsTokenLinearChoiceGoal_of_hallRealization
                  hRealize))))),
    hallRealizationGoal_of_eraseLastHallCutsSelection⟩

theorem eraseLastHallCutsSelectionGoal_iff_tokenLinearChoiceGoal :
    EraseLastHallCutsSelectionGoal.{uX, uC} ↔
      EraseLastHallCutsTokenLinearChoiceGoal.{uX, uC} :=
  ⟨eraseLastHallCutsTokenLinearChoiceGoal_of_selection,
    fun hToken =>
      (hallRealizationGoal_iff_eraseLastHallCutsSelectionGoal).1
        (hallRealizationGoal_of_eraseLastHallCutsTokenLinearChoice hToken)⟩

theorem hallRealizationGoal_iff_eraseLastHallCutsChoiceGoal :
    HallRealizationGoal.{uX, uC} ↔
      EraseLastHallCutsChoiceGoal.{uX, uC} :=
  ⟨fun hRealize =>
      eraseLastHallCutsChoiceGoal_of_slackChoice
        (eraseLastHallCutsSlackChoiceGoal_of_nontrivial
          (eraseLastHallCutsNontrivialSlackChoiceGoal_of_linear
            (eraseLastHallCutsLinearChoiceGoal_of_tokenLinear
              (eraseLastHallCutsTokenLinearChoiceGoal_of_hallRealization
                hRealize)))),
    hallRealizationGoal_of_eraseLastHallCutsChoice⟩

theorem hallRealizationGoal_iff_eraseLastHallCutsSlackChoiceGoal :
    HallRealizationGoal.{uX, uC} ↔
      EraseLastHallCutsSlackChoiceGoal.{uX, uC} :=
  ⟨fun hRealize =>
      eraseLastHallCutsSlackChoiceGoal_of_nontrivial
        (eraseLastHallCutsNontrivialSlackChoiceGoal_of_linear
          (eraseLastHallCutsLinearChoiceGoal_of_tokenLinear
            (eraseLastHallCutsTokenLinearChoiceGoal_of_hallRealization
              hRealize))),
    hallRealizationGoal_of_eraseLastHallCutsSlackChoice⟩

theorem hallRealizationGoal_iff_eraseLastHallCutsNontrivialSlackChoiceGoal :
    HallRealizationGoal.{uX, uC} ↔
      EraseLastHallCutsNontrivialSlackChoiceGoal.{uX, uC} :=
  ⟨fun hRealize =>
      eraseLastHallCutsNontrivialSlackChoiceGoal_of_linear
        (eraseLastHallCutsLinearChoiceGoal_of_tokenLinear
          (eraseLastHallCutsTokenLinearChoiceGoal_of_hallRealization hRealize)),
    hallRealizationGoal_of_eraseLastHallCutsNontrivialSlackChoice⟩

theorem hallRealizationGoal_iff_eraseLastHallCutsLinearChoiceGoal :
    HallRealizationGoal.{uX, uC} ↔
      EraseLastHallCutsLinearChoiceGoal.{uX, uC} :=
  ⟨fun hRealize =>
      eraseLastHallCutsLinearChoiceGoal_of_tokenLinear
        (eraseLastHallCutsTokenLinearChoiceGoal_of_hallRealization hRealize),
    hallRealizationGoal_of_eraseLastHallCutsLinearChoice⟩

theorem eraseLastHallCutsTokenLinearChoiceGoal_of_hoffmanOrderedSDR
    (hHoffman : HoffmanOrderedSDRGoal.{uX, uC}) :
    EraseLastHallCutsTokenLinearChoiceGoal.{uX, uC} :=
  eraseLastHallCutsTokenLinearChoiceGoal_of_hallRealization
    (hallRealizationGoal_of_hoffmanOrderedSDR hHoffman)

theorem symbolingWithResidues_of_feasible_and_realization
    (hRealize : HallRealizationGoal.{uX, uC})
    {m T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C}
    (hFeasible : FeasibleWithResidues I R) :
    SymbolingWithResidues I R := by
  rcases hFeasible with ⟨M, hHall, hResidues⟩
  rcases @hRealize T X C _ _ _ _ I M hHall with ⟨Φ, hRealizes⟩
  exact ⟨Φ, Φ.hasResidues_of_realizes hRealizes hResidues⟩

theorem symbolingWithResidues_of_feasible_and_eraseLastHallCuts
    (hErase : EraseLastHallCutsGoal.{uX, uC})
    {m T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C}
    (hFeasible : FeasibleWithResidues I R) :
    SymbolingWithResidues I R :=
  symbolingWithResidues_of_feasible_and_realization
    (hallRealizationGoal_of_eraseLastHallCuts hErase) hFeasible

theorem symbolingWithResidues_of_feasible_and_eraseLastHallCutsSelection
    (hSelect : EraseLastHallCutsSelectionGoal.{uX, uC})
    {m T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C}
    (hFeasible : FeasibleWithResidues I R) :
    SymbolingWithResidues I R :=
  symbolingWithResidues_of_feasible_and_realization
    (hallRealizationGoal_of_eraseLastHallCutsSelection hSelect)
    hFeasible

theorem symbolingWithResidues_of_feasible_and_hoffmanOrderedSDR
    (hHoffman : HoffmanOrderedSDRGoal.{uX, uC})
    {m T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C}
    (hFeasible : FeasibleWithResidues I R) :
    SymbolingWithResidues I R :=
  symbolingWithResidues_of_feasible_and_realization
    (hallRealizationGoal_of_hoffmanOrderedSDR hHoffman) hFeasible

theorem symbolingWithResidues_of_feasible_and_columnFillingUpgrade
    (hUpgrade : ColumnFillingUpgradeGoal.{uX, uC})
    {m T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C}
    (hFeasible : FeasibleWithResidues I R) :
    SymbolingWithResidues I R :=
  symbolingWithResidues_of_feasible_and_realization
    (hallRealizationGoal_of_columnFillingUpgrade hUpgrade) hFeasible

theorem symbolingWithResidues_of_feasible_and_eraseLastHallCutsChoice
    (hChoice : EraseLastHallCutsChoiceGoal.{uX, uC})
    {m T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C}
    (hFeasible : FeasibleWithResidues I R) :
    SymbolingWithResidues I R :=
  symbolingWithResidues_of_feasible_and_realization
    (hallRealizationGoal_of_eraseLastHallCutsChoice hChoice) hFeasible

theorem symbolingWithResidues_of_feasible_and_eraseLastHallCutsSlackChoice
    (hSlackChoice : EraseLastHallCutsSlackChoiceGoal.{uX, uC})
    {m T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C}
    (hFeasible : FeasibleWithResidues I R) :
    SymbolingWithResidues I R :=
  symbolingWithResidues_of_feasible_and_realization
    (hallRealizationGoal_of_eraseLastHallCutsSlackChoice hSlackChoice)
    hFeasible

theorem symbolingWithResidues_of_feasible_and_eraseLastHallCutsNontrivialSlackChoice
    (hNontriv : EraseLastHallCutsNontrivialSlackChoiceGoal.{uX, uC})
    {m T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C}
    (hFeasible : FeasibleWithResidues I R) :
    SymbolingWithResidues I R :=
  symbolingWithResidues_of_feasible_and_realization
    (hallRealizationGoal_of_eraseLastHallCutsNontrivialSlackChoice hNontriv)
    hFeasible

theorem symbolingWithResidues_of_feasible_and_eraseLastHallCutsLinearChoice
    (hLinear : EraseLastHallCutsLinearChoiceGoal.{uX, uC})
    {m T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C}
    (hFeasible : FeasibleWithResidues I R) :
    SymbolingWithResidues I R :=
  symbolingWithResidues_of_feasible_and_realization
    (hallRealizationGoal_of_eraseLastHallCutsLinearChoice hLinear)
    hFeasible

theorem symbolingWithResidues_of_feasible_and_eraseLastHallCutsTokenLinearChoice
    (hToken : EraseLastHallCutsTokenLinearChoiceGoal.{uX, uC})
    {m T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C}
    (hFeasible : FeasibleWithResidues I R) :
    SymbolingWithResidues I R :=
  symbolingWithResidues_of_feasible_and_realization
    (hallRealizationGoal_of_eraseLastHallCutsTokenLinearChoice hToken)
    hFeasible

theorem symbolingWithResidues_of_feasible_and_eraseLastHallCutsProperTokenLinearChoice
    (hProper : EraseLastHallCutsProperTokenLinearChoiceGoal.{uX, uC})
    {m T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C}
    (hFeasible : FeasibleWithResidues I R) :
    SymbolingWithResidues I R :=
  symbolingWithResidues_of_feasible_and_realization
    (hallRealizationGoal_of_eraseLastHallCutsProperTokenLinearChoice hProper)
    hFeasible

theorem feasibleWithResidues_of_symbolingWithResidues
    {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C}
    (hSymboling : SymbolingWithResidues I R) :
    FeasibleWithResidues I R := by
  rcases hSymboling with ⟨Φ, hResidues⟩
  exact ⟨Φ.toCountMatrix, Φ.toCountMatrix_hallCuts, hResidues⟩

theorem symbolingWithResidues_iff_feasible_of_realization
    (hRealize : HallRealizationGoal.{uX, uC})
    {m T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C} :
    SymbolingWithResidues I R ↔ FeasibleWithResidues I R :=
  ⟨feasibleWithResidues_of_symbolingWithResidues,
    symbolingWithResidues_of_feasible_and_realization hRealize⟩

theorem symbolingWithResidues_iff_feasible_of_hoffmanOrderedSDR
    (hHoffman : HoffmanOrderedSDRGoal.{uX, uC})
    {m T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C} :
    SymbolingWithResidues I R ↔ FeasibleWithResidues I R :=
  symbolingWithResidues_iff_feasible_of_realization
    (hallRealizationGoal_of_hoffmanOrderedSDR hHoffman)

theorem symbolingWithResidues_iff_feasible_of_columnFillingUpgrade
    (hUpgrade : ColumnFillingUpgradeGoal.{uX, uC})
    {m T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C} :
    SymbolingWithResidues I R ↔ FeasibleWithResidues I R :=
  symbolingWithResidues_iff_feasible_of_realization
    (hallRealizationGoal_of_columnFillingUpgrade hUpgrade)

theorem symbolingWithResidues_iff_feasible_of_eraseLastHallCutsSelection
    (hSelect : EraseLastHallCutsSelectionGoal.{uX, uC})
    {m T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C} :
    SymbolingWithResidues I R ↔ FeasibleWithResidues I R :=
  symbolingWithResidues_iff_feasible_of_realization
    (hallRealizationGoal_of_eraseLastHallCutsSelection hSelect)

theorem symbolingWithResidues_iff_feasible_of_eraseLastHallCuts
    (hErase : EraseLastHallCutsGoal.{uX, uC})
    {m T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C} :
    SymbolingWithResidues I R ↔ FeasibleWithResidues I R :=
  symbolingWithResidues_iff_feasible_of_realization
    (hallRealizationGoal_of_eraseLastHallCuts hErase)

theorem symbolingWithResidues_iff_feasible_of_eraseLastHallCutsChoice
    (hChoice : EraseLastHallCutsChoiceGoal.{uX, uC})
    {m T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C} :
    SymbolingWithResidues I R ↔ FeasibleWithResidues I R :=
  symbolingWithResidues_iff_feasible_of_realization
    (hallRealizationGoal_of_eraseLastHallCutsChoice hChoice)

theorem symbolingWithResidues_iff_feasible_of_eraseLastHallCutsSlackChoice
    (hSlackChoice : EraseLastHallCutsSlackChoiceGoal.{uX, uC})
    {m T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C} :
    SymbolingWithResidues I R ↔ FeasibleWithResidues I R :=
  symbolingWithResidues_iff_feasible_of_realization
    (hallRealizationGoal_of_eraseLastHallCutsSlackChoice hSlackChoice)

theorem symbolingWithResidues_iff_feasible_of_eraseLastHallCutsNontrivialSlackChoice
    (hNontriv : EraseLastHallCutsNontrivialSlackChoiceGoal.{uX, uC})
    {m T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C} :
    SymbolingWithResidues I R ↔ FeasibleWithResidues I R :=
  symbolingWithResidues_iff_feasible_of_realization
    (hallRealizationGoal_of_eraseLastHallCutsNontrivialSlackChoice hNontriv)

theorem symbolingWithResidues_iff_feasible_of_eraseLastHallCutsLinearChoice
    (hLinear : EraseLastHallCutsLinearChoiceGoal.{uX, uC})
    {m T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C} :
    SymbolingWithResidues I R ↔ FeasibleWithResidues I R :=
  symbolingWithResidues_iff_feasible_of_realization
    (hallRealizationGoal_of_eraseLastHallCutsLinearChoice hLinear)

theorem symbolingWithResidues_iff_feasible_of_eraseLastHallCutsTokenLinearChoice
    (hToken : EraseLastHallCutsTokenLinearChoiceGoal.{uX, uC})
    {m T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C} :
    SymbolingWithResidues I R ↔ FeasibleWithResidues I R :=
  symbolingWithResidues_iff_feasible_of_realization
    (hallRealizationGoal_of_eraseLastHallCutsTokenLinearChoice hToken)

theorem symbolingWithResidues_iff_feasible_of_eraseLastHallCutsProperTokenLinearChoice
    (hProper : EraseLastHallCutsProperTokenLinearChoiceGoal.{uX, uC})
    {m T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C} :
    SymbolingWithResidues I R ↔ FeasibleWithResidues I R :=
  symbolingWithResidues_iff_feasible_of_realization
    (hallRealizationGoal_of_eraseLastHallCutsProperTokenLinearChoice hProper)

namespace SymbolingWithResidues

theorem feasible {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C}
    (hSymboling : SymbolingWithResidues I R) :
    FeasibleWithResidues I R :=
  feasibleWithResidues_of_symbolingWithResidues hSymboling

theorem rowCompatible {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C}
    (hSymboling : SymbolingWithResidues I R) :
    R.RowCompatible I :=
  hSymboling.feasible.rowCompatible

theorem colCompatible {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C}
    (hSymboling : SymbolingWithResidues I R) :
    R.ColCompatible I :=
  hSymboling.feasible.colCompatible

theorem compatible {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C}
    (hSymboling : SymbolingWithResidues I R) :
    R.RowCompatible I ∧ R.ColCompatible I :=
  hSymboling.feasible.compatible

end SymbolingWithResidues

end ActiveHall
end RoundComposite
