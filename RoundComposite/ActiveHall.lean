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

def count {T : Nat} {X C : Type*} [Fintype X] [Fintype C]
    [DecidableEq X] [DecidableEq C] {I : Incidence T X C}
    (Φ : Symboling I) (c : C) (σ : Fin T) : Nat :=
  ∑ x : X, if Φ.color x σ = c then 1 else 0

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

universe uX uC

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
    simpa [choice] using hfActive (f.symm x)
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
    simpa [choice] using hfActive (f.symm x)
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
      rcases hErase I M hHall with ⟨f, hfActive, hReducedHall⟩
      let choice : X → C := fun x => (f.symm x).1
      have hchoice : ∀ x : X, choice x ∈ I.active x := by
        intro x
        simpa [choice] using hfActive (f.symm x)
      have hdegree :
          ∀ c : C,
            Incidence.choiceDegree choice c = M.val c (Fin.last T) :=
        fun c => M.choiceDegree_of_bijective_token_matching
          (Fin.last T) f c
      rcases ih (I.eraseChoice choice hchoice)
          (M.eraseLastCountMatrix choice hchoice hdegree)
          hReducedHall with ⟨Φ, hReal⟩
      exact ⟨Φ.extendLast choice hchoice,
        Φ.extendLast_realizes_eraseLastCountMatrix M choice hchoice hdegree hReal⟩

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

theorem hallRealizationGoal_iff_eraseLastHallCutsTokenLinearChoiceGoal :
    HallRealizationGoal.{uX, uC} ↔
      EraseLastHallCutsTokenLinearChoiceGoal.{uX, uC} :=
  ⟨eraseLastHallCutsTokenLinearChoiceGoal_of_hallRealization,
    hallRealizationGoal_of_eraseLastHallCutsTokenLinearChoice⟩

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
