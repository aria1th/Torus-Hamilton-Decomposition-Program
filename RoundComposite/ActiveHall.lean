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

def cutCap {T : Nat} {X C : Type*} [Fintype X] [Fintype C]
    [DecidableEq X] [DecidableEq C] (I : Incidence T X C)
    (U : Finset C) (S : Finset (Fin T)) : Nat :=
  ∑ x : X, min ((I.active x ∩ U).card) S.card

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

def count {T : Nat} {X C : Type*} [Fintype X] [Fintype C]
    [DecidableEq X] [DecidableEq C] {I : Incidence T X C}
    (Φ : Symboling I) (c : C) (σ : Fin T) : Nat :=
  ∑ x : X, if Φ.color x σ = c then 1 else 0

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

theorem feasibleWithResidues_of_symbolingWithResidues
    {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} {R : ResidueSpec m T C}
    (hSymboling : SymbolingWithResidues I R) :
    FeasibleWithResidues I R := by
  rcases hSymboling with ⟨Φ, hResidues⟩
  exact ⟨Φ.toCountMatrix, Φ.toCountMatrix_hallCuts, hResidues⟩

end ActiveHall
end RoundComposite
