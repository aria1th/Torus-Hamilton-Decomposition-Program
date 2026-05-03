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

def HasResidues {m T : Nat} {X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C]
    {I : Incidence T X C} (M : CountMatrix I)
    (R : ResidueSpec m T C) : Prop :=
  ∀ c σ, (M.val c σ : ZMod m) = R.target c σ

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

end Symboling

end ActiveHall
end RoundComposite
