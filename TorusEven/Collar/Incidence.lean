-- STATUS: main-path
import Mathlib

namespace TorusEven.Collar.Incidence

variable {B Ω : Type*} (A : B → Finset Ω)

def Adjacent (x y : Ω) : Prop := ∃ b, x ∈ A b ∧ y ∈ A b

abbrev Component := Quotient (Relation.EqvGen.setoid (Adjacent A))

def componentOf (x : Ω) : Component A := Quotient.mk _ x

@[simp] theorem componentOf_eq (x y : Ω) :
    componentOf A x = componentOf A y ↔ Relation.EqvGen (Adjacent A) x y := Quotient.eq

def EvenComponents : Prop := ∀ q : Component A, Even (Nat.card {x // componentOf A x = q})

theorem same_component {b : B} {x y : Ω} (hx : x ∈ A b) (hy : y ∈ A b) :
    componentOf A x = componentOf A y := Quotient.sound (Relation.EqvGen.rel _ _ ⟨b, hx, hy⟩)

theorem evenComponents_of_universal_block [Fintype Ω] (b : B) (hb : ∀ x, x ∈ A b)
    (hcard : Even (Fintype.card Ω)) : EvenComponents A := by
  intro q
  induction q using Quotient.inductionOn with | _ x =>
    have h (y : Ω) := same_component A (hb y) (hb x)
    have hc : Nat.card {y // componentOf A y = componentOf A x} = Fintype.card Ω :=
      (Nat.card_congr (Equiv.subtypeUnivEquiv h)).trans Nat.card_eq_fintype_card
    exact hc.symm ▸ hcard

noncomputable def blockComponent (hne : ∀ b, (A b).Nonempty) (b : B) : Component A :=
  componentOf A (hne b).choose

theorem component_eq_block (hne : ∀ b, (A b).Nonempty) {b : B} {x : Ω} (hx : x ∈ A b) :
    componentOf A x = blockComponent A hne b := same_component A hx (hne b).choose_spec

variable {R : Type*}

def Coherent (J : R → Finset Ω) : Prop :=
  ∀ r s, Relation.EqvGen (fun r s => ∃ x, x ∈ J r ∧ x ∈ J s) r s

theorem coherent_blockComponent (J : B → R → Finset Ω)
    (hne : ∀ p : B × R, (J p.1 p.2).Nonempty) (hc : ∀ b, Coherent (J b))
    (b : B) (r s : R) :
    blockComponent (fun p : B × R => J p.1 p.2) hne (b, r) =
      blockComponent (fun p : B × R => J p.1 p.2) hne (b, s) := by
  induction hc b r s with
  | rel r s hrs =>
    obtain ⟨x, hx, hx'⟩ := hrs
    exact (component_eq_block _ hne hx).symm.trans (component_eq_block _ hne hx')
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

theorem copied_component_iff [Nonempty R] (x y : Ω) :
    componentOf A x = componentOf A y ↔
      componentOf (fun p : B × R => A p.1) x = componentOf (fun p : B × R => A p.1) y := by
  rw [componentOf_eq, componentOf_eq]
  constructor
  · apply Relation.EqvGen.mono
    rintro x y ⟨b, hx, hy⟩
    exact ⟨(b, Classical.choice ‹Nonempty R›), hx, hy⟩
  · apply Relation.EqvGen.mono
    rintro x y ⟨p, hx, hy⟩
    exact ⟨p.1, hx, hy⟩

theorem evenComponents_copied [Nonempty R] (h : EvenComponents A) :
    EvenComponents (fun p : B × R => A p.1) := by
  intro q
  induction q using Quotient.inductionOn with | _ x =>
    let e : {y // componentOf A y = componentOf A x} ≃
        {y // componentOf (fun p : B × R => A p.1) y =
          componentOf (fun p : B × R => A p.1) x} :=
      Equiv.subtypeEquivRight (fun y => copied_component_iff A y x)
    exact (Nat.card_congr e) ▸ h (componentOf A x)

end TorusEven.Collar.Incidence
