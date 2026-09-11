-- STATUS: main-path
import TorusEven.Collar.Incidence

namespace TorusEven.Collar.Incidence

variable {B B' Ω Ω' : Type*} {A : B → Finset Ω} {A' : B' → Finset Ω'}

theorem component_map (f : B → B') (g : Ω → Ω')
    (hmem : ∀ b x, x ∈ A b → g x ∈ A' (f b)) {x y : Ω}
    (h : componentOf A x = componentOf A y) : componentOf A' (g x) = componentOf A' (g y) := by
  rw [componentOf_eq] at h ⊢
  induction h with
  | rel x y h =>
    obtain ⟨b, hx, hy⟩ := h
    exact Relation.EqvGen.rel _ _ ⟨f b, hmem b x hx, hmem b y hy⟩
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'

theorem component_reindex_iff (f : B ≃ B') (g : Ω ≃ Ω')
    (hmem : ∀ b x, x ∈ A b ↔ g x ∈ A' (f b)) (x y : Ω) :
    componentOf A x = componentOf A y ↔ componentOf A' (g x) = componentOf A' (g y) := by
  constructor
  · exact component_map f g (fun b x => (hmem b x).mp)
  · intro h
    have hi (b : B') (x : Ω') : x ∈ A' b → g.symm x ∈ A (f.symm b) := by
      simpa using (hmem (f.symm b) (g.symm x)).mpr
    simpa using component_map f.symm g.symm hi h

theorem evenComponents_reindex (f : B ≃ B') (g : Ω ≃ Ω')
    (hmem : ∀ b x, x ∈ A b ↔ g x ∈ A' (f b)) (h : EvenComponents A) : EvenComponents A' := by
  intro q
  induction q using Quotient.inductionOn with | _ y =>
    let e : {x // componentOf A x = componentOf A (g.symm y)} ≃
        {x // componentOf A' x = componentOf A' y} :=
      Equiv.subtypeEquiv g (fun x => by simpa using component_reindex_iff f g hmem x (g.symm y))
    exact (Nat.card_congr e) ▸ h (componentOf A (g.symm y))

end TorusEven.Collar.Incidence
