-- STATUS: main-path
import TorusEven.Collar.Incidence

namespace TorusEven.Collar.Incidence

variable {B Ω J : Type*} (A : B → Finset Ω)

theorem evenComponents_of_pairs [Finite Ω] [Finite J] (e : J × Bool ≃ Ω)
    (hp : ∀ j, componentOf A (e (j, false)) = componentOf A (e (j, true))) :
    EvenComponents A := by
  classical
  letI := Fintype.ofFinite Ω
  letI := Fintype.ofFinite J
  intro q
  apply ZMod.natCast_eq_zero_iff_even.mp
  have hc : (Nat.card {x // componentOf A x = q} : ZMod 2) =
      ∑ x : Ω, if componentOf A x = q then 1 else 0 := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_eq_sum_ones,
      Nat.cast_sum, Nat.cast_one, Finset.sum_filter, apply_ite, Nat.cast_zero]
  rw [hc, ← e.sum_comp (fun x => if componentOf A x = q then (1 : ZMod 2) else 0),
    Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro j _
  simp only [Fintype.sum_bool, hp j]
  split_ifs <;> decide

variable {R : Type*} (J : R → Finset Ω)

theorem coherent_same_component (hne : ∀ r, (J r).Nonempty) (hc : Coherent J)
    {r s : R} {x y : Ω} (hx : x ∈ J r) (hy : y ∈ J s) :
    componentOf J x = componentOf J y := by
  have hb : blockComponent J hne r = blockComponent J hne s := by
    clear hx hy
    induction hc r s with
    | rel r s hrs =>
      obtain ⟨z, hz, hz'⟩ := hrs
      exact (component_eq_block J hne hz).symm.trans (component_eq_block J hne hz')
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih ih' => exact ih.trans ih'
  exact (component_eq_block J hne hx).trans (hb.trans (component_eq_block J hne hy).symm)

theorem coherent_of_map_subset {Ω' : Type*} (K : R → Finset Ω') (f : Ω → Ω')
    (hmem : ∀ r x, x ∈ J r → f x ∈ K r) (hc : Coherent J) : Coherent K := by
  intro r s
  apply Relation.EqvGen.mono _ (hc r s)
  rintro r s ⟨x, hx, hy⟩
  exact ⟨f x, hmem r x hx, hmem s x hy⟩

theorem eq_root_of_descent {α β : Type*} (f : α → β) (root next : α → α) (rank : α → ℕ)
    (h : ∀ x, x = root x ∨
      rank (next x) < rank x ∧ root (next x) = root x ∧ f x = f (next x))
    (x : α) : f x = f (root x) := by
  induction hn : rank x using Nat.strong_induction_on generalizing x with
  | h n ih =>
    rcases h x with hx | ⟨hlt, hr, hf⟩
    · exact congrArg f hx
    · exact hf.trans ((ih (rank (next x)) (by omega) (next x) rfl).trans (congrArg f hr))

end TorusEven.Collar.Incidence
