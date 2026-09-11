-- STATUS: main-path
import TorusEven.Collar.ComponentPairs

namespace TorusEven.Collar.Incidence

variable {B Ω J : Type*} (A : B → Finset Ω)

theorem evenOnComponents_of_pairs [Finite Ω] [Finite J] (target : Finset Ω)
    (e : J × Bool ≃ target)
    (hp : ∀ j, componentOf A (e (j, false)).val = componentOf A (e (j, true)).val) :
    EvenOnComponents A target := by
  classical
  letI := Fintype.ofFinite Ω
  letI := Fintype.ofFinite J
  intro q
  let f : {x // componentOf A x = q ∧ x ∈ target} ≃
      {x : target // componentOf A x.val = q} :=
    ⟨fun x => ⟨⟨x.val, x.property.2⟩, x.property.1⟩,
      fun x => ⟨x.val.val, x.property, x.val.property⟩, fun _ => rfl, fun _ => rfl⟩
  apply ZMod.natCast_eq_zero_iff_even.mp
  have hc : (Nat.card {x // componentOf A x = q ∧ x ∈ target} : ZMod 2) =
      ∑ x : target, if componentOf A x.val = q then 1 else 0 := by
    simp only [Nat.card_congr f, Nat.card_eq_fintype_card, Fintype.card_subtype,
      Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter,
      apply_ite, Nat.cast_zero]
  rw [hc, ← e.sum_comp (fun x => if componentOf A x.val = q then (1 : ZMod 2) else 0),
    Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro j _
  simp only [Fintype.sum_bool, hp j]
  split_ifs <;> decide

end TorusEven.Collar.Incidence
