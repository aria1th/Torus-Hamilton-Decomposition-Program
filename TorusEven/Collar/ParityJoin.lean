-- STATUS: main-path
import TorusEven.Collar.Incidence

namespace TorusEven.Collar.Incidence

variable {B Ω : Type*} [Fintype B] [Fintype Ω] [DecidableEq Ω]

omit [DecidableEq Ω] in
theorem evenComponents_of_boundary (A : B → Finset Ω) (hne : ∀ b, (A b).Nonempty)
    (f : B → Ω → ZMod 2) (hsupp : ∀ b x, x ∉ A b → f b x = 0)
    (hrow : ∀ b, ∑ x, f b x = 0) (hcol : ∀ x, ∑ b, f b x = 1) : EvenComponents A := by
  classical
  intro q
  let v : Ω → ZMod 2 := fun x => if componentOf A x = q then 1 else 0
  let z : B → ZMod 2 := fun b => if blockComponent A hne b = q then 1 else 0
  have hmask (b : B) (x : Ω) : v x * f b x = z b * f b x := by
    by_cases hx : x ∈ A b
    · simp only [v, z, component_eq_block A hne hx]
    · simp only [hsupp b x hx, mul_zero]
  apply ZMod.natCast_eq_zero_iff_even.mp
  have hcard : (Nat.card {x // componentOf A x = q} : ZMod 2) = ∑ x, v x := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_eq_sum_ones,
      Nat.cast_sum, Nat.cast_one, Finset.sum_filter, v, apply_ite, Nat.cast_zero]
  rw [hcard]
  calc
    (∑ x, v x) = ∑ x, v x * (∑ b, f b x) := by simp only [hcol, mul_one]
    _ = ∑ b, ∑ x, v x * f b x := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    _ = 0 := by simp only [hmask, ← Finset.mul_sum, hrow, mul_zero, Finset.sum_const_zero]

private theorem path_boundary (A : B → Finset Ω) {x y : Ω}
    (h : Relation.EqvGen (Adjacent A) x y) :
    ∃ f : B → Ω → ZMod 2,
      (∀ b z, z ∉ A b → f b z = 0) ∧
      (∀ b, ∑ z, f b z = 0) ∧
      (∀ z, ∑ b, f b z = (if z = x then 1 else 0) + if z = y then 1 else 0) := by
  classical
  have htwo : (1 : ZMod 2) + 1 = 0 := by decide
  induction h with
  | rel x y h =>
    obtain ⟨b, hx, hy⟩ := h
    refine ⟨fun c z => if c = b then
      (if z = x then 1 else 0) + (if z = y then 1 else 0) else 0, ?_, ?_, ?_⟩
    · intro c z hz
      by_cases hc : c = b
      · subst c
        have hzx : z ≠ x := fun h => hz (h ▸ hx)
        have hzy : z ≠ y := fun h => hz (h ▸ hy)
        simp [hzx, hzy]
      · simp [hc]
    · intro c
      by_cases hc : c = b <;> simp [hc, Finset.sum_add_distrib, htwo]
    · intro z
      simp
  | refl x =>
    refine ⟨0, by simp, by simp, ?_⟩
    intro z
    by_cases h : z = x <;> simp [h, htwo]
  | symm x y _ ih =>
    obtain ⟨f, hf, hb, hc⟩ := ih
    exact ⟨f, hf, hb, fun z => (hc z).trans (add_comm _ _)⟩
  | trans x y z _ _ ih ih' =>
    obtain ⟨f, hf, hb, hc⟩ := ih
    obtain ⟨g, hg, hb', hc'⟩ := ih'
    refine ⟨fun b w => f b w + g b w, ?_, ?_, ?_⟩
    · intro b w hw
      simp [hf b w hw, hg b w hw]
    · intro b
      simp [Finset.sum_add_distrib, hb, hb']
    · intro w
      rw [Finset.sum_add_distrib, hc, hc']
      have hm : (if w = y then (1 : ZMod 2) else 0) +
          (if w = y then 1 else 0) = 0 := by split_ifs <;> simp [htwo]
      linear_combination hm

omit [Fintype Ω] in
theorem exists_parity_join_on [Finite Ω] (A : B → Finset Ω) (target : Finset Ω)
    (hEven : EvenOnComponents A target) :
    ∃ T : B → Finset Ω, (∀ b, T b ⊆ A b) ∧ (∀ b, Even (T b).card) ∧
      ∀ x, ((Finset.univ.filter (fun b => x ∈ T b)).card : ZMod 2) =
        if x ∈ target then 1 else 0 := by
  classical
  letI := Fintype.ofFinite Ω
  let root : Component A → Ω := Quotient.out
  have hroot (q : Component A) : componentOf A (root q) = q := Quotient.out_eq q
  have hpath (x : Ω) : Relation.EqvGen (Adjacent A) x (root (componentOf A x)) :=
    (componentOf_eq A _ _).mp (hroot _).symm
  choose f hf hb hc using fun x => path_boundary A (hpath x)
  let g : B → Ω → ZMod 2 := fun b z => ∑ x ∈ target, f x b z
  have hg (b : B) (z : Ω) (hz : z ∉ A b) : g b z = 0 := by
    simp [g, hf _ b z hz]
  have hgb (b : B) : ∑ z, g b z = 0 := by
    simp only [g]
    rw [Finset.sum_comm]
    simp [hb]
  have hgc (z : Ω) : ∑ b, g b z = if z ∈ target then 1 else 0 := by
    simp only [g]
    rw [Finset.sum_comm]
    simp only [hc, Finset.sum_add_distrib]
    have hz : ∑ x ∈ target, (if z = root (componentOf A x) then (1 : ZMod 2) else 0) = 0 := by
      by_cases hr : root (componentOf A z) = z
      · have heq (x : Ω) : z = root (componentOf A x) ↔ componentOf A x = componentOf A z := by
          constructor
          · intro h
            rw [h, hroot]
          · intro h
            rw [h, hr]
        simp only [heq]
        exact hEven.sum A (componentOf A z)
      · apply Finset.sum_eq_zero
        intro x _
        apply if_neg
        intro h
        have heq : componentOf A z = componentOf A x := by rw [h, hroot]
        exact hr (by rw [heq, ← h])
    rw [hz, add_zero]
    simp
  have hbit (v : ZMod 2) : (if v = 1 then (1 : ZMod 2) else 0) = v := by
    fin_cases v <;> decide
  refine ⟨fun b => Finset.univ.filter (fun z => g b z = 1), ?_, ?_, ?_⟩
  · intro b z hz
    have h := (Finset.mem_filter.mp hz).2
    by_contra hn
    rw [hg b z hn] at h
    exact zero_ne_one h
  · intro b
    apply ZMod.natCast_eq_zero_iff_even.mp
    simpa only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one,
      Finset.sum_filter, apply_ite, Nat.cast_zero, hbit] using hgb b
  · intro z
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter,
      apply_ite, Nat.cast_zero, hbit] using hgc z

omit [Fintype Ω] in
theorem exists_parity_join [Finite Ω] (A : B → Finset Ω) (hEven : EvenComponents A) :
    ∃ T : B → Finset Ω, (∀ b, T b ⊆ A b) ∧ (∀ b, Even (T b).card) ∧
      ∀ x, Odd ((Finset.univ.filter (fun b => x ∈ T b)).card) := by
  classical
  letI := Fintype.ofFinite Ω
  obtain ⟨T, hT, hb, hc⟩ := exists_parity_join_on A Finset.univ
    ((evenOnComponents_univ A).mpr hEven)
  refine ⟨T, hT, hb, fun x => ZMod.natCast_eq_one_iff_odd.mp ?_⟩
  simpa only [Finset.mem_univ, if_true] using hc x

end TorusEven.Collar.Incidence
