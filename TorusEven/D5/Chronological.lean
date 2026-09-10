-- STATUS: main-path (manuscript Lemma `lem:chronological`, proved)
import TorusEven.D5.FirstReturn
import TorusEven.D5.ChronologicalTransversalGoal

/-!
# The chronological transversal splice

Proof of `TorusEven.Chronological.ChronologicalTransversalGoal` through the orbit-form
surgery lemma.  The order hypothesis on `e` is not needed for the orbit statement.
-/

namespace TorusEven
namespace Chronological

open Function Surgery

variable {X : Type} [AddCommGroup X] [Fintype X] [DecidableEq X]

theorem coset_def' (H : AddSubgroup X) (x y : X) : y ∈ coset H x ↔ y - x ∈ H := Iff.rfl

theorem orbitSet_eq_surgery (f : X → X) (x : X) : orbitSet f x = Surgery.orbitSet f x := rfl

theorem coset_eq_of_sub_mem (H : AddSubgroup X) {x y : X} (h : y - x ∈ H) :
    coset H y = coset H x := by
  ext u
  simp only [coset_def']
  constructor
  · intro hu
    have := H.add_mem hu h
    simpa [sub_add_sub_cancel] using this
  · intro hu
    have := H.sub_mem hu h
    simpa [sub_sub_sub_cancel_right] using this

theorem mem_coset_self (H : AddSubgroup X) (x : X) : x ∈ coset H x := by
  simp [coset_def']

section Data

variable (H W : AddSubgroup X) [DecidablePred (· ∈ W)] (hHW : IsCompl H W)
variable (P : Equiv.Perm X) (b : X) (hP : ∀ x, P x - x - b ∈ H)
variable (e : X) (he : e ∈ W) (z : X)

/-- `P⁻¹ (z + W)`. -/
def sectionSet : Set X := {x | P x - z ∈ W}

local notation "A" => sectionSet W P z

/-- The splice permutation `r = P⁻¹ ∘ J ∘ P`. -/
def splice (x : X) : X := P.symm (piecewiseAdd W z e (P x))

theorem piecewiseAdd_of_mem {y : X} (hy : y - z ∈ W) : piecewiseAdd W z e y = y + e := by
  simp [piecewiseAdd, hy]

theorem piecewiseAdd_of_not_mem {y : X} (hy : y - z ∉ W) : piecewiseAdd W z e y = y := by
  simp [piecewiseAdd, hy]

include he in
theorem piecewiseAdd_bijective : Bijective (piecewiseAdd W z e) := by
  refine ⟨?_, ?_⟩
  · intro y y' h
    by_cases hy : y - z ∈ W <;> by_cases hy' : y' - z ∈ W
    · rw [piecewiseAdd_of_mem W e z hy, piecewiseAdd_of_mem W e z hy'] at h
      exact add_right_cancel h
    · rw [piecewiseAdd_of_mem W e z hy, piecewiseAdd_of_not_mem W e z hy'] at h
      exfalso
      apply hy'
      rw [← h]
      have : y + e - z = (y - z) + e := by abel
      rw [this]
      exact W.add_mem hy he
    · rw [piecewiseAdd_of_not_mem W e z hy, piecewiseAdd_of_mem W e z hy'] at h
      exfalso
      apply hy
      rw [h]
      have : y' + e - z = (y' - z) + e := by abel
      rw [this]
      exact W.add_mem hy' he
    · rwa [piecewiseAdd_of_not_mem W e z hy, piecewiseAdd_of_not_mem W e z hy'] at h
  · intro y
    by_cases hy : y - z ∈ W
    · refine ⟨y - e, ?_⟩
      have hmem : y - e - z ∈ W := by
        have : y - e - z = (y - z) - e := by abel
        rw [this]
        exact W.sub_mem hy he
      rw [piecewiseAdd_of_mem W e z hmem]
      abel
    · exact ⟨y, piecewiseAdd_of_not_mem W e z hy⟩

include he in
theorem splice_bijective : Bijective (splice W P e z) :=
  P.symm.bijective.comp ((piecewiseAdd_bijective W e he z).comp P.bijective)

theorem splice_of_not_mem {x : X} (hx : x ∉ A) : splice W P e z x = x := by
  unfold splice
  rw [piecewiseAdd_of_not_mem W e z hx]
  simp

include he in
theorem splice_mem {x : X} (hx : x ∈ A) : splice W P e z x ∈ A := by
  unfold splice
  show P (P.symm (piecewiseAdd W z e (P x))) - z ∈ W
  rw [Equiv.apply_symm_apply, piecewiseAdd_of_mem W e z hx]
  have : P x + e - z = (P x - z) + e := by abel
  rw [this]
  exact W.add_mem hx he

include he in
theorem splice_iterate {x : X} (hx : x ∈ A) (k : ℕ) :
    (splice W P e z)^[k] x = P.symm (P x + k • e) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      unfold splice
      rw [Equiv.apply_symm_apply]
      have hmem : P x + k • e - z ∈ W := by
        have : P x + k • e - z = (P x - z) + k • e := by abel
        rw [this]
        exact W.add_mem hx (W.nsmul_mem he k)
      rw [piecewiseAdd_of_mem W e z hmem, succ_nsmul, add_assoc]

/-! ### The section meets every `H`-coset exactly once -/

include hHW in
theorem exists_unique_mem_coset_of_sub_mem (y0 : X) :
    ∃! c, c ∈ coset H y0 ∧ c - z ∈ W := by
  have htop : y0 - z ∈ H ⊔ W := by
    rw [hHW.sup_eq_top]
    exact AddSubgroup.mem_top _
  obtain ⟨h, hh, w, hw, hhw⟩ := AddSubgroup.mem_sup.1 htop
  refine ⟨y0 - h, ⟨?_, ?_⟩, ?_⟩
  · show y0 - h - y0 ∈ H
    have : y0 - h - y0 = -h := by abel
    rw [this]
    exact H.neg_mem hh
  · have : y0 - h - z = w := by
      rw [show y0 - h - z = (y0 - z) - h by abel, ← hhw]
      abel
    rw [this]
    exact hw
  · rintro c ⟨hc1, hc2⟩
    have hdiff : c - (y0 - h) ∈ H ⊓ W := by
      refine AddSubgroup.mem_inf.2 ⟨?_, ?_⟩
      · have : c - (y0 - h) = (c - y0) + h := by abel
        rw [this]
        exact H.add_mem hc1 hh
      · have : c - (y0 - h) = (c - z) - (y0 - h - z) := by abel
        rw [this]
        refine W.sub_mem hc2 ?_
        have : y0 - h - z = w := by
          rw [show y0 - h - z = (y0 - z) - h by abel, ← hhw]
          abel
        rw [this]
        exact hw
    rw [hHW.inf_eq_bot, AddSubgroup.mem_bot, sub_eq_zero] at hdiff
    exact hdiff

include hP in
theorem symm_mem_coset (y : X) : P.symm y ∈ coset H (y - b) := by
  show P.symm y - (y - b) ∈ H
  have := hP (P.symm y)
  rw [Equiv.apply_symm_apply] at this
  have h' : P.symm y - (y - b) = -(y - P.symm y - b) := by abel
  rw [h']
  exact H.neg_mem this

include hP in
theorem apply_mem_coset (x : X) : P x ∈ coset H (x + b) := by
  show P x - (x + b) ∈ H
  have := hP x
  have h' : P x - (x + b) = P x - x - b := by abel
  rw [h']
  exact this

include hHW hP in
theorem exists_mem_section_coset (x : X) : ∃ a, a ∈ A ∧ a ∈ coset H x := by
  obtain ⟨c, ⟨hc1, hc2⟩, _⟩ := exists_unique_mem_coset_of_sub_mem H W hHW z (x + b)
  refine ⟨P.symm c, ?_, ?_⟩
  · show P (P.symm c) - z ∈ W
    rw [Equiv.apply_symm_apply]
    exact hc2
  · have h1 := symm_mem_coset H P b hP c
    rw [coset_eq_of_sub_mem H (x := x) (y := c - b) ?_] at h1
    · exact h1
    · have : c - b - x = c - (x + b) := by abel
      rw [this]
      exact hc1

include hHW hP in
theorem unique_mem_section_coset {a a' : X} (ha : a ∈ A) (ha' : a' ∈ A)
    (hcos : a' ∈ coset H a) : a' = a := by
  obtain ⟨c, _, huniq⟩ := exists_unique_mem_coset_of_sub_mem H W hHW z (a + b)
  have h1 : P a = c := huniq _ ⟨apply_mem_coset H P b hP a, ha⟩
  have h2 : P a' = c := by
    refine huniq _ ⟨?_, ha'⟩
    have := apply_mem_coset H P b hP a'
    rw [coset_eq_of_sub_mem H (x := a + b) (y := a' + b) ?_] at this
    · exact this
    · have : a' + b - (a + b) = a' - a := by abel
      rw [this]
      exact hcos
  exact P.injective (h2.trans h1.symm)

end Data

/-! ### The main theorem -/

theorem sup_zmultiples_coset_eq (H : AddSubgroup X) (e u : X) :
    coset (H ⊔ AddSubgroup.zmultiples e) u = ⋃ k : ℕ, coset H (u + (k + 1) • e) := by
  ext y
  simp only [Set.mem_iUnion, coset_def']
  constructor
  · intro hy
    obtain ⟨h, hh, w, hw, hhw⟩ := AddSubgroup.mem_sup.1 hy
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hw
    have hpos : 0 < addOrderOf e := addOrderOf_pos e
    set k : ℕ := (n % (addOrderOf e : ℤ)).toNat with hk
    have hk' : ((k : ℤ)) = n % (addOrderOf e : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hpos.ne'))
    have hne : n • e = k • e := by
      rw [← mod_addOrderOf_zsmul e n, ← hk', natCast_zsmul]
    refine ⟨k + (addOrderOf e - 1), ?_⟩
    have hkk : k + (addOrderOf e - 1) + 1 = k + addOrderOf e := by omega
    rw [hkk, add_nsmul, addOrderOf_nsmul_eq_zero, add_zero]
    have : y - (u + k • e) = h := by
      calc y - (u + k • e) = (y - u) - k • e := by abel
        _ = (h + n • e) - k • e := by rw [← hhw]
        _ = h := by rw [hne]; abel
    rw [this]
    exact hh
  · rintro ⟨k, hk⟩
    refine AddSubgroup.mem_sup.2 ⟨y - (u + (k + 1) • e), hk, (k + 1) • e, ?_, by abel⟩
    exact AddSubgroup.mem_zmultiples_iff.2 ⟨((k + 1 : ℕ) : ℤ), by rw [natCast_zsmul]⟩

theorem chronological_transversal : ChronologicalTransversalGoal := by
  intro X _ _ _ H W _ hHW S hS P b hP e he m _ z rlet x
  show orbitSet (fun y => S (splice W P e z y)) x = coset (H ⊔ AddSubgroup.zmultiples e) x
  -- decidability of the section
  haveI : DecidablePred (· ∈ sectionSet W P z) := fun x => by
    unfold sectionSet
    exact inferInstance
  set r := splice W P e z with hr_def
  have hsupp : ∀ x, x ∉ sectionSet W P z → r x = x := fun x hx => splice_of_not_mem W P e z hx
  have hmaps : ∀ x, x ∈ sectionSet W P z → r x ∈ sectionSet W P z :=
    fun x hx => splice_mem W P e he z hx
  have hrbij : Bijective r := splice_bijective W P e he z
  have hSr : Bijective (fun y => S (r y)) := S.bijective.comp hrbij
  -- uniqueness of section points on `S`-orbits
  have huniq : ∀ w ∈ sectionSet W P z, ∀ y ∈ Surgery.orbitSet S w, y ∈ sectionSet W P z → y = w := by
    intro w hw y hy hyA
    rw [← orbitSet_eq_surgery, hS w] at hy
    exact unique_mem_section_coset H W hHW P b hP z hw hyA hy
  -- the return map after surgery is `r` itself on the section
  have hafter : ∀ v ∈ sectionSet W P z, afterRet S (sectionSet W P z) r v = r v := by
    intro v hv
    unfold afterRet
    exact ret_eq_self_of_unique S _ (hmaps v hv) (huniq _ (hmaps v hv))
  have hafter_iter : ∀ u ∈ sectionSet W P z, ∀ j,
      (afterRet S (sectionSet W P z) r)^[j] u = r^[j] u := by
    intro u hu j
    induction j with
    | zero => rfl
    | succ j ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
        apply hafter
        rw [← ih]
        exact afterRet_iterate_mem S _ r hmaps hu j
  -- the orbit of a section point
  have hsection : ∀ u ∈ sectionSet W P z,
      Surgery.orbitSet (fun y => S (r y)) u = coset (H ⊔ AddSubgroup.zmultiples e) u := by
    intro u hu
    have h1 := orbitSet_comp_eq S (sectionSet W P z) r hsupp hmaps hrbij hu
    have h2 : (⇑S ∘ r) = fun y => S (r y) := rfl
    rw [h2] at h1
    rw [h1, sup_zmultiples_coset_eq]
    ext y
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨v, ⟨j, rfl⟩, hy⟩
      dsimp only at hy ⊢
      rw [hafter_iter u hu j] at hy
      have hvA : r^[j] u ∈ sectionSet W P z := by
        rw [← hafter_iter u hu j]
        exact afterRet_iterate_mem S _ r hmaps hu j
      rw [seg_eq_orbitSet_of_unique S _ (hmaps _ hvA) (huniq _ (hmaps _ hvA)),
        ← orbitSet_eq_surgery, hS] at hy
      refine ⟨j, ?_⟩
      have hrv : r (r^[j] u) = r^[j + 1] u := (Function.iterate_succ_apply' r j u).symm
      rw [hrv, splice_iterate W P e he z hu] at hy
      have hc := symm_mem_coset H P b hP (P u + (j + 1) • e)
      rw [coset_eq_of_sub_mem H (x := u + (j + 1) • e) (y := P u + (j + 1) • e - b) ?_] at hc
      · rw [coset_eq_of_sub_mem H hc] at hy
        exact hy
      · have : P u + (j + 1) • e - b - (u + (j + 1) • e) = P u - u - b := by abel
        rw [this]
        exact hP u
    · rintro ⟨k, hk⟩
      refine ⟨r^[k] u, ⟨k, hafter_iter u hu k⟩, ?_⟩
      have hvA : r^[k] u ∈ sectionSet W P z := by
        rw [← hafter_iter u hu k]
        exact afterRet_iterate_mem S _ r hmaps hu k
      rw [seg_eq_orbitSet_of_unique S _ (hmaps _ hvA) (huniq _ (hmaps _ hvA)),
        ← orbitSet_eq_surgery, hS]
      have hrv : r (r^[k] u) = r^[k + 1] u := (Function.iterate_succ_apply' r k u).symm
      rw [hrv, splice_iterate W P e he z hu]
      have hc := symm_mem_coset H P b hP (P u + (k + 1) • e)
      rw [coset_eq_of_sub_mem H (x := u + (k + 1) • e) (y := P u + (k + 1) • e - b) ?_] at hc
      · rw [coset_eq_of_sub_mem H hc]
        exact hk
      · have : P u + (k + 1) • e - b - (u + (k + 1) • e) = P u - u - b := by abel
        rw [this]
        exact hP u
  -- a general point lies on the orbit of the section point of its `H`-coset
  obtain ⟨a, haA, hax⟩ := exists_mem_section_coset H W hHW P b hP z x
  have hxa : x ∈ Surgery.orbitSet (fun y => S (r y)) a := by
    rw [hsection a haA]
    show x - a ∈ H ⊔ AddSubgroup.zmultiples e
    have : x - a = -(a - x) := by abel
    rw [this]
    exact AddSubgroup.mem_sup_left (H.neg_mem hax)
  rw [orbitSet_eq_surgery, Surgery.orbitSet_eq_of_mem hSr.1 hxa, hsection a haA]
  apply coset_eq_of_sub_mem
  have : a - x ∈ H := hax
  exact AddSubgroup.mem_sup_left this

end Chronological
end TorusEven
