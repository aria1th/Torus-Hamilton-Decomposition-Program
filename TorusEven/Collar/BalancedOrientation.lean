-- STATUS: main-path
import Mathlib

namespace TorusEven.Collar

namespace Multigraph

variable {E V : Type*} [Fintype E] [Fintype V] [DecidableEq V]

def degree (l r : E → V) (v : V) : ℕ :=
  ∑ e, ((if l e = v then 1 else 0) + (if r e = v then 1 else 0))

theorem sum_degree (l r : E → V) : ∑ v, degree l r v = 2 * Fintype.card E := by
  simp only [degree]
  rw [Finset.sum_comm]
  simp [Finset.sum_add_distrib, mul_comm]

omit [Fintype V] in
theorem exists_half_orientation [Finite V] (l r : E → V) (k : V → ℕ)
    (hk : ∀ v, degree l r v = 2 * k v) :
    ∃ tail : E → V, (∀ e, tail e = l e ∨ tail e = r e) ∧
      ∀ v, (Finset.univ.filter (fun e => tail e = v)).card = k v := by
  classical
  letI := Fintype.ofFinite V
  let rel : E → (Σ v, Fin (k v)) → Prop := fun e p => l e = p.1 ∨ r e = p.1
  have hhall (s : Finset E) : s.card ≤
      (Finset.univ.filter (fun p : Σ v, Fin (k v) => ∃ e ∈ s, rel e p)).card := by
    let N : V → Prop := fun v => ∃ e ∈ s, l e = v ∨ r e = v
    have hcard : (Finset.univ.filter (fun p : Σ v, Fin (k v) => ∃ e ∈ s, rel e p)).card =
        ∑ v, if N v then k v else 0 := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro v _
      change (∑ _ : Fin (k v), if N v then 1 else 0) = _
      by_cases h : N v <;> simp [h]
    have hcount : 2 * s.card ≤ ∑ v, if N v then 2 * k v else 0 := by
      calc
        2 * s.card = ∑ e ∈ s, ∑ v : V,
            ((if l e = v then 1 else 0) + (if r e = v then 1 else 0)) := by
          simp [Finset.sum_add_distrib, mul_comm]
        _ = ∑ v : V, ∑ e ∈ s,
            ((if l e = v then 1 else 0) + (if r e = v then 1 else 0)) := Finset.sum_comm
        _ ≤ ∑ v, if N v then 2 * k v else 0 := by
          apply Finset.sum_le_sum
          intro v _
          by_cases h : N v
          · rw [if_pos h, ← hk]
            exact Finset.sum_le_sum_of_subset (Finset.subset_univ s)
          · rw [if_neg h]
            apply le_of_eq
            apply Finset.sum_eq_zero
            intro e he
            have hl : l e ≠ v := fun hv => h ⟨e, he, Or.inl hv⟩
            have hr : r e ≠ v := fun hv => h ⟨e, he, Or.inr hv⟩
            simp [hl, hr]
    rw [hcard]
    have heq : (∑ v, if N v then 2 * k v else 0) = 2 * ∑ v, if N v then k v else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      by_cases h : N v <;> simp [h]
    rw [heq] at hcount
    omega
  obtain ⟨f, hf, hrel⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective rel).mp hhall
  have hslots : Fintype.card E = Fintype.card (Σ v, Fin (k v)) := by
    have h := sum_degree l r
    simp only [hk, ← Finset.mul_sum] at h
    have hcard : Fintype.card (Σ v, Fin (k v)) = ∑ v, k v := by simp [Fintype.card_sigma]
    rw [hcard]
    omega
  have hbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hslots⟩
  refine ⟨fun e => (f e).1, fun e => (hrel e).elim
    (fun h => Or.inl h.symm) (fun h => Or.inr h.symm), ?_⟩
  intro v
  calc
    (Finset.univ.filter (fun e => (f e).1 = v)).card =
        ∑ e, if (f e).1 = v then 1 else 0 := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ p : (Σ v, Fin (k v)), if p.1 = v then 1 else 0 :=
      hbij.sum_comp (fun p : (Σ v, Fin (k v)) => if p.1 = v then (1 : ℕ) else 0)
    _ = ∑ x, if x = v then k x else 0 := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro x _
      change (∑ _ : Fin (k x), if x = v then (1 : ℕ) else 0) = _
      by_cases h : x = v <;> simp [h]
    _ = k v := by simp

def Reorients (l r u w : E → V) : Prop :=
  ∀ e, (u e = l e ∧ w e = r e) ∨ (u e = r e ∧ w e = l e)

def divergence (l r : E → V) (v : V) : ℤ :=
  ∑ e, ((if r e = v then 1 else 0) - (if l e = v then 1 else 0))

omit [Fintype V] in
theorem exists_even_orientation [Finite V] (l r : E → V) (heven : ∀ v, Even (degree l r v)) :
    ∃ u w : E → V, Reorients l r u w ∧ ∀ v, divergence u w v = 0 := by
  classical
  choose k hk using heven
  obtain ⟨u, hu, hcount⟩ := exists_half_orientation l r k (fun v => by rw [hk]; omega)
  let w : E → V := fun e => if u e = l e then r e else l e
  have hor : Reorients l r u w := by
    intro e
    by_cases h : u e = l e
    · exact Or.inl ⟨h, if_pos h⟩
    · exact Or.inr ⟨(hu e).resolve_left h, if_neg h⟩
  refine ⟨u, w, hor, ?_⟩
  intro v
  have hdeg : degree u w v = degree l r v := by
    apply Finset.sum_congr rfl
    intro e _
    rcases hor e with ⟨hu, hw⟩ | ⟨hu, hw⟩ <;> simp [hu, hw, add_comm]
  have ht : (∑ e, if u e = v then 1 else 0) = k v := by
    simpa only [Finset.card_eq_sum_ones, Finset.sum_filter] using hcount v
  have hh : (∑ e, if w e = v then 1 else 0) = k v := by
    rw [degree, Finset.sum_add_distrib, ht, hk] at hdeg
    omega
  have ht' : (∑ e, if u e = v then (1 : ℤ) else 0) = k v := by exact_mod_cast ht
  have hh' : (∑ e, if w e = v then (1 : ℤ) else 0) = k v := by exact_mod_cast hh
  simp only [divergence, Finset.sum_sub_distrib, ht', hh', sub_self]

omit [Fintype V] in
theorem exists_mixed_orientation [Finite V] (l r : E → V) (target : Finset V)
    (hdegree : ∀ v, (degree l r v : ZMod 2) = if v ∈ target then 1 else 0) :
    ∃ u w : E → V, Reorients l r u w ∧
      (∀ v ∈ target, divergence u w v = 1 ∨ divergence u w v = -1) ∧
      ∀ v ∉ target, divergence u w v = 0 := by
  classical
  letI := Fintype.ofFinite V
  have hcard : Even (Fintype.card target) := by
    apply ZMod.natCast_eq_zero_iff_even.mp
    have h := congrArg (fun n : ℕ => (n : ZMod 2)) (sum_degree l r)
    have htwo : (2 : ZMod 2) = 0 := by decide
    simpa [Nat.cast_sum, hdegree, htwo, Finset.sum_ite_mem] using h
  let L : E ⊕ target → Option V := Sum.elim (fun e => some (l e)) (fun x => some x.val)
  let R : E ⊕ target → Option V := Sum.elim (fun e => some (r e)) (fun _ => none)
  have hdeg (v : V) : degree L R (some v) = degree l r v + if v ∈ target then 1 else 0 := by
    have hs : (∑ x : target, if x.val = v then (1 : ℕ) else 0) =
        if v ∈ target then 1 else 0 := by
      rw [Finset.sum_coe_sort target (fun x => if x = v then (1 : ℕ) else 0)]
      simp
    simp only [degree, Fintype.sum_sum_type, L, R, Sum.elim_inl, Sum.elim_inr,
      Option.some.injEq, reduceCtorEq, if_false, add_zero, hs]
  have heven : ∀ v, Even (degree L R v) := by
    intro v
    cases v with
    | none => simpa [degree, L, R, Fintype.sum_sum_type] using hcard
    | some v =>
      apply ZMod.natCast_eq_zero_iff_even.mp
      rw [hdeg, Nat.cast_add, hdegree]
      by_cases hv : v ∈ target <;>
        simp only [hv, if_true, if_false, Nat.cast_zero, Nat.cast_one] <;> decide
  obtain ⟨U, W, hor, hbal⟩ := exists_even_orientation L R heven
  have hu (e : E) : ∃ u, U (.inl e) = some u := by
    rcases hor (.inl e) with ⟨h, _⟩ | ⟨h, _⟩
    · exact ⟨l e, h⟩
    · exact ⟨r e, h⟩
  have hw (e : E) : ∃ w, W (.inl e) = some w := by
    rcases hor (.inl e) with ⟨_, h⟩ | ⟨_, h⟩
    · exact ⟨r e, h⟩
    · exact ⟨l e, h⟩
  choose u hu using hu
  choose w hw using hw
  let hub (v : V) (x : target) : ℤ :=
    (if W (.inr x) = some v then 1 else 0) - (if U (.inr x) = some v then 1 else 0)
  have hother (v : V) (x : target) (hx : x.val ≠ v) : hub v x = 0 := by
    rcases hor (.inr x) with ⟨hU, hW⟩ | ⟨hU, hW⟩ <;> simp [hub, hU, hW, L, R, hx]
  have htotal (v : V) : divergence u w v + ∑ x : target, hub v x = 0 := by
    have h := hbal (some v)
    change (∑ e, ((if W e = some v then (1 : ℤ) else 0) -
      (if U e = some v then 1 else 0))) = 0 at h
    rw [Fintype.sum_sum_type] at h
    simpa only [hu, hw, Option.some.injEq] using h
  refine ⟨u, w, ?_, ?_, ?_⟩
  · intro e
    have h := hor (.inl e)
    simpa [L, R, hu, hw] using h
  · intro v hv
    let x : target := ⟨v, hv⟩
    have hhub : (∑ y : target, hub v y) = hub v x := by
      apply Finset.sum_eq_single x
      · intro y _ hy
        exact hother v y (fun he => hy (Subtype.ext he))
      · simp
    have h := htotal v
    rw [hhub] at h
    rcases hor (.inr x) with ⟨hU, hW⟩ | ⟨hU, hW⟩
    · left
      have hv : hub v x = -1 := by simp [hub, hU, hW, L, R, x]
      rw [hv] at h
      omega
    · right
      have hv : hub v x = 1 := by simp [hub, hU, hW, L, R, x]
      rw [hv] at h
      omega
  · intro v hv
    have hhub : (∑ x : target, hub v x) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      exact hother v x (fun he => hv (he ▸ x.property))
    simpa only [hhub, add_zero] using htotal v

omit [Fintype V] in
theorem exists_odd_orientation [Finite V] (l r : E → V) (hodd : ∀ v, Odd (degree l r v)) :
    ∃ u w : E → V, Reorients l r u w ∧
      ∀ v, divergence u w v = 1 ∨ divergence u w v = -1 := by
  classical
  letI := Fintype.ofFinite V
  obtain ⟨u, w, hor, hdiv, _⟩ := exists_mixed_orientation l r Finset.univ (fun v => by
    simpa only [Finset.mem_univ, if_true] using (hodd v).natCast_zmod_two)
  exact ⟨u, w, hor, fun v => hdiv v (Finset.mem_univ v)⟩

end Multigraph

end TorusEven.Collar
