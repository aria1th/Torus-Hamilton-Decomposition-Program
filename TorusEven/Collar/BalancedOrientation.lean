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
theorem exists_odd_orientation [Finite V] (l r : E → V) (hodd : ∀ v, Odd (degree l r v)) :
    ∃ u w : E → V, Reorients l r u w ∧
      ∀ v, divergence u w v = 1 ∨ divergence u w v = -1 := by
  classical
  letI := Fintype.ofFinite V
  have hcard : Even (Fintype.card V) := by
    apply ZMod.natCast_eq_zero_iff_even.mp
    have hd (v : V) : (degree l r v : ZMod 2) = 1 := (hodd v).natCast_zmod_two
    have h := congrArg (fun n : ℕ => (n : ZMod 2)) (sum_degree l r)
    have htwo : (2 : ZMod 2) = 0 := by decide
    simpa [Nat.cast_sum, hd, htwo] using h
  let L : E ⊕ V → Option V := Sum.elim (fun e => some (l e)) some
  let R : E ⊕ V → Option V := Sum.elim (fun e => some (r e)) (fun _ => none)
  have hdeg (v : V) : degree L R (some v) = degree l r v + 1 := by
    simp only [degree, Fintype.sum_sum_type]
    simp [L, R, Finset.sum_add_distrib]
  have heven : ∀ v, Even (degree L R v) := by
    intro v
    cases v with
    | none => simpa [degree, L, R, Fintype.sum_sum_type] using hcard
    | some v => rw [hdeg]; exact (hodd v).add_odd (by decide)
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
  refine ⟨u, w, ?_, ?_⟩
  · intro e
    have h := hor (.inl e)
    simpa [L, R, hu, hw] using h
  · intro v
    let hub : V → ℤ := fun x =>
      (if W (.inr x) = some v then 1 else 0) - (if U (.inr x) = some v then 1 else 0)
    have hhub : (∑ x, hub x) = hub v := by
      apply Finset.sum_eq_single v
      · intro x _ hx
        rcases hor (.inr x) with ⟨hU, hW⟩ | ⟨hU, hW⟩ <;> simp [hub, hU, hW, L, R, hx]
      · simp
    have h := hbal (some v)
    change (∑ e, ((if W e = some v then (1 : ℤ) else 0) -
      (if U e = some v then 1 else 0))) = 0 at h
    rw [Fintype.sum_sum_type] at h
    change (∑ e, ((if W (.inl e) = some v then (1 : ℤ) else 0) -
      (if U (.inl e) = some v then 1 else 0))) + ∑ x, hub x = 0 at h
    rw [hhub] at h
    simp only [hu, hw, Option.some.injEq] at h
    change divergence u w v + hub v = 0 at h
    rcases hor (.inr v) with ⟨hU, hW⟩ | ⟨hU, hW⟩
    · left
      have hv : hub v = -1 := by simp [hub, hU, hW, L, R]
      rw [hv] at h
      omega
    · right
      have hv : hub v = 1 := by simp [hub, hU, hW, L, R]
      rw [hv] at h
      omega

end Multigraph

end TorusEven.Collar
