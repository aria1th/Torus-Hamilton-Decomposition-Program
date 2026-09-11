-- STATUS: main-path
import TorusEven.Entry.Rows
import TorusEven.Collar.Circuits

namespace TorusEven.Entry.Star

open Surgery

variable {m : ℕ} [NeZero m] {A : Type*} [AddCommGroup A]

theorem sum_height_translate (f : ZMod m → A) (h : ZMod m) :
    (∑ k ∈ Finset.range m, f (h + (k : ZMod m))) = ∑ t, f t := by
  let e : Fin m ≃ ZMod m :=
    { toFun := fun k => k.val
      invFun := fun t => ⟨t.val, t.val_lt⟩
      left_inv := fun k => Fin.ext (by simp [ZMod.val_natCast, Nat.mod_eq_of_lt k.isLt])
      right_inv := fun t => ZMod.natCast_zmod_val t }
  rw [← Fin.sum_univ_eq_sum_range]
  exact (e.sum_comp (fun t => f (h + t))).trans (Equiv.sum_comp (Equiv.addLeft h) f)

theorem oneSpecial_return (S : Equiv.Perm (ZMod m × A)) (P : Equiv.Perm A)
    (δ : ZMod m → A) (h : ZMod m)
    (hs : ∀ t a, S (t, a) = (t + 1, (if t = h then P a else a) + δ t)) (a : A) :
    S^[m] (h, a) = (h, P a + ∑ t, δ t) := by
  have hi (k : ℕ) (hk : k < m) : S^[k + 1] (h, a) =
      (h + (k + 1 : ℕ), P a + ∑ j ∈ Finset.range (k + 1), δ (h + j)) := by
    induction k with
    | zero => simp [hs]
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega), hs]
      have hne : h + (k + 1 : ℕ) ≠ h := by
        intro he
        exact cast_ne_zero (Nat.succ_pos k) (by omega)
          (add_left_cancel (he.trans (add_zero h).symm))
      rw [if_neg hne, Finset.sum_range_succ (fun j => δ (h + j)) (k + 1)]
      simp only [Nat.cast_add, Nat.cast_one]
      congr 1 <;> abel
  have ht := hi (m - 1) (by have := NeZero.pos m; omega)
  simpa only [Nat.sub_add_cancel (NeZero.pos m), ZMod.natCast_self, add_zero,
    sum_height_translate] using ht

omit [AddCommGroup A] in
theorem singleCycle_of_section [Finite A] (S : Equiv.Perm (ZMod m × A)) (h : ZMod m)
    (hs : ∀ p, (S p).1 = p.1 + 1) (R : Equiv.Perm A)
    (hr : ∀ a, S^[m] (h, a) = (h, R a)) (hR : Shared.IsSingleCycleMap R) :
    Shared.IsSingleCycleMap S := by
  classical
  letI := Fintype.ofFinite A
  have hproj : Function.Semiconj Prod.fst S (fun t : ZMod m => t + 1) := hs
  have hmeet (p : ZMod m × A) : ∃ a, (h, a) ∈ orbitSet S p := by
    let k := (h - p.1).val
    have he : (S^[k] p).1 = h := by
      rw [hproj.iterate_right, add_right_iterate_apply, nsmul_eq_mul]
      simp [k]
    exact ⟨(S^[k] p).2, k, Prod.ext he rfl⟩
  refine ⟨S.bijective, fun p q => ?_⟩
  obtain ⟨a, ha⟩ := hmeet p
  obtain ⟨b, hb⟩ := hmeet q
  obtain ⟨k, hk⟩ := hR.2 a b
  have hab : (h, b) ∈ orbitSet S (h, a) :=
    ⟨k * m, (Shared.iterate_mul_base_of_periodic_return S (fun a => (h, a)) R m hr k a).trans
      (congrArg (fun a => (h, a)) hk)⟩
  have hqb := mem_orbitSet_symm S.injective hb
  rw [orbitSet_eq_of_mem S.injective hab, orbitSet_eq_of_mem S.injective ha] at hqb
  exact hqb

end TorusEven.Entry.Star
