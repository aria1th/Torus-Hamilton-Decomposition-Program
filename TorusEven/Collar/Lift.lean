-- STATUS: main-path
import Shared.Monodromy

namespace TorusEven.Collar

open Function

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (S : Equiv.Perm α)

noncomputable def orbitEquiv (hS : Shared.IsSingleCycleMap S) (u : α) :
    Fin (minimalPeriod S u) ≃ α :=
  Equiv.ofBijective (fun k => S^[k.val] u) (by
    constructor
    · intro j k h
      exact Fin.ext ((iterate_eq_iterate_iff_of_lt_minimalPeriod j.isLt k.isLt).mp h)
    · intro x
      obtain ⟨k, hk⟩ := hS.2 u x
      have hp := minimalPeriod_pos_of_mem_periodicPts (S.injective.mem_periodicPts u)
      exact ⟨⟨k % minimalPeriod S u, Nat.mod_lt _ hp⟩,
        (iterate_mod_minimalPeriod_eq (f := S) (x := u)).trans hk⟩)

variable {m : ℕ} [NeZero m]

def lift (δ : α → ZMod m) : Equiv.Perm (α × ZMod m) where
  toFun p := (S p.1, p.2 + δ p.1)
  invFun p := (S.symm p.1, p.2 - δ (S.symm p.1))
  left_inv p := by simp
  right_inv p := by simp

omit [Fintype α] [DecidableEq α] [NeZero m] in
@[simp] theorem lift_apply (δ : α → ZMod m) (x : α) (t : ZMod m) :
    lift S δ (x, t) = (S x, t + δ x) := rfl

omit [DecidableEq α] in
theorem lift_singleCycle (hS : Shared.IsSingleCycleMap S) (δ : α → ZMod m)
    (u : α) (hunit : IsUnit (∑ x, δ x)) : Shared.IsSingleCycleMap (lift S δ) := by
  have hsum : Shared.skewFiberAdditiveCarry S δ (minimalPeriod S u) u = ∑ x, δ x := by
    rw [Shared.skewFiberAdditiveCarry_eq_sum_range]
    calc
      (∑ k ∈ Finset.range (minimalPeriod S u), δ (S^[k] u)) =
          ∑ k : Fin (minimalPeriod S u), δ (orbitEquiv S hS u k) := by
        change _ = ∑ k : Fin (minimalPeriod S u), δ (S^[k.val] u)
        exact (Fin.sum_univ_eq_sum_range (fun k => δ (S^[k] u)) _).symm
      _ = ∑ x, δ x := (orbitEquiv S hS u).sum_comp δ
  exact Shared.single_cycle_of_skewProduct_zmod_additive_unit_carry S δ u
    (minimalPeriod S u) (∑ x, δ x) S.bijective (iterate_minimalPeriod (f := S) (x := u))
    (fun x => by
      obtain ⟨k, hk⟩ := (orbitEquiv S hS u).surjective x
      exact ⟨k.val, k.isLt, hk⟩) hunit hsum

omit [Fintype α] [DecidableEq α] [NeZero m] in
theorem lift_iterate_zero (δ : α → ZMod m) (u : α) (n : ℕ)
    (hδ : ∀ k, k < n → δ (S^[k] u) = 0) :
    (lift S δ)^[n] (u, 0) = (S^[n] u, 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih (fun k hk => hδ k (by omega))]
      simp only [lift_apply, hδ n (by omega), add_zero, Function.iterate_succ_apply']

def zeroSection (U : Set α) : Set (α × ZMod m) := {p | p.1 ∈ U ∧ p.2 = 0}

def zeroEquiv (U : Set α) : U ≃ zeroSection (m := m) U where
  toFun u := ⟨(u.val, 0), u.property, rfl⟩
  invFun p := ⟨p.val.1, p.property.1⟩
  left_inv u := rfl
  right_inv p := by
    apply Subtype.ext
    exact Prod.ext rfl p.property.2.symm

end TorusEven.Collar
