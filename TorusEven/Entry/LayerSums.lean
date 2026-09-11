-- STATUS: main-path
import TorusEven.Collar.Lift

namespace TorusEven.Entry

variable {m : ℕ} [NeZero m]

theorem sum_zmod_if_eq (a b c : ZMod m) :
    (∑ x : ZMod m, if x = a then b else c) = b - c := by
  have h (x : ZMod m) : (if x = a then b else c) =
      c + if x = a then b - c else 0 := by split_ifs <;> ring
  simp only [h, Finset.sum_add_distrib]
  simp

theorem sum_zmod_two_exceptions (a a' b b' c : ZMod m) (hne : a ≠ a') :
    (∑ x : ZMod m, if x = a then b else if x = a' then b' else c) = b + b' - 2 * c := by
  have h (x : ZMod m) : (if x = a then b else if x = a' then b' else c) =
      c + (if x = a then b - c else 0) + if x = a' then b' - c else 0 := by
    by_cases hx : x = a
    · subst x; simp [hne]
    · by_cases hx' : x = a'
      · subst x; simp [Ne.symm hne]
      · simp [hx, hx']
  simp only [h, Finset.sum_add_distrib]
  simp
  ring

theorem height_singleCycle : Shared.IsSingleCycleMap (Equiv.addRight (1 : ZMod m)) :=
  Shared.single_cycle_of_zmod_rank_equiv _ (Equiv.refl _) (fun _ => rfl)

theorem sum_zmod_val_of_support {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ)
    (hn : n ≤ m) (hf : ∀ i, n ≤ i → f i = 0) :
    (∑ h : ZMod m, f h.val) = ∑ i : Fin n, f i.val := by
  have hv (i : Fin m) : ((ZMod.finEquiv m) i).val = i.val := by
    cases m with
    | zero => exact i.elim0
    | succ m => rfl
  calc
    (∑ h : ZMod m, f h.val) = ∑ i : Fin m, f ((ZMod.finEquiv m) i).val :=
      ((ZMod.finEquiv m).toEquiv.sum_comp (fun h => f h.val)).symm
    _ = ∑ i : Fin m, f i.val := by simp only [hv]
    _ = ∑ i ∈ Finset.range m, f i := Fin.sum_univ_eq_sum_range f m
    _ = ∑ i ∈ Finset.range n, f i := (Finset.sum_subset (Finset.range_mono hn)
      (fun i _ hi => hf i (by simpa using hi))).symm
    _ = ∑ i : Fin n, f i.val := (Fin.sum_univ_eq_sum_range f n).symm

end TorusEven.Entry
