-- STATUS: main-path
import TorusEven.Entry.Star.Induced

namespace TorusEven.Entry.Star.Nondivisible

def chiIndex (k i : ℕ) : ℕ :=
  if i < k - 4 then i + 3 else if i = k - 4 then 2 else if i = k - 3 then 0 else 1

def chi (k : ℕ) (hk : 4 ≤ k) (i : Fin (k - 1)) : Fin (k - 1) :=
  ⟨chiIndex k i.val, by unfold chiIndex; split_ifs <;> have := i.isLt <;> omega⟩

def orderIndex (q r i : ℕ) : ℕ :=
  if i < q + r - 1 then 3 * i else
  if i < 2 * q + r - 1 then 3 * (i - (q + r - 1)) + (3 - r) else
  3 * (i - (2 * q + r - 1)) + r

variable (q r : ℕ) (hq : 1 ≤ q) (hr1 : 1 ≤ r) (hr2 : r ≤ 2)
include hq hr1 hr2

theorem orderIndex_lt (i : Fin (3 * q + r - 1)) : orderIndex q r i.val < 3 * q + r - 1 := by
  unfold orderIndex
  split_ifs <;> have := i.isLt <;> omega

noncomputable def order : Equiv.Perm (Fin (3 * q + r - 1)) := Equiv.ofBijective
  (fun i => ⟨orderIndex q r i.val, orderIndex_lt q r hq hr1 hr2 i⟩) (by
    have hi : Function.Injective (fun i : Fin (3 * q + r - 1) =>
        (⟨orderIndex q r i.val, orderIndex_lt q r hq hr1 hr2 i⟩ : Fin (3 * q + r - 1))) := by
      intro i j h
      apply Fin.ext
      have he := congrArg Fin.val h
      change orderIndex q r i.val = orderIndex q r j.val at he
      unfold orderIndex at he
      split_ifs at he <;> have := i.isLt <;> have := j.isLt <;> omega
    exact ⟨hi, Finite.surjective_of_injective hi⟩)

theorem chi_order (i : Fin (3 * q + r - 1)) :
    chi (3 * q + r) (by omega) (order q r hq hr1 hr2 i) =
      order q r hq hr1 hr2 (finRotate (3 * q + r - 1) i) := by
  apply Fin.ext
  change chiIndex (3 * q + r) (orderIndex q r i.val) =
    orderIndex q r (finRotate (3 * q + r - 1) i).val
  letI : NeZero (3 * q + r - 1) := ⟨by omega⟩
  have hv : (finRotate (3 * q + r - 1) i).val =
      if i.val + 1 < 3 * q + r - 1 then i.val + 1 else 0 := by
    rw [finRotate_apply, Fin.val_add, Fin.val_one']
    have hi := i.isLt
    have h1 : 1 % (3 * q + r - 1) = 1 := Nat.mod_eq_of_lt (by omega)
    rw [h1]
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · have he : i.val + 1 = 3 * q + r - 1 := by omega
      rw [he, Nat.mod_self]
  rw [hv]
  have hi := i.isLt
  generalize ho : orderIndex q r i.val = o
  unfold orderIndex at ho
  split_ifs at ho <;> try (first | contradiction | omega)
  all_goals subst o
  all_goals unfold chiIndex
  all_goals split_ifs <;> try (first | contradiction | omega)
  all_goals unfold orderIndex
  all_goals split_ifs <;> first | contradiction | omega

theorem chi_hamilton_residue : Shared.IsSingleCycleMap (chi (3 * q + r) (by omega)) :=
  Surgery.singleCycle_of_cyclic_order (by omega) (order q r hq hr1 hr2) _
    (chi_order q r hq hr1 hr2)

omit hq hr1 hr2 in
theorem chi_hamilton (k : ℕ) (hk : 4 ≤ k) (hd : ¬ 3 ∣ k) :
    Shared.IsSingleCycleMap (chi k hk) := by
  have hr : k % 3 ≠ 0 := fun h => hd (Nat.dvd_of_mod_eq_zero h)
  obtain ⟨q, r, hq, hr1, hr2, rfl⟩ :
      ∃ q r, 1 ≤ q ∧ 1 ≤ r ∧ r ≤ 2 ∧ k = 3 * q + r :=
    ⟨k / 3, k % 3, by omega, by omega, by omega, by omega⟩
  exact chi_hamilton_residue q r hq hr1 hr2

end TorusEven.Entry.Star.Nondivisible
