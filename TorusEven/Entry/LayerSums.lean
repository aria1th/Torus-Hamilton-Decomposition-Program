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

end TorusEven.Entry
