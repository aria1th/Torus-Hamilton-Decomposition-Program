-- STATUS: main-path
import Shared.RankCycle

namespace TorusEven.Entry.Star.InnerReturn

variable (q : ℕ)

def orderIndex (i : ℕ) : ℕ :=
  if i < q - 1 then 2 * i else
  if i = q - 1 then 2 * q - 3 else
  if i = q then 2 * q - 1 else
  if i = q + 1 then 2 * q else
  if i < 2 * q then 2 * i - 2 * q - 3 else 2 * q - 2

def thetaIndex (i : ℕ) : ℕ :=
  if i = 0 then 2 * q - 1 else
  if i = 1 then 0 else
  if i = 2 then 2 * q else
  if i = 2 * q - 1 then 2 * q - 2 else
  if i = 2 * q then 2 * q - 3 else i - 2

def shiftIndex (i : ℕ) : ℕ := if i + 4 < 2 * q + 1 then i + 4 else i + 4 - (2 * q + 1)

variable (hq : 2 ≤ q)

include hq

theorem orderIndex_lt (i : Fin (2 * q + 1)) : orderIndex q i.val < 2 * q + 1 := by
  unfold orderIndex
  split_ifs <;> have := i.isLt <;> omega

noncomputable def order : Fin (2 * q + 1) ≃ Fin (2 * q + 1) := Equiv.ofBijective
  (fun i => ⟨orderIndex q i.val, orderIndex_lt q hq i⟩) (by
    have hinj : Function.Injective (fun i : Fin (2 * q + 1) =>
        (⟨orderIndex q i.val, orderIndex_lt q hq i⟩ : Fin (2 * q + 1))) := by
      intro i j h
      have he := congrArg Fin.val h
      apply Fin.ext
      change orderIndex q i.val = orderIndex q j.val at he
      unfold orderIndex at he
      split_ifs at he <;> have := i.isLt <;> have := j.isLt <;> omega
    exact ⟨hinj, Finite.surjective_of_injective hinj⟩)

theorem thetaIndex_lt (i : Fin (2 * q + 1)) : thetaIndex q i.val < 2 * q + 1 := by
  unfold thetaIndex
  split_ifs <;> have := i.isLt <;> omega

def theta (i : Fin (2 * q + 1)) : Fin (2 * q + 1) :=
  ⟨thetaIndex q i.val, thetaIndex_lt q hq i⟩

theorem theta_injective : Function.Injective (theta q hq) := by
  intro i j h
  have he := congrArg Fin.val h
  apply Fin.ext
  change thetaIndex q i.val = thetaIndex q j.val at he
  unfold thetaIndex at he
  split_ifs at he <;> have := i.isLt <;> have := j.isLt <;> omega

noncomputable def thetaPerm : Equiv.Perm (Fin (2 * q + 1)) :=
  Equiv.ofBijective (theta q hq)
    ⟨theta_injective q hq, Finite.surjective_of_injective (theta_injective q hq)⟩

theorem shiftIndex_eq (i : Fin (2 * q + 1)) : shiftIndex q i.val = (i.val + 4) % (2 * q + 1) := by
  unfold shiftIndex
  split_ifs with h
  · exact (Nat.mod_eq_of_lt h).symm
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by have := i.isLt; omega)]

def shift (i : Fin (2 * q + 1)) : Fin (2 * q + 1) :=
  ⟨shiftIndex q i.val, by rw [shiftIndex_eq q hq i]; exact Nat.mod_lt _ (by omega)⟩

def step (i : Fin (2 * q + 1)) : Fin (2 * q + 1) := theta q hq (shift q hq i)

theorem step_order (i : Fin (2 * q + 1)) :
    step q hq (order q hq i) = order q hq (finRotate (2 * q + 1) i) := by
  apply Fin.ext
  change thetaIndex q (shiftIndex q (orderIndex q i.val)) =
    orderIndex q (finRotate (2 * q + 1) i).val
  rw [finRotate_apply, Fin.val_add_one]
  simp only [Fin.ext_iff, Fin.val_last]
  have hi := i.isLt
  generalize ho : orderIndex q i.val = o
  unfold orderIndex at ho
  split_ifs at ho <;> try (first | contradiction | omega)
  all_goals subst o
  all_goals unfold shiftIndex
  all_goals split_ifs <;> try (first | contradiction | omega)
  all_goals unfold thetaIndex
  all_goals split_ifs <;> try (first | contradiction | omega)
  all_goals unfold orderIndex
  all_goals split_ifs <;> first | contradiction | omega

theorem hamilton : Shared.IsSingleCycleMap (step q hq) := by
  have hrot : Shared.IsSingleCycleMap (finRotate (2 * q + 1)) :=
    Shared.single_cycle_of_zmod_rank_equiv _ (ZMod.finEquiv (2 * q + 1)).toEquiv (by
      intro i
      change (ZMod.finEquiv (2 * q + 1)) (finRotate (2 * q + 1) i) =
        (ZMod.finEquiv (2 * q + 1)) i + 1
      simp only [finRotate_apply, map_add, map_one])
  have hs : Function.Semiconj (order q hq) (finRotate (2 * q + 1)) (step q hq) :=
    fun i => (step_order q hq i).symm
  refine ⟨?_, fun x y => ?_⟩
  · have he : step q hq = (order q hq) ∘ finRotate (2 * q + 1) ∘ (order q hq).symm := by
      funext x
      obtain ⟨i, rfl⟩ := (order q hq).surjective x
      simpa using step_order q hq i
    rw [he]
    exact (order q hq).bijective.comp ((finRotate _).bijective.comp (order q hq).symm.bijective)
  · obtain ⟨n, hn⟩ := hrot.2 ((order q hq).symm x) ((order q hq).symm y)
    refine ⟨n, ?_⟩
    simpa using (hs.iterate_right n ((order q hq).symm x)).symm.trans (congrArg (order q hq) hn)

end TorusEven.Entry.Star.InnerReturn
