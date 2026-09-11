-- STATUS: main-path
import TorusEven.Entry.Shell.Rows
import TorusEven.Entry.Shell.Partition
import TorusEven.Entry.LayerSums

namespace TorusEven.Entry.Shell

open Collar

variable (p : ℕ) (hp : 2 ≤ p) {m : ℕ} [NeZero m] (hm : 4 ≤ m)

omit [NeZero m] in
include hp in
private theorem wVoltage_nat (c : Color p) (h : ℕ) :
    (if aUser p h c.val then (0 : ZMod m) else 1) =
      if h = (if c.val = 0 ∨ c.val = p then 0 else 1) then
        (if c.val < p then 0 else 1) else (if c.val < p then 1 else 0) := by
  unfold aUser
  split_ifs <;> first | rfl | omega

include hp hm in
theorem wVoltage_sum (c : Color p) :
    (∑ h : ZMod m, wVoltage p c h) = if c.val < p then -1 else 1 := by
  let t : ℕ := if c.val = 0 ∨ c.val = p then 0 else 1
  have ht : t < m := by unfold t; split_ifs <;> omega
  have hv (h : ZMod m) : h.val = t ↔ h = (t : ZMod m) := by
    have he : h.val = (t : ZMod m).val ↔ h = (t : ZMod m) := (ZMod.val_injective m).eq_iff
    simpa only [ZMod.val_natCast_of_lt ht] using he
  have he (h : ZMod m) : wVoltage p c h = if h = (t : ZMod m) then
      (if c.val < p then 0 else 1) else (if c.val < p then 1 else 0) := by
    simp only [wVoltage, mem_aUsers, wVoltage_nat p hp, ← hv]
    rfl
  simp_rw [he]
  rw [sum_zmod_if_eq]
  split_ifs <;> ring

def layerCarry (c : Color p) (h : ℕ) : ZMod m :=
  ∑ i : Fin (pairCount p h),
    ((if endpoint p hp h (i, true) = c then 1 else 0) -
      (if endpoint p hp h (i, false) = c then 1 else 0))

theorem yVoltage_layer_sum (c : Color p) (h : ZMod m) :
    (∑ w : ZMod m, yVoltage p hp c (h, w)) = layerCarry p hp c h.val := by
  have he (w : ZMod m) : yVoltage p hp c (h, w) =
      ∑ x ∈ selected p hp h w, if x = c then (1 : ZMod m) else 0 := by
    simp [yVoltage]
  simp_rw [he]
  exact (pairs p hp h.val).sum_rows (fun x => if x = c then 1 else 0) event _
    (fillers_disjoint p hp h.val)

omit [NeZero m] in
theorem layerCarry_zero (c : Color p) (h : ℕ) (hh : 3 ≤ h) :
    layerCarry (m := m) p hp c h = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hi := i.isLt
  have ht := pairCount_height p h (by omega)
  omega

omit [NeZero m] in
theorem sum_layerCarry (c : Color p) :
    (∑ h : Fin 3, layerCarry p hp c h.val) =
      if ((pairEquiv p hp).symm c).2.2 then (1 : ZMod m) else -1 := by
  have he : (∑ h : Fin 3, layerCarry p hp c h.val) =
      ∑ q : PairSlot p, if pairEquiv p hp q = c then
        (if q.2.2 then (1 : ZMod m) else -1) else 0 := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro h _
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Fintype.sum_bool, pairEquiv_apply]
    change ((if endpoint p hp h.val (i, true) = c then (1 : ZMod m) else 0) -
      (if endpoint p hp h.val (i, false) = c then 1 else 0)) =
      (if endpoint p hp h.val (i, true) = c then 1 else 0) +
      (if endpoint p hp h.val (i, false) = c then -1 else 0)
    split_ifs <;> ring
  rw [he]
  simp only [Equiv.apply_eq_iff_eq_symm_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]

include hm in
theorem yVoltage_sum (c : Color p) :
    (∑ q : ZMod m × ZMod m, yVoltage p hp c q) =
      if ((pairEquiv p hp).symm c).2.2 then 1 else -1 := by
  rw [Fintype.sum_prod_type]
  simp only [yVoltage_layer_sum]
  rw [sum_zmod_val_of_support _ 3 (by omega) (layerCarry_zero p hp c)]
  exact sum_layerCarry p hp c

include hm in
theorem yVoltage_unit (c : Color p) : IsUnit (∑ q : ZMod m × ZMod m, yVoltage p hp c q) := by
  rw [yVoltage_sum p hp hm]
  split_ifs
  · exact isUnit_one
  · exact isUnit_one.neg

end TorusEven.Entry.Shell
