-- STATUS: main-path
import TorusEven.Entry.Shell.Factorization
import TorusEven.Entry.Shell.Carry
import TorusEven.Entry.Anchors

namespace TorusEven.Entry.Shell

open Collar Surgery

variable (p : ℕ) (hp : 2 ≤ p) {m : ℕ} [NeZero m] (hm : 4 ≤ m)
include hp hm

theorem base_hamilton (c : Color p) : Shared.IsSingleCycleMap (baseStep (m := m) p c) := by
  apply lift_singleCycle _ height_singleCycle _ 0
  rw [wVoltage_sum p hp hm]
  split_ifs
  · exact isUnit_one.neg
  · exact isUnit_one

theorem hamilton (c : Color p) :
    Shared.IsSingleCycleMap ((factorization (m := m) p hp).step c) := by
  have hl := lift_singleCycle (baseStep p c) (base_hamilton p hp hm c)
    (yVoltage p hp c) 0 (yVoltage_unit p hp hm c)
  exact Shared.single_cycle_of_equiv_conj NearCore.chart _ _ hl (by
    intro q
    change NearCore.chart.symm (step p hp c (NearCore.chart q)) = _
    rw [step_chart, Equiv.symm_apply_apply])

theorem circuitCount (c : Color p) :
    Surgery.circuitCount ((factorization (m := m) p hp).step c) = 1 :=
  circuitCount_one_of_singleCycle _ (hamilton p hp hm c)

theorem xChart_consistent : CircuitConsistent (factorization (m := m) p hp) xChart where
  direction c q s t := by
    change direction p hp (height (xChart (q, s))) q.2 c =
      direction p hp (height (xChart (q, t))) q.2 c
    simp only [height_xChart]
  circuit c q s t := (circuitOf_eq _ _ _).mpr ((hamilton p hp hm c).2 _ _)

noncomputable def labelEquiv : (factorization (m := m) p hp).CircuitLabel ≃ Color p where
  toFun q := q.1
  invFun c := ⟨c, circuitOf ((factorization p hp).step c) 0⟩
  left_inv q := by
    obtain ⟨c, q⟩ := q
    have hq : circuitOf ((factorization p hp).step c) 0 = q := by
      induction q using Quotient.inductionOn with | _ v =>
        exact (circuitOf_eq _ _ _).mpr ((hamilton p hp hm c).2 _ _)
    exact congrArg (fun r => (⟨c, r⟩ : (factorization p hp).CircuitLabel)) hq
  right_inv _ := rfl

end TorusEven.Entry.Shell
