-- STATUS: main-path
import TorusEven.Entry.Star.Factorization
import TorusEven.Entry.Star.Carry
import TorusEven.Entry.Star.OneSpecial

namespace TorusEven.Entry.Star

open Collar Surgery

variable {m : ℕ} [NeZero m] (hm : 4 ≤ m)

def returnMap (c : Fin 3) (p : Plane m) : Plane m := surgeryMap c p + voltage c

noncomputable def returnPerm (c : Fin 3) : Equiv.Perm (Plane m) :=
  (surgeryPerm hm c).trans (Equiv.addRight (voltage c))

@[simp] theorem returnPerm_apply (c : Fin 3) (p : Plane m) :
    returnPerm hm c p = returnMap c p := by
  change surgeryPerm hm c p + voltage c = _
  rw [surgeryPerm_apply]
  rfl

theorem height_return (c : Fin 3) (p : Plane m) :
    (heightStep hm c)^[m] (1, p) = (1, returnPerm hm c p) := by
  have hs (h : ZMod m) (q : Plane m) : heightStep hm c (h, q) =
      (h + 1, (if h = 1 then surgeryPerm hm c q else q) + carry c h) := by
    by_cases hh : h = 1 <;> simp [heightStep, layer, carry, hh]
  have hr := oneSpecial_return (heightStep hm c) (surgeryPerm hm c) (carry c) 1 hs p
  simpa only [carry_sum hm] using hr

omit [NeZero m] in
theorem returnMap_rotate (c : Fin 3) (p : Plane m) :
    returnMap (rotate c) (turn p) = turn (returnMap c p) := by
  simp only [returnMap, surgeryMap_rotate, voltage_rotate, map_add]

theorem return_singleCycle_rotate (c : Fin 3)
    (hc : Shared.IsSingleCycleMap (returnPerm hm c)) :
    Shared.IsSingleCycleMap (returnPerm hm (rotate c)) := by
  have hs : Function.Semiconj (turn (m := m)) (returnPerm hm c) (returnPerm hm (rotate c)) := by
    intro p
    simp only [returnPerm_apply, returnMap_rotate]
  apply singleCycle_of_circuitCount_one
  exact (circuitCount_congr _ _ turn.toEquiv hs).symm.trans (circuitCount_one_of_singleCycle _ hc)

theorem return_singleCycle (h0 : Shared.IsSingleCycleMap (returnMap (m := m) 0)) (c : Fin 3) :
    Shared.IsSingleCycleMap (returnPerm hm c) := by
  have hzero : Shared.IsSingleCycleMap (returnPerm hm 0) := by
    simpa only [show (returnPerm hm 0 : Plane m → Plane m) = returnMap 0 from
      funext (returnPerm_apply hm 0)] using h0
  fin_cases c
  · exact hzero
  · exact return_singleCycle_rotate hm 0 hzero
  · exact return_singleCycle_rotate hm 1 (return_singleCycle_rotate hm 0 hzero)

theorem hamilton_of_return (h0 : Shared.IsSingleCycleMap (returnMap (m := m) 0)) (c : Fin 3) :
    Shared.IsSingleCycleMap ((factorization hm).step c) := by
  let c' := (Equiv.swap 1 2) c
  have hh : Shared.IsSingleCycleMap (heightStep hm c') :=
    singleCycle_of_section (heightStep hm c') 1 (fun _ => rfl)
      (returnPerm hm c') (height_return hm c') (return_singleCycle hm h0 c')
  have hs : Function.Semiconj (chart (m := m)) (heightStep hm c') (step hm c') :=
    fun p => (step_chart hm c' p).symm
  apply singleCycle_of_circuitCount_one
  exact (circuitCount_congr _ _ chart hs).symm.trans (circuitCount_one_of_singleCycle _ hh)

theorem replacement_hamilton_of_return (h0 : Shared.IsSingleCycleMap (returnMap (m := m) 0))
    (c : Fin 3) : Shared.IsSingleCycleMap ((replacement hm).factorization.step c) := by
  rw [replacement_step]
  exact hamilton_of_return hm h0 c

end TorusEven.Entry.Star
