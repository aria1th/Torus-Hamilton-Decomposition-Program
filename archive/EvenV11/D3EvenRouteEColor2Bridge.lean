import EvenV11.D3EvenRouteEGeSix
import EvenV11.CycleOnBridge
import Shared.Monodromy
import TorusD3Even.Color2

namespace EvenV11

/-!
Bridge data for reusing the old `TorusD3Even.Color2` first-return proof in the
current Route-E root-flat interface.
-/

noncomputable def routeEColorTwoCoordEquiv (m : Nat) :
    D3EvenRouteEGeSix.RootState m ≃ TorusD3Even.P0Coord m where
  toFun w := (w.1, -w.2)
  invFun u := (u.1, -u.2)
  left_inv := by
    intro w
    rcases w with ⟨a, b⟩
    simp
  right_inv := by
    intro u
    rcases u with ⟨a, b⟩
    simp

theorem oldR2xy_singleCycle
    {m : Nat} [NeZero m] (hm_even : Even m) (hm5 : 5 < m) :
    Shared.IsSingleCycleMap (TorusD3Even.R2xy (m := m)) := by
  letI : Fact (Even m) := ⟨hm_even⟩
  letI : Fact (5 < m) := ⟨hm5⟩
  have hm0 : 0 < m := by omega
  letI : NeZero (m ^ 2) := ⟨by
    exact pow_ne_zero 2 (Nat.ne_of_gt hm0)⟩
  have hN : 1 < m ^ 2 := by nlinarith
  exact isSingleCycleMap_of_cycleOn hN
    (TorusD3Even.cycleOn_color2 (m := m))

theorem routeEReturnTwoModel_eq_shifted_zeroLayer
    (m : Nat) (w : D3EvenRouteEGeSix.RootState m) :
    D3EvenRouteEGeSix.routeEReturnTwoModel m w =
      (D3EvenRouteEGeSix.rootShiftFirstIfSecondZero m)
        ((D3EvenRouteEGeSix.rootShiftSecondIfFirstNonzero m)
          (D3EvenRouteEGeSix.routeELayerMap m (0 : ZMod m)
            (2 : Shared.TorusColor 3) w)) := by
  rfl

/-- The old colour-2 first-return map transported to the current Route-E root
coordinates.  The remaining bridge obligation is to identify this map with
`D3EvenRouteEGeSix.routeEReturnTwoModel`. -/
noncomputable def routeEReturnTwoOldConjModel (m : Nat) :
    D3EvenRouteEGeSix.RootState m -> D3EvenRouteEGeSix.RootState m :=
  fun w => (routeEColorTwoCoordEquiv m).symm
    (TorusD3Even.R2xy (m := m) (routeEColorTwoCoordEquiv m w))

theorem routeEReturnTwoOldConjModel_eq_cases
    (m : Nat) (a b : ZMod m) :
    routeEReturnTwoOldConjModel m (a, b) =
      if a = 2 ∧ -b = (2 : ZMod m) then
        (a + 1, b + 2)
      else if -b = (1 : ZMod m) ∧ a ≠ 1 ∧ a ≠ (-1 : ZMod m) then
        (a + 2, b + 1)
      else if (b = 1 ∧ a ≠ (-1 : ZMod m)) ∨
          (a = (-1 : ZMod m) ∧ b = 2) then
        (a, b + 1)
      else if (-b = a ∧ a ≠ 0 ∧ a ≠ 2 ∧ a ≠ (-1 : ZMod m)) ∨
          (a = (-1 : ZMod m) ∧ b = 0) then
        (a, b + 2)
      else if (a = (-1 : ZMod m) ∧ -b ≠ 0 ∧ -b ≠ (-2 : ZMod m)) ∨
          (a = 0 ∧ b = 0) then
        (a + 1, b)
      else
        (a + 1, b + 1) := by
  simp [routeEReturnTwoOldConjModel, routeEColorTwoCoordEquiv,
    TorusD3Even.R2xy]
  split_ifs <;> ext <;> ring_nf

theorem routeEReturnTwoOldConjModel_singleCycle
    {m : Nat} [NeZero m] (hm_even : Even m) (hm5 : 5 < m) :
    Shared.IsSingleCycleMap (routeEReturnTwoOldConjModel m) := by
  refine Shared.single_cycle_of_equiv_conj
    ((routeEColorTwoCoordEquiv m).symm)
    (routeEReturnTwoOldConjModel m)
    (TorusD3Even.R2xy (m := m))
    (oldR2xy_singleCycle (m := m) hm_even hm5) ?_
  intro x
  simp [routeEReturnTwoOldConjModel]

theorem routeEReturnTwoModel_singleCycle_of_eq_oldConj
    {m : Nat} [NeZero m] (hm_even : Even m) (hm5 : 5 < m)
    (hEq :
      ∀ w : D3EvenRouteEGeSix.RootState m,
        D3EvenRouteEGeSix.routeEReturnTwoModel m w =
          routeEReturnTwoOldConjModel m w) :
    Shared.IsSingleCycleMap (D3EvenRouteEGeSix.routeEReturnTwoModel m) := by
  convert routeEReturnTwoOldConjModel_singleCycle
    (m := m) hm_even hm5 using 1
  funext w
  exact hEq w

theorem routeEReturnTwoModel_singleCycle_tail_of_eq_oldConj
    {m : Nat} [NeZero m] (hm_even : Even m) (hm14 : 14 <= m)
    (hEq :
      ∀ w : D3EvenRouteEGeSix.RootState m,
        D3EvenRouteEGeSix.routeEReturnTwoModel m w =
          routeEReturnTwoOldConjModel m w) :
    Shared.IsSingleCycleMap (D3EvenRouteEGeSix.routeEReturnTwoModel m) :=
  routeEReturnTwoModel_singleCycle_of_eq_oldConj
    (m := m) hm_even (by omega) hEq

end EvenV11
