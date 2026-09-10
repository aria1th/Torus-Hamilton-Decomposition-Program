import TorusD3Odometer.Lift
import TorusD3Even.Color2

namespace TorusD3Odometer

abbrev linePoint2 (m : ℕ) := TorusD3Even.linePoint (m := m)
abbrev laneMap2 (m : ℕ) := TorusD3Even.T2 (m := m)
abbrev returnMap2 (m : ℕ) := TorusD3Even.R2xy (m := m)
abbrev returnTime2 (m : ℕ) := TorusD3Even.rho2 (m := m)
abbrev psiLane2 (m : ℕ) := TorusD3Even.psiT2 (m := m)

def psiLane2Equiv [Fact (2 < m)] : ZMod m ≃ ZMod m :=
  TorusD3Even.psiT2Equiv (m := m)

theorem psiLane2_conj [Fact (2 < m)] (x : ZMod m) :
    psiLane2 (m := m) (laneMap2 (m := m) x) =
      TorusD3Even.succMap (m := m) (psiLane2 (m := m) x) := by
  simpa [psiLane2, laneMap2] using TorusD3Even.psiT2_conj (m := m) x

theorem cycleOn_laneMap2 [Fact (2 < m)] :
    TorusD4.CycleOn m (laneMap2 (m := m)) (0 : ZMod m) := by
  simpa [laneMap2] using TorusD3Even.cycleOn_T2 (m := m)

theorem cycleOn_returnMap2 [Fact (Even m)] [Fact (5 < m)] :
    TorusD4.CycleOn (m ^ 2) (returnMap2 (m := m))
      (linePoint2 (m := m) (0 : ZMod m)) := by
  simpa [returnMap2, linePoint2] using TorusD3Even.cycleOn_color2 (m := m)

theorem blockTime_returnMap2 [Fact (Even m)] [Fact (5 < m)] :
    TorusD3Even.blockTime (laneMap2 (m := m)) (returnTime2 (m := m)) (0 : ZMod m) m = m ^ 2 := by
  simpa [laneMap2, returnTime2] using TorusD3Even.hsum (m := m)

theorem cycleOn_full_of_color2_return
    [Fact (Even m)] [Fact (5 < m)]
    {F : FullCoord m → FullCoord m}
    (hstep : ∀ z, (F z).2 = z.2 + 1)
    (hreturn : ∀ u, (F^[m]) (TorusD4.slicePoint (0 : ZMod m) u) =
      TorusD4.slicePoint (0 : ZMod m) (returnMap2 (m := m) u)) :
    TorusD4.CycleOn (m ^ 3) F (TorusD4.slicePoint (0 : ZMod m) (linePoint2 (m := m) (0 : ZMod m))) := by
  have hm0 : 0 < m := by
    have hm5 : 5 < m := Fact.out
    omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : NeZero m := ⟨Nat.ne_of_gt hm0⟩
  simpa [linePoint2] using
    cycleOn_full_of_cycleOn_p0 (m := m) (F := F) (T := returnMap2 (m := m))
      hstep hreturn (u := linePoint2 (m := m) (0 : ZMod m)) (cycleOn_returnMap2 (m := m))

end TorusD3Odometer
