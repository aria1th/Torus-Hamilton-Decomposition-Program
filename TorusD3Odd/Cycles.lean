import TorusD3Odd.ReturnMaps

namespace TorusD3Odd

def psi0Equiv : P0Coord m ≃ P0Coord m where
  toFun := psi0
  invFun u := (u.2 - 2 * u.1, u.1)
  left_inv u := by
    rcases u with ⟨i, k⟩
    ext <;> simp [psi0]
  right_inv u := by
    rcases u with ⟨a, b⟩
    ext <;> simp [psi0]

def psi1Equiv : P0Coord m ≃ P0Coord m where
  toFun := psi1
  invFun u := (u.2, u.1 - 1)
  left_inv u := by
    rcases u with ⟨i, k⟩
    ext <;> simp [psi1]
  right_inv u := by
    rcases u with ⟨a, b⟩
    ext <;> simp [psi1]

def psi2Equiv [Fact (Odd m)] : P0Coord m ≃ P0Coord m where
  toFun := psi2 (m := m)
  invFun u := ((-2 : ZMod m) * (u.2 - u.1), (-2 : ZMod m) * u.1)
  left_inv u := by
    rcases u with ⟨i, k⟩
    ext
    · change (-2 : ZMod m) * (lambda (m := m) * (i + k) - lambda (m := m) * k) = i
      calc
        (-2 : ZMod m) * (lambda (m := m) * (i + k) - lambda (m := m) * k)
            = ((-2 : ZMod m) * lambda (m := m)) * i := by
                ring
        _ = i := by
              rw [neg_two_mul_lambda (m := m)]
              simp
    · change (-2 : ZMod m) * (lambda (m := m) * k) = k
      calc
        (-2 : ZMod m) * (lambda (m := m) * k)
            = ((-2 : ZMod m) * lambda (m := m)) * k := by
                ring
        _ = k := by
              rw [neg_two_mul_lambda (m := m)]
              simp
  right_inv u := by
    rcases u with ⟨a, b⟩
    ext
    · change lambda (m := m) * ((-2 : ZMod m) * a) = a
      calc
        lambda (m := m) * ((-2 : ZMod m) * a)
            = (lambda (m := m) * (-2 : ZMod m)) * a := by
                ring
        _ = a := by
              rw [lambda_mul_neg_two (m := m)]
              simp
    · change
        lambda (m := m) * (((-2 : ZMod m) * (b - a)) + ((-2 : ZMod m) * a)) = b
      calc
        lambda (m := m) * (((-2 : ZMod m) * (b - a)) + ((-2 : ZMod m) * a))
            = lambda (m := m) * ((-2 : ZMod m) * b) := by
                ring
        _ = (lambda (m := m) * (-2 : ZMod m)) * b := by
              ring
        _ = b := by
              rw [lambda_mul_neg_two (m := m)]
              simp

theorem pos_of_odd [Fact (Odd m)] : 0 < m := by
  have hm : Odd m := Fact.out
  exact Nat.pos_of_ne_zero (by
    intro h
    simp [h] at hm)

theorem hasCycle_F0 [Fact (0 < m)] :
    TorusD4.HasCycle (m * m) (F0 (m := m)) := by
  refine ⟨psi0Equiv.symm (TorusD4.shiftEquiv ((0 : ZMod m), (0 : ZMod m))), ?_⟩
  have hsemi : Function.Semiconj psi0Equiv (F0 (m := m)) (TorusD4.odometer (m := m)) := psi0_conj
  have hsymm : Function.Semiconj psi0Equiv.symm (TorusD4.odometer (m := m)) (F0 (m := m)) :=
    hsemi.inverse_left psi0Equiv.left_inv psi0Equiv.right_inv
  exact TorusD4.cycleOn_conj psi0Equiv.symm
    (f := TorusD4.odometer (m := m)) (g := F0 (m := m)) hsymm
    (TorusD4.cycleOn_odometer (m := m))

theorem hasCycle_F1 [Fact (0 < m)] :
    TorusD4.HasCycle (m * m) (F1 (m := m)) := by
  refine ⟨psi1Equiv.symm (TorusD4.shiftEquiv ((0 : ZMod m), (0 : ZMod m))), ?_⟩
  have hsemi : Function.Semiconj psi1Equiv (F1 (m := m)) (TorusD4.odometer (m := m)) := psi1_conj
  have hsymm : Function.Semiconj psi1Equiv.symm (TorusD4.odometer (m := m)) (F1 (m := m)) :=
    hsemi.inverse_left psi1Equiv.left_inv psi1Equiv.right_inv
  exact TorusD4.cycleOn_conj psi1Equiv.symm
    (f := TorusD4.odometer (m := m)) (g := F1 (m := m)) hsymm
    (TorusD4.cycleOn_odometer (m := m))

theorem hasCycle_F2 [Fact (Odd m)] :
    TorusD4.HasCycle (m * m) (F2 (m := m)) := by
  letI : Fact (0 < m) := ⟨pos_of_odd (m := m)⟩
  refine
    ⟨(psi2Equiv (m := m)).symm (TorusD4.shiftEquiv ((0 : ZMod m), (0 : ZMod m))), ?_⟩
  have hsemi :
      Function.Semiconj (psi2Equiv (m := m)) (F2 (m := m)) (TorusD4.odometer (m := m)) := psi2_conj
  have hsymm :
      Function.Semiconj (psi2Equiv (m := m)).symm (TorusD4.odometer (m := m)) (F2 (m := m)) :=
    hsemi.inverse_left (psi2Equiv (m := m)).left_inv (psi2Equiv (m := m)).right_inv
  exact TorusD4.cycleOn_conj (psi2Equiv (m := m)).symm
    (f := TorusD4.odometer (m := m)) (g := F2 (m := m)) hsymm
    (TorusD4.cycleOn_odometer (m := m))

end TorusD3Odd
