import TorusD3Odd.Basic
import TorusD4.Cycles
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace TorusD3Odd

def F0 (u : P0Coord m) : P0Coord m :=
  let (i, k) := u
  (i - 2 + TorusD4.delta m (k = 0), k + 1)

def F1 (u : P0Coord m) : P0Coord m :=
  let (i, k) := u
  (i + TorusD4.delta m (k = (-1 : ZMod m)), k + 1)

def F2 (u : P0Coord m) : P0Coord m :=
  let (i, k) := u
  (i + 2 - 2 * TorusD4.delta m (k = 0), k - 2)

def psi0 (u : P0Coord m) : P0Coord m :=
  (u.2, u.1 + 2 * u.2)

def psi1 (u : P0Coord m) : P0Coord m :=
  (u.2 + 1, u.1)

def lambda [Fact (Odd m)] : ZMod m :=
  -((2 : ZMod m)⁻¹)

def psi2 [Fact (Odd m)] (u : P0Coord m) : P0Coord m :=
  (lambda (m := m) * u.2, lambda (m := m) * (u.1 + u.2))

theorem psi0_conj (u : P0Coord m) :
    psi0 (F0 (m := m) u) = TorusD4.odometer (m := m) (psi0 u) := by
  rcases u with ⟨i, k⟩
  ext <;> by_cases hk0 : k = 0 <;>
    simp [psi0, F0, TorusD4.odometer, TorusD4.delta, hk0]
  · ring
  · ring

theorem psi1_conj (u : P0Coord m) :
    psi1 (F1 (m := m) u) = TorusD4.odometer (m := m) (psi1 u) := by
  rcases u with ⟨i, k⟩
  ext
  · simp [psi1, F1, TorusD4.odometer]
  · by_cases hkneg1 : k = (-1 : ZMod m)
    · simp [psi1, F1, TorusD4.odometer, TorusD4.delta, hkneg1]
    · have hk1ne : k + 1 ≠ (0 : ZMod m) := by
        intro hk1
        exact hkneg1 (eq_neg_iff_add_eq_zero.mpr hk1)
      simp [psi1, F1, TorusD4.odometer, TorusD4.delta, hkneg1, hk1ne]

theorem two_mul_lambda [Fact (Odd m)] :
    (2 : ZMod m) * lambda (m := m) = (-1 : ZMod m) := by
  have hcop : Nat.Coprime 2 m := (Fact.out : Odd m).coprime_two_left
  calc
    (2 : ZMod m) * lambda (m := m) = -((2 : ZMod m) * (2 : ZMod m)⁻¹) := by
      simp [lambda]
    _ = -((1 : ZMod m)) := by
      simpa using congrArg Neg.neg (ZMod.coe_mul_inv_eq_one 2 hcop)
    _ = (-1 : ZMod m) := by simp

theorem neg_two_mul_lambda [Fact (Odd m)] :
    (-2 : ZMod m) * lambda (m := m) = (1 : ZMod m) := by
  calc
    (-2 : ZMod m) * lambda (m := m) = -((2 : ZMod m) * lambda (m := m)) := by ring
    _ = (1 : ZMod m) := by rw [two_mul_lambda (m := m)]; simp

theorem lambda_mul_neg_two [Fact (Odd m)] :
    lambda (m := m) * (-2 : ZMod m) = (1 : ZMod m) := by
  rw [mul_comm, neg_two_mul_lambda (m := m)]

theorem lambda_mul_eq_zero_iff [Fact (Odd m)] (k : ZMod m) :
    lambda (m := m) * k = 0 ↔ k = 0 := by
  constructor
  · intro hk
    calc
      k = (1 : ZMod m) * k := by simp
      _ = (lambda (m := m) * (-2 : ZMod m)) * k := by rw [lambda_mul_neg_two (m := m)]
      _ = lambda (m := m) * ((-2 : ZMod m) * k) := by ring
      _ = (-2 : ZMod m) * (lambda (m := m) * k) := by ring
      _ = 0 := by rw [hk, mul_zero]
  · intro hk
    simp [hk]

theorem psi2_conj [Fact (Odd m)] (u : P0Coord m) :
    psi2 (m := m) (F2 (m := m) u) = TorusD4.odometer (m := m) (psi2 (m := m) u) := by
  rcases u with ⟨i, k⟩
  ext
  · calc
      lambda (m := m) * (k - 2) = lambda (m := m) * k + lambda (m := m) * (-2 : ZMod m) := by
        ring
      _ = lambda (m := m) * k + 1 := by rw [lambda_mul_neg_two (m := m)]
      _ = (psi2 (m := m) (i, k)).1 + 1 := by simp [psi2]
      _ = (TorusD4.odometer (m := m) (psi2 (m := m) (i, k))).1 := by
        simp [TorusD4.odometer]
  · by_cases hk0 : k = 0
    · have hku0 : (psi2 (m := m) (i, k)).1 = 0 := by
        simp [psi2, hk0]
      have hlam0 : lambda (m := m) * k = 0 := by
        simpa [psi2] using hku0
      calc
        lambda (m := m) * ((i + 2 - 2 * TorusD4.delta m (k = 0)) + (k - 2))
            = lambda (m := m) * (i + k - 2 * TorusD4.delta m (k = 0)) := by ring
        _ = lambda (m := m) * (i + k) + lambda (m := m) * ((-2 : ZMod m) * TorusD4.delta m (k = 0)) := by
              ring
        _ = lambda (m := m) * (i + k) + (lambda (m := m) * (-2 : ZMod m)) * TorusD4.delta m (k = 0) := by
              ring
        _ = lambda (m := m) * (i + k) + TorusD4.delta m (k = 0) := by
              rw [lambda_mul_neg_two (m := m), one_mul]
        _ = lambda (m := m) * (i + k) + 1 := by simp [TorusD4.delta, hk0]
        _ = (TorusD4.odometer (m := m) (psi2 (m := m) (i, k))).2 := by
              simp [TorusD4.odometer, psi2, TorusD4.delta, hk0, hlam0]
    · have hku0 : (psi2 (m := m) (i, k)).1 ≠ 0 := by
        intro h
        exact hk0 ((lambda_mul_eq_zero_iff (m := m) k).mp h)
      have hlam0 : lambda (m := m) * k ≠ 0 := by
        simpa [psi2] using hku0
      calc
        lambda (m := m) * ((i + 2 - 2 * TorusD4.delta m (k = 0)) + (k - 2))
            = lambda (m := m) * (i + k - 2 * TorusD4.delta m (k = 0)) := by ring
        _ = lambda (m := m) * (i + k) + lambda (m := m) * ((-2 : ZMod m) * TorusD4.delta m (k = 0)) := by
              ring
        _ = lambda (m := m) * (i + k) + (lambda (m := m) * (-2 : ZMod m)) * TorusD4.delta m (k = 0) := by
              ring
        _ = lambda (m := m) * (i + k) + TorusD4.delta m (k = 0) := by
              rw [lambda_mul_neg_two (m := m), one_mul]
        _ = lambda (m := m) * (i + k) := by simp [TorusD4.delta, hk0]
        _ = (TorusD4.odometer (m := m) (psi2 (m := m) (i, k))).2 := by
              simp [TorusD4.odometer, psi2, TorusD4.delta, hk0, hlam0]

end TorusD3Odd
