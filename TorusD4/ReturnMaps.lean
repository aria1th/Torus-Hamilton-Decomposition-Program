import TorusD4.Basic
import Mathlib.Tactic.Ring

namespace TorusD4

abbrev P0Coord (m : ℕ) := ZMod m × ZMod m × ZMod m
abbrev QCoord (m : ℕ) := ZMod m × ZMod m

def delta (m : ℕ) (p : Prop) [Decidable p] : ZMod m := if p then 1 else 0

def R0 (x : P0Coord m) : P0Coord m :=
  let (a, b, q0) := x
  if q0 = 0 then
    (a - 1, b, q0 - 1)
  else if q0 = -1 ∧ b = 1 then
    (a - 2, b + 1, q0 - 1)
  else
    (a - 1, b + 1, q0 - 1)

def R1 (x : P0Coord m) : P0Coord m :=
  let (a, b, q0) := x
  if q0 = 0 then
    (a, b - 1, q0 + 1)
  else if q0 = -1 ∧ a = -1 then
    (a + 1, b - 2, q0 + 1)
  else
    (a + 1, b - 1, q0 + 1)

def R2 (x : P0Coord m) : P0Coord m :=
  let (a, b, q0) := x
  if q0 = 0 then
    (a, b + 1, q0 - 1)
  else if q0 = -1 ∧ b = 2 then
    (a + 1, b, q0 - 1)
  else
    (a, b, q0 - 1)

def R3 (x : P0Coord m) : P0Coord m :=
  let (a, b, q0) := x
  if q0 = 0 then
    (a + 1, b, q0 + 1)
  else if q0 = -1 ∧ a = 0 then
    (a, b + 1, q0 + 1)
  else
    (a, b, q0 + 1)

def T0 (x : QCoord m) : QCoord m :=
  let (a, b) := x
  (a - delta m (b = (1 : ZMod m)), b - 1)

def T1 (x : QCoord m) : QCoord m :=
  let (a, b) := x
  (a - 1, b - delta m (a = (-1 : ZMod m)))

def T2 (x : QCoord m) : QCoord m :=
  let (a, b) := x
  (a + delta m (b = (2 : ZMod m)), b + 1)

def T3 (x : QCoord m) : QCoord m :=
  let (a, b) := x
  (a + 1, b + delta m (a = (0 : ZMod m)))

def odometer (x : QCoord m) : QCoord m :=
  let (u, v) := x
  (u + 1, v + delta m (u = (0 : ZMod m)))

def psi0 (x : QCoord m) : QCoord m :=
  let (a, b) := x
  (1 - b, -a)

def psi1 (x : QCoord m) : QCoord m :=
  let (a, b) := x
  (-a - 1, -b)

def psi2 (x : QCoord m) : QCoord m :=
  let (a, b) := x
  (b - 2, a)

def psi3 (x : QCoord m) : QCoord m := x

@[simp] theorem delta_true (m : ℕ) : delta m True = 1 := by
  simp [delta]

@[simp] theorem delta_false (m : ℕ) : delta m False = 0 := by
  simp [delta]

@[simp] theorem sub_eq_zero_iff_eq (x c : ZMod m) : x - c = 0 ↔ x = c := by
  simpa using (sub_eq_zero : x - c = 0 ↔ x = c)

@[simp] theorem one_sub_eq_zero_iff (x : ZMod m) : 1 - x = 0 ↔ x = 1 := by
  simpa [eq_comm] using (sub_eq_zero : (1 : ZMod m) - x = 0 ↔ (1 : ZMod m) = x)

@[simp] theorem sub_two_eq_zero_iff (x : ZMod m) : x - 2 = 0 ↔ x = 2 := by
  exact (sub_eq_zero : x - (2 : ZMod m) = 0 ↔ x = 2)

@[simp] theorem neg_add_one_eq_zero_iff (x : ZMod m) : -x + 1 = 0 ↔ x = 1 := by
  simpa [sub_eq_add_neg, add_comm] using (one_sub_eq_zero_iff x)

@[simp] theorem neg_sub_one_eq_zero_iff (x : ZMod m) : -x - 1 = 0 ↔ x = -1 := by
  constructor
  · intro h
    have h' : (-x : ZMod m) = 1 := by
      exact sub_eq_zero.mp h
    exact neg_eq_iff_eq_neg.mp h'
  · intro h
    simp [h]

@[simp] theorem neg_add_neg_one_eq_zero_iff (x : ZMod m) : -x + (-1 : ZMod m) = 0 ↔ x = -1 := by
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (neg_sub_one_eq_zero_iff x)

theorem psi0_conj (x : QCoord m) : psi0 (T0 x) = odometer (psi0 x) := by
  rcases x with ⟨a, b⟩
  ext
  · simp [psi0, T0, odometer, delta]
    ring
  · by_cases hb : b = (1 : ZMod m)
    · simp [psi0, T0, odometer, delta, hb, sub_eq_add_neg, add_comm]
    · simp [psi0, T0, odometer, delta, hb, sub_eq_add_neg, add_comm]

theorem psi1_conj (x : QCoord m) : psi1 (T1 x) = odometer (psi1 x) := by
  rcases x with ⟨a, b⟩
  ext
  · simp [psi1, T1, odometer, delta]
  · by_cases ha : a = (-1 : ZMod m)
    · simp [psi1, T1, odometer, delta, ha, sub_eq_add_neg, add_comm]
    · simp [psi1, T1, odometer, delta, ha, sub_eq_add_neg, add_comm]

theorem psi2_conj (x : QCoord m) : psi2 (T2 x) = odometer (psi2 x) := by
  rcases x with ⟨a, b⟩
  ext <;> simp [psi2, T2, odometer, delta]
  ring

theorem psi3_conj (x : QCoord m) : psi3 (T3 x) = odometer (psi3 x) := by
  rcases x with ⟨a, b⟩
  ext <;> simp [psi3, T3, odometer, delta]

end TorusD4
