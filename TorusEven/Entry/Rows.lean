-- STATUS: main-path
import TorusEven.Collar.Multitorus

namespace TorusEven.Entry

abbrev Point (m : ℕ) := Fin 3 → ZMod m

def height {m : ℕ} (v : Point m) : ZMod m := v 0 + v 1 + v 2

def rotate : Equiv.Perm (Fin 3) where
  toFun := ![1, 2, 0]
  invFun := ![2, 0, 1]
  left_inv c := by fin_cases c <;> rfl
  right_inv c := by fin_cases c <;> rfl

def reflection (z : Fin 3) : Equiv.Perm (Fin 3) :=
  ![Equiv.swap 1 2, Equiv.swap 0 2, Equiv.swap 0 1] z

def nearRow {m : ℕ} (h w : ZMod m) : Equiv.Perm (Fin 3) :=
  if h = 0 then Equiv.swap 0 2 else
  if h = 1 then (if w = 0 ∨ w = 1 then Equiv.swap 1 2 else rotate) else
  if h = 2 ∧ w = 0 then Equiv.swap 0 1 else Equiv.refl _

def starRayRow {m : ℕ} (z : Fin 3) (t : ZMod m) : Equiv.Perm (Fin 3) :=
  if t = 1 then rotate.symm else if t = -1 then rotate else reflection z

def starRow {m : ℕ} (a b : ZMod m) : Equiv.Perm (Fin 3) :=
  if a = 0 ∧ b = 0 then Equiv.refl _ else
  if a + b = 0 then starRayRow 0 a else
  if a = 0 then starRayRow 1 b else
  if b = 0 then starRayRow 2 (-a) else Equiv.refl _

def constantRow {m : ℕ} (h : ZMod m) : Equiv.Perm (Fin 3) :=
  if h = 2 then rotate else
  if ¬ 3 ∣ m ∨ h = 0 ∨ h = 3 ∨ h = 4 then rotate.symm else Equiv.refl _

def terminalRow {m : ℕ} (v : Point m) : Equiv.Perm (Fin 3) :=
  (Equiv.swap 1 2).trans
    (if height v = 1 then starRow (v 1) (v 2 - 3) else constantRow (height v))

def anchor {m : ℕ} (q : Fin 4) : Point m :=
  ![![0, 1, 0], ![1, 1, 0], ![0, 0, 0], ![0, -2, 3]] q

def anchors (m : ℕ) : Set (Point m) := Set.range (anchor (m := m))

theorem cast_ne_zero {m n : ℕ} (hn : 0 < n) (hnm : n < m) : (n : ZMod m) ≠ 0 := by
  intro h
  exact Nat.not_dvd_of_pos_of_lt hn hnm ((ZMod.natCast_eq_zero_iff n m).mp h)

theorem anchor_agreement {m : ℕ} (hm : 4 ≤ m) (q : Fin 4) :
    terminalRow (anchor (m := m) q) = nearRow (m := m) (height (anchor q)) (anchor q 2) := by
  have h1 : (1 : ZMod m) ≠ 0 := by
    simpa using cast_ne_zero (m := m) (n := 1) (by omega) (by omega)
  have h2 : (2 : ZMod m) ≠ 0 := by
    simpa using cast_ne_zero (m := m) (n := 2) (by omega) (by omega)
  have h3 : (3 : ZMod m) ≠ 0 := by
    simpa using cast_ne_zero (m := m) (n := 3) (by omega) (by omega)
  have h21 : (2 : ZMod m) ≠ 1 := by intro h; apply h1; linear_combination h
  have h31 : (3 : ZMod m) ≠ 1 := by intro h; apply h2; linear_combination h
  have h2n : (2 : ZMod m) ≠ -1 := by intro h; apply h3; linear_combination h
  apply Equiv.ext
  intro c
  fin_cases q <;> fin_cases c <;>
    simp [anchor, terminalRow, height, nearRow, starRow, starRayRow, constantRow,
      rotate, reflection, Equiv.swap_apply_def, h1, h2, h3, h21, h31, h2n,
      Ne.symm h1, Ne.symm h2, show (1 : ZMod m) + 1 = 2 by ring,
      show (1 : ZMod m) + -3 = -2 by ring, show -(2 : ZMod m) + 3 = 1 by ring]

end TorusEven.Entry
