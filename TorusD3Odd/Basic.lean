import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace TorusD3Odd

abbrev Coord := Fin 3
abbrev Color := Fin 3
abbrev Point (m : ℕ) := Coord → ZMod m
abbrev P0Coord (m : ℕ) := ZMod m × ZMod m
abbrev FullCoord (m : ℕ) := P0Coord m × ZMod m

def S (x : Point m) : ZMod m := x 0 + x 1 + x 2

def kCoord (x : Point m) : ZMod m := x 2

def bump (x : Point m) (d : Coord) : Point m :=
  fun i => x i + if i = d then 1 else 0

def phiLayer (u : P0Coord m) (s : ZMod m) : Point m :=
  let (i, k) := u
  ![i, s - i - k, k]

def coordOfPoint (x : Point m) : FullCoord m :=
  ((x 0, x 2), S x)

@[simp] theorem phiLayer_apply_0 (u : P0Coord m) (s : ZMod m) :
    phiLayer (m := m) u s 0 = u.1 := by
  rcases u with ⟨i, k⟩
  simp [phiLayer]

@[simp] theorem phiLayer_apply_1 (u : P0Coord m) (s : ZMod m) :
    phiLayer (m := m) u s 1 = s - u.1 - u.2 := by
  rcases u with ⟨i, k⟩
  simp [phiLayer]

@[simp] theorem phiLayer_apply_2 (u : P0Coord m) (s : ZMod m) :
    phiLayer (m := m) u s 2 = u.2 := by
  rcases u with ⟨i, k⟩
  simp [phiLayer]

@[simp] theorem S_phiLayer (u : P0Coord m) (s : ZMod m) :
    S (phiLayer (m := m) u s) = s := by
  rcases u with ⟨i, k⟩
  simp [S, phiLayer]
  ring

@[simp] theorem kCoord_phiLayer (u : P0Coord m) (s : ZMod m) :
    kCoord (phiLayer (m := m) u s) = u.2 := by
  rcases u with ⟨i, k⟩
  simp [kCoord, phiLayer]

@[simp] theorem coordOfPoint_phiLayer (u : P0Coord m) (s : ZMod m) :
    coordOfPoint (m := m) (phiLayer (m := m) u s) = (u, s) := by
  rcases u with ⟨i, k⟩
  simp [coordOfPoint, S, phiLayer]
  ring

@[simp] theorem phiLayer_coordOfPoint (x : Point m) :
    phiLayer (m := m) (coordOfPoint (m := m) x).1 (coordOfPoint (m := m) x).2 = x := by
  ext a
  fin_cases a
  · simp [coordOfPoint, phiLayer]
  · simp [coordOfPoint, phiLayer, S]
    ring
  · simp [coordOfPoint, phiLayer]

def splitPointEquiv : Point m ≃ FullCoord m where
  toFun := coordOfPoint (m := m)
  invFun z := phiLayer (m := m) z.1 z.2
  left_inv := phiLayer_coordOfPoint (m := m)
  right_inv z := by
    rcases z with ⟨u, s⟩
    exact coordOfPoint_phiLayer (m := m) u s

@[simp] theorem splitPointEquiv_apply (x : Point m) :
    splitPointEquiv (m := m) x = coordOfPoint (m := m) x := rfl

@[simp] theorem splitPointEquiv_symm_apply (z : FullCoord m) :
    (splitPointEquiv (m := m)).symm z = phiLayer (m := m) z.1 z.2 := rfl

theorem point_eq_phiLayer_of_coord_eq {x : Point m} {u : P0Coord m} {s : ZMod m}
    (h : coordOfPoint (m := m) x = (u, s)) :
    x = phiLayer (m := m) u s := by
  apply (splitPointEquiv (m := m)).injective
  simpa [splitPointEquiv] using h

@[simp] theorem S_bump (x : Point m) (d : Coord) :
    S (bump x d) = S x + 1 := by
  fin_cases d <;> simp [S, bump]
  all_goals ring_nf

def f0 (x : Point m) : Point m :=
  if hS0 : S x = 0 then
    if hk0 : kCoord x = 0 then
      bump x 0
    else
      bump x 1
  else if hS1 : S x = 1 then
    bump x 2
  else
    bump x 0

def f1 (x : Point m) : Point m :=
  if hS0 : S x = 0 then
    bump x 2
  else if hS1 : S x = 1 then
    if hk0 : kCoord x = 0 then
      bump x 0
    else
      bump x 1
  else
    bump x 1

def f2 (x : Point m) : Point m :=
  if hlow : S x = 0 ∨ S x = 1 then
    if hk0 : kCoord x = 0 then
      bump x 1
    else
      bump x 0
  else
    bump x 2

def colorMap : Color → Point m → Point m
  | 0 => f0
  | 1 => f1
  | 2 => f2

@[simp] theorem S_f0 (x : Point m) : S (f0 (m := m) x) = S x + 1 := by
  by_cases hS0 : S x = 0
  · by_cases hk0 : kCoord x = 0 <;> simp [f0, hS0, hk0, S_bump]
  · by_cases hS1 : S x = 1
    · have h10 : (1 : ZMod m) ≠ 0 := by
        intro h10
        exact hS0 (hS1.trans h10)
      rw [show f0 (m := m) x = bump x 2 by simp [f0, hS0, hS1, h10]]
      rw [S_bump, hS1]
    · rw [show f0 (m := m) x = bump x 0 by simp [f0, hS0, hS1]]
      rw [S_bump]

@[simp] theorem S_f1 (x : Point m) : S (f1 (m := m) x) = S x + 1 := by
  by_cases hS0 : S x = 0
  · simp [f1, hS0, S_bump]
  · by_cases hS1 : S x = 1
    · by_cases hk0 : kCoord x = 0
      · have h10 : (1 : ZMod m) ≠ 0 := by
          intro h10
          exact hS0 (hS1.trans h10)
        rw [show f1 (m := m) x = bump x 0 by simp [f1, hS0, hS1, hk0, h10]]
        rw [S_bump, hS1]
      · have h10 : (1 : ZMod m) ≠ 0 := by
          intro h10
          exact hS0 (hS1.trans h10)
        rw [show f1 (m := m) x = bump x 1 by simp [f1, hS0, hS1, hk0, h10]]
        rw [S_bump, hS1]
    · simp [f1, hS0, hS1, S_bump]

@[simp] theorem S_f2 (x : Point m) : S (f2 (m := m) x) = S x + 1 := by
  by_cases hlow : S x = 0 ∨ S x = 1
  · by_cases hk0 : kCoord x = 0 <;> simp [f2, hlow, hk0, S_bump]
  · simp [f2, hlow, S_bump]

@[simp] theorem S_colorMap (c : Color) (x : Point m) :
    S (colorMap (m := m) c x) = S x + 1 := by
  fin_cases c <;> simp [colorMap]

end TorusD3Odd
