import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace TorusD4

abbrev Coord := Fin 4
abbrev Color := Fin 4
abbrev Point (m : ℕ) := Coord → ZMod m

abbrev DirectionTuple := Equiv.Perm Coord

def canonical : DirectionTuple := Equiv.refl _

def reverseFun : Coord → Coord := ![3, 2, 1, 0]
def swap01Swap23Fun : Coord → Coord := ![1, 0, 3, 2]
def swap13Fun : Coord → Coord := ![0, 3, 2, 1]
def swap02Fun : Coord → Coord := ![2, 1, 0, 3]
def swap13Swap02Fun : Coord → Coord := ![2, 3, 0, 1]

def reverse : DirectionTuple where
  toFun := reverseFun
  invFun := reverseFun
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

def swap01Swap23 : DirectionTuple where
  toFun := swap01Swap23Fun
  invFun := swap01Swap23Fun
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

def swap13 : DirectionTuple where
  toFun := swap13Fun
  invFun := swap13Fun
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

def swap02 : DirectionTuple where
  toFun := swap02Fun
  invFun := swap02Fun
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

def swap13Swap02 : DirectionTuple where
  toFun := swap13Swap02Fun
  invFun := swap13Swap02Fun
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

def S (x : Point m) : ZMod m := x 0 + x 1 + x 2 + x 3

def q (x : Point m) : ZMod m := x 0 + x 2

def bump (x : Point m) (d : Coord) : Point m :=
  fun i => x i + if i = d then 1 else 0

def witness (x : Point m) : DirectionTuple :=
  if _ : S x = 0 then
    if _ : q x = 0 then
      reverse
    else
      swap01Swap23
  else if _ : S x = 1 then
    canonical
  else if _ : S x = 2 then
    if _ : q x = 0 then
      if _ : x 0 = 0 then
        if _ : x 3 = 0 then swap13Swap02 else swap13
      else if _ : x 3 = 0 then
        swap02
      else
        canonical
    else
      canonical
  else
    canonical

def colorMap (c : Color) (x : Point m) : Point m :=
  bump x ((witness x) c)

def phi (a b q0 : ZMod m) : Point m := ![a, b, q0 - a, -q0 - b]

@[simp] theorem phi_apply_0 (a b q0 : ZMod m) : phi a b q0 0 = a := by
  simp [phi]

@[simp] theorem phi_apply_1 (a b q0 : ZMod m) : phi a b q0 1 = b := by
  simp [phi]

@[simp] theorem phi_apply_2 (a b q0 : ZMod m) : phi a b q0 2 = q0 - a := by
  simp [phi]

@[simp] theorem phi_apply_3 (a b q0 : ZMod m) : phi a b q0 3 = -q0 - b := by
  simp [phi]

@[simp] theorem S_phi (a b q0 : ZMod m) : S (phi a b q0) = 0 := by
  simp [S, phi]
  ring

@[simp] theorem q_phi (a b q0 : ZMod m) : q (phi a b q0) = q0 := by
  simp [q, phi]

@[simp] theorem witness_high_layers (x : Point m) (h0 : S x ≠ 0) (h1 : S x ≠ 1)
    (h2 : S x ≠ 2) : witness x = canonical := by
  simp [witness, h0, h1, h2]

@[simp] theorem witness_layer1 [Fact (1 < m)] (x : Point m) (h : S x = 1) :
    witness x = canonical := by
  by_cases h0 : S x = 0
  · have : (1 : ZMod m) = 0 := by
      rw [h] at h0
      exact h0
    exact False.elim (one_ne_zero this)
  · simp [witness, h]

end TorusD4
