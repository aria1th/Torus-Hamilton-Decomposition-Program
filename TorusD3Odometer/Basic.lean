import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace TorusD3Odometer

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

def KMap : Color → FullCoord m → FullCoord m
  | 0, ((i, k), s) => ((i + 1, k), s + 1)
  | 1, (u, s) => (u, s + 1)
  | 2, ((i, k), s) => ((i, k + 1), s + 1)

@[simp] theorem KMap_snd (c : Color) (z : FullCoord m) :
    (KMap (m := m) c z).2 = z.2 + 1 := by
  rcases z with ⟨u, s⟩
  rcases u with ⟨i, k⟩
  fin_cases c <;> rfl

@[simp] theorem S_bump (x : Point m) (d : Coord) :
    S (bump x d) = S x + 1 := by
  fin_cases d <;> simp [S, bump]
  all_goals ring_nf

@[simp] theorem coordOfPoint_bump (c : Color) (x : Point m) :
    coordOfPoint (m := m) (bump x c) = KMap (m := m) c (coordOfPoint (m := m) x) := by
  fin_cases c
  all_goals
    ext <;> simp [coordOfPoint, KMap, S, bump]
    all_goals ring_nf

@[simp] theorem splitPointEquiv_bump (c : Color) (x : Point m) :
    splitPointEquiv (m := m) (bump x c) = KMap (m := m) c (splitPointEquiv (m := m) x) := by
  simpa [splitPointEquiv] using coordOfPoint_bump (m := m) c x

def liftPointMap (f : Point m → Point m) : FullCoord m → FullCoord m :=
  fun z => splitPointEquiv (m := m) (f ((splitPointEquiv (m := m)).symm z))

theorem splitPointEquiv_semiconj_liftPointMap (f : Point m → Point m) :
    Function.Semiconj (splitPointEquiv (m := m)) f (liftPointMap (m := m) f) := by
  intro x
  simp [liftPointMap]

theorem splitPointEquiv_symm_semiconj_pointMap (f : Point m → Point m) :
    Function.Semiconj (splitPointEquiv (m := m)).symm (liftPointMap (m := m) f) f := by
  exact (splitPointEquiv_semiconj_liftPointMap (m := m) f).inverse_left
    (splitPointEquiv (m := m)).left_inv (splitPointEquiv (m := m)).right_inv

@[simp] theorem liftPointMap_snd (f : Point m → Point m)
    (hS : ∀ x, S (f x) = S x + 1) (z : FullCoord m) :
    (liftPointMap (m := m) f z).2 = z.2 + 1 := by
  rcases z with ⟨u, s⟩
  simpa [liftPointMap, coordOfPoint] using hS (phiLayer (m := m) u s)

theorem liftPointMap_eq_KMap_of_step (f : Point m → Point m) (c : Color)
    (u : P0Coord m) (s : ZMod m)
    (h : f (phiLayer (m := m) u s) = bump (phiLayer (m := m) u s) c) :
    liftPointMap (m := m) f (u, s) = KMap (m := m) c (u, s) := by
  calc
    liftPointMap (m := m) f (u, s)
        = splitPointEquiv (m := m) (f (phiLayer (m := m) u s)) := by
            rfl
    _ = splitPointEquiv (m := m) (bump (phiLayer (m := m) u s) c) := by rw [h]
    _ = KMap (m := m) c (splitPointEquiv (m := m) (phiLayer (m := m) u s)) := by
          rw [splitPointEquiv_bump]
    _ = KMap (m := m) c (u, s) := by simp

theorem point_eq_phiLayer_of_splitPointEquiv_eq {x : Point m} {u : P0Coord m} {s : ZMod m}
    (h : splitPointEquiv (m := m) x = (u, s)) :
    x = phiLayer (m := m) u s := by
  apply (splitPointEquiv (m := m)).injective
  calc
    splitPointEquiv (m := m) x = (u, s) := h
    _ = splitPointEquiv (m := m) (phiLayer (m := m) u s) := by
          symm
          exact coordOfPoint_phiLayer (m := m) u s

end TorusD3Odometer
