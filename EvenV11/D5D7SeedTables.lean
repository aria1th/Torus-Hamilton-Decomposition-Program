import Mathlib

/-!
# D5/D7 seed tables — verified data (paper Appendix A/B)

Faithful Lean port of the finite D5/D7 appendix data checked by
`scripts/verify_finite_checks.py`: closing-column primitivity (M*N=1 ⟹ IsUnit det,
unimodular = unit-carry/RF3 basis), support-row ranks (|support|=d-stage-1,
active⊆support), and reserve-point plane equations.  No `sorry`, no `native_decide`.
-/

namespace EvenV11
namespace D5D7SeedTables

open Matrix

/-! ## D5 closing columns (5 colours, 4×4) -/

def d5M0 : Matrix (Fin 4) (Fin 4) ℤ := !![-1, -1, 0, 1; 0, 1, 0, 0; 1, 0, -1, 0; 0, 0, 1, 0]
def d5N0 : Matrix (Fin 4) (Fin 4) ℤ := !![0, 0, 1, 1; 0, 1, 0, 0; 0, 0, 0, 1; 1, 1, 1, 1]
theorem d5MN0 : d5M0 * d5N0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [d5M0, d5N0, Matrix.mul_apply, Fin.sum_univ_four]
theorem d5det0 : IsUnit ((d5M0).det) := by
  have h : (d5M0).det * (d5N0).det = 1 := by
    rw [← Matrix.det_mul, d5MN0, Matrix.det_one]
  exact isUnit_of_mul_eq_one _ h

def d5M1 : Matrix (Fin 4) (Fin 4) ℤ := !![-1, 0, -1, 0; 1, 0, 0, 1; 0, -1, 0, 0; 0, 1, 1, 0]
def d5N1 : Matrix (Fin 4) (Fin 4) ℤ := !![-1, 0, -1, -1; 0, 0, -1, 0; 0, 0, 1, 1; 1, 1, 1, 1]
theorem d5MN1 : d5M1 * d5N1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [d5M1, d5N1, Matrix.mul_apply, Fin.sum_univ_four]
theorem d5det1 : IsUnit ((d5M1).det) := by
  have h : (d5M1).det * (d5N1).det = 1 := by
    rw [← Matrix.det_mul, d5MN1, Matrix.det_one]
  exact isUnit_of_mul_eq_one _ h

def d5M2 : Matrix (Fin 4) (Fin 4) ℤ := !![-1, 0, 0, 0; 1, -1, -1, 1; 0, 1, 0, 0; 0, 0, 1, 0]
def d5N2 : Matrix (Fin 4) (Fin 4) ℤ := !![-1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; 1, 1, 1, 1]
theorem d5MN2 : d5M2 * d5N2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [d5M2, d5N2, Matrix.mul_apply, Fin.sum_univ_four]
theorem d5det2 : IsUnit ((d5M2).det) := by
  have h : (d5M2).det * (d5N2).det = 1 := by
    rw [← Matrix.det_mul, d5MN2, Matrix.det_one]
  exact isUnit_of_mul_eq_one _ h

def d5M3 : Matrix (Fin 4) (Fin 4) ℤ := !![0, 0, -1, 0; 0, -1, 1, 0; -1, 0, 0, 1; 1, 1, 0, 0]
def d5N3 : Matrix (Fin 4) (Fin 4) ℤ := !![1, 1, 0, 1; -1, -1, 0, 0; -1, 0, 0, 0; 1, 1, 1, 1]
theorem d5MN3 : d5M3 * d5N3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [d5M3, d5N3, Matrix.mul_apply, Fin.sum_univ_four]
theorem d5det3 : IsUnit ((d5M3).det) := by
  have h : (d5M3).det * (d5N3).det = 1 := by
    rw [← Matrix.det_mul, d5MN3, Matrix.det_one]
  exact isUnit_of_mul_eq_one _ h

def d5M4 : Matrix (Fin 4) (Fin 4) ℤ := !![0, -1, 0, 0; 0, 0, -1, 0; -1, 0, 1, 0; 1, 1, 0, 1]
def d5N4 : Matrix (Fin 4) (Fin 4) ℤ := !![0, -1, -1, 0; -1, 0, 0, 0; 0, -1, 0, 0; 1, 1, 1, 1]
theorem d5MN4 : d5M4 * d5N4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [d5M4, d5N4, Matrix.mul_apply, Fin.sum_univ_four]
theorem d5det4 : IsUnit ((d5M4).det) := by
  have h : (d5M4).det * (d5N4).det = 1 := by
    rw [← Matrix.det_mul, d5MN4, Matrix.det_one]
  exact isUnit_of_mul_eq_one _ h

theorem d5_closing_primitive :
    IsUnit (d5M0.det) ∧ IsUnit (d5M1.det) ∧ IsUnit (d5M2.det) ∧
      IsUnit (d5M3.det) ∧ IsUnit (d5M4.det) :=
  ⟨d5det0, d5det1, d5det2, d5det3, d5det4⟩

/-! ## D7 closing columns (7 colours, 6×6) -/

def d7M0 : Matrix (Fin 6) (Fin 6) ℤ := !![-1, 0, 0, 0, -1, 1; 1, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0]
def d7N0 : Matrix (Fin 6) (Fin 6) ℤ := !![0, 1, 1, 1, 1, 0; 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1; 1, 1, 1, 1, 1, 1]
theorem d7MN0 : d7M0 * d7N0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [d7M0, d7N0, Matrix.mul_apply, Fin.sum_univ_six]
theorem d7det0 : IsUnit ((d7M0).det) := by
  have h : (d7M0).det * (d7N0).det = 1 := by
    rw [← Matrix.det_mul, d7MN0, Matrix.det_one]
  exact isUnit_of_mul_eq_one _ h

def d7M1 : Matrix (Fin 6) (Fin 6) ℤ := !![0, 0, -1, 0, 0, 0; -1, 0, 0, 0, 0, 1; 1, -1, 0, 0, 0, 0; 0, 0, 1, -1, 0, 0; 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 1, 0]
def d7N1 : Matrix (Fin 6) (Fin 6) ℤ := !![1, 0, 1, 1, 1, 1; 1, 0, 0, 1, 1, 1; -1, 0, 0, 0, 0, 0; -1, 0, 0, -1, 0, 0; 0, 0, 0, 0, 0, 1; 1, 1, 1, 1, 1, 1]
theorem d7MN1 : d7M1 * d7N1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [d7M1, d7N1, Matrix.mul_apply, Fin.sum_univ_six]
theorem d7det1 : IsUnit ((d7M1).det) := by
  have h : (d7M1).det * (d7N1).det = 1 := by
    rw [← Matrix.det_mul, d7MN1, Matrix.det_one]
  exact isUnit_of_mul_eq_one _ h

def d7M2 : Matrix (Fin 6) (Fin 6) ℤ := !![-1, 0, 0, 0, -1, 0; 0, -1, 0, -1, 1, 0; 1, 0, -1, 0, 0, 1; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0]
def d7N2 : Matrix (Fin 6) (Fin 6) ℤ := !![-1, -1, 0, -1, 0, -1; 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1; 0, 1, 0, 1, 0, 1; 1, 1, 1, 1, 1, 1]
theorem d7MN2 : d7M2 * d7N2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [d7M2, d7N2, Matrix.mul_apply, Fin.sum_univ_six]
theorem d7det2 : IsUnit ((d7M2).det) := by
  have h : (d7M2).det * (d7N2).det = 1 := by
    rw [← Matrix.det_mul, d7MN2, Matrix.det_one]
  exact isUnit_of_mul_eq_one _ h

def d7M3 : Matrix (Fin 6) (Fin 6) ℤ := !![0, 0, 0, -1, 0, 0; 0, 0, 0, 0, -1, 0; -1, 0, 0, 0, 0, 1; 1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0; 0, 0, 1, 1, 0, 0]
def d7N3 : Matrix (Fin 6) (Fin 6) ℤ := !![1, 1, 0, 1, 1, 1; 1, 1, 0, 0, 1, 1; 1, 0, 0, 0, 0, 1; -1, 0, 0, 0, 0, 0; 0, -1, 0, 0, 0, 0; 1, 1, 1, 1, 1, 1]
theorem d7MN3 : d7M3 * d7N3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [d7M3, d7N3, Matrix.mul_apply, Fin.sum_univ_six]
theorem d7det3 : IsUnit ((d7M3).det) := by
  have h : (d7M3).det * (d7N3).det = 1 := by
    rw [← Matrix.det_mul, d7MN3, Matrix.det_one]
  exact isUnit_of_mul_eq_one _ h

def d7M4 : Matrix (Fin 6) (Fin 6) ℤ := !![0, 0, 0, -1, 0, 0; 0, -1, 0, 0, -1, 0; -1, 0, 0, 0, 1, 0; 1, 0, 0, 0, 0, 1; 0, 1, -1, 0, 0, 0; 0, 0, 1, 1, 0, 0]
def d7N4 : Matrix (Fin 6) (Fin 6) ℤ := !![-1, -1, -1, 0, -1, -1; 1, 0, 0, 0, 1, 1; 1, 0, 0, 0, 0, 1; -1, 0, 0, 0, 0, 0; -1, -1, 0, 0, -1, -1; 1, 1, 1, 1, 1, 1]
theorem d7MN4 : d7M4 * d7N4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [d7M4, d7N4, Matrix.mul_apply, Fin.sum_univ_six]
theorem d7det4 : IsUnit ((d7M4).det) := by
  have h : (d7M4).det * (d7N4).det = 1 := by
    rw [← Matrix.det_mul, d7MN4, Matrix.det_one]
  exact isUnit_of_mul_eq_one _ h

def d7M5 : Matrix (Fin 6) (Fin 6) ℤ := !![0, -1, -1, 0, 0, 0; 0, 0, 0, -1, 0, 0; 0, 0, 0, 1, -1, 0; 0, 0, 1, 0, 1, 0; -1, 0, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0]
def d7N5 : Matrix (Fin 6) (Fin 6) ℤ := !![1, 1, 1, 1, 0, 1; -1, -1, -1, -1, 0, 0; 0, 1, 1, 1, 0, 0; 0, -1, 0, 0, 0, 0; 0, -1, -1, 0, 0, 0; 1, 1, 1, 1, 1, 1]
theorem d7MN5 : d7M5 * d7N5 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [d7M5, d7N5, Matrix.mul_apply, Fin.sum_univ_six]
theorem d7det5 : IsUnit ((d7M5).det) := by
  have h : (d7M5).det * (d7N5).det = 1 := by
    rw [← Matrix.det_mul, d7MN5, Matrix.det_one]
  exact isUnit_of_mul_eq_one _ h

def d7M6 : Matrix (Fin 6) (Fin 6) ℤ := !![0, -1, 0, 0, 0, 0; 0, 0, -1, 0, 0, 0; 0, 0, 0, -1, 0, 0; 0, 0, 1, 0, -1, 0; -1, 0, 0, 1, 0, 0; 1, 1, 0, 0, 1, 1]
def d7N6 : Matrix (Fin 6) (Fin 6) ℤ := !![0, 0, -1, 0, -1, 0; -1, 0, 0, 0, 0, 0; 0, -1, 0, 0, 0, 0; 0, 0, -1, 0, 0, 0; 0, -1, 0, -1, 0, 0; 1, 1, 1, 1, 1, 1]
theorem d7MN6 : d7M6 * d7N6 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [d7M6, d7N6, Matrix.mul_apply, Fin.sum_univ_six]
theorem d7det6 : IsUnit ((d7M6).det) := by
  have h : (d7M6).det * (d7N6).det = 1 := by
    rw [← Matrix.det_mul, d7MN6, Matrix.det_one]
  exact isUnit_of_mul_eq_one _ h

theorem d7_closing_primitive :
    IsUnit (d7M0.det) ∧ IsUnit (d7M1.det) ∧ IsUnit (d7M2.det) ∧ IsUnit (d7M3.det) ∧
      IsUnit (d7M4.det) ∧ IsUnit (d7M5.det) ∧ IsUnit (d7M6.det) :=
  ⟨d7det0, d7det1, d7det2, d7det3, d7det4, d7det5, d7det6⟩

/-! ## Support-row ranks -/

def d5Support : List (Nat × List (Nat × Nat) × List (Nat × Nat)) :=
  [(1, [(0, 1), (0, 2), (0, 3)], [(0, 1), (0, 2)]),
   (1, [(0, 1), (0, 3), (3, 4)], [(3, 4)]),
   (2, [(0, 1), (0, 4)], [(0, 1), (0, 4)]),
   (2, [(0, 2), (2, 3)], [(2, 3)]),
   (3, [(2, 4)], [(2, 4)])]
def d7Support : List (Nat × List (Nat × Nat) × List (Nat × Nat)) :=
  [(1, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5)], [(0, 2), (0, 1)]),
   (1, [(0, 1), (0, 2), (0, 3), (0, 5), (3, 4)], [(3, 4)]),
   (1, [(0, 1), (0, 2), (0, 3), (0, 5), (5, 6)], [(5, 6)]),
   (2, [(0, 1), (0, 3), (2, 4), (2, 5)], [(2, 5), (2, 4)]),
   (2, [(0, 4), (0, 5), (1, 2), (1, 3)], [(1, 3)]),
   (2, [(0, 1), (0, 2), (0, 3), (0, 6)], [(0, 6)]),
   (3, [(1, 2), (1, 4), (1, 5)], [(1, 2), (1, 4)]),
   (3, [(0, 1), (0, 3), (2, 5)], [(0, 3)]),
   (3, [(0, 2), (0, 3), (5, 6)], [(5, 6)]),
   (4, [(1, 2), (1, 5)], [(1, 5), (1, 2)]),
   (4, [(0, 5), (3, 4)], [(3, 4)]),
   (4, [(0, 6), (2, 3)], [(0, 6)]),
   (5, [(4, 6)], [(4, 6)]),
   (5, [(2, 3)], [(2, 3)])]

theorem d5_support_valid :
    ∀ r ∈ d5Support, r.2.1.length = 5 - r.1 - 1 ∧ ∀ e ∈ r.2.2, e ∈ r.2.1 := by decide

theorem d7_support_valid :
    ∀ r ∈ d7Support, r.2.1.length = 7 - r.1 - 1 ∧ ∀ e ∈ r.2.2, e ∈ r.2.1 := by decide

/-! ## Reserve coordinates (plane equations) -/

def d5Reserve : List (ZMod 6 × ZMod 6 × ZMod 6 × ZMod 6) :=
  [((1 : ZMod 6), (0 : ZMod 6), (2 : ZMod 6), (4 : ZMod 6)),
   ((0 : ZMod 6), (1 : ZMod 6), (2 : ZMod 6), (4 : ZMod 6)),
   ((5 : ZMod 6), (2 : ZMod 6), (2 : ZMod 6), (4 : ZMod 6)),
   ((0 : ZMod 6), (0 : ZMod 6), (2 : ZMod 6), (5 : ZMod 6)),
   ((5 : ZMod 6), (1 : ZMod 6), (2 : ZMod 6), (5 : ZMod 6)),
   ((4 : ZMod 6), (2 : ZMod 6), (2 : ZMod 6), (5 : ZMod 6)),
   ((3 : ZMod 6), (3 : ZMod 6), (2 : ZMod 6), (5 : ZMod 6)),
   ((5 : ZMod 6), (0 : ZMod 6), (2 : ZMod 6), (0 : ZMod 6))]

set_option maxRecDepth 4000 in
/-- D5 reserve points: `x₃ = 2` and `x₁+x₂+x₄ = 5` (mod 6). -/
theorem d5_reserve_valid :
    ∀ p ∈ d5Reserve, p.2.2.1 = 2 ∧ p.1 + p.2.1 + p.2.2.2 = 5 := by
  intro p hp; fin_cases hp <;> decide

def d7Reserve : List (ZMod 8 × ZMod 8 × ZMod 8 × ZMod 8 × ZMod 8 × ZMod 8) :=
  [((1 : ZMod 8), (0 : ZMod 8), (3 : ZMod 8), (5 : ZMod 8), (2 : ZMod 8), (6 : ZMod 8)),
   ((1 : ZMod 8), (7 : ZMod 8), (3 : ZMod 8), (5 : ZMod 8), (2 : ZMod 8), (7 : ZMod 8)),
   ((1 : ZMod 8), (6 : ZMod 8), (3 : ZMod 8), (5 : ZMod 8), (2 : ZMod 8), (0 : ZMod 8)),
   ((1 : ZMod 8), (0 : ZMod 8), (2 : ZMod 8), (5 : ZMod 8), (3 : ZMod 8), (6 : ZMod 8)),
   ((1 : ZMod 8), (7 : ZMod 8), (2 : ZMod 8), (5 : ZMod 8), (3 : ZMod 8), (7 : ZMod 8)),
   ((1 : ZMod 8), (6 : ZMod 8), (2 : ZMod 8), (5 : ZMod 8), (3 : ZMod 8), (0 : ZMod 8)),
   ((1 : ZMod 8), (5 : ZMod 8), (2 : ZMod 8), (5 : ZMod 8), (3 : ZMod 8), (1 : ZMod 8)),
   ((1 : ZMod 8), (4 : ZMod 8), (2 : ZMod 8), (5 : ZMod 8), (3 : ZMod 8), (2 : ZMod 8)),
   ((1 : ZMod 8), (3 : ZMod 8), (2 : ZMod 8), (5 : ZMod 8), (3 : ZMod 8), (3 : ZMod 8)),
   ((1 : ZMod 8), (0 : ZMod 8), (1 : ZMod 8), (5 : ZMod 8), (4 : ZMod 8), (6 : ZMod 8))]

set_option maxRecDepth 4000 in
/-- D7 reserve points: `x₁=1`, `x₄=5`, `x₂+x₆=6`, `x₃+x₅=5` (mod 8). -/
theorem d7_reserve_valid :
    ∀ p ∈ d7Reserve,
      p.1 = 1 ∧ p.2.2.2.1 = 5 ∧ p.2.1 + p.2.2.2.2.2 = 6 ∧ p.2.2.1 + p.2.2.2.2.1 = 5 := by
  intro p hp; fin_cases hp <;> decide

end D5D7SeedTables
end EvenV11
