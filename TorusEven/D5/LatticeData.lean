-- STATUS: main-path (integer certificate data for the twelve degree-five splices)
import TorusEven.D5.Certificates

/-!
# Integer certificates for the degree-five schedule (Table `tab:d5-integral`)

For each (colour, component) row, `Hz` has columns (newest first) the earlier displacements
of that colour and `λ_c`; `L_P` is the functional defining `W_P` as a kernel; `Minv` is an
integer inverse of `L_P * Hz`; `e` is the displacement of the row, and `Hz…next = prepend e Hz`
is the next chain matrix.  For the residual colours `1, 3, 4`, `[Hz | u]` is a unimodular
completion whose inverse's last row is the character `f_c` (`eq:d5-characters`); for
colours `0, 2` the final four columns are unimodular.  Generated from
`evidence/even_d5/checks/verify_integration.py`; every identity is checked over `ℤ`.
-/

namespace TorusEven
namespace D5Data

open Matrix

/-- The functional defining `W_0` as a kernel. -/
def L0 : Matrix (Fin 1) (Fin 4) ℤ := !![1, 1, 1, 1]
/-- The functional defining `W_1` as a kernel. -/
def L1 : Matrix (Fin 1) (Fin 4) ℤ := !![0, 0, 1, 0]
/-- The functional defining `W_2` as a kernel. -/
def L2 : Matrix (Fin 2) (Fin 4) ℤ := !![0, 0, 1, 0; 0, 0, 0, 1]
/-- The functional defining `W_3` as a kernel. -/
def L3 : Matrix (Fin 2) (Fin 4) ℤ := !![0, 1, 0, 0; 1, 1, 1, 1]
/-- The functional defining `W_4` as a kernel. -/
def L4 : Matrix (Fin 3) (Fin 4) ℤ := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1]

def lam_c0 : Fin 4 → ℤ := ![-4, 1, 1, 1]
def Hz_c0base : Matrix (Fin 4) (Fin 1) ℤ := !![-4; 1; 1; 1]
theorem Hz_c0base_eq : Hz_c0base = Cert.prepend lam_c0 (Matrix.of fun _ (j : Fin 0) => j.elim0) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

def lam_c1 : Fin 4 → ℤ := ![1, -4, 1, 1]
def Hz_c1base : Matrix (Fin 4) (Fin 1) ℤ := !![1; -4; 1; 1]
theorem Hz_c1base_eq : Hz_c1base = Cert.prepend lam_c1 (Matrix.of fun _ (j : Fin 0) => j.elim0) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

def lam_c2 : Fin 4 → ℤ := ![1, 1, -4, 1]
def Hz_c2base : Matrix (Fin 4) (Fin 1) ℤ := !![1; 1; -4; 1]
theorem Hz_c2base_eq : Hz_c2base = Cert.prepend lam_c2 (Matrix.of fun _ (j : Fin 0) => j.elim0) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

def lam_c3 : Fin 4 → ℤ := ![1, 1, 1, -4]
def Hz_c3base : Matrix (Fin 4) (Fin 1) ℤ := !![1; 1; 1; -4]
theorem Hz_c3base_eq : Hz_c3base = Cert.prepend lam_c3 (Matrix.of fun _ (j : Fin 0) => j.elim0) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

def lam_c4 : Fin 4 → ℤ := ![1, 1, 1, 1]
def Hz_c4base : Matrix (Fin 4) (Fin 1) ℤ := !![1; 1; 1; 1]
theorem Hz_c4base_eq : Hz_c4base = Cert.prepend lam_c4 (Matrix.of fun _ (j : Fin 0) => j.elim0) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- colour 0, component 0, rank 1, displacement [-1, 0, 1, 0], neutral 0→2. -/
def Hz_c0p0 : Matrix (Fin 4) (Fin 1) ℤ := !![-4; 1; 1; 1]
def Minv_c0p0 : Matrix (Fin 1) (Fin 1) ℤ := !![-1]
def e_c0p0 : Fin 4 → ℤ := ![-1, 0, 1, 0]
theorem Hz_c0p0_eq : Hz_c0p0 = Hz_c0base := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl
theorem e_c0p0_ker : L0 *ᵥ e_c0p0 = 0 := by
  ext i
  fin_cases i <;> simp [L0, e_c0p0, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
def Hz_c0p0next : Matrix (Fin 4) (Fin 2) ℤ := !![-1, -4; 0, 1; 1, 1; 0, 1]
theorem Hz_c0p0next_eq : Hz_c0p0next = Cert.prepend e_c0p0 Hz_c0p0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- colour 1, component 0, rank 1, displacement [1, -1, 0, 0], neutral 1→0. -/
def Hz_c1p0 : Matrix (Fin 4) (Fin 1) ℤ := !![1; -4; 1; 1]
def Minv_c1p0 : Matrix (Fin 1) (Fin 1) ℤ := !![-1]
def e_c1p0 : Fin 4 → ℤ := ![1, -1, 0, 0]
theorem Hz_c1p0_eq : Hz_c1p0 = Hz_c1base := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl
theorem e_c1p0_ker : L0 *ᵥ e_c1p0 = 0 := by
  ext i
  fin_cases i <;> simp [L0, e_c1p0, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
def Hz_c1p0next : Matrix (Fin 4) (Fin 2) ℤ := !![1, 1; -1, -4; 0, 1; 0, 1]
theorem Hz_c1p0next_eq : Hz_c1p0next = Cert.prepend e_c1p0 Hz_c1p0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- colour 2, component 0, rank 1, displacement [0, 1, -1, 0], neutral 2→1. -/
def Hz_c2p0 : Matrix (Fin 4) (Fin 1) ℤ := !![1; 1; -4; 1]
def Minv_c2p0 : Matrix (Fin 1) (Fin 1) ℤ := !![-1]
def e_c2p0 : Fin 4 → ℤ := ![0, 1, -1, 0]
theorem Hz_c2p0_eq : Hz_c2p0 = Hz_c2base := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl
theorem e_c2p0_ker : L0 *ᵥ e_c2p0 = 0 := by
  ext i
  fin_cases i <;> simp [L0, e_c2p0, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
def Hz_c2p0next : Matrix (Fin 4) (Fin 2) ℤ := !![0, 1; 1, 1; -1, -4; 0, 1]
theorem Hz_c2p0next_eq : Hz_c2p0next = Cert.prepend e_c2p0 Hz_c2p0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- colour 3, component 1, rank 1, displacement [0, 0, 0, -1], neutral 3→4. -/
def Hz_c3p1 : Matrix (Fin 4) (Fin 1) ℤ := !![1; 1; 1; -4]
def Minv_c3p1 : Matrix (Fin 1) (Fin 1) ℤ := !![1]
def e_c3p1 : Fin 4 → ℤ := ![0, 0, 0, -1]
theorem Hz_c3p1_eq : Hz_c3p1 = Hz_c3base := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl
theorem e_c3p1_ker : L1 *ᵥ e_c3p1 = 0 := by
  ext i
  fin_cases i <;> simp [L1, e_c3p1, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
def Hz_c3p1next : Matrix (Fin 4) (Fin 2) ℤ := !![0, 1; 0, 1; 0, 1; -1, -4]
theorem Hz_c3p1next_eq : Hz_c3p1next = Cert.prepend e_c3p1 Hz_c3p1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- colour 4, component 1, rank 1, displacement [0, 0, 0, 1], neutral 4→3. -/
def Hz_c4p1 : Matrix (Fin 4) (Fin 1) ℤ := !![1; 1; 1; 1]
def Minv_c4p1 : Matrix (Fin 1) (Fin 1) ℤ := !![1]
def e_c4p1 : Fin 4 → ℤ := ![0, 0, 0, 1]
theorem Hz_c4p1_eq : Hz_c4p1 = Hz_c4base := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl
theorem e_c4p1_ker : L1 *ᵥ e_c4p1 = 0 := by
  ext i
  fin_cases i <;> simp [L1, e_c4p1, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
def Hz_c4p1next : Matrix (Fin 4) (Fin 2) ℤ := !![0, 1; 0, 1; 0, 1; 1, 1]
theorem Hz_c4p1next_eq : Hz_c4p1next = Cert.prepend e_c4p1 Hz_c4p1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- colour 0, component 2, rank 2, displacement [1, -1, 0, 0], neutral 1→0. -/
def Hz_c0p2 : Matrix (Fin 4) (Fin 2) ℤ := !![-1, -4; 0, 1; 1, 1; 0, 1]
def Minv_c0p2 : Matrix (Fin 2) (Fin 2) ℤ := !![1, -1; 0, 1]
def e_c0p2 : Fin 4 → ℤ := ![1, -1, 0, 0]
theorem Hz_c0p2_eq : Hz_c0p2 = Hz_c0p0next := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl
theorem e_c0p2_ker : L2 *ᵥ e_c0p2 = 0 := by
  ext i
  fin_cases i <;> simp [L2, e_c0p2, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
def Hz_c0p2next : Matrix (Fin 4) (Fin 3) ℤ := !![1, -1, -4; -1, 0, 1; 0, 1, 1; 0, 0, 1]
theorem Hz_c0p2next_eq : Hz_c0p2next = Cert.prepend e_c0p2 Hz_c0p2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- colour 3, component 2, rank 2, displacement [0, 1, 0, 0], neutral 4→1. -/
def Hz_c3p2 : Matrix (Fin 4) (Fin 2) ℤ := !![0, 1; 0, 1; 0, 1; -1, -4]
def Minv_c3p2 : Matrix (Fin 2) (Fin 2) ℤ := !![-4, -1; 1, 0]
def e_c3p2 : Fin 4 → ℤ := ![0, 1, 0, 0]
theorem Hz_c3p2_eq : Hz_c3p2 = Hz_c3p1next := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl
theorem e_c3p2_ker : L2 *ᵥ e_c3p2 = 0 := by
  ext i
  fin_cases i <;> simp [L2, e_c3p2, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
def Hz_c3p2next : Matrix (Fin 4) (Fin 3) ℤ := !![0, 0, 1; 1, 0, 1; 0, 0, 1; 0, -1, -4]
theorem Hz_c3p2next_eq : Hz_c3p2next = Cert.prepend e_c3p2 Hz_c3p2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- colour 4, component 2, rank 2, displacement [-1, 0, 0, 0], neutral 0→4. -/
def Hz_c4p2 : Matrix (Fin 4) (Fin 2) ℤ := !![0, 1; 0, 1; 0, 1; 1, 1]
def Minv_c4p2 : Matrix (Fin 2) (Fin 2) ℤ := !![-1, 1; 1, 0]
def e_c4p2 : Fin 4 → ℤ := ![-1, 0, 0, 0]
theorem Hz_c4p2_eq : Hz_c4p2 = Hz_c4p1next := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl
theorem e_c4p2_ker : L2 *ᵥ e_c4p2 = 0 := by
  ext i
  fin_cases i <;> simp [L2, e_c4p2, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
def Hz_c4p2next : Matrix (Fin 4) (Fin 3) ℤ := !![-1, 0, 1; 0, 0, 1; 0, 0, 1; 0, 1, 1]
theorem Hz_c4p2next_eq : Hz_c4p2next = Cert.prepend e_c4p2 Hz_c4p2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- colour 1, component 3, rank 2, displacement [0, 0, -1, 1], neutral 2→3. -/
def Hz_c1p3 : Matrix (Fin 4) (Fin 2) ℤ := !![1, 1; -1, -4; 0, 1; 0, 1]
def Minv_c1p3 : Matrix (Fin 2) (Fin 2) ℤ := !![-1, 4; 0, -1]
def e_c1p3 : Fin 4 → ℤ := ![0, 0, -1, 1]
theorem Hz_c1p3_eq : Hz_c1p3 = Hz_c1p0next := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl
theorem e_c1p3_ker : L3 *ᵥ e_c1p3 = 0 := by
  ext i
  fin_cases i <;> simp [L3, e_c1p3, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
def Hz_c1p3next : Matrix (Fin 4) (Fin 3) ℤ := !![0, 1, 1; 0, -1, -4; -1, 0, 1; 1, 0, 1]
theorem Hz_c1p3next_eq : Hz_c1p3next = Cert.prepend e_c1p3 Hz_c1p3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- colour 2, component 3, rank 2, displacement [0, 0, 1, -1], neutral 3→2. -/
def Hz_c2p3 : Matrix (Fin 4) (Fin 2) ℤ := !![0, 1; 1, 1; -1, -4; 0, 1]
def Minv_c2p3 : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 0, -1]
def e_c2p3 : Fin 4 → ℤ := ![0, 0, 1, -1]
theorem Hz_c2p3_eq : Hz_c2p3 = Hz_c2p0next := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl
theorem e_c2p3_ker : L3 *ᵥ e_c2p3 = 0 := by
  ext i
  fin_cases i <;> simp [L3, e_c2p3, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
def Hz_c2p3next : Matrix (Fin 4) (Fin 3) ℤ := !![0, 0, 1; 0, 1, 1; 1, -1, -4; -1, 0, 1]
theorem Hz_c2p3next_eq : Hz_c2p3next = Cert.prepend e_c2p3 Hz_c2p3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- colour 0, component 4, rank 3, displacement [0, 0, -1, 0], neutral 2→4. -/
def Hz_c0p4 : Matrix (Fin 4) (Fin 3) ℤ := !![1, -1, -4; -1, 0, 1; 0, 1, 1; 0, 0, 1]
def Minv_c0p4 : Matrix (Fin 3) (Fin 3) ℤ := !![0, -1, 1; -1, -1, -3; 0, 0, 1]
def e_c0p4 : Fin 4 → ℤ := ![0, 0, -1, 0]
theorem Hz_c0p4_eq : Hz_c0p4 = Hz_c0p2next := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl
theorem e_c0p4_ker : L4 *ᵥ e_c0p4 = 0 := by
  ext i
  fin_cases i <;> simp [L4, e_c0p4, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
def Hz_c0p4next : Matrix (Fin 4) (Fin 4) ℤ := !![0, 1, -1, -4; 0, -1, 0, 1; -1, 0, 1, 1; 0, 0, 0, 1]
theorem Hz_c0p4next_eq : Hz_c0p4next = Cert.prepend e_c0p4 Hz_c0p4 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- colour 2, component 4, rank 3, displacement [0, 0, 1, 0], neutral 4→2. -/
def Hz_c2p4 : Matrix (Fin 4) (Fin 3) ℤ := !![0, 0, 1; 0, 1, 1; 1, -1, -4; -1, 0, 1]
def Minv_c2p4 : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, -1; -1, 1, 0; 1, 0, 0]
def e_c2p4 : Fin 4 → ℤ := ![0, 0, 1, 0]
theorem Hz_c2p4_eq : Hz_c2p4 = Hz_c2p3next := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl
theorem e_c2p4_ker : L4 *ᵥ e_c2p4 = 0 := by
  ext i
  fin_cases i <;> simp [L4, e_c2p4, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
def Hz_c2p4next : Matrix (Fin 4) (Fin 4) ℤ := !![0, 0, 0, 1; 0, 0, 1, 1; 1, 1, -1, -4; 0, -1, 0, 1]
theorem Hz_c2p4next_eq : Hz_c2p4next = Cert.prepend e_c2p4 Hz_c2p4 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

def Hfullinv_c0 : Matrix (Fin 4) (Fin 4) ℤ := !![-1, -1, -1, -2; 0, -1, 0, 1; -1, -1, 0, -3; 0, 0, 0, 1]

def u_c1 : Fin 4 → ℤ := ![-2, -2, 1, 2]
def Qinv_c1 : Matrix (Fin 4) (Fin 4) ℤ := !![-1, -1, -2, -1; 8, 7, 10, 10; -3, -3, -4, -4; 2, 2, 3, 3]
def f_c1 : Fin 4 → ℤ := ![2, 2, 3, 3]

def Hfullinv_c2 : Matrix (Fin 4) (Fin 4) ℤ := !![2, 1, 1, 1; 1, 0, 0, -1; -1, 1, 0, 0; 1, 0, 0, 0]

def u_c3 : Fin 4 → ℤ := ![-2, -2, -1, -2]
def Qinv_c3 : Matrix (Fin 4) (Fin 4) ℤ := !![-1, 1, 0, 0; 6, 0, -10, -1; -1, 0, 2, 0; -1, 0, 1, 0]
def f_c3 : Fin 4 → ℤ := ![-1, 0, 1, 0]

def u_c4 : Fin 4 → ℤ := ![-2, -2, -1, -2]
def Qinv_c4 : Matrix (Fin 4) (Fin 4) ℤ := !![-1, 1, 0, 0; 0, -1, 0, 1; 0, -1, 2, 0; 0, -1, 1, 0]
def f_c4 : Fin 4 → ℤ := ![0, -1, 1, 0]

theorem inv1_c0p0 : ∀ v : Fin 1 → ℤ, L0 *ᵥ (Hz_c0p0 *ᵥ (Minv_c0p0 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [L0, Hz_c0p0, Minv_c0p0, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv2_c0p0 : ∀ v : Fin 1 → ℤ, Minv_c0p0 *ᵥ (L0 *ᵥ (Hz_c0p0 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [L0, Hz_c0p0, Minv_c0p0, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv1_c1p0 : ∀ v : Fin 1 → ℤ, L0 *ᵥ (Hz_c1p0 *ᵥ (Minv_c1p0 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [L0, Hz_c1p0, Minv_c1p0, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv2_c1p0 : ∀ v : Fin 1 → ℤ, Minv_c1p0 *ᵥ (L0 *ᵥ (Hz_c1p0 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [L0, Hz_c1p0, Minv_c1p0, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv1_c2p0 : ∀ v : Fin 1 → ℤ, L0 *ᵥ (Hz_c2p0 *ᵥ (Minv_c2p0 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [L0, Hz_c2p0, Minv_c2p0, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv2_c2p0 : ∀ v : Fin 1 → ℤ, Minv_c2p0 *ᵥ (L0 *ᵥ (Hz_c2p0 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [L0, Hz_c2p0, Minv_c2p0, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv1_c3p1 : ∀ v : Fin 1 → ℤ, L1 *ᵥ (Hz_c3p1 *ᵥ (Minv_c3p1 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [L1, Hz_c3p1, Minv_c3p1, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv2_c3p1 : ∀ v : Fin 1 → ℤ, Minv_c3p1 *ᵥ (L1 *ᵥ (Hz_c3p1 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [L1, Hz_c3p1, Minv_c3p1, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv1_c4p1 : ∀ v : Fin 1 → ℤ, L1 *ᵥ (Hz_c4p1 *ᵥ (Minv_c4p1 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [L1, Hz_c4p1, Minv_c4p1, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv2_c4p1 : ∀ v : Fin 1 → ℤ, Minv_c4p1 *ᵥ (L1 *ᵥ (Hz_c4p1 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [L1, Hz_c4p1, Minv_c4p1, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv1_c0p2 : ∀ v : Fin 2 → ℤ, L2 *ᵥ (Hz_c0p2 *ᵥ (Minv_c0p2 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [L2, Hz_c0p2, Minv_c0p2, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv2_c0p2 : ∀ v : Fin 2 → ℤ, Minv_c0p2 *ᵥ (L2 *ᵥ (Hz_c0p2 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [L2, Hz_c0p2, Minv_c0p2, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv1_c3p2 : ∀ v : Fin 2 → ℤ, L2 *ᵥ (Hz_c3p2 *ᵥ (Minv_c3p2 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [L2, Hz_c3p2, Minv_c3p2, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv2_c3p2 : ∀ v : Fin 2 → ℤ, Minv_c3p2 *ᵥ (L2 *ᵥ (Hz_c3p2 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [L2, Hz_c3p2, Minv_c3p2, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv1_c4p2 : ∀ v : Fin 2 → ℤ, L2 *ᵥ (Hz_c4p2 *ᵥ (Minv_c4p2 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [L2, Hz_c4p2, Minv_c4p2, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv2_c4p2 : ∀ v : Fin 2 → ℤ, Minv_c4p2 *ᵥ (L2 *ᵥ (Hz_c4p2 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [L2, Hz_c4p2, Minv_c4p2, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv1_c1p3 : ∀ v : Fin 2 → ℤ, L3 *ᵥ (Hz_c1p3 *ᵥ (Minv_c1p3 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [L3, Hz_c1p3, Minv_c1p3, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv2_c1p3 : ∀ v : Fin 2 → ℤ, Minv_c1p3 *ᵥ (L3 *ᵥ (Hz_c1p3 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [L3, Hz_c1p3, Minv_c1p3, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv1_c2p3 : ∀ v : Fin 2 → ℤ, L3 *ᵥ (Hz_c2p3 *ᵥ (Minv_c2p3 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [L3, Hz_c2p3, Minv_c2p3, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv2_c2p3 : ∀ v : Fin 2 → ℤ, Minv_c2p3 *ᵥ (L3 *ᵥ (Hz_c2p3 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [L3, Hz_c2p3, Minv_c2p3, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv1_c0p4 : ∀ v : Fin 3 → ℤ, L4 *ᵥ (Hz_c0p4 *ᵥ (Minv_c0p4 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [L4, Hz_c0p4, Minv_c0p4, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv2_c0p4 : ∀ v : Fin 3 → ℤ, Minv_c0p4 *ᵥ (L4 *ᵥ (Hz_c0p4 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [L4, Hz_c0p4, Minv_c0p4, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv1_c2p4 : ∀ v : Fin 3 → ℤ, L4 *ᵥ (Hz_c2p4 *ᵥ (Minv_c2p4 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [L4, Hz_c2p4, Minv_c2p4, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv2_c2p4 : ∀ v : Fin 3 → ℤ, Minv_c2p4 *ᵥ (L4 *ᵥ (Hz_c2p4 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [L4, Hz_c2p4, Minv_c2p4, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem full_c0 : ∀ v : Fin 4 → ℤ, Hz_c0p4next *ᵥ (Hfullinv_c0 *ᵥ v) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Hz_c0p4next, Hfullinv_c0, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem aug1_c1 : ∀ v : Fin 4 → ℤ, Cert.augment Hz_c1p3next u_c1 *ᵥ (Qinv_c1 *ᵥ v) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Cert.augment, Hz_c1p3next, u_c1, Qinv_c1, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem aug2_c1 : ∀ v : Fin 4 → ℤ, Qinv_c1 *ᵥ (Cert.augment Hz_c1p3next u_c1 *ᵥ v) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Cert.augment, Hz_c1p3next, u_c1, Qinv_c1, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem lastRow_c1 : ∀ j, Qinv_c1 3 j = f_c1 j := by
  decide

theorem full_c2 : ∀ v : Fin 4 → ℤ, Hz_c2p4next *ᵥ (Hfullinv_c2 *ᵥ v) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Hz_c2p4next, Hfullinv_c2, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem aug1_c3 : ∀ v : Fin 4 → ℤ, Cert.augment Hz_c3p2next u_c3 *ᵥ (Qinv_c3 *ᵥ v) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Cert.augment, Hz_c3p2next, u_c3, Qinv_c3, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem aug2_c3 : ∀ v : Fin 4 → ℤ, Qinv_c3 *ᵥ (Cert.augment Hz_c3p2next u_c3 *ᵥ v) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Cert.augment, Hz_c3p2next, u_c3, Qinv_c3, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem lastRow_c3 : ∀ j, Qinv_c3 3 j = f_c3 j := by
  decide

theorem aug1_c4 : ∀ v : Fin 4 → ℤ, Cert.augment Hz_c4p2next u_c4 *ᵥ (Qinv_c4 *ᵥ v) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Cert.augment, Hz_c4p2next, u_c4, Qinv_c4, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem aug2_c4 : ∀ v : Fin 4 → ℤ, Qinv_c4 *ᵥ (Cert.augment Hz_c4p2next u_c4 *ᵥ v) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Cert.augment, Hz_c4p2next, u_c4, Qinv_c4, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem lastRow_c4 : ∀ j, Qinv_c4 3 j = f_c4 j := by
  decide

end D5Data
end TorusEven
