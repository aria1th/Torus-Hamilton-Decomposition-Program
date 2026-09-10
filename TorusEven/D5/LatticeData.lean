-- STATUS: main-path (integer certificate data for the twelve degree-five splices)
import TorusEven.D5.Certificates

/-!
# Integer certificates for the degree-five schedule (Table `tab:d5-integral`)

For each (colour, component) row: `Hz` has columns `λ_c` followed by the earlier
displacements of that colour, `Lz` is the functional defining `W_P` as a kernel, `Minv` is an
integer inverse of `Lz * Hz`, and `e` is the displacement of the row.  For the residual
colours `1, 3, 4`, `[Hfin | u]` is an integer unimodular completion whose inverse's last row
is the character `f_c` of `eq:d5-characters`; for colours `0, 2` the final four columns are
unimodular.  Generated from `evidence/even_d5/checks/verify_integration.py` and checked
here as vector identities over `ℤ`.
-/

namespace TorusEven
namespace D5Data

open Matrix

/-- colour 0, component 0, rank 1, displacement [-1, 0, 1, 0], neutral 0→2. -/
def Hz_c0p0 : Matrix (Fin 4) (Fin 1) ℤ := !![-4; 1; 1; 1]
def Lz_c0p0 : Matrix (Fin 1) (Fin 4) ℤ := !![1, 1, 1, 1]
def Minv_c0p0 : Matrix (Fin 1) (Fin 1) ℤ := !![-1]
def e_c0p0 : Fin 4 → ℤ := ![-1, 0, 1, 0]

/-- colour 1, component 0, rank 1, displacement [1, -1, 0, 0], neutral 1→0. -/
def Hz_c1p0 : Matrix (Fin 4) (Fin 1) ℤ := !![1; -4; 1; 1]
def Lz_c1p0 : Matrix (Fin 1) (Fin 4) ℤ := !![1, 1, 1, 1]
def Minv_c1p0 : Matrix (Fin 1) (Fin 1) ℤ := !![-1]
def e_c1p0 : Fin 4 → ℤ := ![1, -1, 0, 0]

/-- colour 2, component 0, rank 1, displacement [0, 1, -1, 0], neutral 2→1. -/
def Hz_c2p0 : Matrix (Fin 4) (Fin 1) ℤ := !![1; 1; -4; 1]
def Lz_c2p0 : Matrix (Fin 1) (Fin 4) ℤ := !![1, 1, 1, 1]
def Minv_c2p0 : Matrix (Fin 1) (Fin 1) ℤ := !![-1]
def e_c2p0 : Fin 4 → ℤ := ![0, 1, -1, 0]

/-- colour 3, component 1, rank 1, displacement [0, 0, 0, -1], neutral 3→4. -/
def Hz_c3p1 : Matrix (Fin 4) (Fin 1) ℤ := !![1; 1; 1; -4]
def Lz_c3p1 : Matrix (Fin 1) (Fin 4) ℤ := !![0, 0, 1, 0]
def Minv_c3p1 : Matrix (Fin 1) (Fin 1) ℤ := !![1]
def e_c3p1 : Fin 4 → ℤ := ![0, 0, 0, -1]

/-- colour 4, component 1, rank 1, displacement [0, 0, 0, 1], neutral 4→3. -/
def Hz_c4p1 : Matrix (Fin 4) (Fin 1) ℤ := !![1; 1; 1; 1]
def Lz_c4p1 : Matrix (Fin 1) (Fin 4) ℤ := !![0, 0, 1, 0]
def Minv_c4p1 : Matrix (Fin 1) (Fin 1) ℤ := !![1]
def e_c4p1 : Fin 4 → ℤ := ![0, 0, 0, 1]

/-- colour 0, component 2, rank 2, displacement [1, -1, 0, 0], neutral 1→0. -/
def Hz_c0p2 : Matrix (Fin 4) (Fin 2) ℤ := !![-4, -1; 1, 0; 1, 1; 1, 0]
def Lz_c0p2 : Matrix (Fin 2) (Fin 4) ℤ := !![0, 0, 1, 0; 0, 0, 0, 1]
def Minv_c0p2 : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, -1]
def e_c0p2 : Fin 4 → ℤ := ![1, -1, 0, 0]

/-- colour 3, component 2, rank 2, displacement [0, 1, 0, 0], neutral 4→1. -/
def Hz_c3p2 : Matrix (Fin 4) (Fin 2) ℤ := !![1, 0; 1, 0; 1, 0; -4, -1]
def Lz_c3p2 : Matrix (Fin 2) (Fin 4) ℤ := !![0, 0, 1, 0; 0, 0, 0, 1]
def Minv_c3p2 : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; -4, -1]
def e_c3p2 : Fin 4 → ℤ := ![0, 1, 0, 0]

/-- colour 4, component 2, rank 2, displacement [-1, 0, 0, 0], neutral 0→4. -/
def Hz_c4p2 : Matrix (Fin 4) (Fin 2) ℤ := !![1, 0; 1, 0; 1, 0; 1, 1]
def Lz_c4p2 : Matrix (Fin 2) (Fin 4) ℤ := !![0, 0, 1, 0; 0, 0, 0, 1]
def Minv_c4p2 : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; -1, 1]
def e_c4p2 : Fin 4 → ℤ := ![-1, 0, 0, 0]

/-- colour 1, component 3, rank 2, displacement [0, 0, -1, 1], neutral 2→3. -/
def Hz_c1p3 : Matrix (Fin 4) (Fin 2) ℤ := !![1, 1; -4, -1; 1, 0; 1, 0]
def Lz_c1p3 : Matrix (Fin 2) (Fin 4) ℤ := !![0, 1, 0, 0; 1, 1, 1, 1]
def Minv_c1p3 : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; -1, 4]
def e_c1p3 : Fin 4 → ℤ := ![0, 0, -1, 1]

/-- colour 2, component 3, rank 2, displacement [0, 0, 1, -1], neutral 3→2. -/
def Hz_c2p3 : Matrix (Fin 4) (Fin 2) ℤ := !![1, 0; 1, 1; -4, -1; 1, 0]
def Lz_c2p3 : Matrix (Fin 2) (Fin 4) ℤ := !![0, 1, 0, 0; 1, 1, 1, 1]
def Minv_c2p3 : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, 1]
def e_c2p3 : Fin 4 → ℤ := ![0, 0, 1, -1]

/-- colour 0, component 4, rank 3, displacement [0, 0, -1, 0], neutral 2→4. -/
def Hz_c0p4 : Matrix (Fin 4) (Fin 3) ℤ := !![-4, -1, 1; 1, 0, -1; 1, 1, 0; 1, 0, 0]
def Lz_c0p4 : Matrix (Fin 3) (Fin 4) ℤ := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1]
def Minv_c0p4 : Matrix (Fin 3) (Fin 3) ℤ := !![0, 0, 1; -1, -1, -3; 0, -1, 1]
def e_c0p4 : Fin 4 → ℤ := ![0, 0, -1, 0]

/-- colour 2, component 4, rank 3, displacement [0, 0, 1, 0], neutral 4→2. -/
def Hz_c2p4 : Matrix (Fin 4) (Fin 3) ℤ := !![1, 0, 0; 1, 1, 0; -4, -1, 1; 1, 0, -1]
def Lz_c2p4 : Matrix (Fin 3) (Fin 4) ℤ := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1]
def Minv_c2p4 : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 0; -1, 1, 0; 1, 0, -1]
def e_c2p4 : Fin 4 → ℤ := ![0, 0, 1, 0]

def Hfull_c0 : Matrix (Fin 4) (Fin 4) ℤ := !![-4, -1, 1, 0; 1, 0, -1, 0; 1, 1, 0, -1; 1, 0, 0, 0]
def Hfullinv_c0 : Matrix (Fin 4) (Fin 4) ℤ := !![0, 0, 0, 1; -1, -1, 0, -3; 0, -1, 0, 1; -1, -1, -1, -2]

def Hfin_c1 : Matrix (Fin 4) (Fin 3) ℤ := !![1, 1, 0; -4, -1, 0; 1, 0, -1; 1, 0, 1]
def u_c1 : Fin 4 → ℤ := ![-2, -2, 1, 2]
def Qinv_c1 : Matrix (Fin 4) (Fin 4) ℤ := !![-3, -3, -4, -4; 8, 7, 10, 10; -1, -1, -2, -1; 2, 2, 3, 3]
def f_c1 : Fin 4 → ℤ := ![2, 2, 3, 3]

def Hfull_c2 : Matrix (Fin 4) (Fin 4) ℤ := !![1, 0, 0, 0; 1, 1, 0, 0; -4, -1, 1, 1; 1, 0, -1, 0]
def Hfullinv_c2 : Matrix (Fin 4) (Fin 4) ℤ := !![1, 0, 0, 0; -1, 1, 0, 0; 1, 0, 0, -1; 2, 1, 1, 1]

def Hfin_c3 : Matrix (Fin 4) (Fin 3) ℤ := !![1, 0, 0; 1, 0, 1; 1, 0, 0; -4, -1, 0]
def u_c3 : Fin 4 → ℤ := ![-2, -2, -1, -2]
def Qinv_c3 : Matrix (Fin 4) (Fin 4) ℤ := !![-1, 0, 2, 0; 6, 0, -10, -1; -1, 1, 0, 0; -1, 0, 1, 0]
def f_c3 : Fin 4 → ℤ := ![-1, 0, 1, 0]

def Hfin_c4 : Matrix (Fin 4) (Fin 3) ℤ := !![1, 0, -1; 1, 0, 0; 1, 0, 0; 1, 1, 0]
def u_c4 : Fin 4 → ℤ := ![-2, -2, -1, -2]
def Qinv_c4 : Matrix (Fin 4) (Fin 4) ℤ := !![0, -1, 2, 0; 0, -1, 0, 1; -1, 1, 0, 0; 0, -1, 1, 0]
def f_c4 : Fin 4 → ℤ := ![0, -1, 1, 0]

theorem inv1_c0p0 : ∀ v : Fin 1 → ℤ, Lz_c0p0 *ᵥ (Hz_c0p0 *ᵥ (Minv_c0p0 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Lz_c0p0, Hz_c0p0, Minv_c0p0, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv2_c0p0 : ∀ v : Fin 1 → ℤ, Minv_c0p0 *ᵥ (Lz_c0p0 *ᵥ (Hz_c0p0 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Lz_c0p0, Hz_c0p0, Minv_c0p0, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv1_c1p0 : ∀ v : Fin 1 → ℤ, Lz_c1p0 *ᵥ (Hz_c1p0 *ᵥ (Minv_c1p0 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Lz_c1p0, Hz_c1p0, Minv_c1p0, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv2_c1p0 : ∀ v : Fin 1 → ℤ, Minv_c1p0 *ᵥ (Lz_c1p0 *ᵥ (Hz_c1p0 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Lz_c1p0, Hz_c1p0, Minv_c1p0, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv1_c2p0 : ∀ v : Fin 1 → ℤ, Lz_c2p0 *ᵥ (Hz_c2p0 *ᵥ (Minv_c2p0 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Lz_c2p0, Hz_c2p0, Minv_c2p0, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv2_c2p0 : ∀ v : Fin 1 → ℤ, Minv_c2p0 *ᵥ (Lz_c2p0 *ᵥ (Hz_c2p0 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Lz_c2p0, Hz_c2p0, Minv_c2p0, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv1_c3p1 : ∀ v : Fin 1 → ℤ, Lz_c3p1 *ᵥ (Hz_c3p1 *ᵥ (Minv_c3p1 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Lz_c3p1, Hz_c3p1, Minv_c3p1, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv2_c3p1 : ∀ v : Fin 1 → ℤ, Minv_c3p1 *ᵥ (Lz_c3p1 *ᵥ (Hz_c3p1 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Lz_c3p1, Hz_c3p1, Minv_c3p1, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv1_c4p1 : ∀ v : Fin 1 → ℤ, Lz_c4p1 *ᵥ (Hz_c4p1 *ᵥ (Minv_c4p1 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Lz_c4p1, Hz_c4p1, Minv_c4p1, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv2_c4p1 : ∀ v : Fin 1 → ℤ, Minv_c4p1 *ᵥ (Lz_c4p1 *ᵥ (Hz_c4p1 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Lz_c4p1, Hz_c4p1, Minv_c4p1, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv1_c0p2 : ∀ v : Fin 2 → ℤ, Lz_c0p2 *ᵥ (Hz_c0p2 *ᵥ (Minv_c0p2 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Lz_c0p2, Hz_c0p2, Minv_c0p2, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv2_c0p2 : ∀ v : Fin 2 → ℤ, Minv_c0p2 *ᵥ (Lz_c0p2 *ᵥ (Hz_c0p2 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Lz_c0p2, Hz_c0p2, Minv_c0p2, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv1_c3p2 : ∀ v : Fin 2 → ℤ, Lz_c3p2 *ᵥ (Hz_c3p2 *ᵥ (Minv_c3p2 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Lz_c3p2, Hz_c3p2, Minv_c3p2, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv2_c3p2 : ∀ v : Fin 2 → ℤ, Minv_c3p2 *ᵥ (Lz_c3p2 *ᵥ (Hz_c3p2 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Lz_c3p2, Hz_c3p2, Minv_c3p2, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv1_c4p2 : ∀ v : Fin 2 → ℤ, Lz_c4p2 *ᵥ (Hz_c4p2 *ᵥ (Minv_c4p2 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Lz_c4p2, Hz_c4p2, Minv_c4p2, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv2_c4p2 : ∀ v : Fin 2 → ℤ, Minv_c4p2 *ᵥ (Lz_c4p2 *ᵥ (Hz_c4p2 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Lz_c4p2, Hz_c4p2, Minv_c4p2, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv1_c1p3 : ∀ v : Fin 2 → ℤ, Lz_c1p3 *ᵥ (Hz_c1p3 *ᵥ (Minv_c1p3 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Lz_c1p3, Hz_c1p3, Minv_c1p3, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv2_c1p3 : ∀ v : Fin 2 → ℤ, Minv_c1p3 *ᵥ (Lz_c1p3 *ᵥ (Hz_c1p3 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Lz_c1p3, Hz_c1p3, Minv_c1p3, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv1_c2p3 : ∀ v : Fin 2 → ℤ, Lz_c2p3 *ᵥ (Hz_c2p3 *ᵥ (Minv_c2p3 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Lz_c2p3, Hz_c2p3, Minv_c2p3, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv2_c2p3 : ∀ v : Fin 2 → ℤ, Minv_c2p3 *ᵥ (Lz_c2p3 *ᵥ (Hz_c2p3 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Lz_c2p3, Hz_c2p3, Minv_c2p3, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv1_c0p4 : ∀ v : Fin 3 → ℤ, Lz_c0p4 *ᵥ (Hz_c0p4 *ᵥ (Minv_c0p4 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Lz_c0p4, Hz_c0p4, Minv_c0p4, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv2_c0p4 : ∀ v : Fin 3 → ℤ, Minv_c0p4 *ᵥ (Lz_c0p4 *ᵥ (Hz_c0p4 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Lz_c0p4, Hz_c0p4, Minv_c0p4, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv1_c2p4 : ∀ v : Fin 3 → ℤ, Lz_c2p4 *ᵥ (Hz_c2p4 *ᵥ (Minv_c2p4 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Lz_c2p4, Hz_c2p4, Minv_c2p4, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem inv2_c2p4 : ∀ v : Fin 3 → ℤ, Minv_c2p4 *ᵥ (Lz_c2p4 *ᵥ (Hz_c2p4 *ᵥ v)) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Lz_c2p4, Hz_c2p4, Minv_c2p4, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem full_c0 : ∀ v : Fin 4 → ℤ, Hfull_c0 *ᵥ (Hfullinv_c0 *ᵥ v) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Hfull_c0, Hfullinv_c0, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem full_c2 : ∀ v : Fin 4 → ℤ, Hfull_c2 *ᵥ (Hfullinv_c2 *ᵥ v) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Hfull_c2, Hfullinv_c2, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem aug1_c1 : ∀ v : Fin 4 → ℤ, Cert.augment Hfin_c1 u_c1 *ᵥ (Qinv_c1 *ᵥ v) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Cert.augment, Hfin_c1, u_c1, Qinv_c1, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem aug2_c1 : ∀ v : Fin 4 → ℤ, Qinv_c1 *ᵥ (Cert.augment Hfin_c1 u_c1 *ᵥ v) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Cert.augment, Hfin_c1, u_c1, Qinv_c1, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem lastRow_c1 : ∀ j, Qinv_c1 3 j = f_c1 j := by
  decide

theorem aug1_c3 : ∀ v : Fin 4 → ℤ, Cert.augment Hfin_c3 u_c3 *ᵥ (Qinv_c3 *ᵥ v) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Cert.augment, Hfin_c3, u_c3, Qinv_c3, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem aug2_c3 : ∀ v : Fin 4 → ℤ, Qinv_c3 *ᵥ (Cert.augment Hfin_c3 u_c3 *ᵥ v) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Cert.augment, Hfin_c3, u_c3, Qinv_c3, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem lastRow_c3 : ∀ j, Qinv_c3 3 j = f_c3 j := by
  decide

theorem aug1_c4 : ∀ v : Fin 4 → ℤ, Cert.augment Hfin_c4 u_c4 *ᵥ (Qinv_c4 *ᵥ v) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Cert.augment, Hfin_c4, u_c4, Qinv_c4, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem aug2_c4 : ∀ v : Fin 4 → ℤ, Qinv_c4 *ᵥ (Cert.augment Hfin_c4 u_c4 *ᵥ v) = v := by
  intro v
  ext i
  fin_cases i <;> simp [Cert.augment, Hfin_c4, u_c4, Qinv_c4, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

theorem lastRow_c4 : ∀ j, Qinv_c4 3 j = f_c4 j := by
  decide

end D5Data
end TorusEven
