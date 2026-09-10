-- STATUS: main-path (masks as affine cosets of kernels; the per-colour subgroup chains)
import TorusEven.D5.Schedule
import TorusEven.D5.LatticeData
import TorusEven.D5.Chronological

/-!
# Cylinders as affine cosets and the subgroup chains

Each cylinder `C_P` of Table `tab:d5-cylinders` is `z_P + W_P` with `W_P = ker L_P`; the
`piecewiseAdd` of the chronological lemma on `C_P` is the mask-conditional translation used
by the schedule.  For each colour the chain `H_0 ⊆ H_1 ⊆ ⋯` of column spans is complementary
to the relevant `W_P` at each step (integer certificates), starts at `⟨λ_c⟩`, and ends at the
whole space (colours `0, 2`) or at `ker f_c` (colours `1, 3, 4`).
-/

namespace TorusEven
namespace D5

open Cert D5Data Chronological Matrix

variable {m : ℕ} [NeZero m]

/-! ### Cylinders -/

def zP : Fin 5 → Root m
  | 0 => 0
  | 1 => castV ![0, 0, 1, 0]
  | 2 => 0
  | 3 => castV ![-1, 0, 0, 0]
  | 4 => 0

def WP (m : ℕ) : Fin 5 → AddSubgroup (Root m)
  | 0 => kerOf (castM L0)
  | 1 => kerOf (castM L1)
  | 2 => kerOf (castM L2)
  | 3 => kerOf (castM L3)
  | 4 => kerOf (castM L4)

instance (P : Fin 5) : DecidablePred (· ∈ WP m P) :=
  match P with
  | 0 => Cert.decidableMemKerOf _
  | 1 => Cert.decidableMemKerOf _
  | 2 => Cert.decidableMemKerOf _
  | 3 => Cert.decidableMemKerOf _
  | 4 => Cert.decidableMemKerOf _

def maskP : Fin 5 → Root m → Prop
  | 0 => mask0
  | 1 => mask1
  | 2 => mask2
  | 3 => mask3
  | 4 => mask4

instance (P : Fin 5) : DecidablePred (maskP (m := m) P) :=
  match P with
  | 0 => (inferInstance : DecidablePred (mask0 (m := m)))
  | 1 => (inferInstance : DecidablePred (mask1 (m := m)))
  | 2 => (inferInstance : DecidablePred (mask2 (m := m)))
  | 3 => (inferInstance : DecidablePred (mask3 (m := m)))
  | 4 => (inferInstance : DecidablePred (mask4 (m := m)))

theorem mem_WP_iff (P : Fin 5) (x : Root m) : x - zP P ∈ WP m P ↔ maskP P x := by
  fin_cases P <;>
    simp [WP, zP, maskP, mask0, mask1, mask2, mask3, mask4, mem_kerOf, sum4, Matrix.mulVec,
      dotProduct, castM, castV, L0, L1, L2, L3, L4, Fin.sum_univ_four, funext_iff,
      Fin.forall_fin_succ, sub_eq_zero]
  all_goals (try (intro _; constructor <;> intro h <;> linear_combination h))


/-- The mask-conditional translation is the `piecewiseAdd` of the chronological lemma. -/
theorem piecewiseAdd_WP (P : Fin 5) (e : Root m) (x : Root m) :
    piecewiseAdd (WP m P) (zP P) e x = if maskP P x then x + e else x := by
  by_cases h : maskP P x
  · simp [piecewiseAdd, h, (mem_WP_iff P x).2 h]
  · simp [piecewiseAdd, h, mt (mem_WP_iff P x).1 h]

/-! ### Membership of displacements and the subgroup chains -/

theorem castV_mem_kerOf {r : ℕ} (L : Matrix (Fin r) (Fin 4) ℤ) (e : Fin 4 → ℤ) (h : L *ᵥ e = 0) :
    castV (m := m) e ∈ kerOf (castM L) := by
  rw [mem_kerOf, castM_mulVec_castV, h]
  funext i
  simp [castV]

theorem colSpan_empty : colSpan (castM (m := m) (Matrix.of fun _ (j : Fin 0) => j.elim0)) = ⊥ := by
  ext x
  rw [mem_colSpan, AddSubgroup.mem_bot]
  constructor
  · rintro ⟨a, rfl⟩
    funext i
    simp [Matrix.mulVec, dotProduct]
  · rintro rfl
    exact ⟨0, Matrix.mulVec_zero _⟩

theorem base_c0 : colSpan (castM (m := m) Hz_c0base) = AddSubgroup.zmultiples (castV lam_c0) := by
  rw [Hz_c0base_eq, colSpan_prepend, colSpan_empty, bot_sup_eq]

theorem isCompl_c0p0 : IsCompl (colSpan (castM (m := m) Hz_c0base)) (WP m 0) := by
  rw [← Hz_c0p0_eq]
  exact isCompl_of_inverse Hz_c0p0 L0 Minv_c0p0 inv1_c0p0 inv2_c0p0

theorem e_mem_c0p0 : castV (m := m) e_c0p0 ∈ WP m 0 :=
  castV_mem_kerOf L0 e_c0p0 e_c0p0_ker

theorem chain_c0p0 : colSpan (castM (m := m) Hz_c0p0next) =
    colSpan (castM Hz_c0base) ⊔ AddSubgroup.zmultiples (castV e_c0p0) := by
  rw [Hz_c0p0next_eq, colSpan_prepend, Hz_c0p0_eq]

theorem isCompl_c0p2 : IsCompl (colSpan (castM (m := m) Hz_c0p0next)) (WP m 2) := by
  rw [← Hz_c0p2_eq]
  exact isCompl_of_inverse Hz_c0p2 L2 Minv_c0p2 inv1_c0p2 inv2_c0p2

theorem e_mem_c0p2 : castV (m := m) e_c0p2 ∈ WP m 2 :=
  castV_mem_kerOf L2 e_c0p2 e_c0p2_ker

theorem chain_c0p2 : colSpan (castM (m := m) Hz_c0p2next) =
    colSpan (castM Hz_c0p0next) ⊔ AddSubgroup.zmultiples (castV e_c0p2) := by
  rw [Hz_c0p2next_eq, colSpan_prepend, Hz_c0p2_eq]

theorem isCompl_c0p4 : IsCompl (colSpan (castM (m := m) Hz_c0p2next)) (WP m 4) := by
  rw [← Hz_c0p4_eq]
  exact isCompl_of_inverse Hz_c0p4 L4 Minv_c0p4 inv1_c0p4 inv2_c0p4

theorem e_mem_c0p4 : castV (m := m) e_c0p4 ∈ WP m 4 :=
  castV_mem_kerOf L4 e_c0p4 e_c0p4_ker

theorem chain_c0p4 : colSpan (castM (m := m) Hz_c0p4next) =
    colSpan (castM Hz_c0p2next) ⊔ AddSubgroup.zmultiples (castV e_c0p4) := by
  rw [Hz_c0p4next_eq, colSpan_prepend, Hz_c0p4_eq]

theorem final_c0 : colSpan (castM (m := m) Hz_c0p4next) = ⊤ :=
  colSpan_eq_top_of_inverse Hz_c0p4next Hfullinv_c0 full_c0

theorem base_c1 : colSpan (castM (m := m) Hz_c1base) = AddSubgroup.zmultiples (castV lam_c1) := by
  rw [Hz_c1base_eq, colSpan_prepend, colSpan_empty, bot_sup_eq]

theorem isCompl_c1p0 : IsCompl (colSpan (castM (m := m) Hz_c1base)) (WP m 0) := by
  rw [← Hz_c1p0_eq]
  exact isCompl_of_inverse Hz_c1p0 L0 Minv_c1p0 inv1_c1p0 inv2_c1p0

theorem e_mem_c1p0 : castV (m := m) e_c1p0 ∈ WP m 0 :=
  castV_mem_kerOf L0 e_c1p0 e_c1p0_ker

theorem chain_c1p0 : colSpan (castM (m := m) Hz_c1p0next) =
    colSpan (castM Hz_c1base) ⊔ AddSubgroup.zmultiples (castV e_c1p0) := by
  rw [Hz_c1p0next_eq, colSpan_prepend, Hz_c1p0_eq]

theorem isCompl_c1p3 : IsCompl (colSpan (castM (m := m) Hz_c1p0next)) (WP m 3) := by
  rw [← Hz_c1p3_eq]
  exact isCompl_of_inverse Hz_c1p3 L3 Minv_c1p3 inv1_c1p3 inv2_c1p3

theorem e_mem_c1p3 : castV (m := m) e_c1p3 ∈ WP m 3 :=
  castV_mem_kerOf L3 e_c1p3 e_c1p3_ker

theorem chain_c1p3 : colSpan (castM (m := m) Hz_c1p3next) =
    colSpan (castM Hz_c1p0next) ⊔ AddSubgroup.zmultiples (castV e_c1p3) := by
  rw [Hz_c1p3next_eq, colSpan_prepend, Hz_c1p3_eq]

theorem final_c1 : kerOf (castM (m := m) (rowM f_c1)) = colSpan (castM Hz_c1p3next) :=
  kerOf_rowM_eq_colSpan Hz_c1p3next u_c1 Qinv_c1 f_c1 aug1_c1 aug2_c1 lastRow_c1

theorem base_c2 : colSpan (castM (m := m) Hz_c2base) = AddSubgroup.zmultiples (castV lam_c2) := by
  rw [Hz_c2base_eq, colSpan_prepend, colSpan_empty, bot_sup_eq]

theorem isCompl_c2p0 : IsCompl (colSpan (castM (m := m) Hz_c2base)) (WP m 0) := by
  rw [← Hz_c2p0_eq]
  exact isCompl_of_inverse Hz_c2p0 L0 Minv_c2p0 inv1_c2p0 inv2_c2p0

theorem e_mem_c2p0 : castV (m := m) e_c2p0 ∈ WP m 0 :=
  castV_mem_kerOf L0 e_c2p0 e_c2p0_ker

theorem chain_c2p0 : colSpan (castM (m := m) Hz_c2p0next) =
    colSpan (castM Hz_c2base) ⊔ AddSubgroup.zmultiples (castV e_c2p0) := by
  rw [Hz_c2p0next_eq, colSpan_prepend, Hz_c2p0_eq]

theorem isCompl_c2p3 : IsCompl (colSpan (castM (m := m) Hz_c2p0next)) (WP m 3) := by
  rw [← Hz_c2p3_eq]
  exact isCompl_of_inverse Hz_c2p3 L3 Minv_c2p3 inv1_c2p3 inv2_c2p3

theorem e_mem_c2p3 : castV (m := m) e_c2p3 ∈ WP m 3 :=
  castV_mem_kerOf L3 e_c2p3 e_c2p3_ker

theorem chain_c2p3 : colSpan (castM (m := m) Hz_c2p3next) =
    colSpan (castM Hz_c2p0next) ⊔ AddSubgroup.zmultiples (castV e_c2p3) := by
  rw [Hz_c2p3next_eq, colSpan_prepend, Hz_c2p3_eq]

theorem isCompl_c2p4 : IsCompl (colSpan (castM (m := m) Hz_c2p3next)) (WP m 4) := by
  rw [← Hz_c2p4_eq]
  exact isCompl_of_inverse Hz_c2p4 L4 Minv_c2p4 inv1_c2p4 inv2_c2p4

theorem e_mem_c2p4 : castV (m := m) e_c2p4 ∈ WP m 4 :=
  castV_mem_kerOf L4 e_c2p4 e_c2p4_ker

theorem chain_c2p4 : colSpan (castM (m := m) Hz_c2p4next) =
    colSpan (castM Hz_c2p3next) ⊔ AddSubgroup.zmultiples (castV e_c2p4) := by
  rw [Hz_c2p4next_eq, colSpan_prepend, Hz_c2p4_eq]

theorem final_c2 : colSpan (castM (m := m) Hz_c2p4next) = ⊤ :=
  colSpan_eq_top_of_inverse Hz_c2p4next Hfullinv_c2 full_c2

theorem base_c3 : colSpan (castM (m := m) Hz_c3base) = AddSubgroup.zmultiples (castV lam_c3) := by
  rw [Hz_c3base_eq, colSpan_prepend, colSpan_empty, bot_sup_eq]

theorem isCompl_c3p1 : IsCompl (colSpan (castM (m := m) Hz_c3base)) (WP m 1) := by
  rw [← Hz_c3p1_eq]
  exact isCompl_of_inverse Hz_c3p1 L1 Minv_c3p1 inv1_c3p1 inv2_c3p1

theorem e_mem_c3p1 : castV (m := m) e_c3p1 ∈ WP m 1 :=
  castV_mem_kerOf L1 e_c3p1 e_c3p1_ker

theorem chain_c3p1 : colSpan (castM (m := m) Hz_c3p1next) =
    colSpan (castM Hz_c3base) ⊔ AddSubgroup.zmultiples (castV e_c3p1) := by
  rw [Hz_c3p1next_eq, colSpan_prepend, Hz_c3p1_eq]

theorem isCompl_c3p2 : IsCompl (colSpan (castM (m := m) Hz_c3p1next)) (WP m 2) := by
  rw [← Hz_c3p2_eq]
  exact isCompl_of_inverse Hz_c3p2 L2 Minv_c3p2 inv1_c3p2 inv2_c3p2

theorem e_mem_c3p2 : castV (m := m) e_c3p2 ∈ WP m 2 :=
  castV_mem_kerOf L2 e_c3p2 e_c3p2_ker

theorem chain_c3p2 : colSpan (castM (m := m) Hz_c3p2next) =
    colSpan (castM Hz_c3p1next) ⊔ AddSubgroup.zmultiples (castV e_c3p2) := by
  rw [Hz_c3p2next_eq, colSpan_prepend, Hz_c3p2_eq]

theorem final_c3 : kerOf (castM (m := m) (rowM f_c3)) = colSpan (castM Hz_c3p2next) :=
  kerOf_rowM_eq_colSpan Hz_c3p2next u_c3 Qinv_c3 f_c3 aug1_c3 aug2_c3 lastRow_c3

theorem base_c4 : colSpan (castM (m := m) Hz_c4base) = AddSubgroup.zmultiples (castV lam_c4) := by
  rw [Hz_c4base_eq, colSpan_prepend, colSpan_empty, bot_sup_eq]

theorem isCompl_c4p1 : IsCompl (colSpan (castM (m := m) Hz_c4base)) (WP m 1) := by
  rw [← Hz_c4p1_eq]
  exact isCompl_of_inverse Hz_c4p1 L1 Minv_c4p1 inv1_c4p1 inv2_c4p1

theorem e_mem_c4p1 : castV (m := m) e_c4p1 ∈ WP m 1 :=
  castV_mem_kerOf L1 e_c4p1 e_c4p1_ker

theorem chain_c4p1 : colSpan (castM (m := m) Hz_c4p1next) =
    colSpan (castM Hz_c4base) ⊔ AddSubgroup.zmultiples (castV e_c4p1) := by
  rw [Hz_c4p1next_eq, colSpan_prepend, Hz_c4p1_eq]

theorem isCompl_c4p2 : IsCompl (colSpan (castM (m := m) Hz_c4p1next)) (WP m 2) := by
  rw [← Hz_c4p2_eq]
  exact isCompl_of_inverse Hz_c4p2 L2 Minv_c4p2 inv1_c4p2 inv2_c4p2

theorem e_mem_c4p2 : castV (m := m) e_c4p2 ∈ WP m 2 :=
  castV_mem_kerOf L2 e_c4p2 e_c4p2_ker

theorem chain_c4p2 : colSpan (castM (m := m) Hz_c4p2next) =
    colSpan (castM Hz_c4p1next) ⊔ AddSubgroup.zmultiples (castV e_c4p2) := by
  rw [Hz_c4p2next_eq, colSpan_prepend, Hz_c4p2_eq]

theorem final_c4 : kerOf (castM (m := m) (rowM f_c4)) = colSpan (castM Hz_c4p2next) :=
  kerOf_rowM_eq_colSpan Hz_c4p2next u_c4 Qinv_c4 f_c4 aug1_c4 aug2_c4 lastRow_c4

end D5
end TorusEven
