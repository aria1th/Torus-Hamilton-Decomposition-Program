import EvenV11.RootFlatCycleData
import Shared.RankCycle

/-!
# D2 anti-diagonal base — faithful port of the verified root-flat pseudocode

Paper: `root_flat_first_returns.tex`, Prop "two-dimensional anti-diagonal base".
Verified pseudocode: `scripts/verify_rootflat_certificates.py` `[E]`
(`d2_antidiagonal_dir` passes RF1/RF2/RF3 for even `m`).

First **complete, `sorry`-free** instance of `RootFlatCycle.RootFlatCycleData`
from a concrete `dir`: it shows end-to-end that "supply a `dir` + RF1/RF2/RF3"
produces a `FinalRootFlatTorusCertificate`, and fixes the RF1/RF2/RF3 proof
pattern reused by the harder bases (H1/H3/H4).

`dir` (`n = 1`, colours/directions `Fin 2`): colour 0 increments the free
coordinate at the height-`0` layer (direction `0`) and is a no-op (direction `1`)
elsewhere — first return `+1`; colour 1 is the complementary Latin choice —
first return `+(m-1)`. Both carries are units, so RF3 follows from
`Shared.zmod_add_single_cycle_of_unit`.
-/

namespace EvenV11
namespace D2AntiDiagonal

open Shared StandardRootFlatLift

variable {m : Nat} [NeZero m]

theorem m_pos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)

/-- The standard generator step is a translation by a fixed vector, hence
bijective. -/
theorem rootStep_bijective {n : Nat} (i : Fin (n + 1)) :
    Function.Bijective
      (StandardRootFlatLift.rootStep i : RootState n m → RootState n m) := by
  have h :
      (StandardRootFlatLift.rootStep i : RootState n m → RootState n m)
        = fun w => w + fun j => if i = j.castSucc then (1 : ZMod m) else 0 := by
    funext w j
    simp only [StandardRootFlatLift.rootStep, Pi.add_apply]
    by_cases hh : i = j.castSucc <;> simp [hh]
  rw [h]
  exact (Equiv.addRight _).bijective

/-- The "last" direction is a no-op. -/
theorem rootStep_last {n : Nat} (w : RootState n m) :
    StandardRootFlatLift.rootStep (Fin.last n) w = w := by
  funext j
  have hne : Fin.last n ≠ j.castSucc := fun h => (Fin.castSucc_lt_last j).ne (h.symm)
  simp [StandardRootFlatLift.rootStep, hne]

/-- Direction `0` increments the single coordinate (`n = 1`). -/
theorem rootStep_zero (w : RootState 1 m) :
    StandardRootFlatLift.rootStep (0 : Fin 2) w = fun _ => w 0 + 1 := by
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  simp [StandardRootFlatLift.rootStep]

/-- D2 anti-diagonal row word: identity at the height-`0` layer, the
transposition `(0 1)` at every other layer. -/
def row (t : ZMod m) (_w : RootState 1 m) : TorusColor 2 ≃ TorusDirection 2 :=
  if t = 0 then Equiv.refl (Fin 2) else Equiv.swap 0 1

/-- The induced direction table. -/
def dir (t : ZMod m) (w : RootState 1 m) (c : TorusColor 2) : TorusDirection 2 :=
  row t w c

/-! ## RF1 — Latin rows (automatic from the row equivalence) -/

theorem rowLatin : (RootFlatCycle.schedule (dir (m := m))).rowLatin :=
  fun t w => (row t w).bijective

/-! ## RF2 — bijective layer maps (the direction is constant in `w`) -/

theorem layerBijective : (RootFlatCycle.schedule (dir (m := m))).layerBijective := by
  intro t c
  have hmap :
      (RootFlatCycle.schedule (dir (m := m))).layerMap t c
        = StandardRootFlatLift.rootStep
            ((if t = 0 then Equiv.refl (Fin 2) else Equiv.swap 0 1) c) := by
    funext w
    rfl
  rw [hmap]
  exact rootStep_bijective _

/-! ## RF3 — first returns are single cycles -/

theorem cast_ne_zero_of_lt {k : Nat} (hk : 1 ≤ k) (hkm : k < m) :
    (k : ZMod m) ≠ 0 := by
  intro h
  rw [CharP.cast_eq_zero_iff (ZMod m) m k] at h
  have := Nat.le_of_dvd (by omega) h
  omega

theorem one_eq_last : (1 : Fin 2) = Fin.last 1 := by decide

/-- Colour-0 prefix maps collapse to a single `+1` increment. -/
theorem prefixMap0_eq :
    ∀ k, 1 ≤ k → k ≤ m → ∀ w : RootState 1 m,
      (RootFlatCycle.schedule (dir (m := m))).prefixMap (0 : TorusColor 2) k w
        = fun _ => w 0 + 1
  | 1, _, _, w => by
      have heq :
          (RootFlatCycle.schedule (dir (m := m))).layerMap ((0 : Nat) : ZMod m)
              (0 : TorusColor 2) w
            = StandardRootFlatLift.rootStep (0 : Fin 2) w := by
        simp [Shared.RootFlatSchedule.layerMap, RootFlatCycle.schedule, dir, row]
      have hpre :
          (RootFlatCycle.schedule (dir (m := m))).prefixMap (0 : TorusColor 2) 1 w
            = (RootFlatCycle.schedule (dir (m := m))).layerMap ((0 : Nat) : ZMod m)
                (0 : TorusColor 2) w := rfl
      rw [hpre, heq, rootStep_zero]
  | (k + 2), _, hkm, w => by
      have hk1 : 1 ≤ k + 1 := by omega
      have hk1m : k + 1 ≤ m := by omega
      have ih := prefixMap0_eq (k + 1) hk1 hk1m w
      have hne : ((k : ZMod m) + 1) ≠ 0 := by
        have h := cast_ne_zero_of_lt (m := m) (k := k + 1) (by omega) (by omega)
        simpa using h
      have hpre :
          (RootFlatCycle.schedule (dir (m := m))).prefixMap (0 : TorusColor 2) (k + 2) w
            = (RootFlatCycle.schedule (dir (m := m))).layerMap ((k + 1 : Nat) : ZMod m)
                (0 : TorusColor 2)
                ((RootFlatCycle.schedule (dir (m := m))).prefixMap (0 : TorusColor 2) (k + 1) w) :=
        rfl
      rw [hpre, ih]
      have heq :
          (RootFlatCycle.schedule (dir (m := m))).layerMap ((k + 1 : Nat) : ZMod m)
              (0 : TorusColor 2) (fun _ => w 0 + 1)
            = StandardRootFlatLift.rootStep (1 : Fin 2) (fun _ => w 0 + 1) := by
        simp [Shared.RootFlatSchedule.layerMap, RootFlatCycle.schedule, dir, row,
          if_neg hne, Equiv.swap_apply_left]
      rw [heq, one_eq_last, rootStep_last]

/-- Colour-1 prefix maps accumulate `+(k-1)` increments. -/
theorem prefixMap1_eq :
    ∀ k, 1 ≤ k → k ≤ m → ∀ w : RootState 1 m,
      (RootFlatCycle.schedule (dir (m := m))).prefixMap (1 : TorusColor 2) k w
        = fun _ => w 0 + ((k - 1 : Nat) : ZMod m)
  | 1, _, _, w => by
      have heq :
          (RootFlatCycle.schedule (dir (m := m))).layerMap ((0 : Nat) : ZMod m)
              (1 : TorusColor 2) w
            = StandardRootFlatLift.rootStep (1 : Fin 2) w := by
        simp [Shared.RootFlatSchedule.layerMap, RootFlatCycle.schedule, dir, row]
      have hpre :
          (RootFlatCycle.schedule (dir (m := m))).prefixMap (1 : TorusColor 2) 1 w
            = (RootFlatCycle.schedule (dir (m := m))).layerMap ((0 : Nat) : ZMod m)
                (1 : TorusColor 2) w := rfl
      rw [hpre, heq, one_eq_last, rootStep_last]
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      simp
  | (k + 2), _, hkm, w => by
      have hk1 : 1 ≤ k + 1 := by omega
      have hk1m : k + 1 ≤ m := by omega
      have ih := prefixMap1_eq (k + 1) hk1 hk1m w
      have hne : ((k : ZMod m) + 1) ≠ 0 := by
        have h := cast_ne_zero_of_lt (m := m) (k := k + 1) (by omega) (by omega)
        simpa using h
      have hpre :
          (RootFlatCycle.schedule (dir (m := m))).prefixMap (1 : TorusColor 2) (k + 2) w
            = (RootFlatCycle.schedule (dir (m := m))).layerMap ((k + 1 : Nat) : ZMod m)
                (1 : TorusColor 2)
                ((RootFlatCycle.schedule (dir (m := m))).prefixMap (1 : TorusColor 2) (k + 1) w) :=
        rfl
      rw [hpre, ih]
      have heq :
          (RootFlatCycle.schedule (dir (m := m))).layerMap ((k + 1 : Nat) : ZMod m)
              (1 : TorusColor 2) (fun _ => w 0 + ((k + 1 - 1 : Nat) : ZMod m))
            = StandardRootFlatLift.rootStep (0 : Fin 2)
                (fun _ => w 0 + ((k + 1 - 1 : Nat) : ZMod m)) := by
        simp [Shared.RootFlatSchedule.layerMap, RootFlatCycle.schedule, dir, row,
          if_neg hne, Equiv.swap_apply_right]
      rw [heq, rootStep_zero]
      have e1' : (k + 1 - 1 : Nat) = k := by omega
      have e2' : (k + 2 - 1 : Nat) = k + 1 := by omega
      funext j
      rw [e1', e2']
      push_cast
      ring

/-- The coordinate equivalence `RootState 1 m ≃ ZMod m`. -/
def e1 : RootState 1 m ≃ ZMod m := Equiv.funUnique (Fin 1) (ZMod m)

theorem returnMap0_eq (w : RootState 1 m) :
    (RootFlatCycle.schedule (dir (m := m))).returnMap (0 : TorusColor 2) w
      = fun _ => w 0 + 1 := by
  rw [Shared.RootFlatSchedule.returnMap_eq_prefixMap]
  exact prefixMap0_eq m m_pos (le_refl m) w

theorem returnMap1_eq (w : RootState 1 m) :
    (RootFlatCycle.schedule (dir (m := m))).returnMap (1 : TorusColor 2) w
      = fun _ => w 0 + ((m - 1 : Nat) : ZMod m) := by
  rw [Shared.RootFlatSchedule.returnMap_eq_prefixMap]
  exact prefixMap1_eq m m_pos (le_refl m) w

theorem cast_m_sub_one : ((m - 1 : Nat) : ZMod m) = -1 := by
  rw [Nat.cast_sub m_pos, ZMod.natCast_self]
  simp

theorem returnsSingleCycle_zero :
    IsSingleCycleMap ((RootFlatCycle.schedule (dir (m := m))).returnMap (0 : TorusColor 2)) := by
  refine single_cycle_of_equiv_conj (e1 (m := m)).symm _
    (fun x : ZMod m => x + 1)
    (zmod_add_single_cycle_of_unit isUnit_one) ?_
  intro x
  rw [returnMap0_eq]
  simp [e1, Equiv.funUnique, Equiv.symm_symm]

theorem returnsSingleCycle_one :
    IsSingleCycleMap ((RootFlatCycle.schedule (dir (m := m))).returnMap (1 : TorusColor 2)) := by
  refine single_cycle_of_equiv_conj (e1 (m := m)).symm _
    (fun x : ZMod m => x + ((m - 1 : Nat) : ZMod m))
    (zmod_add_single_cycle_of_unit (by rw [cast_m_sub_one]; exact isUnit_one.neg)) ?_
  intro x
  rw [returnMap1_eq]
  simp [e1, Equiv.funUnique, Equiv.symm_symm]

theorem returnsSingleCycle :
    (RootFlatCycle.schedule (dir (m := m))).returnsSingleCycle := by
  intro c
  fin_cases c
  · exact returnsSingleCycle_zero
  · exact returnsSingleCycle_one

/-! ## Assembly -/

/-- The verified D2 anti-diagonal cycle data. -/
def cycleData : RootFlatCycle.RootFlatCycleData 1 m where
  dir := dir
  rowLatin := rowLatin
  layerBijective := layerBijective
  returnsSingleCycle := returnsSingleCycle

/-- `D₂(m)` root-flat certificate, for every `m ≥ 1`, with **no `sorry`**. -/
theorem d2Certificate : FinalRootFlatTorusCertificate 2 m :=
  RootFlatCycle.finalRootFlatTorusCertificate_of_cycleData (cycleData (m := m))

end D2AntiDiagonal
end EvenV11
