import D7Odd.Handoff.ReturnCriterion

namespace D7Odd
namespace Handoff

/-!
Lean-facing interface for the Target-A `23/32` seam quotient.

The current proof notes reduce the generic `23/32` primitive block to an
arithmetic quotient on `{1,...,h}`.  This file records that quotient as a
formal proof target.  It does not assert the theorem unconditionally; the
missing arithmetic proof is packaged as `TargetASeamQuotientArithmetic`.
-/

namespace TargetA

def phiNat (h x : Nat) : Nat :=
  if x < 3 then
    (x + h - 3) % h
  else if x < 5 then
    (x + h - 8) % h
  else
    (x + h - 5) % h

def phi (h : Nat) [NeZero h] : Fin h → Fin h :=
  fun x => ⟨phiNat h x.val, by
    unfold phiNat
    split
    · exact Nat.mod_lt _ (NeZero.pos h)
    · split
      · exact Nat.mod_lt _ (NeZero.pos h)
      · exact Nat.mod_lt _ (NeZero.pos h)⟩

def phiInvNat (h x : Nat) : Nat :=
  if x + 5 < h then
    (x + 5) % h
  else if x + 5 = h then
    3 % h
  else if x + 4 = h then
    4 % h
  else if x + 3 = h then
    0
  else if x + 2 = h then
    1 % h
  else
    2 % h

def phiInv (h : Nat) [NeZero h] : Fin h → Fin h :=
  fun x => ⟨phiInvNat h x.val, by
    unfold phiInvNat
    split
    · exact Nat.mod_lt _ (NeZero.pos h)
    · split
      · exact Nat.mod_lt _ (NeZero.pos h)
      · split
        · exact Nat.mod_lt _ (NeZero.pos h)
        · split
          · exact Nat.zero_lt_of_lt (NeZero.pos h)
          · split
            · exact Nat.mod_lt _ (NeZero.pos h)
            · exact Nat.mod_lt _ (NeZero.pos h)⟩

def residueShift (h : Nat) : ZMod 5 :=
  (3 : ZMod 5) - h

def goodPhiClass (h : Nat) : Prop :=
  h % 5 ≠ 3

private theorem add_sub_mod_eq_sub {h x c : Nat} (hc : c ≤ x) (hx : x < h) :
    (x + h - c) % h = x - c := by
  have hrewrite : x + h - c = h + (x - c) := by omega
  rw [hrewrite, Nat.add_mod_left]
  exact Nat.mod_eq_of_lt (by omega)

theorem phiInvNat_phiNat_of_lt {h x : Nat} (hh : 6 ≤ h) (hx : x < h) :
    phiInvNat h (phiNat h x) = x := by
  unfold phiNat
  by_cases hx3 : x < 3
  · have hx_cases : x = 0 ∨ x = 1 ∨ x = 2 := by omega
    rcases hx_cases with rfl | rfl | rfl
    · have hmod : (0 + h - 3) % h = h - 3 := by
        rw [show 0 + h - 3 = h - 3 by omega]
        exact Nat.mod_eq_of_lt (by omega)
      rw [if_pos (by omega), hmod]
      unfold phiInvNat
      have hnot1 : ¬ (h - 3 + 5 < h) := by omega
      have hnot2 : ¬ (h - 3 + 5 = h) := by omega
      have hnot3 : ¬ (h - 3 + 4 = h) := by omega
      have hyes : h - 3 + 3 = h := by omega
      simp [hnot1, hnot2, hnot3, hyes]
    · have hmod : (1 + h - 3) % h = h - 2 := by
        rw [show 1 + h - 3 = h - 2 by omega]
        exact Nat.mod_eq_of_lt (by omega)
      rw [if_pos (by omega), hmod]
      unfold phiInvNat
      have hnot1 : ¬ (h - 2 + 5 < h) := by omega
      have hnot2 : ¬ (h - 2 + 5 = h) := by omega
      have hnot3 : ¬ (h - 2 + 4 = h) := by omega
      have hnot4 : ¬ (h - 2 + 3 = h) := by omega
      have hyes : h - 2 + 2 = h := by omega
      simp [hnot1, hnot2, hnot3, hnot4, hyes,
        Nat.mod_eq_of_lt (by omega : 1 < h)]
    · have hmod : (2 + h - 3) % h = h - 1 := by
        rw [show 2 + h - 3 = h - 1 by omega]
        exact Nat.mod_eq_of_lt (by omega)
      rw [if_pos (by omega), hmod]
      unfold phiInvNat
      have hnot1 : ¬ (h - 1 + 5 < h) := by omega
      have hnot2 : ¬ (h - 1 + 5 = h) := by omega
      have hnot3 : ¬ (h - 1 + 4 = h) := by omega
      have hnot4 : ¬ (h - 1 + 3 = h) := by omega
      have hnot5 : ¬ (h - 1 + 2 = h) := by omega
      simp [hnot1, hnot2, hnot3, hnot4, hnot5,
        Nat.mod_eq_of_lt (by omega : 2 < h)]
  · by_cases hx5 : x < 5
    · have hx_cases : x = 3 ∨ x = 4 := by omega
      rcases hx_cases with rfl | rfl
      · have hmod : (3 + h - 8) % h = h - 5 := by
          rw [show 3 + h - 8 = h - 5 by omega]
          exact Nat.mod_eq_of_lt (by omega)
        rw [if_neg (by omega), if_pos (by omega), hmod]
        unfold phiInvNat
        have hyes : h - 5 + 5 = h := by omega
        simp [hyes, Nat.mod_eq_of_lt (by omega : 3 < h)]
      · have hmod : (4 + h - 8) % h = h - 4 := by
          rw [show 4 + h - 8 = h - 4 by omega]
          exact Nat.mod_eq_of_lt (by omega)
        rw [if_neg (by omega), if_pos (by omega), hmod]
        unfold phiInvNat
        have hnot1 : ¬ (h - 4 + 5 < h) := by omega
        have hnot2 : ¬ (h - 4 + 5 = h) := by omega
        have hyes : h - 4 + 4 = h := by omega
        simp [hnot1, hnot2, hyes, Nat.mod_eq_of_lt (by omega : 4 < h)]
    · have hxge5 : 5 ≤ x := by omega
      have hmod : (x + h - 5) % h = x - 5 :=
        add_sub_mod_eq_sub hxge5 hx
      rw [if_neg hx3, if_neg hx5, hmod]
      unfold phiInvNat
      have hlt : x - 5 + 5 < h := by omega
      rw [if_pos hlt]
      have hsum : x - 5 + 5 = x := by omega
      rw [hsum]
      exact Nat.mod_eq_of_lt hx

theorem phiInv_phi_of_six_le {h : Nat} [NeZero h] (hh : 6 ≤ h) :
    Function.LeftInverse (phiInv h) (phi h) := by
  intro x
  apply Fin.ext
  exact phiInvNat_phiNat_of_lt hh x.isLt

theorem phiNat_phiInvNat_of_lt {h x : Nat} (hh : 6 ≤ h) (hx : x < h) :
    phiNat h (phiInvNat h x) = x := by
  unfold phiInvNat
  by_cases hlt : x + 5 < h
  · rw [if_pos hlt]
    have hmod : (x + 5) % h = x + 5 := Nat.mod_eq_of_lt hlt
    rw [hmod]
    unfold phiNat
    rw [if_neg (by omega : ¬ x + 5 < 3)]
    rw [if_neg (by omega : ¬ x + 5 < 5)]
    have hsum : x + 5 + h - 5 = h + x := by omega
    rw [hsum, Nat.add_mod_left]
    exact Nat.mod_eq_of_lt hx
  · rw [if_neg hlt]
    by_cases heq5 : x + 5 = h
    · rw [if_pos heq5]
      have hmod3 : 3 % h = 3 := Nat.mod_eq_of_lt (by omega)
      rw [hmod3]
      unfold phiNat
      rw [if_neg (by omega : ¬ 3 < 3)]
      rw [if_pos (by omega : 3 < 5)]
      have hmod : (3 + h - 8) % h = h - 5 := by
        rw [show 3 + h - 8 = h - 5 by omega]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hmod]
      omega
    · rw [if_neg heq5]
      by_cases heq4 : x + 4 = h
      · rw [if_pos heq4]
        have hmod4 : 4 % h = 4 := Nat.mod_eq_of_lt (by omega)
        rw [hmod4]
        unfold phiNat
        rw [if_neg (by omega : ¬ 4 < 3)]
        rw [if_pos (by omega : 4 < 5)]
        have hmod : (4 + h - 8) % h = h - 4 := by
          rw [show 4 + h - 8 = h - 4 by omega]
          exact Nat.mod_eq_of_lt (by omega)
        rw [hmod]
        omega
      · rw [if_neg heq4]
        by_cases heq3 : x + 3 = h
        · rw [if_pos heq3]
          unfold phiNat
          rw [if_pos (by omega : 0 < 3)]
          have hmod : (0 + h - 3) % h = h - 3 := by
            rw [show 0 + h - 3 = h - 3 by omega]
            exact Nat.mod_eq_of_lt (by omega)
          rw [hmod]
          omega
        · rw [if_neg heq3]
          by_cases heq2 : x + 2 = h
          · rw [if_pos heq2]
            have hmod1 : 1 % h = 1 := Nat.mod_eq_of_lt (by omega)
            rw [hmod1]
            unfold phiNat
            rw [if_pos (by omega : 1 < 3)]
            have hmod : (1 + h - 3) % h = h - 2 := by
              rw [show 1 + h - 3 = h - 2 by omega]
              exact Nat.mod_eq_of_lt (by omega)
            rw [hmod]
            omega
          · rw [if_neg heq2]
            have hxlast : x + 1 = h := by omega
            have hmod2 : 2 % h = 2 := Nat.mod_eq_of_lt (by omega)
            rw [hmod2]
            unfold phiNat
            rw [if_pos (by omega : 2 < 3)]
            have hmod : (2 + h - 3) % h = h - 1 := by
              rw [show 2 + h - 3 = h - 1 by omega]
              exact Nat.mod_eq_of_lt (by omega)
            rw [hmod]
            omega

theorem phi_phiInv_of_six_le {h : Nat} [NeZero h] (hh : 6 ≤ h) :
    Function.RightInverse (phiInv h) (phi h) := by
  intro x
  apply Fin.ext
  exact phiNat_phiInvNat_of_lt hh x.isLt

theorem phi_bijective_of_six_le {h : Nat} [NeZero h] (hh : 6 ≤ h) :
    Function.Bijective (phi h) :=
  bijective_of_inverse (phi h) (phiInv h)
    (phiInv_phi_of_six_le hh) (phi_phiInv_of_six_le hh)

structure TargetASeamQuotientArithmetic (h : Nat) [NeZero h] : Type where
  hmin : 6 ≤ h
  single_cycle_iff : IsSingleCycleMap (phi h) ↔ goodPhiClass h
  bad_class_five_cycles :
    h % 5 = 3 →
      ∃ C : Finset (Fin h → Prop),
        C.card = 5 ∧
        ∀ x : Fin h, ∃ component ∈ C, component x

theorem TargetASeamQuotientArithmetic.phi_bijective
    {h : Nat} [NeZero h] (pkg : TargetASeamQuotientArithmetic h) :
    Function.Bijective (phi h) :=
  phi_bijective_of_six_le pkg.hmin

structure TargetASeamQuotientPackage (m h : Nat) [NeZero m] [NeZero h] : Type where
  hm : m = 2 * h + 1
  hodd_range : 13 ≤ m
  arithmetic : TargetASeamQuotientArithmetic h
  q_hitting_23 : Prop
  q_hitting_23_proof : q_hitting_23
  q_hitting_32 : Prop
  q_hitting_32_proof : q_hitting_32
  q_first_return_23 : Prop
  q_first_return_23_proof : q_first_return_23
  q_first_return_32 : Prop
  q_first_return_32_proof : q_first_return_32
  length_sum_23 : Prop
  length_sum_23_proof : length_sum_23
  length_sum_32 : Prop
  length_sum_32_proof : length_sum_32

end TargetA
end Handoff
end D7Odd
