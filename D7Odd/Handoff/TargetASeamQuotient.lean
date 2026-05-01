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

structure TargetASeamQuotientArithmetic (h : Nat) [NeZero h] : Type where
  hmin : 6 ≤ h
  left_inverse : Function.LeftInverse (phiInv h) (phi h)
  right_inverse : Function.RightInverse (phiInv h) (phi h)
  single_cycle_iff : IsSingleCycleMap (phi h) ↔ goodPhiClass h
  bad_class_five_cycles :
    h % 5 = 3 →
      ∃ C : Finset (Fin h → Prop),
        C.card = 5 ∧
        ∀ x : Fin h, ∃ component ∈ C, component x

theorem TargetASeamQuotientArithmetic.phi_bijective
    {h : Nat} [NeZero h] (pkg : TargetASeamQuotientArithmetic h) :
    Function.Bijective (phi h) :=
  bijective_of_inverse (phi h) (phiInv h)
    pkg.left_inverse pkg.right_inverse

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
