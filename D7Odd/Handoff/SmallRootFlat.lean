import D7Odd.Handoff.ReturnCriterion

namespace D7Odd
namespace Handoff

def rootSixVec {m : Nat} (x : Fin 6 → ZMod m) : Vec7 m :=
  ![x 0, x 1, x 2, x 3, x 4, x 5, -(x 0 + x 1 + x 2 + x 3 + x 4 + x 5)]

theorem root7_rootSixVec {m : Nat} (x : Fin 6 → ZMod m) :
    Root7 m (rootSixVec x) := by
  unfold Root7 sum7 rootSixVec
  rw [Fin.sum_univ_seven]
  simp

def rootOfSix {m : Nat} (x : Fin 6 → ZMod m) : RootState7 m :=
  ⟨rootSixVec x, root7_rootSixVec x⟩

def sixOfRoot {m : Nat} (w : RootState7 m) : Fin 6 → ZMod m :=
  fun i => w.1 ⟨i.val, by omega⟩

theorem sixOfRoot_rootOfSix {m : Nat} (x : Fin 6 → ZMod m) :
    sixOfRoot (rootOfSix x) = x := by
  funext i
  fin_cases i <;> simp [sixOfRoot, rootOfSix, rootSixVec]

theorem rootSix_six_coord {m : Nat} (w : RootState7 m) :
    w.1 6 = -(w.1 0 + w.1 1 + w.1 2 + w.1 3 + w.1 4 + w.1 5) := by
  have h := w.2
  unfold Root7 sum7 at h
  rw [Fin.sum_univ_seven] at h
  rw [eq_neg_iff_add_eq_zero]
  simpa [add_assoc, add_comm, add_left_comm] using h

set_option linter.flexible false in
theorem rootOfSix_sixOfRoot {m : Nat} (w : RootState7 m) :
    rootOfSix (sixOfRoot w) = w := by
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [sixOfRoot, rootOfSix, rootSixVec]
  rw [rootSix_six_coord w]
  ring

def rootSixEquiv (m : Nat) : (Fin 6 → ZMod m) ≃ RootState7 m where
  toFun := rootOfSix
  invFun := sixOfRoot
  left_inv := sixOfRoot_rootOfSix
  right_inv := rootOfSix_sixOfRoot

def zeroMaskVec (m : Nat) (w : Vec7 m) : Nat :=
  Finset.univ.sum fun i : Fin 7 => if w i = 0 then 2 ^ i.val else 0

def zeroMask (m : Nat) (w : RootState7 m) : Nat :=
  zeroMaskVec m w.1

def shiftIndex7 (i c : Fin 7) : Fin 7 :=
  Fin.ofNat 7 (i.val + 7 - c.val)

def shiftMask7 (mask : Nat) (c : Fin 7) : Nat :=
  Finset.univ.sum fun i : Fin 7 =>
    if mask.testBit i.val then 2 ^ (shiftIndex7 i c).val else 0

end Handoff
end D7Odd
