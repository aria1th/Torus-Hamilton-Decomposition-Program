import D7Odd.Handoff.SmallRootFlat

namespace D7Odd
namespace Handoff

def stateIndexNat (m : Nat) (x : Fin 6 → ZMod m) : Nat :=
  (((((x 0).val * m + (x 1).val) * m + (x 2).val) * m + (x 3).val) * m +
      (x 4).val) * m + (x 5).val

def stateIndex3 (x : Fin 6 → ZMod 3) : Fin 729 :=
  ⟨stateIndexNat 3 x % 729, Nat.mod_lt _ (by decide)⟩

def stateIndex5 (x : Fin 6 → ZMod 5) : Fin 15625 :=
  ⟨stateIndexNat 5 x % 15625, Nat.mod_lt _ (by decide)⟩

def indexToSix3 (i : Fin 729) : Fin 6 → ZMod 3 :=
  fun j => ((i.val / 3 ^ (5 - j.val)) % 3 : Nat)

def indexToSix5 (i : Fin 15625) : Fin 6 → ZMod 5 :=
  fun j => ((i.val / 5 ^ (5 - j.val)) % 5 : Nat)

set_option maxHeartbeats 2000000 in
-- Native evaluation checks all `3^6` states for the base-3 index codec.
set_option linter.style.nativeDecide false in
theorem indexToSix3_stateIndex3 :
    ∀ x : Fin 6 → ZMod 3, indexToSix3 (stateIndex3 x) = x := by
  native_decide

set_option maxHeartbeats 2000000 in
-- Native evaluation checks all `3^6` indices for the base-3 index codec.
set_option linter.style.nativeDecide false in
theorem stateIndex3_indexToSix3 :
    ∀ i : Fin 729, stateIndex3 (indexToSix3 i) = i := by
  native_decide

set_option maxHeartbeats 5000000 in
-- Native evaluation checks all `5^6` states for the base-5 index codec.
set_option linter.style.nativeDecide false in
theorem indexToSix5_stateIndex5 :
    ∀ x : Fin 6 → ZMod 5, indexToSix5 (stateIndex5 x) = x := by
  native_decide

set_option maxHeartbeats 5000000 in
-- Native evaluation checks all `5^6` indices for the base-5 index codec.
set_option linter.style.nativeDecide false in
theorem stateIndex5_indexToSix5 :
    ∀ i : Fin 15625, stateIndex5 (indexToSix5 i) = i := by
  native_decide

theorem stateIndex3_bijective : Function.Bijective stateIndex3 :=
  bijective_of_inverse stateIndex3 indexToSix3
    indexToSix3_stateIndex3 stateIndex3_indexToSix3

theorem stateIndex5_bijective : Function.Bijective stateIndex5 :=
  bijective_of_inverse stateIndex5 indexToSix5
    indexToSix5_stateIndex5 stateIndex5_indexToSix5

theorem indexToSix3_bijective : Function.Bijective indexToSix3 :=
  bijective_of_inverse indexToSix3 stateIndex3
    stateIndex3_indexToSix3 indexToSix3_stateIndex3

theorem indexToSix5_bijective : Function.Bijective indexToSix5 :=
  bijective_of_inverse indexToSix5 stateIndex5
    stateIndex5_indexToSix5 indexToSix5_stateIndex5

end Handoff
end D7Odd
