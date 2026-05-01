import D5Odd.Matching
import D7Odd.Handoff.Additive4Plus2

namespace D7Odd
namespace Handoff
namespace Additive4Plus2

def d5BaseZeroSetDirection {m : Nat}
    (base : D5Odd.ARoot5 m) (slot : D5Odd.Color) :
    D5Odd.Direction :=
  D5Odd.Lambda1 (D5Odd.zeroMaskMinusOne base.1) slot

def d5BaseZeroSetStep {m : Nat}
    (slot : D5Odd.Color) (base : D5Odd.ARoot5 m) :
    D5Odd.ARoot5 m :=
  baseAddQ (d5BaseZeroSetDirection base slot) base

theorem d5BaseZeroSetDirection_rowLatin {m : Nat}
    (base : D5Odd.ARoot5 m) :
    Function.Bijective fun slot : D5Odd.Color =>
      d5BaseZeroSetDirection base slot := by
  exact D5Odd.Lambda1_latin (D5Odd.zeroMaskMinusOne base.1)

set_option linter.flexible false in
theorem baseAddQ_eq_add_q5 {m : Nat}
    (i : D5Odd.Direction) (w : D5Odd.ARoot5 m) :
    baseAddQ i w =
      ⟨w.1 + D5Odd.q5 m i, D5Odd.root5_add_q5 w.2 i⟩ := by
  apply Subtype.ext
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [baseAddQ, vec5OfPrefix, D5Odd.q5, D5Odd.e5]
  all_goals
    try rw [root5_sink_eq]
    ring

theorem d5BaseZeroSetStep_bijective {m : Nat} [NeZero m]
    (hm : 5 ≤ m) (slot : D5Odd.Color) :
    Function.Bijective (d5BaseZeroSetStep (m := m) slot) := by
  let t1 : Fin m := ⟨1, by omega⟩
  have h :=
    D5Odd.layerMap_bijective_of_exactCover
      (D5Odd.ge5Schedule_exact (m := m) hm) t1 slot
  convert h using 1
  funext base
  simp [d5BaseZeroSetStep, d5BaseZeroSetDirection, D5Odd.layerMap,
    D5Odd.ge5Schedule, D5Odd.ge5Dir, t1, baseAddQ_eq_add_q5]

end Additive4Plus2
end Handoff
end D7Odd
