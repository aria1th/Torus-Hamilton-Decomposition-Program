import D5Odd.ZeroSetTable
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

end Additive4Plus2
end Handoff
end D7Odd
