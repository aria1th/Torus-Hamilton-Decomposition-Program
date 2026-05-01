import D7Odd.Handoff.Additive4Plus2

namespace D7Odd
namespace Handoff
namespace Additive4Plus2

def d3OddSinkCoord {m : Nat} (layer : ZMod m) (fiber : ARoot3 m) :
    ZMod m :=
  fiber.1 2 + layer

def d3OddDirection {m : Nat}
    (layer : ZMod m) (fiber : ARoot3 m) (slot : Direction3) :
    Direction3 :=
  if slot = 0 then
    if layer = 0 ∧ d3OddSinkCoord layer fiber ≠ 0 then 1
    else if layer = 1 then 2
    else 0
  else if slot = 1 then
    if layer = 0 then 2
    else if layer = 1 ∧ d3OddSinkCoord layer fiber = 0 then 0
    else 1
  else
    if layer = 0 ∨ layer = 1 then
      if d3OddSinkCoord layer fiber = 0 then 1 else 0
    else 2

def d3OddStep {m : Nat}
    (layer : ZMod m) (slot : Direction3) (fiber : ARoot3 m) :
    ARoot3 m :=
  fiberAddQ (d3OddDirection layer fiber slot) fiber

theorem zmod_zero_ne_one_of_two_le {m : Nat} (hm : 2 ≤ m) :
    (0 : ZMod m) ≠ 1 := by
  intro h
  have hcast : ((1 : Nat) : ZMod m) = 0 := by
    simpa [eq_comm] using h
  have hdiv : m ∣ 1 := (ZMod.natCast_eq_zero_iff 1 m).mp hcast
  have hm1 : m = 1 := Nat.dvd_one.mp hdiv
  omega

set_option linter.flexible false in
set_option linter.style.nativeDecide false in
theorem d3OddDirection_rowLatin_of_zero_ne_one {m : Nat}
    (layer : ZMod m) (fiber : ARoot3 m)
    (h01 : (0 : ZMod m) ≠ 1) :
    Function.Bijective fun slot : Direction3 =>
      d3OddDirection layer fiber slot := by
  by_cases h0 : layer = 0
  · subst layer
    by_cases hk : (d3OddSinkCoord (m := m) (0 : ZMod m) fiber = 0)
    · simp [d3OddDirection, h01, hk]
      native_decide
    · simp [d3OddDirection, h01, hk]
      native_decide
  · by_cases h1 : layer = 1
    · subst layer
      by_cases hk : (d3OddSinkCoord (m := m) (1 : ZMod m) fiber = 0)
      · simp [d3OddDirection, h0, hk]
        native_decide
      · simp [d3OddDirection, h0, hk]
        native_decide
    · by_cases hk : d3OddSinkCoord layer fiber = 0
      · simp [d3OddDirection, h0, h1, hk]
        native_decide
      · simp [d3OddDirection, h0, h1, hk]
        native_decide

theorem d3OddDirection_rowLatin_of_two_le {m : Nat}
    (hm : 2 ≤ m) (layer : ZMod m) (fiber : ARoot3 m) :
    Function.Bijective fun slot : Direction3 =>
      d3OddDirection layer fiber slot :=
  d3OddDirection_rowLatin_of_zero_ne_one layer fiber
    (zmod_zero_ne_one_of_two_le hm)

end Additive4Plus2
end Handoff
end D7Odd
