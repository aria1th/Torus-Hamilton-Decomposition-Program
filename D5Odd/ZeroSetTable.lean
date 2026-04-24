import D5Odd.Basic

namespace D5Odd

abbrev Mask5 := Fin 5 -> Bool

def mask5 (b0 b1 b2 b3 b4 : Bool) : Mask5 :=
  ![b0, b1, b2, b3, b4]

def row5 (d0 d1 d2 d3 d4 : Direction) : Color -> Direction :=
  ![d0, d1, d2, d3, d4]

def zeroMask {m : Nat} (w : Vec5 m) : Mask5 :=
  fun i => decide (w i = 0)

def zeroMaskMinusOne {m : Nat} (w : Vec5 m) : Mask5 :=
  fun i => zeroMask w (fin5AddNat i 1)

def Lambda1 (S : Mask5) : Color -> Direction :=
  if S = mask5 false false false false false then row5 0 1 2 3 4 else
  if S = mask5 true false false false false then row5 0 1 3 2 4 else
  if S = mask5 false true false false false then row5 0 1 2 4 3 else
  if S = mask5 true true false false false then row5 4 1 3 2 0 else
  if S = mask5 false false true false false then row5 4 1 2 3 0 else
  if S = mask5 true false true false false then row5 4 1 3 0 2 else
  if S = mask5 false true true false false then row5 1 0 2 4 3 else
  if S = mask5 true true true false false then row5 1 0 3 4 2 else
  if S = mask5 false false false true false then row5 1 0 2 3 4 else
  if S = mask5 true false false true false then row5 1 3 0 2 4 else
  if S = mask5 false true false true false then row5 3 0 2 4 1 else
  if S = mask5 true true false true false then row5 4 3 0 2 1 else
  if S = mask5 false false true true false then row5 4 2 1 3 0 else
  if S = mask5 true false true true false then row5 4 3 1 0 2 else
  if S = mask5 false true true true false then row5 3 2 1 4 0 else
  if S = mask5 true true true true false then row5 0 1 2 3 4 else
  if S = mask5 false false false false true then row5 0 2 1 3 4 else
  if S = mask5 true false false false true then row5 0 2 1 4 3 else
  if S = mask5 false true false false true then row5 0 2 4 1 3 else
  if S = mask5 true true false false true then row5 4 2 3 1 0 else
  if S = mask5 false false true false true then row5 2 4 1 3 0 else
  if S = mask5 true false true false true then row5 2 4 1 0 3 else
  if S = mask5 false true true false true then row5 2 0 4 1 3 else
  if S = mask5 true true true false true then row5 0 1 2 3 4 else
  if S = mask5 false false false true true then row5 1 0 3 2 4 else
  if S = mask5 true false false true true then row5 1 2 0 4 3 else
  if S = mask5 false true false true true then row5 3 0 4 2 1 else
  if S = mask5 true true false true true then row5 0 1 2 3 4 else
  if S = mask5 false false true true true then row5 1 4 3 2 0 else
  if S = mask5 true false true true true then row5 0 1 2 3 4 else
  if S = mask5 false true true true true then row5 0 1 2 3 4 else
  row5 0 1 2 3 4

def p5 {m : Nat} (w : Vec5 m) : Direction :=
  Lambda1 (zeroMaskMinusOne w) 0

set_option linter.style.nativeDecide false in
theorem Lambda1_latin : ∀ S : Mask5, Function.Bijective (Lambda1 S) := by
  native_decide

end D5Odd
