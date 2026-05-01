import D7Odd.Basic

namespace D7Odd

inductive GateTag
  | C0
  | C5
  | S0
  | S3
deriving DecidableEq, Repr, Fintype

inductive Gate (m : Nat) [NeZero m]
  | C0 (a : ZMod m) (s : ZMod m) (hs : s ≠ 0)
  | C5 (a : ZMod m) (s : ZMod m) (hs : s ≠ 0)
  | S0 (a : ZMod m) (b : ZMod m)
  | S3 (a : ZMod m) (b : ZMod m)

namespace Gate

def tag {m : Nat} [NeZero m] : Gate m -> GateTag
  | C0 .. => .C0
  | C5 .. => .C5
  | S0 .. => .S0
  | S3 .. => .S3

def aCoord {m : Nat} [NeZero m] : Gate m -> ZMod m
  | C0 a .. => a
  | C5 a .. => a
  | S0 a _ => a
  | S3 a _ => a

end Gate

end D7Odd
