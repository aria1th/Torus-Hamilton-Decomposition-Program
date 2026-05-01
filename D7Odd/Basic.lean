import Mathlib

namespace D7Odd

abbrev Z (m : Nat) := ZMod m

abbrev Vec7 (m : Nat) := Fin 7 -> ZMod m

def e7 (m : Nat) (i : Fin 7) : Vec7 m :=
  fun j => if j = i then 1 else 0

def q7 (m : Nat) (i : Fin 7) : Vec7 m :=
  e7 m i - e7 m 6

def sum7 (m : Nat) (w : Vec7 m) : ZMod m :=
  Finset.univ.sum fun i : Fin 7 => w i

def Root7 (m : Nat) (w : Vec7 m) : Prop :=
  sum7 m w = 0

def markerVec (m : Nat) (tau : ZMod m) : Vec7 m :=
  tau • (e7 m 0 - e7 m 1)

def markedCell (m : Nat) (cell : Vec7 m -> Prop) (tau : ZMod m) (w : Vec7 m) :
    Prop :=
  cell (w - markerVec m tau)

@[simp] theorem markerVec_zero (m : Nat) (tau : ZMod m) :
    markerVec m tau 0 = tau := by
  simp [markerVec, e7]

@[simp] theorem markerVec_one (m : Nat) (tau : ZMod m) :
    markerVec m tau 1 = -tau := by
  simp [markerVec, e7]

@[simp] theorem markerVec_two (m : Nat) (tau : ZMod m) :
    markerVec m tau 2 = 0 := by
  simp [markerVec, e7]

@[simp] theorem markerVec_three (m : Nat) (tau : ZMod m) :
    markerVec m tau 3 = 0 := by
  simp [markerVec, e7]

@[simp] theorem markerVec_four (m : Nat) (tau : ZMod m) :
    markerVec m tau 4 = 0 := by
  simp [markerVec, e7]

@[simp] theorem markerVec_five (m : Nat) (tau : ZMod m) :
    markerVec m tau 5 = 0 := by
  simp [markerVec, e7]

@[simp] theorem markerVec_six (m : Nat) (tau : ZMod m) :
    markerVec m tau 6 = 0 := by
  simp [markerVec, e7]

theorem zmod_natCast_ne_of_lt
    (_hm : 5 <= m) {a b : Nat} (ha : a < m) (hb : b < m) (hab : a ≠ b) :
    ((a : ZMod m) ≠ (b : ZMod m)) := by
  intro h
  exact hab <| ((ZMod.natCast_eq_natCast_iff a b m).1 h).eq_of_lt_of_lt ha hb

theorem zmod_natCast_ne_of_lt' {m a b : Nat} (ha : a < m) (hb : b < m)
    (hab : a ≠ b) :
    ((a : ZMod m) ≠ (b : ZMod m)) := by
  intro h
  exact hab <| ((ZMod.natCast_eq_natCast_iff a b m).1 h).eq_of_lt_of_lt ha hb

theorem zmod_neg_one_ne_zero_of_ge5 (hm : 5 <= m) [NeZero m] :
    (-1 : ZMod m) ≠ 0 := by
  intro h
  have h10 : (1 : ZMod m) = 0 := by
    simpa using congrArg Neg.neg h
  exact (zmod_natCast_ne_of_lt (m := m) hm (a := 0) (b := 1)
    (by omega) (by omega) (by omega)) (by simpa using h10.symm)

end D7Odd
