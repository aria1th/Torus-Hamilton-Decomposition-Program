import D7Odd.Basic

namespace D7Odd

inductive Stage
  | R1a | R1b
  | R2a | R2b
  | R3a | R3b | R3c
  | R4a | R4b | R4c
  | R4pa | R4pb
deriving DecidableEq, Repr, Fintype

namespace Stage

def tau : Stage -> Nat
  | .R1b | .R3a | .R3b | .R3c | .R4a => 0
  | .R1a | .R4pa | .R4pb => 1
  | .R4b | .R4c => 2
  | .R2a | .R2b => 3

def tauZ (m : Nat) (s : Stage) : ZMod m :=
  (tau s : ZMod m)

theorem tau_lt_four (s : Stage) : tau s < 4 := by
  cases s <;> decide

theorem tau_lt_of_ge5 (hm : 5 <= m) (s : Stage) : tau s < m :=
  lt_of_lt_of_le (tau_lt_four s) (by omega)

theorem tauZ_inj_of_ge5 (hm : 5 <= m) {s t : Stage}
    (h : tauZ m s = tauZ m t) : tau s = tau t := by
  exact ((ZMod.natCast_eq_natCast_iff (tau s) (tau t) m).1 h).eq_of_lt_of_lt
    (tau_lt_of_ge5 hm s) (tau_lt_of_ge5 hm t)

end Stage

def R1aCell (m : Nat) (w : Vec7 m) : Prop :=
  exists a s u : ZMod m,
    s ≠ 0 /\ (-a - s - u) ≠ 0 /\
    w 0 = 0 /\
    w 1 = a /\
    w 2 = 0 /\
    w 3 = -a - s - u /\
    w 4 = 0 /\
    w 5 = s /\
    w 6 = u

def R1bCell (m : Nat) (w : Vec7 m) : Prop :=
  exists a s u : ZMod m,
    s ≠ 0 /\ (s - u) ≠ 0 /\
    w 0 = 0 /\
    w 1 = a /\
    w 2 = 0 /\
    w 3 = u /\
    w 4 = 0 /\
    w 5 = s - u /\
    w 6 = -a - s

def R2aCell (m : Nat) (w : Vec7 m) : Prop :=
  exists a s u : ZMod m,
    s ≠ 0 /\ (-a - s - u) ≠ 0 /\
    w 0 = 0 /\
    w 1 = a /\
    w 2 = 0 /\
    w 3 = s /\
    w 4 = 0 /\
    w 5 = u /\
    w 6 = -a - s - u

def R2bCell (m : Nat) (w : Vec7 m) : Prop :=
  exists a s : ZMod m,
    s ≠ 0 /\
    w 0 = 0 /\
    w 1 = a /\
    w 2 = 0 /\
    w 3 = s /\
    w 4 = 0 /\
    w 5 = -a - s /\
    w 6 = 0

def R3aCell (m : Nat) (w : Vec7 m) : Prop :=
  exists a b u : ZMod m,
    (b - u) ≠ 0 /\
    w 0 = 0 /\
    w 1 = a /\
    w 2 = -1 /\
    w 3 = b - u /\
    w 4 = u /\
    w 5 = 1 - a - b /\
    w 6 = 0

def R3bCell (m : Nat) (w : Vec7 m) : Prop :=
  exists a b u : ZMod m,
    u ≠ 0 /\
    w 0 = 0 /\
    w 1 = a /\
    w 2 = -1 /\
    w 3 = 0 /\
    w 4 = b /\
    w 5 = u /\
    w 6 = 1 - a - b - u

def R3cCell (m : Nat) (w : Vec7 m) : Prop :=
  exists a b : ZMod m,
    w 0 = 0 /\
    w 1 = a /\
    w 2 = -1 /\
    w 3 = 0 /\
    w 4 = b /\
    w 5 = 0 /\
    w 6 = 1 - a - b

def R4aCell (m : Nat) (w : Vec7 m) : Prop :=
  exists a b u : ZMod m,
    b ≠ 0 /\ (b - u) ≠ 0 /\
    w 0 = 0 /\
    w 1 = a /\
    w 2 = 0 /\
    w 3 = 0 /\
    w 4 = b - u /\
    w 5 = -1 + u /\
    w 6 = 1 - a - b

def R4bCell (m : Nat) (w : Vec7 m) : Prop :=
  exists a b u : ZMod m,
    b ≠ 0 /\ (1 - a - b - u) ≠ 0 /\
    w 0 = 0 /\
    w 1 = a /\
    w 2 = 0 /\
    w 3 = u /\
    w 4 = 0 /\
    w 5 = b - 1 /\
    w 6 = 1 - a - b - u

def R4cCell (m : Nat) (w : Vec7 m) : Prop :=
  exists a b : ZMod m,
    b ≠ 0 /\
    w 0 = 0 /\
    w 1 = a /\
    w 2 = 0 /\
    w 3 = 1 - a - b /\
    w 4 = 0 /\
    w 5 = b - 1 /\
    w 6 = 0

def R4paCell (m : Nat) (w : Vec7 m) : Prop :=
  exists a u : ZMod m,
    (1 - a - u) ≠ 0 /\
    w 0 = 0 /\
    w 1 = a /\
    w 2 = 0 /\
    w 3 = 0 /\
    w 4 = 0 /\
    w 5 = u - 1 /\
    w 6 = 1 - a - u

def R4pbCell (m : Nat) (w : Vec7 m) : Prop :=
  exists a : ZMod m,
    w 0 = 0 /\
    w 1 = a /\
    w 2 = 0 /\
    w 3 = 0 /\
    w 4 = 0 /\
    w 5 = -a /\
    w 6 = 0

def stageCell (m : Nat) (s : Stage) : Vec7 m -> Prop :=
  match s with
  | .R1a => R1aCell m
  | .R1b => R1bCell m
  | .R2a => R2aCell m
  | .R2b => R2bCell m
  | .R3a => R3aCell m
  | .R3b => R3bCell m
  | .R3c => R3cCell m
  | .R4a => R4aCell m
  | .R4b => R4bCell m
  | .R4c => R4cCell m
  | .R4pa => R4paCell m
  | .R4pb => R4pbCell m

theorem rawCell_w0_zero {m : Nat} {s : Stage} {w : Vec7 m}
    (h : stageCell m s w) : w 0 = 0 := by
  cases s <;>
    simp [stageCell, R1aCell, R1bCell, R2aCell, R2bCell, R3aCell, R3bCell,
      R3cCell, R4aCell, R4bCell, R4cCell, R4paCell, R4pbCell] at h <;>
    aesop

theorem R1a_w3_ne {m : Nat} {w : Vec7 m} (h : stageCell m .R1a w) :
    w 3 ≠ 0 := by
  simp [stageCell, R1aCell] at h
  aesop

theorem R1b_w2_zero {m : Nat} {w : Vec7 m} (h : stageCell m .R1b w) :
    w 2 = 0 := by
  simp [stageCell, R1bCell] at h
  aesop

theorem R1b_w4_zero {m : Nat} {w : Vec7 m} (h : stageCell m .R1b w) :
    w 4 = 0 := by
  simp [stageCell, R1bCell] at h
  aesop

theorem R2a_w6_ne {m : Nat} {w : Vec7 m} (h : stageCell m .R2a w) :
    w 6 ≠ 0 := by
  simp [stageCell, R2aCell] at h
  aesop

theorem R2b_w6_zero {m : Nat} {w : Vec7 m} (h : stageCell m .R2b w) :
    w 6 = 0 := by
  simp [stageCell, R2bCell] at h
  aesop

theorem R3a_w2_neg_one {m : Nat} {w : Vec7 m} (h : stageCell m .R3a w) :
    w 2 = -1 := by
  simp [stageCell, R3aCell] at h
  aesop

theorem R3a_w3_ne {m : Nat} {w : Vec7 m} (h : stageCell m .R3a w) :
    w 3 ≠ 0 := by
  simp [stageCell, R3aCell] at h
  aesop

theorem R3b_w2_neg_one {m : Nat} {w : Vec7 m} (h : stageCell m .R3b w) :
    w 2 = -1 := by
  simp [stageCell, R3bCell] at h
  aesop

theorem R3b_w3_zero {m : Nat} {w : Vec7 m} (h : stageCell m .R3b w) :
    w 3 = 0 := by
  simp [stageCell, R3bCell] at h
  aesop

theorem R3b_w5_ne {m : Nat} {w : Vec7 m} (h : stageCell m .R3b w) :
    w 5 ≠ 0 := by
  simp [stageCell, R3bCell] at h
  aesop

theorem R3c_w2_neg_one {m : Nat} {w : Vec7 m} (h : stageCell m .R3c w) :
    w 2 = -1 := by
  simp [stageCell, R3cCell] at h
  aesop

theorem R3c_w3_zero {m : Nat} {w : Vec7 m} (h : stageCell m .R3c w) :
    w 3 = 0 := by
  simp [stageCell, R3cCell] at h
  aesop

theorem R3c_w5_zero {m : Nat} {w : Vec7 m} (h : stageCell m .R3c w) :
    w 5 = 0 := by
  simp [stageCell, R3cCell] at h
  aesop

theorem R4a_w2_zero {m : Nat} {w : Vec7 m} (h : stageCell m .R4a w) :
    w 2 = 0 := by
  simp [stageCell, R4aCell] at h
  aesop

theorem R4a_w4_ne {m : Nat} {w : Vec7 m} (h : stageCell m .R4a w) :
    w 4 ≠ 0 := by
  simp [stageCell, R4aCell] at h
  aesop

theorem R4b_w6_ne {m : Nat} {w : Vec7 m} (h : stageCell m .R4b w) :
    w 6 ≠ 0 := by
  simp [stageCell, R4bCell] at h
  aesop

theorem R4c_w6_zero {m : Nat} {w : Vec7 m} (h : stageCell m .R4c w) :
    w 6 = 0 := by
  simp [stageCell, R4cCell] at h
  aesop

theorem R4pa_w3_zero {m : Nat} {w : Vec7 m} (h : stageCell m .R4pa w) :
    w 3 = 0 := by
  simp [stageCell, R4paCell] at h
  aesop

theorem R4pa_w6_ne {m : Nat} {w : Vec7 m} (h : stageCell m .R4pa w) :
    w 6 ≠ 0 := by
  simp [stageCell, R4paCell] at h
  aesop

theorem R4pb_w3_zero {m : Nat} {w : Vec7 m} (h : stageCell m .R4pb w) :
    w 3 = 0 := by
  simp [stageCell, R4pbCell] at h
  aesop

theorem R4pb_w6_zero {m : Nat} {w : Vec7 m} (h : stageCell m .R4pb w) :
    w 6 = 0 := by
  simp [stageCell, R4pbCell] at h
  aesop

end D7Odd
