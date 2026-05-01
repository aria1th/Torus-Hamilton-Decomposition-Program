import D7Odd.Handoff.ReturnCriterion

namespace D7Odd
namespace Handoff
namespace PrimeRoot

structure PrimeDimension where
  p : Nat
  prime : Nat.Prime p

namespace PrimeDimension

def sink (D : PrimeDimension) : Fin D.p :=
  ⟨D.p - 1, by
    have hp : 0 < D.p := D.prime.pos
    omega⟩

abbrev Color (D : PrimeDimension) := Fin D.p

abbrev Direction (D : PrimeDimension) := Fin D.p

abbrev Vec (D : PrimeDimension) (m : Nat) := Fin D.p → ZMod m

def e (D : PrimeDimension) (m : Nat) (i : D.Direction) : D.Vec m :=
  fun j => if j = i then 1 else 0

def q (D : PrimeDimension) (m : Nat) (i : D.Direction) : D.Vec m :=
  D.e m i - D.e m D.sink

def sum (D : PrimeDimension) (m : Nat) (w : D.Vec m) : ZMod m :=
  Finset.univ.sum fun i : Fin D.p => w i

def Root (D : PrimeDimension) (m : Nat) (w : D.Vec m) : Prop :=
  D.sum m w = 0

abbrev RootState (D : PrimeDimension) (m : Nat) :=
  {w : D.Vec m // D.Root m w}

abbrev Prefix (D : PrimeDimension) (m : Nat) :=
  Fin (D.p - 1) → ZMod m

abbrev Rho (D : PrimeDimension) :=
  {r : Fin D.p // 1 ≤ r.val}

def zero (D : PrimeDimension) : Fin D.p :=
  ⟨0, D.prime.pos⟩

def one (D : PrimeDimension) : Fin D.p :=
  ⟨1, D.prime.one_lt⟩

abbrev CanonSym (D : PrimeDimension) :=
  Fin D.p

def prefixLabelToDirection (D : PrimeDimension) (r : Fin D.p) : D.Direction :=
  ⟨D.p - 1 - r.val, by
    have hp : 0 < D.p := D.prime.pos
    omega⟩

def prefixLabelStep (D : PrimeDimension) {m : Nat}
    (r : Fin D.p) (z : D.Prefix m) : D.Prefix m :=
  fun k => z k - if k.val < r.val then 1 else 0

def prefixLabelUnstep (D : PrimeDimension) {m : Nat}
    (r : Fin D.p) (z : D.Prefix m) : D.Prefix m :=
  fun k => z k + if k.val < r.val then 1 else 0

def canonicalPrefixLabelOfRho (D : PrimeDimension)
    (rho : D.Rho) (sym : D.CanonSym) : Fin D.p :=
  if sym = D.zero then D.zero
  else if sym = D.one then rho.1
  else if rho.1.val < sym.val then sym
  else ⟨sym.val - 1, by
    have hs : sym.val < D.p := sym.isLt
    omega⟩

def canonicalDirOfRho (D : PrimeDimension)
    (rho : D.Rho) (sym : D.CanonSym) : D.Direction :=
  D.prefixLabelToDirection (D.canonicalPrefixLabelOfRho rho sym)

def seven : PrimeDimension where
  p := 7
  prime := by norm_num

@[simp] theorem seven_p : seven.p = 7 := rfl

@[simp] theorem seven_sink_val : seven.sink.val = 6 := rfl

@[simp] theorem seven_zero : seven.zero = (0 : Fin 7) := rfl

@[simp] theorem seven_one : seven.one = (1 : Fin 7) := rfl

@[simp] theorem e_seven (m : Nat) (i : Fin 7) :
    seven.e m i = e7 m i := by
  rfl

theorem q_seven (m : Nat) (i : Fin 7) :
    seven.q m i = q7 m i := by
  ext j
  change
    (if j = i then (1 : ZMod m) else 0) -
        (if j = (6 : Fin 7) then (1 : ZMod m) else 0) =
      (if j = i then (1 : ZMod m) else 0) -
        (if j = (6 : Fin 7) then (1 : ZMod m) else 0)
  rfl

@[simp] theorem sum_seven (m : Nat) (w : Vec7 m) :
    seven.sum m w = sum7 m w := by
  rfl

@[simp] theorem root_seven (m : Nat) (w : Vec7 m) :
    seven.Root m w ↔ Root7 m w := by
  rfl

def rootStateSevenEquiv (m : Nat) :
    seven.RootState m ≃ RootState7 m where
  toFun w := ⟨w.1, by
    simpa [Root, Root7] using w.2⟩
  invFun w := ⟨w.1, by
    simpa [Root, Root7] using w.2⟩
  left_inv := by
    intro w
    rfl
  right_inv := by
    intro w
    rfl

def prefixSevenEquiv (m : Nat) :
    seven.Prefix m ≃ (Fin 6 → ZMod m) :=
  Equiv.refl _

def rhoSevenEquiv :
    seven.Rho ≃ {r : Fin 7 // 1 ≤ r.val} where
  toFun r := ⟨r.1, r.2⟩
  invFun r := ⟨r.1, r.2⟩
  left_inv := by
    intro r
    rfl
  right_inv := by
    intro r
    rfl

theorem prefixLabelToDirection_seven (r : Fin 7) :
    seven.prefixLabelToDirection r =
      (⟨6 - r.val, by
        have hr : r.val < 7 := r.isLt
        omega⟩ : Fin 7) := by
  apply Fin.ext
  simp [prefixLabelToDirection, seven]

theorem prefixLabelStep_seven {m : Nat}
    (r : Fin 7) (z : seven.Prefix m) :
    seven.prefixLabelStep r z =
      fun k : Fin 6 => z k - if k.val < r.val then 1 else 0 := by
  rfl

theorem prefixLabelUnstep_seven {m : Nat}
    (r : Fin 7) (z : seven.Prefix m) :
    seven.prefixLabelUnstep r z =
      fun k : Fin 6 => z k + if k.val < r.val then 1 else 0 := by
  rfl

end PrimeDimension

end PrimeRoot
end Handoff
end D7Odd
