import Mathlib

namespace D5Odd

abbrev Z (m : Nat) := ZMod m

abbrev Vec5 (m : Nat) := Fin 5 -> ZMod m

abbrev Color := Fin 5

abbrev Direction := Fin 5

def e5 (m : Nat) (i : Fin 5) : Vec5 m :=
  fun j => if j = i then 1 else 0

def q5 (m : Nat) (i : Fin 5) : Vec5 m :=
  e5 m i - e5 m 4

def sum5 (m : Nat) (w : Vec5 m) : ZMod m :=
  Finset.univ.sum fun i : Fin 5 => w i

def Root5 (m : Nat) (w : Vec5 m) : Prop :=
  sum5 m w = 0

abbrev ARoot5 (m : Nat) := { w : Vec5 m // Root5 m w }

def fin5AddNat (i : Fin 5) (k : Nat) : Fin 5 :=
  ⟨(i.val + k) % 5, Nat.mod_lt _ (by decide)⟩

@[simp] theorem fin5AddNat_zero (i : Fin 5) :
    fin5AddNat i 0 = i := by
  ext
  simp [fin5AddNat]

set_option linter.style.nativeDecide false in
theorem fin5AddNat_three_bijective : Function.Bijective fun c : Color => fin5AddNat c 3 := by
  native_decide

set_option linter.style.nativeDecide false in
theorem fin5AddNat_four_bijective : Function.Bijective fun c : Color => fin5AddNat c 4 := by
  native_decide

theorem sum5_e5 (m : Nat) (i : Fin 5) :
    sum5 m (e5 m i) = 1 := by
  simp [sum5, e5]

theorem sum5_add (m : Nat) (x y : Vec5 m) :
    sum5 m (x + y) = sum5 m x + sum5 m y := by
  simp [sum5, Finset.sum_add_distrib]

theorem sum5_q5 (m : Nat) (i : Fin 5) :
    sum5 m (q5 m i) = 0 := by
  calc
    sum5 m (q5 m i) = sum5 m (e5 m i) - sum5 m (e5 m 4) := by
      simp [q5, sum5, Pi.sub_apply, Finset.sum_sub_distrib]
    _ = 0 := by
      rw [sum5_e5, sum5_e5]
      simp

theorem root5_add_q5 {m : Nat} {w : Vec5 m} (hw : Root5 m w) (i : Fin 5) :
    Root5 m (w + q5 m i) := by
  unfold Root5 at hw ⊢
  rw [sum5_add, hw, sum5_q5]
  simp

theorem root5_sub_q5 {m : Nat} {w : Vec5 m} (hw : Root5 m w) (i : Fin 5) :
    Root5 m (w - q5 m i) := by
  unfold Root5 at hw ⊢
  rw [sub_eq_add_neg, sum5_add, hw]
  have hq : sum5 m (-q5 m i) = 0 := by
    calc
      sum5 m (-q5 m i) = -sum5 m (q5 m i) := by
        simp [sum5, Finset.sum_neg_distrib]
      _ = 0 := by
        rw [sum5_q5]
        simp
  simpa using hq

end D5Odd
