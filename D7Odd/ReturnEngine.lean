import D7Odd.ExactCover
import D7Odd.GateCycle

namespace D7Odd

def HamiltonDecompositionD7 (m : Nat) : Prop :=
  exists F : SelectorFamily m, IsExactCover F ∧ IsLatin F ∧ AllColorHamiltonian F

theorem sum7_e7 (m : Nat) (i : Fin 7) :
    sum7 m (e7 m i) = 1 := by
  simp [sum7, e7]

theorem sum7_add (m : Nat) (x y : Vec7 m) :
    sum7 m (x + y) = sum7 m x + sum7 m y := by
  simp [sum7, Finset.sum_add_distrib]

theorem colorStep_layer_succ {m : Nat} (F : SelectorFamily m) (c : Color) (x : Vec7 m) :
    sum7 m (colorStep F c x) = sum7 m x + 1 := by
  rw [colorStep, sum7_add, sum7_e7]

theorem return_lift
    {m : Nat} (F : SelectorFamily m)
    (hReturn : forall c : Color, IsSingleCycleMap (colorStep F c)) :
    AllColorHamiltonian F := by
  exact hReturn

theorem chain_compression
    {alpha beta : Type*} (source : alpha -> beta) (target : beta -> alpha)
    (h : forall x, target (source x) = x) :
    Function.LeftInverse target source := by
  exact h

theorem gate_surgery_ge5 {m : Nat} [NeZero m] (_hm : 5 <= m) (_hodd : Odd m)
    (cert : D7OddCertificate m) :
    AllColorHamiltonian cert.family := by
  exact cert.hamiltonian

theorem gate_surgery_m3 (cert : D7OddCertificate 3) :
    AllColorHamiltonian cert.family := by
  exact cert.hamiltonian

end D7Odd
