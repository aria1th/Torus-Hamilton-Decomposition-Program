import Shared.ReturnLift

namespace Shared

abbrev TorusVertex (d m : Nat) := Fin d → ZMod m

abbrev TorusDirection (d : Nat) := Fin d

abbrev TorusColor (d : Nat) := Fin d

def torusBasis (d m : Nat) (i : TorusDirection d) : TorusVertex d m :=
  fun j => if j = i then 1 else 0

def cayleyColorStep {d m : Nat}
    (colorDir : TorusColor d → TorusVertex d m → TorusDirection d)
    (c : TorusColor d) : TorusVertex d m → TorusVertex d m :=
  fun x => x + torusBasis d m (colorDir c x)

def IsCayleyEdgePartition {d m : Nat}
    (colorDir : TorusColor d → TorusVertex d m → TorusDirection d) : Prop :=
  ∀ x : TorusVertex d m, ∀ i : TorusDirection d,
    ∃! c : TorusColor d, colorDir c x = i

def IsCayleyColorHamiltonian {d m : Nat}
    (colorDir : TorusColor d → TorusVertex d m → TorusDirection d) : Prop :=
  ∀ c : TorusColor d, IsSingleCycleMap (cayleyColorStep colorDir c)

structure CayleyDecomposition (d m : Nat) where
  colorDir : TorusColor d → TorusVertex d m → TorusDirection d
  edgePartition : IsCayleyEdgePartition colorDir
  colorHamiltonian : IsCayleyColorHamiltonian colorDir

def CayleyHamiltonDecomposition (d m : Nat) : Prop :=
  Nonempty (CayleyDecomposition d m)

def TorusHamiltonDecomposition (d m : Nat) : Prop :=
  CayleyHamiltonDecomposition d m

theorem torusHamiltonDecomposition_iff_cayley
    {d m : Nat} :
    TorusHamiltonDecomposition d m ↔ CayleyHamiltonDecomposition d m := by
  rfl

end Shared
