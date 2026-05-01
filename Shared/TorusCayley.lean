import Shared.ReturnLift

namespace Shared

abbrev TorusVertex (d m : Nat) := Fin d → ZMod m

abbrev TorusDirection (d : Nat) := Fin d

abbrev TorusColor (d : Nat) := Fin d

def torusBasis (d m : Nat) (i : TorusDirection d) : TorusVertex d m :=
  fun j => if j = i then 1 else 0

def blockIndexEquiv (a b : Nat) : Fin b × Fin a ≃ Fin (a * b) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm b a))

def torusVertexBlockEquiv (a b m : Nat) :
    TorusVertex (a * b) m ≃ (Fin b → TorusVertex a m) where
  toFun x := fun j i => x (blockIndexEquiv a b (j, i))
  invFun y := fun k =>
    y ((blockIndexEquiv a b).symm k).1 ((blockIndexEquiv a b).symm k).2
  left_inv := by
    intro x
    funext k
    simp
  right_inv := by
    intro y
    funext j i
    simp

theorem torusVertexBlockEquiv_apply
    {a b m : Nat} (x : TorusVertex (a * b) m)
    (j : Fin b) (i : Fin a) :
    torusVertexBlockEquiv a b m x j i =
      x (blockIndexEquiv a b (j, i)) := by
  rfl

theorem torusVertexBlockEquiv_symm_apply
    {a b m : Nat} (y : Fin b → TorusVertex a m)
    (k : Fin (a * b)) :
    (torusVertexBlockEquiv a b m).symm y k =
      y ((blockIndexEquiv a b).symm k).1
        ((blockIndexEquiv a b).symm k).2 := by
  rfl

theorem card_torusVertex (d m : Nat) [NeZero m] :
    Fintype.card (TorusVertex d m) = m ^ d := by
  calc
    Fintype.card (TorusVertex d m) = Fintype.card (ZMod m) ^ d := by
      simp [TorusVertex]
    _ = m ^ d := by
      rw [ZMod.card m]

theorem torusVertexBlockEquiv_torusBasis_apply
    {a b m : Nat} (j j' : Fin b) (i i' : Fin a) :
    torusVertexBlockEquiv a b m
        (torusBasis (a * b) m (blockIndexEquiv a b (j, i))) j' i' =
      if j' = j ∧ i' = i then 1 else 0 := by
  by_cases h : j' = j ∧ i' = i
  · rcases h with ⟨rfl, rfl⟩
    simp [torusVertexBlockEquiv_apply, torusBasis]
  · have hne : blockIndexEquiv a b (j', i') ≠ blockIndexEquiv a b (j, i) := by
      intro heq
      exact h <| Prod.ext_iff.1 ((blockIndexEquiv a b).injective heq)
    simp [torusVertexBlockEquiv_apply, torusBasis, h, hne]

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
