import D7Odd.Torus
import Shared.TorusCayley

namespace D7Odd

def IsCayleyEdgePartition {m : Nat} (F : SelectorFamily m) : Prop :=
  ∀ x : Vertex7 m, ∀ i : Direction, ∃! c : Color, F.dir c x = i

def IsCayleyColorHamiltonian {m : Nat} (F : SelectorFamily m) : Prop :=
  ∀ c : Color, IsSingleCycleMap (colorStep F c)

def CayleyHamiltonDecompositionD7 (m : Nat) : Prop :=
  ∃ F : SelectorFamily m, IsCayleyEdgePartition F ∧ IsCayleyColorHamiltonian F

theorem cayleyEdgePartition_of_latin {m : Nat}
    {F : SelectorFamily m} (hLatin : IsLatin F) :
    IsCayleyEdgePartition F := by
  intro x i
  let f : Color → Direction := fun c => F.dir c x
  have hf : Function.Bijective f := hLatin x
  rcases hf.2 i with ⟨c, hc⟩
  refine ⟨c, hc, ?_⟩
  intro c' hc'
  apply hf.1
  exact hc'.trans hc.symm

theorem cayleyColorHamiltonian_of_torus {m : Nat}
    {F : SelectorFamily m} (hCycle : AllColorHamiltonian F) :
    IsCayleyColorHamiltonian F := by
  intro c
  exact hCycle c

theorem cayleyHamiltonDecomposition_of_torus {m : Nat}
    (h : TorusHamiltonDecompositionD7 m) :
    CayleyHamiltonDecompositionD7 m := by
  rcases h with ⟨F, _hExact, hLatin, hCycle⟩
  exact ⟨F, cayleyEdgePartition_of_latin hLatin,
    cayleyColorHamiltonian_of_torus hCycle⟩

theorem sharedCayleyHamiltonDecomposition_of_cayley
    {m : Nat} (h : CayleyHamiltonDecompositionD7 m) :
    Shared.CayleyHamiltonDecomposition 7 m := by
  rcases h with ⟨F, hEdge, hHam⟩
  refine ⟨{
    colorDir := fun c x => F.dir c x
    edgePartition := ?_
    colorHamiltonian := ?_
  }⟩
  · intro x i
    exact hEdge x i
  · intro c
    simpa [Shared.IsSingleCycleMap, IsSingleCycleMap,
      Shared.cayleyColorStep, Shared.torusBasis, colorStep, e7]
      using hHam c

theorem D7_odd_cayley_unconditional {m : Nat} [NeZero m]
    (hodd : Odd m) (hm3 : 3 <= m) :
    CayleyHamiltonDecompositionD7 m := by
  exact cayleyHamiltonDecomposition_of_torus
    (D7_odd_torus_unconditional hodd hm3)

theorem D7_odd_shared_cayley_unconditional {m : Nat} [NeZero m]
    (hodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition 7 m := by
  exact sharedCayleyHamiltonDecomposition_of_cayley
    (D7_odd_cayley_unconditional hodd hm3)

theorem D7_odd_shared_cayley_uniform :
    ∀ {m : Nat}, 3 <= m → Odd m →
      Shared.CayleyHamiltonDecomposition 7 m := by
  intro m hm3 hodd
  haveI : NeZero m := ⟨by omega⟩
  exact D7_odd_shared_cayley_unconditional hodd hm3

end D7Odd
