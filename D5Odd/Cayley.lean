import D5Odd.Torus
import Shared.TorusCayley

namespace D5Odd

structure CayleyEdge5 (m : Nat) [NeZero m] where
  src : Vertex5 m
  dir : Direction
  dst : Vertex5 m
  hdst : dst = src + e5 m dir

def cayleyColorDir {m : Nat} [NeZero m] (F : LayerSchedule m) (c : Color)
    (x : Vertex5 m) : Direction :=
  F.dir (layerOf x) c (rootAtLayer x).1

def cayleyColorStep {m : Nat} [NeZero m] (F : LayerSchedule m) (c : Color)
    (x : Vertex5 m) : Vertex5 m :=
  x + e5 m (cayleyColorDir F c x)

def cayleyColorEdge {m : Nat} [NeZero m] (F : LayerSchedule m) (c : Color)
    (x : Vertex5 m) : CayleyEdge5 m where
  src := x
  dir := cayleyColorDir F c x
  dst := cayleyColorStep F c x
  hdst := rfl

theorem cayleyColorStep_eq_torusColorStep {m : Nat} [NeZero m]
    (F : LayerSchedule m) (c : Color) :
    cayleyColorStep F c = torusColorStep F c := by
  funext x
  rfl

def IsCayleyEdgePartition {m : Nat} [NeZero m] (F : LayerSchedule m) : Prop :=
  forall x : Vertex5 m, forall i : Direction, ∃! c : Color, cayleyColorDir F c x = i

def IsCayleyColorHamiltonian {m : Nat} [NeZero m] (F : LayerSchedule m) : Prop :=
  forall c : Color, IsSingleCycleMap (cayleyColorStep F c)

def CayleyHamiltonDecompositionD5 (m : Nat) [NeZero m] : Prop :=
  exists F : LayerSchedule m, IsCayleyEdgePartition F ∧ IsCayleyColorHamiltonian F

theorem cayleyColorDir_latin {m : Nat} [NeZero m]
    {F : LayerSchedule m} (hLatin : IsScheduleLatin F) (x : Vertex5 m) :
    Function.Bijective fun c : Color => cayleyColorDir F c x := by
  exact hLatin (layerOf x) (rootAtLayer x).1

theorem cayleyEdgePartition_of_latin {m : Nat} [NeZero m]
    {F : LayerSchedule m} (hLatin : IsScheduleLatin F) :
    IsCayleyEdgePartition F := by
  intro x i
  let f : Color -> Direction := fun c => cayleyColorDir F c x
  have hf : Function.Bijective f := cayleyColorDir_latin hLatin x
  rcases hf.2 i with ⟨c, hc⟩
  refine ⟨c, hc, ?_⟩
  intro c' hc'
  apply hf.1
  exact hc'.trans hc.symm

theorem cayleyColorHamiltonian_of_torus {m : Nat} [NeZero m]
    {F : LayerSchedule m}
    (hCycle : forall c : Color, IsSingleCycleMap (torusColorStep F c)) :
    IsCayleyColorHamiltonian F := by
  intro c
  simpa [cayleyColorStep_eq_torusColorStep F c] using hCycle c

theorem cayleyHamiltonDecomposition_of_torus {m : Nat} [NeZero m]
    (h : TorusHamiltonDecompositionD5 m) :
    CayleyHamiltonDecompositionD5 m := by
  rcases h with ⟨F, _hExact, hLatin, hCycle⟩
  exact ⟨F, cayleyEdgePartition_of_latin hLatin, cayleyColorHamiltonian_of_torus hCycle⟩

theorem sharedCayleyHamiltonDecomposition_of_cayley
    {m : Nat} [NeZero m] (h : CayleyHamiltonDecompositionD5 m) :
    Shared.CayleyHamiltonDecomposition 5 m := by
  rcases h with ⟨F, hEdge, hHam⟩
  refine ⟨{
    colorDir := fun c x => cayleyColorDir F c x
    edgePartition := ?_
    colorHamiltonian := ?_
  }⟩
  · intro x i
    exact hEdge x i
  · intro c
    simpa [Shared.IsSingleCycleMap, IsSingleCycleMap,
      Shared.cayleyColorStep, Shared.torusBasis, cayleyColorStep, e5]
      using hHam c

theorem D5_odd_cayley_unconditional {m : Nat} [NeZero m]
    (hodd : Odd m) (hm3 : 3 <= m) :
    CayleyHamiltonDecompositionD5 m := by
  exact cayleyHamiltonDecomposition_of_torus (D5_odd_torus_unconditional hodd hm3)

theorem D5_odd_shared_cayley_unconditional {m : Nat} [NeZero m]
    (hodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition 5 m := by
  exact sharedCayleyHamiltonDecomposition_of_cayley
    (D5_odd_cayley_unconditional hodd hm3)

end D5Odd
