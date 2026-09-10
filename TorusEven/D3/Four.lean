-- STATUS: main-path (finite leaf D_3(4) from the Park3 Appendix D table; kernel `decide`)
import Shared.TorusCayley
import Shared.RankCycle
import TorusEven.Goals

/-!
# `D_3(4)`: the finite witness

The direction table is Appendix D of arXiv:2603.24708 (rows `j`, columns `k`, word `d0 d1 d2`).
`rank c` records the position of each vertex on the colour-`c` cycle through the origin.
Both facts are checked by kernel `decide` over the 64 vertices.
-/

namespace TorusEven
namespace D3Four

/-- Vertex index `16 i + 4 j + k`. -/
def idx (x : Shared.TorusVertex 3 4) : Nat :=
  16 * (x 0).val + 4 * (x 1).val + (x 2).val

def dir0Data : Array Nat := #[2, 0, 1, 0, 2, 0, 1, 2, 1, 0, 2, 2, 2, 2, 2, 1, 1, 2, 1, 2, 1, 0, 2, 0, 0, 2, 2, 1, 2, 2, 0, 2, 0, 2, 2, 0, 0, 2, 1, 2, 2, 1, 2, 1, 1, 1, 0, 2, 0, 2, 0, 1, 2, 2, 1, 0, 2, 0, 2, 2, 2, 1, 2, 2]

def dir1Data : Array Nat := #[1, 1, 2, 2, 0, 2, 2, 1, 2, 1, 0, 1, 0, 0, 1, 0, 2, 1, 2, 1, 0, 2, 0, 1, 2, 0, 1, 2, 1, 0, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 1, 2, 1, 0, 0, 0, 1, 1, 2, 0, 1, 2, 1, 1, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1]

def dir2Data : Array Nat := #[0, 2, 0, 1, 1, 1, 0, 0, 0, 2, 1, 0, 1, 1, 0, 2, 0, 0, 0, 0, 2, 1, 1, 2, 1, 1, 0, 0, 0, 1, 2, 1, 1, 0, 1, 1, 2, 1, 0, 0, 0, 0, 0, 2, 2, 2, 2, 0, 1, 1, 2, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0]

def rank0Data : Array Nat := #[0, 1, 30, 39, 53, 54, 31, 52, 34, 15, 32, 33, 35, 36, 37, 38, 41, 2, 3, 40, 42, 55, 4, 5, 43, 16, 17, 18, 20, 21, 22, 19, 62, 47, 48, 49, 7, 56, 57, 6, 44, 45, 58, 59, 61, 46, 23, 60, 63, 28, 29, 50, 8, 9, 10, 51, 13, 14, 11, 12, 26, 27, 24, 25]

def rank1Data : Array Nat := #[0, 21, 62, 63, 1, 22, 23, 24, 54, 55, 36, 25, 7, 56, 61, 26, 9, 10, 39, 40, 2, 11, 12, 41, 43, 44, 37, 42, 8, 57, 38, 27, 30, 31, 48, 29, 3, 32, 13, 14, 4, 45, 46, 15, 5, 58, 47, 28, 19, 20, 49, 18, 52, 33, 50, 51, 53, 34, 35, 16, 6, 59, 60, 17]

def rank2Data : Array Nat := #[0, 9, 10, 23, 53, 34, 15, 24, 54, 35, 36, 45, 63, 8, 37, 62, 1, 30, 11, 40, 26, 27, 16, 25, 55, 28, 17, 46, 56, 29, 38, 39, 2, 31, 12, 41, 3, 4, 13, 42, 48, 5, 18, 47, 57, 58, 59, 60, 51, 32, 21, 22, 52, 33, 14, 43, 49, 6, 19, 44, 50, 7, 20, 61]

def dirData : Fin 3 → Array Nat
  | 0 => dir0Data
  | 1 => dir1Data
  | 2 => dir2Data

def rankData : Fin 3 → Array Nat
  | 0 => rank0Data
  | 1 => rank1Data
  | 2 => rank2Data

def colorDir (c : Fin 3) (x : Shared.TorusVertex 3 4) : Fin 3 :=
  ⟨(dirData c).getD (idx x) 0 % 3, Nat.mod_lt _ (by decide)⟩

def rank (c : Fin 3) (x : Shared.TorusVertex 3 4) : ZMod 64 :=
  ((rankData c).getD (idx x) 0 : ZMod 64)

set_option maxRecDepth 100000 in
theorem rowLatin : ∀ x : Shared.TorusVertex 3 4, Function.Bijective (fun c => colorDir c x) := by
  decide

set_option maxRecDepth 100000 in
theorem rank_bijective : ∀ c : Fin 3, Function.Bijective (rank c) := by
  decide

set_option maxRecDepth 100000 in
theorem rank_step :
    ∀ c : Fin 3, ∀ x : Shared.TorusVertex 3 4,
      rank c (Shared.cayleyColorStep colorDir c x) = rank c x + 1 := by
  decide

theorem edgePartition : Shared.IsCayleyEdgePartition colorDir := by
  intro x i
  rcases (rowLatin x).2 i with ⟨c, hc⟩
  refine ⟨c, hc, ?_⟩
  intro c' hc'
  exact (rowLatin x).1 (hc'.trans hc.symm)

theorem colorHamiltonian : Shared.IsCayleyColorHamiltonian colorDir := by
  intro c
  exact Shared.single_cycle_of_zmod_rank _ (rank c) (rank_bijective c) (rank_step c)

end D3Four

/-- `D_3(4)` has a Hamilton decomposition. -/
theorem d3_even_four : Solved 3 4 :=
  ⟨{ colorDir := D3Four.colorDir
     edgePartition := D3Four.edgePartition
     colorHamiltonian := D3Four.colorHamiltonian }⟩

end TorusEven
