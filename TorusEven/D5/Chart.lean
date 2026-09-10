-- STATUS: main-path (root-height chart: a RootFlatSchedule on (ZMod m)^n gives D_{n+1}(m))
import Shared.RootFlat
import Shared.TorusCayley
import Shared.Monodromy

/-!
# Root-height chart

Physical vertices of `D_{n+1}(m)` are `Fin (n+1) → ZMod m`.  With root `w : Fin n → ZMod m`
and height `t`, the chart `(t, w) ↦ (w, t - Σ w)` identifies `ZMod m × Root` with the vertex
set, and a step in direction `j` (`j < n`: add `e_j` to the root; `j = n`: fix the root) is
exactly a positive basis step of the torus that raises the height by one.  This is the
manuscript's root-height chart in general dimension.
-/

namespace TorusEven
namespace Chart

variable {n m : ℕ}

abbrev Root (n m : ℕ) := Fin n → ZMod m

/-- Direction `j` acting on the root: `e_j` for `j < n`, nothing for `j = n`. -/
def rootStep (n m : ℕ) (j : Fin (n + 1)) (w : Root n m) : Root n m :=
  fun i => w i + if (i.castSucc : Fin (n + 1)) = j then 1 else 0

def sumRoot (w : Root n m) : ZMod m := ∑ i, w i

def toVertex (z : ZMod m × Root n m) : Shared.TorusVertex (n + 1) m :=
  Fin.snoc z.2 (z.1 - sumRoot z.2)

def ofVertex (x : Shared.TorusVertex (n + 1) m) : ZMod m × Root n m :=
  (x (Fin.last n) + sumRoot (Fin.init x), Fin.init x)

theorem ofVertex_toVertex (z : ZMod m × Root n m) : ofVertex (toVertex z) = z := by
  rcases z with ⟨t, w⟩
  simp [toVertex, ofVertex, Fin.init_snoc, Fin.snoc_last]

theorem toVertex_ofVertex (x : Shared.TorusVertex (n + 1) m) : toVertex (ofVertex x) = x := by
  simp [toVertex, ofVertex, Fin.snoc_init_self]

def chart (n m : ℕ) : ZMod m × Root n m ≃ Shared.TorusVertex (n + 1) m where
  toFun := toVertex
  invFun := ofVertex
  left_inv := ofVertex_toVertex
  right_inv := toVertex_ofVertex

theorem sumRoot_rootStep (j : Fin (n + 1)) (w : Root n m) :
    sumRoot (rootStep n m j w) = sumRoot w + if j = Fin.last n then 0 else 1 := by
  unfold sumRoot rootStep
  rw [Finset.sum_add_distrib]
  congr 1
  refine Fin.lastCases ?_ (fun j' => ?_) j
  · simp [Fin.castSucc_ne_last]
  · simp [Fin.castSucc_inj, Fin.castSucc_ne_last]

theorem toVertex_step (t : ZMod m) (w : Root n m) (j : Fin (n + 1)) :
    toVertex (t + 1, rootStep n m j w) = toVertex (t, w) + Shared.torusBasis (n + 1) m j := by
  funext i
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · simp only [toVertex, Fin.snoc_last, Pi.add_apply, Shared.torusBasis, sumRoot_rootStep]
    split_ifs with h1 h2 h2
    · ring
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · ring
  · simp only [toVertex, Fin.snoc_castSucc, Pi.add_apply, Shared.torusBasis, rootStep]

/-! ### From a root-flat schedule to a Cayley decomposition -/

variable [NeZero m]

/-- The colour-`c` direction at a physical vertex. -/
def colorDir (S : Shared.RootFlatSchedule (Fin (n + 1)) (Fin (n + 1)) (Root n m) m)
    (c : Fin (n + 1)) (x : Shared.TorusVertex (n + 1) m) : Fin (n + 1) :=
  S.dir (ofVertex x).1 (ofVertex x).2 c

theorem colorStep_eq (S : Shared.RootFlatSchedule (Fin (n + 1)) (Fin (n + 1)) (Root n m) m)
    (hstep : S.step = rootStep n m) (c : Fin (n + 1)) (z : ZMod m × Root n m) :
    Shared.cayleyColorStep (colorDir S) c (toVertex z) = toVertex (S.fullStep c z) := by
  rcases z with ⟨t, w⟩
  simp only [Shared.cayleyColorStep, colorDir, ofVertex_toVertex,
    Shared.RootFlatSchedule.fullStep, Shared.RootFlatSchedule.layerMap, hstep]
  rw [toVertex_step]

theorem edgePartition (S : Shared.RootFlatSchedule (Fin (n + 1)) (Fin (n + 1)) (Root n m) m)
    (hRow : S.rowLatin) : Shared.IsCayleyEdgePartition (colorDir S) := by
  intro x i
  have hb := hRow (ofVertex x).1 (ofVertex x).2
  rcases hb.2 i with ⟨c, hc⟩
  refine ⟨c, hc, ?_⟩
  intro c' hc'
  exact hb.1 (hc'.trans hc.symm)

theorem colorHamiltonian (S : Shared.RootFlatSchedule (Fin (n + 1)) (Fin (n + 1)) (Root n m) m)
    (hstep : S.step = rootStep n m) (hLayer : S.layerBijective)
    (hRet : S.returnsSingleCycle) :
    Shared.IsCayleyColorHamiltonian (colorDir S) := by
  intro c
  refine Shared.single_cycle_of_equiv_conj (chart n m)
    (Shared.cayleyColorStep (colorDir S) c) (S.fullStep c)
    (S.fullStepsHamiltonian_of_return hLayer hRet c) ?_
  intro z
  show ofVertex (Shared.cayleyColorStep (colorDir S) c (toVertex z)) = S.fullStep c z
  rw [colorStep_eq S hstep, ofVertex_toVertex]

/-- A root-height schedule with Latin rows, bijective layers and single-cycle returns is a
Hamilton decomposition of `D_{n+1}(m)`. -/
theorem cayley_of_rootFlat
    (S : Shared.RootFlatSchedule (Fin (n + 1)) (Fin (n + 1)) (Root n m) m)
    (hstep : S.step = rootStep n m) (hRow : S.rowLatin) (hLayer : S.layerBijective)
    (hRet : S.returnsSingleCycle) :
    Shared.CayleyHamiltonDecomposition (n + 1) m :=
  ⟨{ colorDir := colorDir S
     edgePartition := edgePartition S hRow
     colorHamiltonian := colorHamiltonian S hstep hLayer hRet }⟩

end Chart
end TorusEven
