-- STATUS: main-path
import TorusEven.Entry.Seed.Components

namespace TorusEven.Entry.Seed

open Collar Incidence

abbrev NumericColor (p : ℕ) := Fin (4 + 2 * p)

def numericSupport (p : ℕ) (hp : 2 ≤ p) (j : Fin 3) (hw : Fin 4 × Fin 4) :
    Finset (NumericColor p) :=
  (supportNat p hp j hw.1.val hw.2.val).map finSumFinEquiv.toEmbedding

def numberedPairs (p : ℕ) : Fin (p + 2) × Bool ≃ NumericColor p :=
  (Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm).trans
    (finProdFinEquiv.trans (finCongr (by omega)))

structure SmallCertificate (p : ℕ) (hp : 2 ≤ p) where
  root : Fin 3 → NumericColor p → NumericColor p
  next : Fin 3 → NumericColor p → NumericColor p
  rank : Fin 3 → NumericColor p → ℕ
  row : Fin 3 → NumericColor p → Fin 4 × Fin 4
  pair : Fin (p + 2) × Bool ≃ NumericColor p
  descent : ∀ j x, x = root j x ∨
    rank j (next j x) < rank j x ∧ root j (next j x) = root j x ∧
      x ∈ numericSupport p hp j (row j x) ∧ next j x ∈ numericSupport p hp j (row j x)
  paired : ∀ j i, root j (pair (i, false)) = root j (pair (i, true))

theorem SmallCertificate.evenComponents {p : ℕ} {hp : 2 ≤ p} (K : SmallCertificate p hp)
    {m : ℕ} [NeZero m] (heven : Even m) (hm : 4 ≤ m) (j : Fin 3) :
    EvenComponents (support p hp heven j) := by
  let e : Fin 4 ⊕ Shell.Color p ≃ NumericColor p := finSumFinEquiv
  let f := fun x => component p hp heven j (e.symm x)
  have h (x : NumericColor p) : f x = f (K.root j x) := by
    apply eq_root_of_descent f (K.root j) (K.next j) (K.rank j) _ x
    intro x
    rcases K.descent j x with hx | ⟨hr, he, hx, hy⟩
    · exact Or.inl hx
    · refine Or.inr ⟨hr, he, ?_⟩
      exact same_component_nat p hp heven hm (K.row j x).1.val (K.row j x).2.val
        (K.row j x).1.isLt (K.row j x).2.isLt
        (Finset.mem_map_equiv.mp hx) (Finset.mem_map_equiv.mp hy)
  apply evenComponents_of_pairs _ (K.pair.trans e.symm)
  intro i
  exact (h (K.pair (i, false))).trans
    ((congrArg f (K.paired j i)).trans (h (K.pair (i, true))).symm)

end TorusEven.Entry.Seed
