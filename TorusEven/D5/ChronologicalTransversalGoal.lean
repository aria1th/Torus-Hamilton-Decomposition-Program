-- STATUS: conditional (statement of the E3-b interface; proof pending)
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Logic.Function.Iterate

/-!
# Chronological transversal splice (manuscript Lemma `lem:chronological`)

Interface 1 of `evidence/even_d5/INTERFACES.md`, written without any coset library:
orbits and cosets are plain `Set`s so that the statement can be checked against the
manuscript by eye.  Composition convention: permutations act on the left and products
are read right to left, so `S r` in the manuscript is `fun x => S (r x)` here.

Hypotheses:
* `X = H ⊕ W` (`IsCompl H W` for additive subgroups of a finite abelian group);
* the cycles of `S` are exactly the `H`-cosets;
* the prefix `P` satisfies `P x ∈ x + b + H` for a fixed `b`;
* `e ∈ W` has order `m`, and `J` adds `e` on the affine coset `z + W` only.

Conclusion: the cycles of `S ∘ P⁻¹ ∘ J ∘ P` are exactly the cosets of `H + ⟨e⟩`.
-/

namespace TorusEven
namespace Chronological

variable {X : Type*} [AddCommGroup X] [Fintype X] [DecidableEq X]

/-- Forward orbit of `x` under iteration; for a bijection on a finite type this is its cycle. -/
def orbitSet (f : X → X) (x : X) : Set X :=
  Set.range fun n : ℕ => f^[n] x

/-- The coset `x + H` as a set. -/
def coset (H : AddSubgroup X) (x : X) : Set X :=
  {y | y - x ∈ H}

/-- Add `e` on the affine coset `z + W`, identity elsewhere. -/
def piecewiseAdd (W : AddSubgroup X) [DecidablePred (· ∈ W)] (z e : X) (y : X) : X :=
  if y - z ∈ W then y + e else y

/-- The manuscript lemma as a single proposition. -/
def ChronologicalTransversalGoal : Prop :=
  ∀ {X : Type} [AddCommGroup X] [Fintype X] [DecidableEq X]
    (H W : AddSubgroup X) [DecidablePred (· ∈ W)]
    (_hHW : IsCompl H W)
    (S : Equiv.Perm X) (_hS : ∀ x, orbitSet S x = coset H x)
    (P : Equiv.Perm X) (b : X) (_hP : ∀ x, P x - x - b ∈ H)
    (e : X) (_he : e ∈ W) (m : ℕ) (_hm : addOrderOf e = m)
    (z : X),
    let r : X → X := fun x => P.symm (piecewiseAdd W z e (P x))
    ∀ x, orbitSet (fun y => S (r y)) x = coset (H ⊔ AddSubgroup.zmultiples e) x

/-- Sub-lemma (i): `P⁻¹ (z + W)` meets every `H`-coset exactly once. -/
def TransversalSectionGoal : Prop :=
  ∀ {X : Type} [AddCommGroup X] [Fintype X] [DecidableEq X]
    (H W : AddSubgroup X) (_hHW : IsCompl H W)
    (P : Equiv.Perm X) (b : X) (_hP : ∀ x, P x - x - b ∈ H) (z : X) (x : X),
    ∃! a, a ∈ coset H x ∧ P a - z ∈ W

end Chronological
end TorusEven
