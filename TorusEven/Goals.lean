-- STATUS: main-path
import TorusEven.Dispatch

/-!
# Even-modulus proof obligations

Each `Goal` below names a theorem interface from
`docs/EVEN_MODULUS_FORMALIZATION_PLAN_20260910.md`. The interfaces are discharged
in `D3`, `D5`, `Collar.EvenDegree`, `Entry.OddDegree`, and `Endpoints`.
Manuscript references are to `even_directed_tori_integrated.tex`.
-/

namespace TorusEven

/-- E2: manuscript Proposition (anchored three-colour decomposition), all even `m ≥ 4`. -/
def D3EvenGoal : Prop :=
  ∀ {m : Nat}, Even m → 4 ≤ m → Solved 3 m

/-- E3 (m ≥ 6): manuscript Theorem `thm:d5large`, chronological transversal route. -/
def D5EvenLargeGoal : Prop :=
  ∀ {m : Nat}, Even m → 6 ≤ m → Solved 5 m

/-- E5 (p = 2): manuscript Lemma `lem:entry-seven` with the collar closure. -/
def D7EvenGoal : Prop :=
  ∀ {m : Nat}, Even m → 4 ≤ m → Solved 7 m

/-- Successor closure in the odd-dispatcher shape (not the manuscript's route). -/
def EvenSuccessorGoal : Prop := evenClass.SuccessorClosure

/-- E4 + E5: manuscript Theorem `thm:oddconstruction`, every odd `d ≥ 7`. -/
def EvenOddDegreeGoal : Prop := evenClass.OddDegreeClosure

/-- E4 special case: manuscript Theorem `thm:even-dim`, every even `d ≥ 2` via the empty palette.
Discharged by `even_degree_collar`, independently of the odd-degree entry goal. -/
def EvenDegreeCollarGoal : Prop :=
  ∀ {d m : Nat}, Even d → 2 ≤ d → Even m → 4 ≤ m → Solved d m

/-- The final even-modulus theorem shape. -/
def EvenModulusToriAllDimensionsGoal : Prop :=
  ∀ {d m : Nat}, 2 ≤ d → Even m → 4 ≤ m → Solved d m

end TorusEven
