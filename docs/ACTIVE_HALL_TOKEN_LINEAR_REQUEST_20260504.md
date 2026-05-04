# Active Hall Ordered-SDR / Erase-Last Request

Date: 2026-05-04.

## Purpose

The current abstract Active Hall realization is reduced to one finite ordered
SDR theorem, equivalently one of several erase-last choice theorems.  A proof
of any equivalent target below would close the erase-last induction used by
`RoundComposite.ActiveHall.HallRealizationGoal`.

## Files To Read

1. `RoundComposite/ActiveHall.lean`
2. `docs/ODD_TORI_CURRENT_GOAL_V3_1_20260504.md`
3. Optionally, for broader context:
   `docs/GPT55_PRO_ACTIVE_HALL_TOKEN_LINEAR_RESPONSE_20260504.md`

## Preferred Lean Target

The cleanest standalone theorem is the Hoffman ordered-SDR formulation:

```lean
def RoundComposite.ActiveHall.HoffmanOrderedSDRGoal : Prop :=
  ∀ {T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C],
    ∀ (I : Incidence T X C) (m : C → Fin T → Nat),
      (∀ c : C, (∑ σ : Fin T, m c σ) = I.colorDegree c) →
      (∀ σ : Fin T, (∑ c : C, m c σ) = Fintype.card X) →
      (∀ U : Finset C, ∀ S : Finset (Fin T),
        (∑ c ∈ U, ∑ σ ∈ S, m c σ) ≤ I.cutCap U S) →
      ∃ e : (∀ x : X, Fin T ≃ {c : C // c ∈ I.active x}),
        ∀ c : C, ∀ σ : Fin T,
          Incidence.choiceDegree (fun x : X => ((e x) σ).1) c
            = m c σ
```

This is Lean-equivalent to `HallRealizationGoal`, and it is the mathematically
standard form: ordered systems of distinct representatives with prescribed
symbol counts.

## Equivalent Erase-Last Target

The token-linear erase-last theorem remains a sharp alternative target:

```lean
def RoundComposite.ActiveHall.EraseLastHallCutsTokenLinearChoiceGoal : Prop :=
  forall {T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C],
    forall (I : Incidence (T + 1) X C) (M : CountMatrix I),
      M.HallCuts ->
      exists f : (Sigma fun c : C => Fin (M.val c (Fin.last T))) ≃ X,
        (forall q : Sigma fun c : C => Fin (M.val c (Fin.last T)),
            q.1 ∈ I.active (f q)) ∧
          forall U : Finset C, forall S : Finset (Fin T),
            U.Nonempty -> U != (Finset.univ : Finset C) -> S.Nonempty ->
              Incidence.tokenLoadOn f (Incidence.lowCutSet I U S) U
                <= M.cutSlack U
                    (S.image (Fin.castSucc : Fin T -> Fin (T + 1)))
```

Here `f` places the last-column color tokens into vertices.  The active
condition says a token of color `c` may only be placed at a vertex whose active
set contains `c`.  The inequality controls how many tokens from a color cut
`U` land in the lower-symbol danger set `lowCutSet I U S`.

## Already Lean-Closed

The following reductions and bridges are already present and build:

```lean
theorem eraseLastHallCutsTokenLinearChoiceGoal_of_hallRealization
    (hRealize : HallRealizationGoal) :
    EraseLastHallCutsTokenLinearChoiceGoal

theorem eraseLastHallCutsTokenLinearChoiceGoal_of_selection
    (hSelect : EraseLastHallCutsSelectionGoal) :
    EraseLastHallCutsTokenLinearChoiceGoal

theorem eraseLastHallCutsLinearChoiceGoal_of_tokenLinear
    (hToken : EraseLastHallCutsTokenLinearChoiceGoal) :
    EraseLastHallCutsLinearChoiceGoal

theorem eraseLastHallCutsGoal_of_tokenLinearChoice
    (hToken : EraseLastHallCutsTokenLinearChoiceGoal) :
    EraseLastHallCutsGoal

theorem hallRealizationGoal_of_eraseLastHallCutsTokenLinearChoice
    (hToken : EraseLastHallCutsTokenLinearChoiceGoal) :
    HallRealizationGoal

theorem symbolingWithResidues_of_feasible_and_eraseLastHallCutsTokenLinearChoice
    (hToken : EraseLastHallCutsTokenLinearChoiceGoal)
    (hFeasible : FeasibleWithResidues I R) :
    SymbolingWithResidues I R

theorem symbolingWithResidues_of_feasible_and_eraseLastHallCutsSelection
    (hSelect : EraseLastHallCutsSelectionGoal)
    (hFeasible : FeasibleWithResidues I R) :
    SymbolingWithResidues I R

theorem hallRealizationGoal_iff_eraseLastHallCutsTokenLinearChoiceGoal :
    HallRealizationGoal <-> EraseLastHallCutsTokenLinearChoiceGoal

theorem hallRealizationGoal_iff_eraseLastHallCutsGoal :
    HallRealizationGoal <-> EraseLastHallCutsGoal

theorem hallRealizationGoal_iff_eraseLastHallCutsSelectionGoal :
    HallRealizationGoal <-> EraseLastHallCutsSelectionGoal

theorem eraseLastHallCutsSelectionGoal_iff_tokenLinearChoiceGoal :
    EraseLastHallCutsSelectionGoal <->
      EraseLastHallCutsTokenLinearChoiceGoal

theorem hallRealizationGoal_iff_eraseLastHallCutsChoiceGoal :
    HallRealizationGoal <-> EraseLastHallCutsChoiceGoal

theorem hallRealizationGoal_iff_eraseLastHallCutsSlackChoiceGoal :
    HallRealizationGoal <-> EraseLastHallCutsSlackChoiceGoal

theorem hallRealizationGoal_iff_eraseLastHallCutsNontrivialSlackChoiceGoal :
    HallRealizationGoal <-> EraseLastHallCutsNontrivialSlackChoiceGoal

theorem hallRealizationGoal_iff_eraseLastHallCutsLinearChoiceGoal :
    HallRealizationGoal <-> EraseLastHallCutsLinearChoiceGoal

def HoffmanOrderedSDRGoal : Prop

theorem hallRealizationGoal_iff_hoffmanOrderedSDRGoal :
    HallRealizationGoal <-> HoffmanOrderedSDRGoal

theorem eraseLastHallCutsTokenLinearChoiceGoal_of_hoffmanOrderedSDR
    (hHoffman : HoffmanOrderedSDRGoal) :
    EraseLastHallCutsTokenLinearChoiceGoal

theorem symbolingWithResidues_of_feasible_and_hoffmanOrderedSDR
    (hHoffman : HoffmanOrderedSDRGoal)
    (hFeasible : FeasibleWithResidues I R) :
    SymbolingWithResidues I R

def ColumnFillingUpgradeGoal : Prop

theorem hallRealizationGoal_iff_columnFillingUpgradeGoal :
    HallRealizationGoal <-> ColumnFillingUpgradeGoal

theorem symbolingWithResidues_of_feasible_and_columnFillingUpgrade
    (hUpgrade : ColumnFillingUpgradeGoal)
    (hFeasible : FeasibleWithResidues I R) :
    SymbolingWithResidues I R

theorem symbolingWithResidues_iff_feasible_of_realization
    (hRealize : HallRealizationGoal) :
    SymbolingWithResidues I R <-> FeasibleWithResidues I R

theorem symbolingWithResidues_iff_feasible_of_hoffmanOrderedSDR
    (hHoffman : HoffmanOrderedSDRGoal) :
    SymbolingWithResidues I R <-> FeasibleWithResidues I R

theorem symbolingWithResidues_iff_feasible_of_columnFillingUpgrade
    (hUpgrade : ColumnFillingUpgradeGoal) :
    SymbolingWithResidues I R <-> FeasibleWithResidues I R

theorem symbolingWithResidues_iff_feasible_of_eraseLastHallCutsSelection
    (hSelect : EraseLastHallCutsSelectionGoal) :
    SymbolingWithResidues I R <-> FeasibleWithResidues I R

theorem symbolingWithResidues_iff_feasible_of_eraseLastHallCuts
    (hErase : EraseLastHallCutsGoal) :
    SymbolingWithResidues I R <-> FeasibleWithResidues I R

theorem symbolingWithResidues_iff_feasible_of_eraseLastHallCutsChoice
    (hChoice : EraseLastHallCutsChoiceGoal) :
    SymbolingWithResidues I R <-> FeasibleWithResidues I R

theorem symbolingWithResidues_iff_feasible_of_eraseLastHallCutsSlackChoice
    (hSlackChoice : EraseLastHallCutsSlackChoiceGoal) :
    SymbolingWithResidues I R <-> FeasibleWithResidues I R

theorem symbolingWithResidues_iff_feasible_of_eraseLastHallCutsNontrivialSlackChoice
    (hNontriv : EraseLastHallCutsNontrivialSlackChoiceGoal) :
    SymbolingWithResidues I R <-> FeasibleWithResidues I R

theorem symbolingWithResidues_iff_feasible_of_eraseLastHallCutsLinearChoice
    (hLinear : EraseLastHallCutsLinearChoiceGoal) :
    SymbolingWithResidues I R <-> FeasibleWithResidues I R

theorem symbolingWithResidues_iff_feasible_of_eraseLastHallCutsTokenLinearChoice
    (hToken : EraseLastHallCutsTokenLinearChoiceGoal) :
    SymbolingWithResidues I R <-> FeasibleWithResidues I R
```

Also available:

```lean
structure CountMatrix.ColumnFilling
theorem CountMatrix.exists_columnFilling_of_hallCuts
def Symboling.toColumnFilling
Incidence.tokenLoadOn
Incidence.tokenLoadOn_eq_choiceHitCountOn
Incidence.tokenLoadOn_eq_sum_choiceDegreeOn
Incidence.tokenLoadOn_le_card
Incidence.tokenLoadOn_mono_set
Incidence.tokenLoadOn_mono_colors
Incidence.tokenLoadOn_set_empty
Incidence.tokenLoadOn_colors_empty
Incidence.tokenLoadOn_colors_univ
eraseLastHallCutsTokenLinearChoice_zero
```

`CountMatrix.exists_columnFilling_of_hallCuts` is the strongest result that
follows immediately from plain Hall matching: each symbol column can be filled
with active colors and the prescribed column counts.  This relaxation does not
force the colors chosen at a fixed vertex to be distinct, so it is not yet a
`Symboling`.  The remaining theorem is the capacitated/Hoffman strengthening
that upgrades column-wise fillings to row-Latin symbolings.

Equivalently, one may prove `ColumnFillingUpgradeGoal`: given `M.HallCuts` and
a column-wise filling, upgrade it to a genuine `Symboling` realizing the same
matrix.  This is Lean-equivalent to `HallRealizationGoal`.

## Mathematical Request

Find a proof strategy for `HoffmanOrderedSDRGoal` or any of the equivalent
erase-last choice theorems above.

The expected proof should be a pure finite combinatorics argument, independent
of torus geometry.  It may use Hall's theorem, max-flow/min-cut,
Hoffman circulation, polymatroid intersection, or a clean equivalent finite
matching theorem, but the output should explain exactly what auxiliary theorem
is needed and how `M.HallCuts` implies its hypotheses.

The most useful answer would provide:

1. A Lean-friendly intermediate theorem statement.
2. A proof outline for deriving that theorem from `M.HallCuts`.
3. A proof outline for deriving `EraseLastHallCutsTokenLinearChoiceGoal`.
4. Any counterexample risk if the theorem is too strong as stated.

## Small Sanity Search

An ad hoc brute-force search was run on 2026-05-04 for small abstract
instances.  It exhaustively checked the following blocks:

```text
C = 2, active size K = 2, |X| <= 7
C = 3, active size K = 2, |X| <= 7
C = 3, active size K = 3, |X| <= 6
C = 4, active size K = 2, |X| <= 5
```

For each block, the search enumerated:

1. all active-set assignments `X -> Finset C` with constant active size `K`;
2. all nonnegative count matrices with the forced row sums and column sums;
3. the full `M.HallCuts` condition;
4. all last-column active token placements, checking the token-linear
   lower-cut inequalities.

No counterexample was found.  The largest checked block was
`C = 4, K = 2, |X| <= 5`, with `192666` row/column-compatible matrices
examined and `162930` Hall matrices passing the Hall filter.

This is only a finite sanity check.  It is not a proof and should not be used
as a Lean dependency.

## Important Boundary

Do not solve the torus construction here.  The target is only the abstract
finite token-placement theorem in `RoundComposite.ActiveHall`.
