# Active-Hall Realization Request

Date: 2026-05-03.

This note isolates the remaining finite Hall/Hoffman theorem behind the
small-modulus Hall-slack branch.  It is intended as a prompt for a separate
mathematical proof or Lean formalization attempt.

## Source Files To Read

Read these files first:

1. `RoundComposite/ActiveHall.lean`
2. `docs/ODD_TORI_CURRENT_GOAL_V2_8_20260504.md`
3. `docs/ODD_TORI_GLOBAL_COMPLETION_AUDIT_20260503.md`
4. `docs/GPT55_PRO_ACTIVE_HALL_SLACK_RESPONSE_20260503.md`
5. `docs/PREFIX_COUNT_ODD_TORI_OVERHAULED_V4_ABSORPTION_20260504.md`

The theorem below is not a torus theorem.  It is a finite combinatorial
realization theorem for active symbolings.

## Lean Target

The current isolated target is:

```lean
def ActiveHall.HallRealizationGoal : Prop :=
  ∀ {T : Nat} {X : Type uX} {C : Type uC}
    [Fintype X] [Fintype C] [DecidableEq X] [DecidableEq C],
    ∀ (I : ActiveHall.Incidence T X C) (M : ActiveHall.CountMatrix I),
      M.HallCuts →
      ∃ Φ : ActiveHall.Symboling I, Φ.Realizes M.val
```

Unpacked:

- each base vertex `x : X` has an active set `I.active x : Finset C` of
  cardinality `T`;
- a symboling assigns the symbols `Fin T` bijectively to `I.active x` for
  every `x`;
- `M.val c σ` prescribes how often color `c` receives symbol `σ`;
- the row sums of `M` are forced to be `I.colorDegree c`;
- the column sums of `M` are forced to be `Fintype.card X`;
- `M.HallCuts` states

```lean
M.cutMass U S ≤ I.cutCap U S
```

for every `U : Finset C` and `S : Finset (Fin T)`, where

```lean
M.cutMass U S = ∑ c ∈ U, ∑ σ ∈ S, M.val c σ
I.cutCap U S = ∑ x : X, min ((I.active x ∩ U).card) S.card
```

## Important Warning

This is not just ordinary Hall matching on demand tokens
`(c, σ, k)` against slots `(x, σ)`.  Such a matching would not by itself stop
the same color `c` from being used twice at the same vertex `x` with two
different symbols.  The required object is closer to a capacitated bipartite
edge-coloring or Hoffman circulation theorem:

- the bipartite graph has left side `X`, right side `C`, and edges
  `(x,c)` when `c ∈ I.active x`;
- every edge `(x,c)` must receive exactly one symbol `σ : Fin T`;
- at each `x`, all symbols are used exactly once;
- for each `(c, σ)`, exactly `M.val c σ` incident edges at color `c` receive
  symbol `σ`.

The cut condition above is expected to be the right necessary and sufficient
condition for this realization problem.

## Already Lean-Closed Support

`RoundComposite/ActiveHall.lean` already proves:

- row and column sums for an existing `Symboling`;
- `Symboling.toCountMatrix_hallCuts`;
- the converse sanity adapter
  `feasibleWithResidues_of_symbolingWithResidues`;
- color-degree double counting:
  `Incidence.sum_colorDegree`, `Incidence.sum_colorDegree_on`;
- empty/full cut reductions:
  `CountMatrix.hallCuts_iff_nontrivial`;
- cut monotonicity:
  `Incidence.cutCap_mono`, `CountMatrix.cutMass_mono`;
- one-symbol Hall extraction:
  `Incidence.hitCount`, `Incidence.cutCap_symbol_singleton`,
  `CountMatrix.cutMass_symbol_singleton`, `CountMatrix.singleSymbol_hall`,
  `CountMatrix.exists_singleSymbol_token_matching`;
- ordinary Hall token matching:
  `Incidence.exists_injective_token_matching_of_hall`;
- residue compatibility adapters for feasible matrices and symbolings.

Thus the missing theorem should not reprove the torus machinery.  It should
focus only on finite realization.

## Brute-Force Sanity Check

There is a small executable sanity check:

```text
python3 scripts/active_hall_realization_bruteforce.py
```

It exhaustively checks the default cases

```text
(T,C,X) = (2,2,2), (2,3,2), (2,3,3), (2,4,3), (3,3,3), (3,4,3)
```

by enumerating active incidences, all row/column compatible matrices, all
matrices satisfying `HallCuts`, and all realized symboling count matrices.  The
current default run finds no counterexample.  This is only evidence; it is not
a proof and should not be used as a theorem dependency.

## Requested Output

Please provide one of the following:

1. A Lean proof plan for `ActiveHall.HallRealizationGoal` using existing
   mathlib theorems, with exact imported theorem names where possible.
2. A mathematically complete proof reducing the target to a standard theorem
   such as Hoffman circulation, max-flow/min-cut, or bipartite `b`-matching.
3. If the stated `HallCuts` condition is insufficient, provide a concrete
   finite counterexample and the corrected cut condition.

The most useful result is a Lean-friendly theorem statement that can replace
or imply `ActiveHall.HallRealizationGoal` without adding any torus-specific
assumptions.

## Suggested Proof Routes

Possible approaches:

1. Model the problem as an integral circulation with source supplies for
   `(c, σ)`, edge capacities through active incidences `(x,c)`, and vertex
   capacities enforcing one occurrence of each symbol at each `x`.
2. Use Hoffman circulation inequalities and prove they reduce exactly to
   `M.HallCuts` plus the existing row/column sum fields.
3. Use a bipartite `b`-matching formulation in an expanded graph, but ensure
   the construction enforces both constraints:
   each active edge `(x,c)` is used once, and each `(x,σ)` is used once.
4. If using ordinary Hall's theorem, identify the correct expanded left/right
   sets and prove that the Hall inequalities are equivalent to
   `M.HallCuts`.

## Why This Matters

Closing this theorem would remove one of the abstract finite-combinatorial
obstacles in the `OddCoreSmallModulusSlackPacketLiftGoal` path.  It does not
finish the full odd-tori theorem by itself, but it converts a major
Hall-symboling existence step into a reusable Lean theorem.
