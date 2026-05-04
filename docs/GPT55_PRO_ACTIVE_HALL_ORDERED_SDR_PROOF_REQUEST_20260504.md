# GPT-5.5 Pro Active Hall Ordered-SDR Proof Request

Date: 2026-05-04.

Purpose: ask for an implementable Lean proof decomposition of the remaining
abstract Active Hall theorem, not just the identification with Hoffman's
ordered-SDR theorem.

Model settings requested by the user:

```text
model: gpt-5.5-pro
reasoning effort: xhigh
max_output_tokens: 100000
mode: background
```

Response id:

```text
response_id = resp_050d642997a6ebc00069f8dceccb388192ae6b3842da834279
initial_status = queued
initial_submit_date = 2026-05-04
latest_poll_status = in_progress
latest_poll_date = 2026-05-04
final_status = completed
final_poll_date = 2026-05-04
response_doc = docs/GPT55_PRO_ACTIVE_HALL_ORDERED_SDR_PROOF_RESPONSE_20260504.md
```

## Files To Read

1. `RoundComposite/ActiveHall.lean`
2. `docs/ACTIVE_HALL_TOKEN_LINEAR_REQUEST_20260504.md`
3. `docs/GPT55_PRO_ACTIVE_HALL_TOKEN_LINEAR_RESPONSE_20260504.md`
4. `docs/ODD_TORI_REMAINING_FIELD_REQUESTS_20260504.md`

## Current Lean Target

Preferred exact target:

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
          Incidence.choiceDegree (fun x : X => ((e x) σ).1) c = m c σ
```

Equivalent targets already in Lean:

```lean
HallRealizationGoal
EraseLastHallCutsTokenLinearChoiceGoal
EraseLastHallCutsSelectionGoal
EraseLastHallCutsChoiceGoal
EraseLastHallCutsSlackChoiceGoal
EraseLastHallCutsNontrivialSlackChoiceGoal
EraseLastHallCutsLinearChoiceGoal
ColumnFillingUpgradeGoal
```

Lean already proves all iff/wrapper implications between these formulations.

## Prompt

Give a Lean-facing proof strategy that actually proves one of the equivalent
targets above.

The previous response correctly identified the theorem as classical Hoffman
ordered-SDR / prescribed-degree one-sided bipartite edge-colouring, but did not
give enough implementation detail.  This request asks for the missing proof
decomposition.

Please provide one of:

1. A derivation of `HoffmanOrderedSDRGoal` from an existing mathlib theorem,
   with exact theorem names and adaptation steps.
2. A proof of `EraseLastHallCutsTokenLinearChoiceGoal` using only finite Hall
   matching plus an explicitly stated auxiliary theorem.  The auxiliary theorem
   should be smaller than the original ordered-SDR statement.
3. A proof of `ColumnFillingUpgradeGoal`: given `M.HallCuts` and
   `M.ColumnFilling`, upgrade the column-wise filling to a genuine local
   permutation `Symboling`.
4. If none of these can realistically be formalized from current mathlib, state
   the smallest external theorem that should be added, with exact Lean
   statement and proof outline.

Important constraints:

1. Plain independent Hall matchings for each symbol column are insufficient;
   they do not force distinct colors at a fixed `x`.
2. The answer must be concrete about finite types, copied tokens, cut
   inequalities, and how the current definitions `Incidence.cutCap`,
   `CountMatrix.cutMass`, `CountMatrix.cutSlack`, `lowCutSet`, and
   `tokenLoadOn` are used.
3. Prefer an induction-on-`T` proof if possible, since `ActiveHall.lean`
   already has erase-last infrastructure and a closed `T = 0` base case.
4. Avoid suggesting a new broad development unless it is truly necessary; the
   target is to close the current `ActiveHall` abstraction for this project.

The ideal response is a sequence of Lean theorem statements and proof sketches
that can be implemented incrementally in `RoundComposite/ActiveHall.lean`.
