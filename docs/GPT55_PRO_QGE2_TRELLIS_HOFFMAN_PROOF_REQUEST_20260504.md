# GPT-5.5 Pro q>=2 Trellis-Hoffman Proof Request

Date: 2026-05-04.

Purpose: ask for a Lean-facing proof plan, with auxiliary theorem statements,
for the remaining high-modulus ordinary q>=2 signed-trellis field.

Model settings requested by the user:

```text
model: gpt-5.5-pro
reasoning effort: xhigh
max_output_tokens: 100000
mode: background
```

Response id:

```text
response_id = resp_0078009c9235b49c0069f8dc9d25548194b2b94fd491d49cd7
initial_status = queued
initial_submit_date = 2026-05-04
latest_poll_status = completed
latest_poll_date = 2026-05-04
final_status = completed
final_poll_date = 2026-05-04
response_doc = docs/GPT55_PRO_QGE2_TRELLIS_HOFFMAN_PROOF_RESPONSE_20260504.md
```

Implementation note: the response has been absorbed into
`RoundComposite/PrefixCount.lean`.  Lean now exposes
`OrdinaryQge2SignedFullSupportTrellisGoal`,
`OrdinaryQge2IndicatorToFullSupportGoal`,
`OrdinaryQge2SupportViolationGivesIndicatorCutGoal`, and the wrappers
`ordinaryQge2IndicatorToFullSupportGoal_of_separation` and
`ordinaryQge2SignedTrellisHoffmanGoal_of_fullSupport`.

## Files To Read

1. `RoundComposite/PrefixCount.lean`
2. `docs/ODD_TORI_CURRENT_GOAL_V3_4_20260504.md`
3. `docs/ODD_TORI_REMAINING_FIELD_REQUESTS_20260504.md`
4. `docs/GPT55_PRO_QGE2_PROPER_CUT_RESPONSE_20260504.md`
5. `/data/angel/repos/etc/prefix_count_odd_tori_overhauled_v7.tex`

## Current Lean Target

```lean
def RoundComposite.PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal : Prop :=
  ∀ {n r : Nat},
    Even n → 4 ≤ n → Odd r → r < n → 0 < r →
    ∀ (a : Fin n → Nat) (epsBit : Fin n → Nat) (c : Fin (n - 1) → Nat),
      (∀ i : Fin n, a i = 1 ∨ a i = 2) →
      (∀ i : Fin n, epsBit i = 0 ∨ epsBit i = 1) →
      (∀ k : Fin (n - 1), c k = 1 ∨ c k = 2) →
      (∑ i : Fin n, epsBit i) = r →
      (∑ i : Fin n, a i) = (∑ k : Fin (n - 1), c k) →
      (∀ J : Finset (Fin n),
        (∑ i ∈ J, ((r : Int) - (a i : Int)
            - (n : Int) * (epsBit i : Int)))
          ≤ ∑ k : Fin (n - 1), qge2ColumnCapacity n J.card (c k)) →
      ∃ X : Fin (n - 1) → Fin n → Int,
        (∀ k i, IsSignedVal (X k i)) ∧
        (∀ k : Fin (n - 1), (∑ i : Fin n, X k i) = - (c k : Int)) ∧
        (∀ i : Fin n,
          (∑ k : Fin (n - 1), X k i)
            = (r : Int) - (a i : Int) - (n : Int) * (epsBit i : Int))
```

Lean already proves:

```lean
theorem RoundComposite.PrefixCount
  .ordinaryQge2SignedSeedProperCutClosureGoal_of_signedTrellisHoffman
    (hHoffman : OrdinaryQge2SignedTrellisHoffmanGoal) :
    OrdinaryQge2SignedSeedProperCutClosureGoal
```

and the current all-dimensional endpoint now needs only:

```lean
PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal
OddSuccessorSmallModulusBaseTailGoal
```

## Prompt

Prove, or give a Lean-friendly proof decomposition for,
`OrdinaryQge2SignedTrellisHoffmanGoal`.

Important constraints:

1. Do not replace the target by an arbitrary row-demand signed-column packing
   theorem.  That stronger theorem is false; the row demands must keep the
   ordinary trellis shape
   `(r : Int) - (a i : Int) - (n : Int) * (epsBit i : Int)`.
2. It is acceptable to use a standard finite theorem such as integral
   Hoffman circulation, Edmonds-Giles, polymatroid intersection, or
   consecutive-ones network matrices, but the response should state the exact
   intermediate Lean theorem that would be imported/proved.
3. Prefer a proof that exploits the special data:
   `a_i ∈ {1,2}`, `epsBit_i ∈ {0,1}`, `c_k ∈ {1,2}`,
   `Even n`, `Odd r`, `0 < r < n`, and the all-cut inequalities already in the
   Lean target.
4. Output should be concrete enough to implement in Lean:
   auxiliary definitions, theorem statements, induction or flow construction
   order, and exact places where current lemmas in `PrefixCount.lean` apply.
5. If the target as stated is false, provide a concrete counterexample
   satisfying all hypotheses and all cuts.

The ideal result is a short chain of auxiliary theorems that reduces the target
to one standard combinatorial theorem already present in mathlib or to a
small, special-purpose theorem that can realistically be formalized here.
