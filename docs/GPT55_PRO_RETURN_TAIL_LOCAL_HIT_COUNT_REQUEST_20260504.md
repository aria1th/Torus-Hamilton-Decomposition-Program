# GPT-5.5 Pro Return-Tail Local Hit Count Request

Date: 2026-05-04.

Purpose: ask for a Lean-friendly proof of the remaining fixed-`t` local
first-hit count field.  Lean now reduces the full signed return-tail cocycle
sum to this local target.

Model settings requested by the user:

```text
model: gpt-5.5-pro
reasoning effort: xhigh
max_output_tokens: 100000
mode: background
```

Response id:

```text
response_id = resp_0e7bd18aaea13bdc0069f8d27d0e78819fba47cc2a63240713
initial_status = queued
initial_submit_date = 2026-05-04
latest_poll_status = in_progress
latest_poll_date = 2026-05-04
response_doc = docs/GPT55_PRO_RETURN_TAIL_LOCAL_HIT_COUNT_RESPONSE_20260504.md
```

Retrieve with:

```bash
set -a
. /data/angel/repos/etc/.env
set +a
curl -s -H "Authorization: Bearer $OPENAI_API_KEY" \
  https://api.openai.com/v1/responses/resp_0e7bd18aaea13bdc0069f8d27d0e78819fba47cc2a63240713
```

## Files To Read

1. `RoundComposite/OddCore.lean`
2. `RoundComposite/PrefixCount.lean`
3. `Shared/Monodromy.lean`
4. `Shared/RootFlat.lean`
5. `docs/GPT55_PRO_SIGNED_RETURN_TAIL_COCYCLE_SUM_REQUEST_20260504.md`
6. `docs/GPT55_PRO_SIGNED_RETURN_TAIL_COCYCLE_SUM_RESPONSE_20260504.md`
7. `docs/ODD_TORI_REMAINING_FIELD_REQUESTS_20260504.md`
8. `../prefix_count_odd_tori_overhauled_v7.tex`

## Current Lean Reduction

Lean has the local goal:

```lean
def RoundComposite.Concrete
  .PrefixCountFirstHitReturnTailLocalHitConditionSumGoal : Prop := ...
```

and proves:

```lean
theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnTailCocycleSumGoal_of_localHitConditionSum
    (hLocal : PrefixCountFirstHitReturnTailLocalHitConditionSumGoal) :
    PrefixCountFirstHitReturnTailCocycleSumGoal
```

Thus the full signed exact carry field is no longer the right proof request;
the remaining mathematical proof should target the fixed-`t` local count.
After this request was submitted, Lean also closed the pure symbol split and
the abstract reindex/iff wrapper:

```lean
noncomputable def RoundComposite.Concrete
  .prefixCountFirstHitReturnLowResidualState

noncomputable def RoundComposite.Concrete
  .prefixCountFirstHitReturnLowResidual

theorem RoundComposite.Concrete
  .prefixCountReturnTailLocalSymbolSplitIndicatorSum :
    ...

theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnLowResidual_eq_zero_iff_hitNat :
    ...

theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnLowResidual_exactLastZero_iff_rho_eq :
    ...

theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnLowResidual_hitBeforeLastZero_iff_rho_lt :
    ...

theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnLowResidual_noZero_iff_rho_not_lt :
    ...

theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnFiberHitCondition_lowResidual_iff :
    ...

def RoundComposite.Concrete
  .PrefixCountFirstHitReturnLowResidualReindexGoal : Prop := ...

theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnTailLocalHitConditionSum_eq_signedCoeff_of_reindex :
    ...

theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnTailLocalHitConditionSumGoal_of_lowResidualReindex
    (hReindex : PrefixCountFirstHitReturnLowResidualReindexGoal) :
    PrefixCountFirstHitReturnTailLocalHitConditionSumGoal
```

So the remaining constructive task is even narrower: prove the reindexing of
the now-defined map
`(x,u) ↦ prefixCountFirstHitReturnLowResidual hd2 L c hk t u x` onto
`Fin (k + 1) -> ZMod m`.

## Exact Target Shape

For fixed `t ∈ Finset.range m`, prove that:

```lean
(∑ x : (Fin k → ZMod m),
  ∑ u ∈ Finset.range m,
    if prefixCountFirstHitReturnFiberHitCondition hd2 L c
        (((prefixCountFirstHitReturnBaseStep (m := m) C c)^[u])
          (0 : ZMod m))
        (Shared.skewFiberIterate
          (prefixCountFirstHitReturnBaseStep (m := m) C c)
          (prefixCountFirstHitReturnFiberStep hd2 L c)
          u (0 : ZMod m)
          (Shared.zmodVectorExtendZero (Nat.le_of_lt hk) x))
        ⟨k, hk⟩ t
    then (1 : ZMod m) else 0) =
  prefixCountReturnTailSignedCoeff hd2 hk
    (L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c)
```

under the hypotheses:

```lean
{d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d}
Odd d → 5 ≤ d → Odd m → d ≤ m →
C.Admissible m →
(L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) →
∀ c : Fin d, ∀ k : Nat, ∀ hk : k < d - 2,
∀ t ∈ Finset.range m, ...
```

## Useful Closed Lemmas

Lean already has:

```lean
prefixCountFirstHitReturnTailCocycle_eq_sum_hitCondition
prefixCountReturnTailSignedCoeff
prefixCountReturnTailSignedCoeff_layer_sum_eq_matrix
prefixCount_toMatrix_rawStep_sub_delta_zmod
prefixCountFirstHitReturnBaseStep_sum_range_iterate
Shared.zmodVectorTake_extendZero_apply_bijective_of_incrementDependsOnTake
prefixCountFirstHitSkewFiberIterate_lowPrefix_bijective
prefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal
prefixCountPcNoZeroIndicatorSum
prefixCountPcSomeZeroIndicatorSum
prefixCountPcExactLastZeroIndicatorSum
prefixCountPcHitBeforeLastZeroIndicatorSum
```

## Requested Output

Please give a Lean-friendly proof plan and theorem interface for the fixed-`t`
local hit count.  The most useful answer would include:

1. a theorem that the map `(x,u) ↦ lowResidual` reindexes the nested
   `x,u` sum onto all `Fin (k + 1) -> ZMod m`;
2. exact Lean statement sketches showing how to prove that reindex theorem,
   preferably by triangular coordinates or by composing the closed base-orbit
   and projected-low-prefix bijections.

Please do not reprove the generic lower-triangular odometer theorem, row-Latin
property, layer-symbol matrix count, or final torus lift.  Those are already
closed in Lean.  Focus only on the fixed-`t` low-residual reindexing and
first-hit event split.
