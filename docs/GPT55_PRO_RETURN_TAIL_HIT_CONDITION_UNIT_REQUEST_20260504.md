# GPT-5.5 Pro Return-Tail Hit-Condition/Unit Request

Date: 2026-05-04.

Purpose: ask for a Lean-friendly proof route for the two remaining first-hit
return-tail fields after the generic lower-triangular odometer theorem was
closed.

Model settings requested by the user:

```text
model: gpt-5.5-pro
reasoning effort: xhigh
max_output_tokens: 100000
mode: background
```

Response id:

```text
resp_0db37919e35976200069f8bc2d05408192981ff22f53fe7f37
initial_status = queued
latest_poll_status = in_progress
latest_poll_date = 2026-05-04
response_doc = docs/GPT55_PRO_RETURN_TAIL_HIT_CONDITION_UNIT_RESPONSE_20260504.md
final_status = completed
final_poll_date = 2026-05-04
```

Retrieve with:

```bash
set -a
. /data/angel/repos/etc/.env
set +a
curl -s -H "Authorization: Bearer $OPENAI_API_KEY" \
  https://api.openai.com/v1/responses/resp_0db37919e35976200069f8bc2d05408192981ff22f53fe7f37
```

The prompt targets exactly:

```lean
RoundComposite.Concrete
  .PrefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal

RoundComposite.Concrete
  .PrefixCountFirstHitReturnTailCocycleUnitGoal
```

Local progress after this request was sent:

```lean
theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal :
    PrefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal
```

Lean also now reduces the unit-carry field from the exact sum target:

```lean
theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnTailCocycleUnitGoal_of_sum
    (hSum : PrefixCountFirstHitReturnTailCocycleSumGoal) :
    PrefixCountFirstHitReturnTailCocycleUnitGoal
```

Thus the useful remaining part of the response is the exact cocycle-sum
calculation for
`PrefixCountFirstHitReturnTailCocycleSumGoal`.

The completed response records the intended arithmetic value as

```lean
((C.toMatrix hd2) c ⟨k + 2, _⟩ : ZMod m) -
((C.toMatrix hd2) c ⟨1, _⟩ : ZMod m)
```

which should then be identified with the target-side expression
`((-1 : ZMod m) ^ (k + 1)) *
  ((C.step c ⟨k, hk⟩ : Int) - (C.delta c : Int) : ZMod m)`.

Correction recorded after local finite verification: the unsigned
`C.step - C.delta` target is false for admissible small examples.  The
canonical prefix-count carry has the sign `(-1)^(k+1)`, which is still a unit
and therefore preserves the unit-carry reduction.

It explicitly asks not to reprove the generic lower-triangular odometer theorem.
That theorem is already closed in `Shared` and is consumed by:

```lean
RoundComposite.Concrete
  .prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_hitConditionUnitBlocks
```

The requested output is a set of smaller Lean lemma statements and proof
sketches for:

1. one-step hit-condition locality;
2. total carry/cocycle unit calculation;
3. the exact arithmetic value of the total carry, if identifiable from
   `PrefixCount.Parts.Admissible` and `PrefixCount.LayerPermCounts`;
4. warnings about false strengthenings or hidden dependencies.

The prompt included excerpts from:

```text
RoundComposite/OddCore.lean
Shared/Monodromy.lean
docs/ODD_TORI_CURRENT_GOAL_V3_4_20260504.md
../prefix_count_odd_tori_overhauled_v7.tex
```
