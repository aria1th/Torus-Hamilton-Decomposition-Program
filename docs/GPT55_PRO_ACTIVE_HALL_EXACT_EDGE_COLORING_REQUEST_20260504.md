# GPT-5.5 Pro Active-Hall Exact Edge-Coloring Request

Date: 2026-05-04.

Purpose: ask for a Lean-facing proof of the remaining copied-edge finite
Hoffman/de Werra theorem
`RoundComposite.ActiveHall.FiniteHoffman.ExactEdgeColoringGoal`.

Model settings requested by the user:

```text
model: gpt-5.5-pro
reasoning effort: xhigh
max_output_tokens: 100000
mode: background
```

Response id:

```text
response_id = resp_0cd087a6b2f8d1cf0069f8e8faaf4881a0beb65e653ae30d4c
initial_status = queued
initial_submit_date = 2026-05-04
latest_poll_status = completed
latest_poll_date = 2026-05-04
final_status = completed
final_poll_date = 2026-05-04
response_doc = docs/GPT55_PRO_ACTIVE_HALL_EXACT_EDGE_COLORING_RESPONSE_20260504.md
```

Implementation note after submission: Lean now also exposes the more standard
raw edge-colouring endpoint and an adapter into the target above:

```lean
def RoundComposite.ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal : Prop := ...

theorem RoundComposite.ActiveHall.FiniteHoffman.exactEdgeColoringGoal_of_raw
    (hRaw : RawExactEdgeColoringGoal) :
    ExactEdgeColoringGoal
```

Thus an answer proving `RawExactEdgeColoringGoal` is sufficient.

Second implementation note after receiving the response: Lean now also exposes
the still more standard compatible de Werra endpoint and adapters:

```lean
def RoundComposite.ActiveHall.FiniteHoffman.CompatibleDeWerraGoal : Prop := ...

theorem RoundComposite.ActiveHall.FiniteHoffman.rawExactEdgeColoringGoal_of_compatibleDeWerra
    (hDW : CompatibleDeWerraGoal) :
    RawExactEdgeColoringGoal

theorem RoundComposite.ActiveHall.FiniteHoffman.exactEdgeColoringGoal_of_compatibleDeWerra
    (hDW : CompatibleDeWerraGoal) :
    ExactEdgeColoringGoal
```

## Files To Read

1. `RoundComposite/ActiveHall.lean`
2. `docs/GPT55_PRO_ACTIVE_HALL_ORDERED_SDR_PROOF_RESPONSE_20260504.md`
3. `docs/ODD_TORI_CURRENT_GOAL_V3_4_20260504.md`
4. `docs/ODD_TORI_REMAINING_FIELD_REQUESTS_20260504.md`

## Current Lean Target

```lean
namespace RoundComposite.ActiveHall.FiniteHoffman

def edgeLeftDegree {C E : Type*} [Fintype E] [DecidableEq E]
    [DecidableEq C] (left : E -> C) (c : C) : Nat := ...

def edgeRightDegree {T : Nat} {E : Type*} [Fintype E] [DecidableEq E]
    (right : E -> Fin T) (sigma : Fin T) : Nat := ...

def edgeRectCount {T : Nat} {C E : Type*} [Fintype E] [DecidableEq E]
    [DecidableEq C] (left : E -> C) (right : E -> Fin T)
    (U : Finset C) (S : Finset (Fin T)) : Nat := ...

def edgePairCount {T : Nat} {C E : Type*} [Fintype E] [DecidableEq E]
    [DecidableEq C] (left : E -> C) (right : E -> Fin T)
    (c : C) (sigma : Fin T) : Nat := ...

def activeDegree {X C : Type*} [Fintype X] [DecidableEq X]
    [DecidableEq C] (active : X -> Finset C) (c : C) : Nat := ...

def ExactEdgeColoringGoal : Prop :=
  ∀ {T : Nat} {X : Type uX} {C : Type uC} {E : Type uC}
    [Fintype X] [Fintype C] [Fintype E]
    [DecidableEq X] [DecidableEq C] [DecidableEq E],
    ∀ (left : E -> C) (right : E -> Fin T) (active : X -> Finset C),
      (∀ x : X, (active x).card = T) ->
      (∀ c : C, edgeLeftDegree left c = activeDegree active c) ->
      (∀ sigma : Fin T, edgeRightDegree right sigma = Fintype.card X) ->
      (∀ U : Finset C, ∀ S : Finset (Fin T),
        edgeRectCount left right U S
          <= ∑ x : X, min ((active x ∩ U).card) S.card) ->
      ∃ e : (∀ x : X, Fin T ≃ {c : C // c ∈ active x}),
        ∀ c : C, ∀ sigma : Fin T,
          Incidence.choiceDegree (fun x : X => ((e x) sigma).1) c =
            edgePairCount left right c sigma

end RoundComposite.ActiveHall.FiniteHoffman
```

This theorem is consumed by:

```lean
theorem RoundComposite.ActiveHall
  .hallRealizationGoal_of_exactEdgeColoring
    (hEdge : ActiveHall.FiniteHoffman.ExactEdgeColoringGoal) :
    ActiveHall.HallRealizationGoal

theorem RoundComposite.Concrete
  .oddModulusToriAllDimensionsGoal_of_v4_returnTailClosedFullSupportTrellisGeometryEdge
    (hFull : PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal)
    (hLift : PrefixCount.OrdinaryQge2IndicatorToFullSupportGoal)
    (hGeom : OddSuccessorSmallModulusBaseTailGeometryFromHallGoal)
    (hEdge : ActiveHall.FiniteHoffman.ExactEdgeColoringGoal) :
    OddModulusToriAllDimensionsGoal
```

## Mathematical Meaning

There is a finite bipartite multigraph with copied edges `E`, left side `C`,
and right side `Fin T`.  The "colours" are `X`.  A colour `x` may be used on a
left endpoint `c` exactly when `c ∈ active x`.  Each active set has size `T`.

The degree hypotheses say:

```text
left degree of c = number of x with c active for x
right degree of sigma = |X|
```

The rectangle condition is:

```text
edges(U,S) <= sum_x min(|active(x) ∩ U|, |S|)
```

The conclusion asks for local bijections

```lean
e x : Fin T ≃ {c : C // c ∈ active x}
```

such that, for every pair `(c, sigma)`, the number of colours `x` assigning
`sigma` to `c` is exactly the number of copied edges with endpoints
`(c, sigma)`.

This is the finite prescribed bipartite edge-colouring theorem of
Hoffman/de Werra in copied-edge form.

## Prompt

Please prove, or give a Lean-friendly proof decomposition for,
`ActiveHall.FiniteHoffman.ExactEdgeColoringGoal`.

The most useful answer is one of:

1. a direct proof by induction on `T`, with an exact last-fibre Hall matching
   lemma and residual rectangle-cut preservation;
2. a reduction to a standard finite theorem already suitable for mathlib, such
   as de Werra's balanced edge-colouring theorem, Hoffman circulation, or a
   bipartite b-matching/factor theorem;
3. a smaller external theorem statement with a short Lean adapter into the
   current `ExactEdgeColoringGoal`.

Please make the output Lean-facing:

- state auxiliary theorem names and exact types;
- identify where current `ActiveHall.lean` definitions apply;
- avoid changing the final target into a weaker existence statement that does
  not preserve the pair counts `edgePairCount left right c sigma`;
- if using an edge-colouring map `kappa : E -> X`, explain exactly how to build
  the local equivalences `Fin T ≃ {c // c ∈ active x}` and prove the
  `choiceDegree = edgePairCount` equation.
