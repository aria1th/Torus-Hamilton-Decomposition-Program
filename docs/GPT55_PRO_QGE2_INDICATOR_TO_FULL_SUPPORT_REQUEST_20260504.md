# GPT-5.5 Pro q>=2 Indicator-To-Full-Support Request

Date: 2026-05-04.

Purpose: ask for a Lean-facing proof of the ordinary q>=2 cut-completion
theorem
`RoundComposite.PrefixCount.OrdinaryQge2IndicatorToFullSupportGoal`, preferably
through the separation endpoint
`OrdinaryQge2SupportViolationGivesIndicatorCutGoal`.

Model settings requested by the user:

```text
model: gpt-5.5-pro
reasoning effort: xhigh
max_output_tokens: 100000
mode: background
```

Response id:

```text
response_id = resp_0c636bbdc33191c10069f8e747ade0819c8ef13cac38681513
initial_status = queued
initial_submit_date = 2026-05-04
latest_poll_status = in_progress
latest_poll_date = 2026-05-04
final_status = pending
final_poll_date = pending
response_doc = docs/GPT55_PRO_QGE2_INDICATOR_TO_FULL_SUPPORT_RESPONSE_20260504.md
```

## Files To Read

1. `RoundComposite/PrefixCount.lean`
2. `docs/GPT55_PRO_QGE2_TRELLIS_HOFFMAN_PROOF_RESPONSE_20260504.md`
3. `docs/ODD_TORI_CURRENT_GOAL_V3_4_20260504.md`
4. `/data/angel/repos/etc/prefix_count_odd_tori_overhauled_v7.tex`

The relevant paper sections are:

```text
prefix_count_odd_tori_overhauled_v7.tex:
  section 4.2, "The ordinary signed transportation case q>=2"
  appendix "Row-subset cut decomposition"
  appendix proof of the ordinary signed closure theorem
```

## Current Lean Definitions

```lean
def RoundComposite.PrefixCount.qge2OrdinaryRowTarget
    (n r : Nat) (a epsBit : Fin n -> Nat) (i : Fin n) : Int :=
  (r : Int) - (a i : Int) - (n : Int) * (epsBit i : Int)

abbrev RoundComposite.PrefixCount.SignedValInt : Type := Fin 4

def RoundComposite.PrefixCount.SignedValInt.toInt
    (v : SignedValInt) : Int := ...

def RoundComposite.PrefixCount.qge2SignedColumnFinset
    (n c : Nat) : Finset (Fin n -> SignedValInt) := ...

noncomputable def RoundComposite.PrefixCount.qge2SignedColumnSupport
    (n c : Nat) (w : Fin n -> Int) : Int := ...
```

The target:

```lean
def RoundComposite.PrefixCount.OrdinaryQge2IndicatorToFullSupportGoal : Prop :=
  ∀ {n r : Nat},
    Even n -> 4 <= n -> Odd r -> r < n -> 0 < r ->
    ∀ (a : Fin n -> Nat) (epsBit : Fin n -> Nat) (c : Fin (n - 1) -> Nat),
      (∀ i : Fin n, a i = 1 ∨ a i = 2) ->
      (∀ i : Fin n, epsBit i = 0 ∨ epsBit i = 1) ->
      (∀ k : Fin (n - 1), c k = 1 ∨ c k = 2) ->
      (∑ i : Fin n, epsBit i) = r ->
      (∑ i : Fin n, a i) = (∑ k : Fin (n - 1), c k) ->
      (∀ J : Finset (Fin n),
        (∑ i ∈ J, qge2OrdinaryRowTarget n r a epsBit i)
          <= ∑ k : Fin (n - 1), qge2ColumnCapacity n J.card (c k)) ->
      ∀ w : Fin n -> Int,
        (∑ i : Fin n, w i * qge2OrdinaryRowTarget n r a epsBit i)
          <= ∑ k : Fin (n - 1), qge2SignedColumnSupport n (c k) w
```

Lean already proves the contraposition wrapper:

```lean
def RoundComposite.PrefixCount
  .OrdinaryQge2SupportViolationGivesIndicatorCutGoal : Prop := ...

theorem RoundComposite.PrefixCount
  .ordinaryQge2IndicatorToFullSupportGoal_of_separation
    (hSep : OrdinaryQge2SupportViolationGivesIndicatorCutGoal) :
    OrdinaryQge2IndicatorToFullSupportGoal
```

So it is enough to prove the separation target:

```lean
def RoundComposite.PrefixCount
  .OrdinaryQge2SupportViolationGivesIndicatorCutGoal : Prop :=
  ∀ {n r : Nat},
    Even n -> 4 <= n -> Odd r -> r < n -> 0 < r ->
    ∀ (a : Fin n -> Nat) (epsBit : Fin n -> Nat) (c : Fin (n - 1) -> Nat),
      (∀ i : Fin n, a i = 1 ∨ a i = 2) ->
      (∀ i : Fin n, epsBit i = 0 ∨ epsBit i = 1) ->
      (∀ k : Fin (n - 1), c k = 1 ∨ c k = 2) ->
      (∑ i : Fin n, epsBit i) = r ->
      (∑ i : Fin n, a i) = (∑ k : Fin (n - 1), c k) ->
      ∀ w : Fin n -> Int,
        (∑ i : Fin n, w i * qge2OrdinaryRowTarget n r a epsBit i)
          > ∑ k : Fin (n - 1), qge2SignedColumnSupport n (c k) w ->
      ∃ J : Finset (Fin n),
        (∑ i ∈ J, qge2OrdinaryRowTarget n r a epsBit i)
          > ∑ k : Fin (n - 1), qge2ColumnCapacity n J.card (c k)
```

## Paper Context

For `c in {1,2}`, the paper defines

```text
C_c(L) = {x in {-2,-1,1,2}^L : sum_i x_i = -c}
U_c(j) = max_{x in C_c(L)} max_{|J|=j} sum_{i in J} x_i
```

and proves

```text
U_c(j) = min { 2j, 2(L-j)-c }.
```

Lean already has this as:

```lean
def qge2ColumnCapacity (n j c : Nat) : Int :=
  min (2 * (j : Int)) (2 * ((n - j : Nat) : Int) - (c : Int))

theorem qge2ColumnCapacity_upper_bound
    {n c : Nat} {v : Fin n -> Int}
    (hv : forall i : Fin n, IsSignedVal (v i))
    (hsum : (sum i : Fin n, v i) = - (c : Int))
    (J : Finset (Fin n)) :
    (sum i in J, v i) <= qge2ColumnCapacity n J.card c
```

The paper's row-subset cut decomposition says that the direct sum of signed
column trellises has upper HEG cuts exactly

```text
R(J) <= sum_k U_{c_k}(|J|)
```

and lower cuts are complementary once the total balance is fixed.  The new Lean
`IndicatorToFullSupport` target asks for the corresponding statement in support
function language: every violated full-support inequality for an integer weight
`w` should yield some violated row-subset/indicator cut `J`.

## Prompt

Please prove, or give a Lean-friendly proof decomposition for,
`OrdinaryQge2IndicatorToFullSupportGoal`, preferably by proving
`OrdinaryQge2SupportViolationGivesIndicatorCutGoal`.

The key task is to bridge:

```text
all row-subset cuts R(J) <= sum_k U_{c_k}(|J|)
```

to:

```text
all integer support inequalities
  <w,R> <= sum_k h_{C_{c_k}}(w)
```

for the ordinary row vector

```text
R_i = r - a_i - n eps_i,
a_i,c_k in {1,2}, eps_i in {0,1}, sum eps_i = r,
sum_i a_i = sum_k c_k.
```

The most useful answer is a short chain of auxiliary Lean theorem statements
and proof outlines.  In particular, please specify whether the proof should use:

1. Lovasz/submodular base-polyhedron separation;
2. Edmonds polymatroid intersection/base-polytope theorem;
3. sorting/level-set decomposition of integer weights `w`;
4. or a direct ordinary-row argument exploiting the two-level form of
   `R_i = r-a_i-n eps_i`.

Avoid claiming the false arbitrary-row theorem with only cardinality cuts.  The
proof must use the ordinary row shape or a standard theorem whose hypotheses
exactly match the signed-column support functions.
