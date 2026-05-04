# GPT-5.5 Pro q>=2 Full-Support Trellis Request

Date: 2026-05-04.

Purpose: ask for a Lean-facing proof of the remaining full-support signed
trellis theorem
`RoundComposite.PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal`.

Model settings requested by the user:

```text
model: gpt-5.5-pro
reasoning effort: xhigh
max_output_tokens: 100000
mode: background
```

Response id:

```text
response_id = resp_0bcd9e078159726f0069f8ebcb1594819db42229b737abe499
initial_status = queued
initial_submit_date = 2026-05-04
latest_poll_status = in_progress
latest_poll_date = 2026-05-04
final_status = pending
final_poll_date = pending
response_doc = docs/GPT55_PRO_QGE2_FULL_SUPPORT_TRELLIS_RESPONSE_20260504.md
```

## Files To Read

1. `RoundComposite/PrefixCount.lean`
2. `docs/GPT55_PRO_QGE2_TRELLIS_HOFFMAN_PROOF_RESPONSE_20260504.md`
3. `docs/GPT55_PRO_QGE2_INDICATOR_TO_FULL_SUPPORT_REQUEST_20260504.md`
4. `/data/angel/repos/etc/prefix_count_odd_tori_overhauled_v7.tex`

## Current Lean Target

```lean
def RoundComposite.PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal
    : Prop :=
  ∀ {n r : Nat},
    Even n -> 4 <= n -> Odd r -> r < n -> 0 < r ->
    ∀ (a : Fin n -> Nat) (epsBit : Fin n -> Nat) (c : Fin (n - 1) -> Nat),
      (∀ i : Fin n, a i = 1 ∨ a i = 2) ->
      (∀ i : Fin n, epsBit i = 0 ∨ epsBit i = 1) ->
      (∀ k : Fin (n - 1), c k = 1 ∨ c k = 2) ->
      (∑ i : Fin n, epsBit i) = r ->
      (∑ i : Fin n, a i) = (∑ k : Fin (n - 1), c k) ->
      (∀ w : Fin n -> Int,
        (∑ i : Fin n, w i * qge2OrdinaryRowTarget n r a epsBit i)
          <= ∑ k : Fin (n - 1), qge2SignedColumnSupport n (c k) w) ->
      ∃ X : Fin (n - 1) -> Fin n -> Int,
        (∀ k i, IsSignedVal (X k i)) ∧
        (∀ k : Fin (n - 1), (∑ i : Fin n, X k i) = - (c k : Int)) ∧
        (∀ i : Fin n,
          (∑ k : Fin (n - 1), X k i)
            = qge2OrdinaryRowTarget n r a epsBit i)
```

Definitions:

```lean
def qge2OrdinaryRowTarget (n r : Nat)
    (a epsBit : Fin n -> Nat) (i : Fin n) : Int :=
  (r : Int) - (a i : Int) - (n : Int) * (epsBit i : Int)

abbrev SignedValInt : Type := Fin 4

def SignedValInt.toInt (v : SignedValInt) : Int := ...

def qge2SignedColumnFinset (n c : Nat) :
    Finset (Fin n -> SignedValInt) := ...

noncomputable def qge2SignedColumnSupport
    (n c : Nat) (w : Fin n -> Int) : Int := ...
```

This theorem is consumed by:

```lean
theorem PrefixCount.ordinaryQge2SignedTrellisHoffmanGoal_of_fullSupport
    (hFull : OrdinaryQge2SignedFullSupportTrellisGoal)
    (hLift : OrdinaryQge2IndicatorToFullSupportGoal) :
    OrdinaryQge2SignedTrellisHoffmanGoal
```

and ultimately by:

```lean
theorem RoundComposite.Concrete
  .oddModulusToriAllDimensionsGoal_of_v4_returnTailClosedFullSupportTrellisGeometryRawEdge
    (hFull : PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal)
    (hLift : PrefixCount.OrdinaryQge2IndicatorToFullSupportGoal)
    (hGeom : OddSuccessorSmallModulusBaseTailGeometryFromHallGoal)
    (hRaw : ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal) :
    OddModulusToriAllDimensionsGoal
```

## Mathematical Meaning

For each column `k`, the feasible column set is:

```text
C_{c_k}(n) = {x in {-2,-1,1,2}^n : sum_i x_i = -c_k}
```

The hypothesis says that the ordinary row target vector `R` satisfies every
integer support inequality:

```text
<w, R> <= sum_k max_{x in C_{c_k}(n)} <w, x>
```

The conclusion asks for actual signed columns `X k` from those finite sets
whose sum is `R`.

For arbitrary integer row vectors this is not a consequence of the older
cardinality cuts; Lean already contains a counterexample to the arbitrary-row
column packing target.  This theorem is ordinary-row only.

## Prompt

Please prove, or give a Lean-friendly proof decomposition for,
`OrdinaryQge2SignedFullSupportTrellisGoal`.

Useful routes:

1. Reduce to an integral Hoffman/Edmonds-Giles theorem for the direct sum of
   the signed-column trellises.
2. Prove a specialized integer-decomposition theorem for the Minkowski sum of
   the signed-column path polytopes.
3. State the smallest external theorem that is standard enough to import/prove
   separately, then give the Lean adapter from that theorem to the target above.

The answer should identify:

- the exact finite network/trellis representation of one signed column;
- why the support inequalities are the correct separation inequalities;
- why the resulting feasible point can be chosen integral;
- how an integral feasible point decomposes into actual columns with entries
  in `{-2,-1,1,2}`;
- which hypotheses use the ordinary row shape
  `R_i = r - a_i - n * epsBit_i`.

Avoid replacing this by the false arbitrary-row theorem using only cardinality
cuts.  The output should be a chain of Lean theorem statements plus proof
outline precise enough to implement.
