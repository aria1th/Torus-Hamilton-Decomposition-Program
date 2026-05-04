# Successor Closure Internal Plan v1

Date: 2026-05-04.

This note fixes the near-term Lean goal for the successor closure.  The goal is
not to close the whole odd-tori theorem here.  It is to record the internal
Lean structure for the successor wrapper and the `q >= 2` half-slack bridge,
while moving the finite Hoffman/de Werra combinatorics to a separate module.

## Target

The final theorem remains:

```lean
theorem odd_modulus_tori_all_dimensions
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

The current Lean package target is:

```lean
RoundComposite.Concrete.OddModulusToriAllDimensionsGoal
```

For this internal-plan step, the success criterion is narrower:

```text
Record the Lean-closed successor wrapper, and fix the internal q>=2
half-slack proof checklist that will feed
PrefixCount.OrdinaryQge2IndicatorToFullSupportGoal.
```

## 1. Successor Closure Wrapper

The dispatcher from small seeds plus successor closure is already closed in
Lean:

```lean
def RoundComposite.Concrete.OddSuccessorClosureGoal : Prop :=
  forall {b m : Nat},
    5 <= b ->
    Odd m -> 3 <= m ->
    StandardCayleySolved b m ->
    StandardCayleySolved (2 * b + 1) m

theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_357_and_successor
    (hSucc : OddSuccessorClosureGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

This uses only:

```text
D2, D3, D5, D7 seeds
product closure
successor closure b -> 2*b + 1
```

The successor closure itself is closed by the high/small split:

```lean
theorem RoundComposite.Concrete
  .oddSuccessorClosureGoal_of_successorHigh_and_successorSmall
    (hHigh : OddSuccessorHighModulusPrefixCountGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddSuccessorClosureGoal
```

The branch split is exactly:

```text
m >= 2*b + 1 : OddSuccessorHighModulusPrefixCountGoal
m <  2*b + 1 : OddSuccessorSmallModulusBaseTailGoal
```

Pointwise successor theorem already exposed:

```lean
theorem RoundComposite.Concrete
  .odd_successor_closure_of_successorHigh_and_successorSmall
    (hHigh : OddSuccessorHighModulusPrefixCountGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {b m : Nat}
    (hb5 : 5 <= b)
    (hmodd : Odd m) (hm3 : 3 <= m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2 * b + 1) m
```

No additional Lean work is planned for this wrapper unless later module splits
change theorem names.

## 2. High Branch Interface

The high branch is:

```lean
def RoundComposite.Concrete.OddSuccessorHighModulusPrefixCountGoal : Prop :=
  forall {b m : Nat},
    5 <= b -> Odd m -> 2 * b + 1 <= m ->
      StandardCayleySolved (2 * b + 1) m
```

The current preferred route closes it through the q>=2 signed trellis plus the
already Lean-closed first-hit return-tail chain:

```lean
PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal
```

That trellis goal is split as:

```lean
def PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal : Prop := ...
def PrefixCount.OrdinaryQge2IndicatorToFullSupportGoal : Prop := ...

theorem PrefixCount.ordinaryQge2SignedTrellisHoffmanGoal_of_fullSupport
    (hFull : OrdinaryQge2SignedFullSupportTrellisGoal)
    (hLift : OrdinaryQge2IndicatorToFullSupportGoal) :
    OrdinaryQge2SignedTrellisHoffmanGoal
```

For this internal plan, only `hLift` is in scope.  The full-support finite
Hoffman theorem `hFull` is out of scope and should be proved in a separate
finite-combinatorics module.

## 3. Half-Slack q>=2 Internal Goal

Do not attack this field directly:

```lean
PrefixCount.OrdinaryQge2IndicatorToFullSupportGoal
```

Instead, the internal target is the two-field half-slack split:

```lean
PrefixCount.Qge2IndicatorCutsHalfSlackToSupportGoal
PrefixCount.Qge2OrdinaryHalfSlackGoal
```

Lean already has the bridge:

```lean
theorem PrefixCount.ordinaryQge2IndicatorToFullSupportGoal_of_halfSlackBridge
    (hBridge : PrefixCount.Qge2IndicatorCutsHalfSlackToSupportGoal)
    (hHalf : PrefixCount.Qge2OrdinaryHalfSlackGoal) :
    PrefixCount.OrdinaryQge2IndicatorToFullSupportGoal
```

So the immediate implementation plan is:

```text
Qge2IndicatorCutsHalfSlackToSupportGoal
+ Qge2OrdinaryHalfSlackGoal
=> OrdinaryQge2IndicatorToFullSupportGoal
=> OrdinaryQge2SignedTrellisHoffmanGoal, once hFull is imported
```

## 4. Level-Set Decomposition Checklist

The generic bridge should be proved by decomposing an arbitrary integer weight
`w : Fin n -> Int` into a constant plus nonnegative level sets.

Proposed helper statements:

```lean
lemma exists_nat_shift_of_int_weight {n : Nat} (w : Fin n -> Int) :
    exists (lo : Int) (u : Fin n -> Nat) (D : Nat),
      (forall i, w i = lo + (u i : Int)) /\
      (forall i, u i <= D)
```

```lean
lemma int_weight_dot_eq_nat_upperLevels {n : Nat}
    (R w : Fin n -> Int) (lo : Int) (u : Fin n -> Nat) (D : Nat)
    (hw : forall i, w i = lo + (u i : Int))
    (hD : forall i, u i <= D) :
    (sum i : Fin n, w i * R i)
      =
    lo * (sum i : Fin n, R i)
      + sum t in Finset.range D,
          sum i in PrefixCount.qge2UpperLevel u t, R i
```

Existing definitions:

```lean
def PrefixCount.qge2UpperLevel {n : Nat}
    (u : Fin n -> Nat) (t : Nat) : Finset (Fin n)

def PrefixCount.qge2HalfLevelPenalty
    (n : Nat) (u : Fin n -> Nat) (t : Nat) : Int
```

Proof notes:

```text
1. Choose lo below every coordinate of w.
2. Define u i = Int.toNat (w i - lo).
3. Use u i = sum_{t < D} 1_{t < u i}.
4. Exchange finite sums.
```

This is pure `Finset` bookkeeping and should stay in `PrefixCount`.

## 5. Signed Column Support With Half-Level Penalty

The bridge needs a lower bound on the signed-column support.  The `c = 2`
column has a one-unit defect at the middle level `j = n / 2`; this is why the
plain indicator-cut-to-support theorem is not the right target.

Proposed one-column helper:

```lean
theorem qge2SignedColumnSupport_ge_levelCapacity_sub_halfPenalty
    {n c : Nat}
    (hnEven : Even n) (hn4 : 4 <= n)
    (hc : c = 1 \/ c = 2)
    (w : Fin n -> Int) (lo : Int) (u : Fin n -> Nat) (D : Nat)
    (hw : forall i, w i = lo + (u i : Int))
    (hD : forall i, u i <= D) :
    lo * (-(c : Int))
      + sum t in Finset.range D,
          (PrefixCount.qge2ColumnCapacity n
              (PrefixCount.qge2UpperLevel u t).card c
            - PrefixCount.qge2HalfLevelPenalty n u t)
      <= PrefixCount.qge2SignedColumnSupport n c w
```

Proposed summed helper:

```lean
theorem qge2SignedColumnSupport_sum_ge_levelCapacity_sub_halfPenalty
    {n : Nat}
    (hnEven : Even n) (hn4 : 4 <= n)
    (c : Fin (n - 1) -> Nat)
    (hc : forall k, c k = 1 \/ c k = 2)
    (w : Fin n -> Int) (lo : Int) (u : Fin n -> Nat) (D : Nat)
    (hw : forall i, w i = lo + (u i : Int))
    (hD : forall i, u i <= D) :
    lo * (-(sum k : Fin (n - 1), (c k : Int)))
      + sum t in Finset.range D,
          ((sum k : Fin (n - 1),
              PrefixCount.qge2ColumnCapacity n
                (PrefixCount.qge2UpperLevel u t).card (c k))
            - (((n - 1 : Nat) : Int) *
                PrefixCount.qge2HalfLevelPenalty n u t))
      <= sum k : Fin (n - 1),
          PrefixCount.qge2SignedColumnSupport n (c k) w
```

Proof notes:

```text
c = 1: choose the sorted signed column pattern
  2, ..., 2, 1, -2, ..., -2.

c = 2: choose the sorted signed column pattern
  2, ..., 2, -1, -1, -2, ..., -2.

For every upper level S, the prefix sum is qge2ColumnCapacity n S.card c,
except for c = 2 at S.card = n/2, where it is smaller by exactly 1.
```

This remains an internal `PrefixCount` proof because it is highly specialized
to the local signed alphabet and `qge2ColumnCapacity`.

## 6. Indicator Cuts Plus Half-Slack

The target theorem is already exposed:

```lean
def PrefixCount.Qge2IndicatorCutsHalfSlackToSupportGoal : Prop :=
  forall {n : Nat},
    Even n -> 4 <= n ->
    forall (c : Fin (n - 1) -> Nat),
      (forall k : Fin (n - 1), c k = 1 \/ c k = 2) ->
      forall (R : Fin n -> Int),
        (sum i : Fin n, R i)
          = - (sum k : Fin (n - 1), (c k : Int)) ->
        (forall J : Finset (Fin n),
          (sum i in J, R i)
            <= sum k : Fin (n - 1),
                PrefixCount.qge2ColumnCapacity n J.card (c k)) ->
        (forall J : Finset (Fin n), J.card = n / 2 ->
          (sum i in J, R i)
            <= (sum k : Fin (n - 1),
                PrefixCount.qge2ColumnCapacity n J.card (c k))
                - ((n - 1 : Nat) : Int)) ->
        forall w : Fin n -> Int,
          (sum i : Fin n, w i * R i)
            <= sum k : Fin (n - 1),
                PrefixCount.qge2SignedColumnSupport n (c k) w
```

Implementation route:

```text
1. Apply exists_nat_shift_of_int_weight to w.
2. Rewrite dot product by int_weight_dot_eq_nat_upperLevels.
3. Rewrite the constant term using the total-sum hypothesis.
4. For each level set S_t:
   - if S_t.card = n/2, use hHalf;
   - otherwise use hCuts.
5. Sum the resulting inequalities.
6. Compare against
   qge2SignedColumnSupport_sum_ge_levelCapacity_sub_halfPenalty.
```

Expected Lean pressure points:

```text
Finset.sum_comm
Finset.sum_le_sum
Int/Nat casts for (n - 1 : Nat) : Int
case split on (qge2UpperLevel u t).card = n / 2
normalizing qge2HalfLevelPenalty
```

## 7. Ordinary Row Half-Size Slack

The second internal target is:

```lean
def PrefixCount.Qge2OrdinaryHalfSlackGoal : Prop := ...
```

Concrete proof target:

```lean
theorem qge2OrdinaryRowTarget_halfLevel_le_capacity_sub_allColumns
    {n r : Nat}
    (hnEven : Even n) (hn4 : 4 <= n)
    (hrlt : r < n) (hrpos : 0 < r)
    (a epsBit : Fin n -> Nat) (c : Fin (n - 1) -> Nat)
    (ha : forall i : Fin n, a i = 1 \/ a i = 2)
    (heps : forall i : Fin n, epsBit i = 0 \/ epsBit i = 1)
    (hc : forall k : Fin (n - 1), c k = 1 \/ c k = 2)
    (hepsSum : (sum i : Fin n, epsBit i) = r)
    (J : Finset (Fin n)) (hJ : J.card = n / 2) :
    (sum i in J, PrefixCount.qge2OrdinaryRowTarget n r a epsBit i)
      <= (sum k : Fin (n - 1),
            PrefixCount.qge2ColumnCapacity n J.card (c k))
          - ((n - 1 : Nat) : Int)
```

Proof outline:

```text
Let n = 2*m and J.card = m.

Upper bound row target on J:
  sum_J ((r : Int) - a_i - n * eps_i)
  <= m*(r - 1) - n * eps(J),
because each a_i >= 1.

If r <= m:
  eps(J) >= 0, so row sum <= m*(m - 1).

If r > m:
  the complement has m elements and epsBit <= 1, so eps(J) >= r - m;
  again row sum <= m*(m - 1).

At half-size, each column capacity satisfies enough slack:
  qge2ColumnCapacity n (n/2) (c k)
is at least the needed per-column contribution, and summing over n-1 columns
pays the global -(n-1) penalty.
```

Suggested helper lemmas:

```lean
lemma qge2ColumnCapacity_half_of_one
    (hnEven : Even n) :
    PrefixCount.qge2ColumnCapacity n (n / 2) 1 = ...

lemma qge2ColumnCapacity_half_of_two
    (hnEven : Even n) :
    PrefixCount.qge2ColumnCapacity n (n / 2) 2 = ...

lemma sum_eps_on_half_lower_bound
    (heps : forall i, epsBit i = 0 \/ epsBit i = 1)
    (hepsSum : (sum i, epsBit i) = r)
    (hJ : J.card = n / 2) :
    ...
```

This proof is arithmetic-heavy but local.  It should remain inside
`PrefixCount`, possibly after moving the half-slack helpers to a new file such
as:

```text
RoundComposite/PrefixCountHalfSlack.lean
```

if `PrefixCount.lean` becomes too large.  Do not use
`RoundComposite/PrefixCount/HalfSlack.lean` unless `PrefixCount.lean` is first
refactored into a directory module, because the current repository already has
`RoundComposite/PrefixCount.lean` as a file.

## 8. Out Of Scope For This Goal

The following are not part of the internal half-slack goal:

```lean
PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal
ActiveHall.FiniteHoffman.CompatibleDeWerraGoal
ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal
ActiveHall.FiniteHoffman.ExactEdgeColoringGoal
```

They should be proved in a separate finite-combinatorics module/folder and
then imported into the successor closure chain.

Recommended future module boundary:

```text
RoundComposite/FiniteHoffman/
  Basic.lean
  EdgeColoring.lean
  SignedTrellis.lean
```

Expected imports into the main chain:

```lean
import RoundComposite.FiniteHoffman.EdgeColoring
import RoundComposite.FiniteHoffman.SignedTrellis
```

The small-modulus geometry field is also not solved by this note:

```lean
OddSuccessorSmallModulusBaseTailGeometryFromHallGoal
```

It is a project-specific geometry glue theorem.  It should be planned after
the finite Hall/edge-colouring API is stable, because its cleanest statement
depends on the exact imported realization theorem.

## Completion Checklist For This Plan

- The successor wrapper and high/small split are identified by exact Lean
  theorem names.
- The q>=2 internal target is fixed as the pair
  `Qge2IndicatorCutsHalfSlackToSupportGoal` and
  `Qge2OrdinaryHalfSlackGoal`.
- The level-set decomposition lemma is named and scoped.
- The signed-column support lower bound with half-level penalty is named and
  scoped.
- The ordinary half-size slack inequality is named and scoped.
- The bridge to `OrdinaryQge2IndicatorToFullSupportGoal` is already present in
  Lean and recorded here.
- Finite Hoffman/de Werra and raw/exact edge-colouring are explicitly out of
  scope for this internal goal and assigned to a future separate module.
