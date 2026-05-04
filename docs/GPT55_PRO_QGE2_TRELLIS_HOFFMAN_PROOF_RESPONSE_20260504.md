# GPT-5.5 Pro q>=2 Trellis-Hoffman Proof Response

Date: 2026-05-04.

Response id: `resp_0078009c9235b49c0069f8dc9d25548194b2b94fd491d49cd7`.

Status: `completed`.

---

Below is the Lean-facing decomposition I would use.  It keeps the ordinary row
shape, and it does **not** assert the false arbitrary-row theorem with only
cardinality row cuts.

## 1. Add a full-support trellis cut interface

Define the true one-column support function: maximum of a linear functional over
actual signed columns, not over the box relaxation.

```lean
namespace RoundComposite.PrefixCount

def qge2OrdinaryRowTarget
    (n r : Nat) (a epsBit : Fin n → Nat) (i : Fin n) : Int :=
  (r : Int) - (a i : Int) - (n : Int) * (epsBit i : Int)

/-- Finite type of signed values. Implement using existing `IsSignedVal`. -/
def SignedValInt : Type := {z : Int // IsSignedVal z}

/-- Finite set of actual signed columns with total `-c`. -/
def qge2SignedColumnFinset (n c : Nat) :
    Finset (Fin n → SignedValInt) :=
  Finset.univ.filter
    (fun x => (∑ i : Fin n, (x i : Int)) = - (c : Int))

/-- Support function of the actual one-column signed trellis. -/
noncomputable def qge2SignedColumnSupport
    (n c : Nat) (w : Fin n → Int) : Int :=
  (((qge2SignedColumnFinset n c).image
      (fun x => ∑ i : Fin n, w i * (x i : Int))).max?).getD 0
```

Then expose this ordinary-only full-support theorem as the standard HEG/EG input:

```lean
/--
Standard finite integral Hoffman/Edmonds-Giles trellis theorem, specialized to
the ordinary q >= 2 row vector.  The cuts are full support-function cuts over
all integer weights `w`, not merely indicator/cardinality cuts.
-/
def OrdinaryQge2SignedFullSupportTrellisGoal : Prop :=
  ∀ {n r : Nat},
    Even n → 4 ≤ n → Odd r → r < n → 0 < r →
    ∀ (a : Fin n → Nat) (epsBit : Fin n → Nat) (c : Fin (n - 1) → Nat),
      (∀ i : Fin n, a i = 1 ∨ a i = 2) →
      (∀ i : Fin n, epsBit i = 0 ∨ epsBit i = 1) →
      (∀ k : Fin (n - 1), c k = 1 ∨ c k = 2) →
      (∑ i : Fin n, epsBit i) = r →
      (∑ i : Fin n, a i) = (∑ k : Fin (n - 1), c k) →
      (∀ w : Fin n → Int,
        (∑ i : Fin n,
          w i * qge2OrdinaryRowTarget n r a epsBit i)
          ≤ ∑ k : Fin (n - 1),
              qge2SignedColumnSupport n (c k) w) →
      ∃ X : Fin (n - 1) → Fin n → Int,
        (∀ k i, IsSignedVal (X k i)) ∧
        (∀ k : Fin (n - 1), (∑ i : Fin n, X k i) = - (c k : Int)) ∧
        (∀ i : Fin n,
          (∑ k : Fin (n - 1), X k i)
            = qge2OrdinaryRowTarget n r a epsBit i)
```

This is the exact standard theorem to import/prove from integral HEG or
consecutive-ones/network-matrix normality of the signed trellis path
configuration.

## 2. Add the ordinary cut-completion theorem

This is the only ordinary arithmetic theorem needed to turn the current Lean
hypothesis into the full HEG cuts.

```lean
/--
For ordinary q >= 2 row targets, the existing indicator/cardinality cuts imply
all full signed-trellis support cuts.

This theorem is deliberately ordinary-only.  It is false for arbitrary row
vectors.
-/
def OrdinaryQge2IndicatorToFullSupportGoal : Prop :=
  ∀ {n r : Nat},
    Even n → 4 ≤ n → Odd r → r < n → 0 < r →
    ∀ (a : Fin n → Nat) (epsBit : Fin n → Nat) (c : Fin (n - 1) → Nat),
      (∀ i : Fin n, a i = 1 ∨ a i = 2) →
      (∀ i : Fin n, epsBit i = 0 ∨ epsBit i = 1) →
      (∀ k : Fin (n - 1), c k = 1 ∨ c k = 2) →
      (∑ i : Fin n, epsBit i) = r →
      (∑ i : Fin n, a i) = (∑ k : Fin (n - 1), c k) →
      (∀ J : Finset (Fin n),
        (∑ i ∈ J, qge2OrdinaryRowTarget n r a epsBit i)
          ≤ ∑ k : Fin (n - 1), qge2ColumnCapacity n J.card (c k)) →
      ∀ w : Fin n → Int,
        (∑ i : Fin n,
          w i * qge2OrdinaryRowTarget n r a epsBit i)
          ≤ ∑ k : Fin (n - 1),
              qge2SignedColumnSupport n (c k) w
```

A convenient proof of this theorem is by contraposition using the exact
separation lemma:

```lean
def OrdinaryQge2SupportViolationGivesIndicatorCutGoal : Prop :=
  ∀ {n r : Nat},
    Even n → 4 ≤ n → Odd r → r < n → 0 < r →
    ∀ (a : Fin n → Nat) (epsBit : Fin n → Nat) (c : Fin (n - 1) → Nat),
      (∀ i : Fin n, a i = 1 ∨ a i = 2) →
      (∀ i : Fin n, epsBit i = 0 ∨ epsBit i = 1) →
      (∀ k : Fin (n - 1), c k = 1 ∨ c k = 2) →
      (∑ i : Fin n, epsBit i) = r →
      (∑ i : Fin n, a i) = (∑ k : Fin (n - 1), c k) →
      ∀ w : Fin n → Int,
        (∑ i : Fin n,
          w i * qge2OrdinaryRowTarget n r a epsBit i)
          > ∑ k : Fin (n - 1),
              qge2SignedColumnSupport n (c k) w →
        ∃ J : Finset (Fin n),
          (∑ i ∈ J, qge2OrdinaryRowTarget n r a epsBit i)
            > ∑ k : Fin (n - 1), qge2ColumnCapacity n J.card (c k)
```

Then:

```lean
theorem ordinaryQge2IndicatorToFullSupportGoal_of_separation
    (hSep : OrdinaryQge2SupportViolationGivesIndicatorCutGoal) :
    OrdinaryQge2IndicatorToFullSupportGoal := by
  classical
  intro n r hnEven hn4 hrOdd hrlt hrpos a epsBit c ha heps hc
    heps_sum ha_eq_c hCuts w
  by_contra hbad
  have hbad' :
      (∑ i : Fin n, w i * qge2OrdinaryRowTarget n r a epsBit i)
        > ∑ k : Fin (n - 1), qge2SignedColumnSupport n (c k) w := by
    omega
  rcases hSep hnEven hn4 hrOdd hrlt hrpos a epsBit c
      ha heps hc heps_sum ha_eq_c w hbad' with ⟨J, hJ⟩
  exact not_lt_of_ge (hCuts J) hJ
```

The proof of `OrdinaryQge2SupportViolationGivesIndicatorCutGoal` should use:

1. `qge2SignedColumnSupport_indicator`:
   ```lean
   theorem qge2SignedColumnSupport_indicator
       {n c : Nat} (hnEven : Even n) (hn4 : 4 ≤ n)
       (hc : c = 1 ∨ c = 2) (J : Finset (Fin n)) :
       qge2SignedColumnSupport n c (fun i => if i ∈ J then 1 else 0)
         = qge2ColumnCapacity n J.card c
   ```
   This is the bridge to the existing `qge2ColumnCapacity` lemmas.

2. Constant-shift and permutation lemmas for support:
   ```lean
   theorem qge2SignedColumnSupport_add_const
       {n c : Nat} (hnEven : Even n) (hn4 : 4 ≤ n)
       (hc : c = 1 ∨ c = 2) (w : Fin n → Int) (t : Int) :
       qge2SignedColumnSupport n c (fun i => w i + t)
         = qge2SignedColumnSupport n c w - (c : Int) * t
   ```

3. A sorted-weight formula for `qge2SignedColumnSupport`, maximizing over
   counts of `2,1,-1,-2`.  After sorting `w` decreasingly, the support is the
   finite maximum over tuples
   `n₂ n₁ m₁ m₂ : Nat` with
   ```lean
   n₂ + n₁ + m₁ + m₂ = n
   2*n₂ + n₁ - m₁ - 2*m₂ = -c
   ```
   of the corresponding weighted prefix expression.

4. An ordinary-only uncrossing lemma: with
   `R_i = r - a_i - n * epsBit_i`, any strict sorted support violation has a
   strict violation on one of the nested prefix sets.  This is exactly where the
   hypotheses `a_i ∈ {1,2}`, `epsBit_i ∈ {0,1}`, `∑ epsBit = r`, `Odd r`,
   `Even n`, and `0 < r < n` are used.

## 3. Final wrapper proving the requested target

Once the two auxiliary goals above are available, the current target is a short
wrapper.

```lean
theorem ordinaryQge2SignedTrellisHoffmanGoal_of_fullSupport
    (hFull : OrdinaryQge2SignedFullSupportTrellisGoal)
    (hLift : OrdinaryQge2IndicatorToFullSupportGoal) :
    OrdinaryQge2SignedTrellisHoffmanGoal := by
  classical
  intro n r hnEven hn4 hrOdd hrlt hrpos a epsBit c
    ha heps hc heps_sum ha_eq_c hCuts
  exact hFull hnEven hn4 hrOdd hrlt hrpos
    a epsBit c ha heps hc heps_sum ha_eq_c
    (hLift hnEven hn4 hrOdd hrlt hrpos
      a epsBit c ha heps hc heps_sum ha_eq_c hCuts)
```

Then the theorem wanted by the endpoint is obtained by supplying:

```lean
theorem ordinaryQge2SignedFullSupportTrellis :
    OrdinaryQge2SignedFullSupportTrellisGoal := by
  -- integral HEG / Edmonds-Giles / trellis normality proof
  ...

theorem ordinaryQge2IndicatorToFullSupport :
    OrdinaryQge2IndicatorToFullSupportGoal := by
  exact ordinaryQge2IndicatorToFullSupportGoal_of_separation
    ordinaryQge2SupportViolationGivesIndicatorCut
```

and finally:

```lean
theorem ordinaryQge2SignedTrellisHoffman :
    OrdinaryQge2SignedTrellisHoffmanGoal :=
  ordinaryQge2SignedTrellisHoffmanGoal_of_fullSupport
    ordinaryQge2SignedFullSupportTrellis
    ordinaryQge2IndicatorToFullSupport
```

## Why this avoids the false strengthening

The false arbitrary-row theorem uses only indicator cuts.  The full-support cuts
are strictly stronger.  For the known bad example
`n = 4`, three columns all `c = 2`, and
`R = (6, 0, -6, -6)`, the indicator cuts hold, but the full support cut with
`w = (1, 0, -1, -1)` fails:

```text
w · R = 18,
one-column support for c = 2 is 5,
three-column RHS = 15.
```

So the standard full-support HEG theorem does not imply the false arbitrary
row-subset packing theorem.  The only converse from indicator cuts to full
support cuts is the ordinary-only theorem above.
