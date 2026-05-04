# GPT-5.5 Pro q>=2 Indicator-To-Full-Support Response

Date: 2026-05-04.

Response id: `resp_0c636bbdc33191c10069f8e747ade0819c8ef13cac38681513`.

Status: `completed`.

---

Use route **(3)+(4)**: integer level-set decomposition, plus one extra ordinary-row slack lemma at half-size sets. Do **not** use the plain Lovasz/base-polyhedron theorem alone: for `c = 2` the signed column misses the value `0`, so the Lovasz extension of `U₂` can overestimate the true support. The ordinary row shape supplies enough slack to pay for exactly this defect.

Below is the Lean-facing decomposition I would implement.

```lean
namespace RoundComposite.PrefixCount

open scoped BigOperators

def qge2UpperLevel {n : Nat} (u : Fin n → Nat) (t : Nat) : Finset (Fin n) :=
  Finset.univ.filter (fun i => t < u i)

def qge2HalfLevelPenalty (n : Nat) (u : Fin n → Nat) (t : Nat) : Int :=
  if (qge2UpperLevel u t).card = n / 2 then 1 else 0
```

### 1. Generic integer layer decomposition

Use a Nat-shift of an arbitrary integer weight.

```lean
lemma exists_nat_shift_of_int_weight {n : Nat} (w : Fin n → Int) :
    ∃ (lo : Int) (u : Fin n → Nat) (D : Nat),
      (∀ i, w i = lo + (u i : Int)) ∧
      (∀ i, u i ≤ D)
```

One easy proof: take `lo = - (∑ i, (w i).natAbs : Nat)`, `u i = Int.toNat (w i - lo)`, and `D = ∑ i, u i`.

Then prove the layer identity:

```lean
lemma int_weight_dot_eq_nat_upperLevels {n : Nat}
    (R w : Fin n → Int) (lo : Int) (u : Fin n → Nat) (D : Nat)
    (hw : ∀ i, w i = lo + (u i : Int))
    (hD : ∀ i, u i ≤ D) :
    (∑ i : Fin n, w i * R i)
      =
    lo * (∑ i : Fin n, R i)
      + ∑ t in Finset.range D,
          ∑ i in qge2UpperLevel u t, R i
```

This is just `u i = ∑ t in range D, if t < u i then 1 else 0`.

---

### 2. The needed signed-column support lower bound

This is the key replacement for the false arbitrary Lovasz theorem. Prove the following weak but sufficient support lower bound:

```lean
theorem qge2SignedColumnSupport_ge_levelCapacity_sub_halfPenalty
    {n c : Nat}
    (hnEven : Even n) (hn4 : 4 ≤ n)
    (hc : c = 1 ∨ c = 2)
    (w : Fin n → Int) (lo : Int) (u : Fin n → Nat) (D : Nat)
    (hw : ∀ i, w i = lo + (u i : Int))
    (hD : ∀ i, u i ≤ D) :
    lo * (-(c : Int))
      + ∑ t in Finset.range D,
          (qge2ColumnCapacity n (qge2UpperLevel u t).card c
            - qge2HalfLevelPenalty n u t)
      ≤ qge2SignedColumnSupport n c w
```

Proof idea:

* Sort the rows in weakly decreasing order of `u`.
* Write `n = 2*m`.
* For `c = 1`, use the signed column pattern

  ```text
  2,...,2︸ m-1 times, 1, -2,...,-2︸ m times
  ```

  Its prefix sums are exactly `qge2ColumnCapacity n j 1`.

* For `c = 2`, use the pattern

  ```text
  2,...,2︸ m-1 times, -1, -1, -2,...,-2︸ m-1 times
  ```

  Its prefix sums are exactly `qge2ColumnCapacity n j 2` except at `j = m = n/2`, where they are smaller by `1`.

Thus for every upper level set `S_t = {i | t < u i}`, the chosen column has

```lean
∑ i in S_t, v_i.toInt
  ≥ qge2ColumnCapacity n S_t.card c - qge2HalfLevelPenalty n u t
```

and layer-expanding `∑ i, w i * v_i.toInt` gives the theorem.

For summing over all columns, package the previous theorem as:

```lean
theorem qge2SignedColumnSupport_sum_ge_levelCapacity_sub_halfPenalty
    {n : Nat}
    (hnEven : Even n) (hn4 : 4 ≤ n)
    (c : Fin (n - 1) → Nat)
    (hc : ∀ k, c k = 1 ∨ c k = 2)
    (w : Fin n → Int) (lo : Int) (u : Fin n → Nat) (D : Nat)
    (hw : ∀ i, w i = lo + (u i : Int))
    (hD : ∀ i, u i ≤ D) :
    lo * (-(∑ k : Fin (n - 1), (c k : Int)))
      + ∑ t in Finset.range D,
          ((∑ k : Fin (n - 1),
              qge2ColumnCapacity n (qge2UpperLevel u t).card (c k))
            - (((n - 1 : Nat) : Int) * qge2HalfLevelPenalty n u t))
      ≤ ∑ k : Fin (n - 1), qge2SignedColumnSupport n (c k) w
```

This is just summing the one-column bound and using `Fintype.card (Fin (n - 1)) = n - 1`.

---

### 3. Abstract bridge: cuts plus half-slack imply support

This is the clean reusable theorem. Notice the extra `hHalf`; without it, the theorem is false.

```lean
theorem qge2_indicatorCuts_halfSlack_to_support
    {n : Nat}
    (hnEven : Even n) (hn4 : 4 ≤ n)
    (c : Fin (n - 1) → Nat)
    (hc : ∀ k, c k = 1 ∨ c k = 2)
    (R : Fin n → Int)
    (hTotal :
      (∑ i : Fin n, R i)
        = - (∑ k : Fin (n - 1), (c k : Int)))
    (hCuts :
      ∀ J : Finset (Fin n),
        (∑ i in J, R i)
          ≤ ∑ k : Fin (n - 1),
              qge2ColumnCapacity n J.card (c k))
    (hHalf :
      ∀ J : Finset (Fin n), J.card = n / 2 →
        (∑ i in J, R i)
          ≤ (∑ k : Fin (n - 1),
                qge2ColumnCapacity n J.card (c k))
              - ((n - 1 : Nat) : Int)) :
    ∀ w : Fin n → Int,
      (∑ i : Fin n, w i * R i)
        ≤ ∑ k : Fin (n - 1), qge2SignedColumnSupport n (c k) w
```

Proof:

1. Choose `lo,u,D` using `exists_nat_shift_of_int_weight`.
2. Expand the left side by `int_weight_dot_eq_nat_upperLevels`.
3. Use `hTotal` for the constant level.
4. For each level set `S_t`:
   * if `S_t.card = n / 2`, use `hHalf`;
   * otherwise use `hCuts`.
5. Compare with `qge2SignedColumnSupport_sum_ge_levelCapacity_sub_halfPenalty`.

---

### 4. Ordinary row supplies the half-slack

First total balance:

```lean
lemma qge2OrdinaryRowTarget_sum_eq_neg_columnSum
    {n r : Nat}
    (a epsBit : Fin n → Nat) (c : Fin (n - 1) → Nat)
    (hepsSum : (∑ i : Fin n, epsBit i) = r)
    (haSum : (∑ i : Fin n, a i) = (∑ k : Fin (n - 1), c k)) :
    (∑ i : Fin n, qge2OrdinaryRowTarget n r a epsBit i)
      = - (∑ k : Fin (n - 1), (c k : Int))
```

Then the ordinary half-size slack:

```lean
theorem qge2OrdinaryRowTarget_halfLevel_le_capacity_sub_allColumns
    {n r : Nat}
    (hnEven : Even n) (hn4 : 4 ≤ n)
    (hrlt : r < n) (hrpos : 0 < r)
    (a epsBit : Fin n → Nat) (c : Fin (n - 1) → Nat)
    (ha : ∀ i : Fin n, a i = 1 ∨ a i = 2)
    (heps : ∀ i : Fin n, epsBit i = 0 ∨ epsBit i = 1)
    (hc : ∀ k : Fin (n - 1), c k = 1 ∨ c k = 2)
    (hepsSum : (∑ i : Fin n, epsBit i) = r)
    (J : Finset (Fin n)) (hJ : J.card = n / 2) :
    (∑ i in J, qge2OrdinaryRowTarget n r a epsBit i)
      ≤ (∑ k : Fin (n - 1),
            qge2ColumnCapacity n J.card (c k))
          - ((n - 1 : Nat) : Int)
```

Proof sketch:

* Write `n = 2*m`, so `J.card = m`.
* Since `a_i ≥ 1`,

  ```text
  R(J) ≤ m*(r - 1) - n * eps(J).
  ```

* If `r ≤ m`, then `R(J) ≤ m*(m - 1)`.
* If `r > m`, the complement of `J` has `m` elements and each `epsBit ≤ 1`, so `eps(J) ≥ r - m`; again `R(J) ≤ m*(m - 1)`.
* For each column, at half-size,

  ```text
  qge2ColumnCapacity n (n/2) c_k - 1 ≥ n - 3.
  ```

  because `c_k ∈ {1,2}`.
* Therefore

  ```text
  ∑_k qge2ColumnCapacity n (n/2) c_k - (n-1)
    ≥ (n-1)*(n-3)
    ≥ m*(m-1).
  ```

The final quadratic comparison is a small `nlinarith` after `n = 2*m`, `2 ≤ m`.

---

### 5. Separation target

Now the separation endpoint is short.

```lean
theorem ordinaryQge2SupportViolationGivesIndicatorCutGoal :
    OrdinaryQge2SupportViolationGivesIndicatorCutGoal := by
  intro n r hnEven hn4 hrOdd hrlt hrpos
  intro a epsBit c ha heps hc hepsSum haSum
  intro w hviol

  let R : Fin n → Int :=
    fun i => qge2OrdinaryRowTarget n r a epsBit i

  by_contra hno

  have hCuts :
      ∀ J : Finset (Fin n),
        (∑ i in J, R i)
          ≤ ∑ k : Fin (n - 1),
              qge2ColumnCapacity n J.card (c k) := by
    intro J
    apply le_of_not_gt
    intro hJ
    exact hno ⟨J, by simpa [R] using hJ⟩

  have hTotal :
      (∑ i : Fin n, R i)
        = - (∑ k : Fin (n - 1), (c k : Int)) := by
    simpa [R] using
      qge2OrdinaryRowTarget_sum_eq_neg_columnSum
        a epsBit c hepsSum haSum

  have hHalf :
      ∀ J : Finset (Fin n), J.card = n / 2 →
        (∑ i in J, R i)
          ≤ (∑ k : Fin (n - 1),
                qge2ColumnCapacity n J.card (c k))
              - ((n - 1 : Nat) : Int) := by
    intro J hJ
    simpa [R] using
      qge2OrdinaryRowTarget_halfLevel_le_capacity_sub_allColumns
        hnEven hn4 hrlt hrpos a epsBit c ha heps hc hepsSum J hJ

  have hle :
      (∑ i : Fin n, w i * R i)
        ≤ ∑ k : Fin (n - 1), qge2SignedColumnSupport n (c k) w :=
    qge2_indicatorCuts_halfSlack_to_support
      hnEven hn4 c hc R hTotal hCuts hHalf w

  exact (not_lt_of_ge hle) (by simpa [R] using hviol)
```

Then the requested full-support theorem follows from the existing wrapper:

```lean
theorem ordinaryQge2IndicatorToFullSupportGoal :
    OrdinaryQge2IndicatorToFullSupportGoal :=
  ordinaryQge2IndicatorToFullSupportGoal_of_separation
    ordinaryQge2SupportViolationGivesIndicatorCutGoal
```

The essential point is the extra half-size slack. It pays for the single missing `0` in the `c = 2` signed column greedy prefix. This avoids the false arbitrary-row theorem while keeping the proof mostly level-set/sorting arithmetic.