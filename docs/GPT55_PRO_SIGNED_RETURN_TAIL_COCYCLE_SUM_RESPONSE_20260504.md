Below is the Lean interface I would add.  The key is to make the signed local coefficient explicit and prove one fixed-`t` local first-hit count.  After that, the final target is just sum reordering + the closed layer-count and matrix-conversion lemmas.

---

## 1. Signed coefficient

```lean
namespace RoundComposite.Concrete

open scoped BigOperators

abbrev prefixCountReturnTailDeltaCol {d : Nat} (hd2 : 2 ≤ d) : Fin d :=
  ⟨1, by omega⟩

abbrev prefixCountReturnTailStepCol {d k : Nat} (hk : k < d - 2) : Fin d :=
  ⟨k + 2, by omega⟩

def prefixCountReturnTailSignedCoeff
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {k : Nat} (hk : k < d - 2) (s : Fin d) : ZMod m :=
  ((-1 : ZMod m) ^ (k + 1)) *
    ((if s = prefixCountReturnTailStepCol hk then (1 : ZMod m) else 0) -
     (if s = prefixCountReturnTailDeltaCol hd2 then (1 : ZMod m) else 0))
```

So the coefficient is

```lean
-- Delta-symbol contribution
prefixCountReturnTailSignedCoeff hd2 hk (prefixCountReturnTailDeltaCol hd2)
  = -((-1 : ZMod m) ^ (k + 1))

-- k+2-symbol contribution
prefixCountReturnTailSignedCoeff hd2 hk (prefixCountReturnTailStepCol hk)
  = ((-1 : ZMod m) ^ (k + 1))

-- middle/other symbols contribute 0
```

This avoids any unsigned strengthening.

---

## 2. The main missing local theorem

The most useful cut is the following fixed-`t` theorem.

```lean
theorem prefixCountFirstHitReturnTail_local_hitCondition_sum_eq_signedCoeff
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d}
    (hdOdd : Odd d) (hd5 : 5 ≤ d) (hmOdd : Odd m) (hdm : d ≤ m)
    (hC : C.Admissible m)
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) {k : Nat} (hk : k < d - 2)
    {t : Nat} (ht : t ∈ Finset.range m) :
  (∑ x : Fin k → ZMod m,
    ∑ u in Finset.range m,
      if prefixCountFirstHitReturnFiberHitCondition hd2 L c
          (((prefixCountFirstHitReturnBaseStep C c)^[u]) 0)
          (Shared.skewFiberIterate
            (prefixCountFirstHitReturnBaseStep C c)
            (prefixCountFirstHitReturnFiberStep hd2 L c)
            u 0
            (Shared.zmodVectorExtendZero (Nat.le_of_lt hk) x))
          ⟨k, hk⟩ t
      then (1 : ZMod m) else 0)
  =
  prefixCountReturnTailSignedCoeff hd2 hk
    (L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c)
```

This is the finite first-hit count.  It should be proved by exposing the low-prefix residual vector used by `prefixCountCanonicalRho`.

Recommended helper interface:

```lean
/--
The first `k+1` rho-test residuals, shifted so that a hit is residual `0`.
This is extracted after the schedule `prefixMap c t` from the state produced
by the `u` base iterate and the skew-fiber iterate from `x`.
-/
def prefixCountFirstHitReturnLowResidual
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) (k : Nat) (hk : k < d - 2)
    (t u : Nat) (x : Fin k → ZMod m) :
    Fin (k + 1) → ZMod m :=
  -- definition by unfolding the rho-test coordinates, subtracting their hit values
  sorry
```

Then prove the reindexing theorem:

```lean
theorem prefixCountFirstHitReturn_lowResidual_reindex_sum
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d}
    (hdOdd : Odd d) (hd5 : 5 ≤ d) (hmOdd : Odd m) (hdm : d ≤ m)
    (hC : C.Admissible m)
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) {k : Nat} (hk : k < d - 2)
    {t : Nat} (ht : t ∈ Finset.range m)
    (F : (Fin (k + 1) → ZMod m) → ZMod m) :
  (∑ x : Fin k → ZMod m,
    ∑ u in Finset.range m,
      F (prefixCountFirstHitReturnLowResidual hd2 L c k hk t u x))
  =
  ∑ y : Fin (k + 1) → ZMod m, F y
```

Proof sketch: convert the `u ∈ range m` coordinate to a `ZMod m` coordinate, then apply the already-proved lower-triangular odometer/bijection theorem.  The coordinate form should be triangular:

```text
y₀       = unit * u + constant
yᵢ₊₁     = unitᵢ * xᵢ + function of earlier coordinates
```

The only non-generic check is that the base orbit supplied by `C.zero c` is a unit/permutation modulo `m`.

Then prove the rho-event descriptions:

```lean
def pcNoZero {m n : Nat} [NeZero m] (y : Fin n → ZMod m) : Prop :=
  ∀ i, y i ≠ 0

def pcExactLastZero {m k : Nat} [NeZero m]
    (y : Fin (k + 1) → ZMod m) : Prop :=
  (∀ i : Fin k, y i.castSucc ≠ 0) ∧ y (Fin.last k) = 0

def pcHitBeforeLastZero {m k : Nat} [NeZero m]
    (y : Fin (k + 1) → ZMod m) : Prop :=
  ∃ i : Fin k, y i.castSucc = 0
```

The hit-condition rewrite should be:

```lean
theorem prefixCountFirstHitReturnFiberHitCondition_lowResidual_iff
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d}
    (hdOdd : Odd d) (hd5 : 5 ≤ d) (hmOdd : Odd m) (hdm : d ≤ m)
    (hC : C.Admissible m)
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) {k : Nat} (hk : k < d - 2)
    {t u : Nat} (ht : t ∈ Finset.range m)
    (x : Fin k → ZMod m) :
  let z :=
    (((prefixCountFirstHitReturnBaseStep C c)^[u]) 0)
  let tail :=
    Shared.skewFiberIterate
      (prefixCountFirstHitReturnBaseStep C c)
      (prefixCountFirstHitReturnFiberStep hd2 L c)
      u 0
      (Shared.zmodVectorExtendZero (Nat.le_of_lt hk) x)
  let s :=
    L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c
  let y :=
    prefixCountFirstHitReturnLowResidual hd2 L c k hk t u x
  prefixCountFirstHitReturnFiberHitCondition hd2 L c z tail ⟨k, hk⟩ t
  ↔
    (s = prefixCountReturnTailDeltaCol hd2 ∧ pcExactLastZero y) ∨
    (s.val = k + 1 ∧ 1 < s.val ∧ pcHitBeforeLastZero y) ∨
    (s = prefixCountReturnTailStepCol hk ∧ pcNoZero y)
```

This is where `prefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal` is used: it lets the full skew state be replaced by the low-prefix residual data.

---

## 3. Pure finite first-hit counts

These are independent of the prefix-count machinery.

```lean
theorem zmod_sum_pcNoZero
    {m n : Nat} [NeZero m] :
  (∑ y : Fin n → ZMod m,
    if pcNoZero y then (1 : ZMod m) else 0)
  =
  (-1 : ZMod m) ^ n
```

```lean
theorem zmod_sum_pcSomeZero
    {m n : Nat} [NeZero m] (hn : 0 < n) :
  (∑ y : Fin n → ZMod m,
    if (∃ i, y i = 0) then (1 : ZMod m) else 0)
  =
  -((-1 : ZMod m) ^ n)
```

```lean
theorem zmod_sum_pcExactLastZero
    {m k : Nat} [NeZero m] :
  (∑ y : Fin (k + 1) → ZMod m,
    if pcExactLastZero y then (1 : ZMod m) else 0)
  =
  -((-1 : ZMod m) ^ (k + 1))
```

```lean
theorem zmod_sum_pcHitBeforeLastZero
    {m k : Nat} [NeZero m] :
  (∑ y : Fin (k + 1) → ZMod m,
    if pcHitBeforeLastZero y then (1 : ZMod m) else 0)
  =
  0
```

Proof sketches:

* `pcNoZero`: product-sum factorization gives  
  `∏ i, (∑ z : ZMod m, if z ≠ 0 then 1 else 0) = (-1)^n`.
* `pcSomeZero`: complement of `pcNoZero`; total cardinality is `m^n = 0` in `ZMod m` when `0 < n`.
* `pcExactLastZero`: first `k` coordinates nonzero and last coordinate zero, so count is `(m - 1)^k`, which is `(-1)^k = -(-1)^(k+1)`.
* `pcHitBeforeLastZero`: the predicate depends only on the first `k` coordinates, leaving the last coordinate free, hence a factor `m = 0` in `ZMod m`.

Important: the Delta clause is naturally the `pcExactLastZero` event, not literally the whole `pcSomeZero` event, although both have the same value modulo `m`.

---

## 4. Layer-symbol count

Once the fixed-`t` local theorem is available, the layer count is clean:

```lean
theorem prefixCountReturnTailSignedCoeff_layer_sum_eq_matrix
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) {k : Nat} (hk : k < d - 2) :
  (∑ t in Finset.range m,
    prefixCountReturnTailSignedCoeff hd2 hk
      (L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c))
  =
  ((-1 : ZMod m) ^ (k + 1)) *
    ((((C.toMatrix hd2) c (prefixCountReturnTailStepCol hk) : Nat) : ZMod m) -
     (((C.toMatrix hd2) c (prefixCountReturnTailDeltaCol hd2) : Nat) : ZMod m))
```

Proof sketch: unfold `prefixCountReturnTailSignedCoeff`, pull out the constant sign, and apply

```lean
prefixCountLayerCount_range_eq_matrix_zmod
```

twice, once with `s = prefixCountReturnTailStepCol hk` and once with `s = prefixCountReturnTailDeltaCol hd2`.

---

## 5. Final target proof skeleton

After the local theorem and layer theorem:

```lean
theorem prefixCountFirstHitReturnTailCocycle_signed_sum_goal :
  RoundComposite.Concrete.PrefixCountFirstHitReturnTailCocycleSumGoal := by
  classical
  intro d m hne hd2 C hdOdd hd5 hmOdd hdm hC L c k hk

  let ε : ZMod m := (-1 : ZMod m) ^ (k + 1)
  let Δ : Fin d := prefixCountReturnTailDeltaCol hd2
  let R : Fin d := prefixCountReturnTailStepCol hk

  calc
    (∑ x : Fin k → ZMod m,
      prefixCountFirstHitReturnTailCocycle hd2 L c k hk x)
        =
      ∑ t in Finset.range m,
        prefixCountReturnTailSignedCoeff hd2 hk
          (L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c) := by
          -- Expand using prefixCountFirstHitReturnTailCocycle_eq_sum_hitCondition.
          -- Commute sums:
          --   ∑ x ∑ u ∑ t  ->  ∑ t ∑ x ∑ u
          -- Then apply prefixCountFirstHitReturnTail_local_hitCondition_sum_eq_signedCoeff.
          sorry

    _ =
      ε *
        ((((C.toMatrix hd2) c R : Nat) : ZMod m) -
         (((C.toMatrix hd2) c Δ : Nat) : ZMod m)) := by
          simpa [ε, R, Δ] using
            prefixCountReturnTailSignedCoeff_layer_sum_eq_matrix
              (hd2 := hd2) (C := C) L c hk

    _ =
      ε *
        (((C.step c ⟨k, hk⟩ : Int) - (C.delta c : Int)) : ZMod m) := by
          have hmat :=
            prefixCount_toMatrix_rawStep_sub_delta_zmod
              (hd2 := hd2) (C := C) (c := c) (k := k) (hk := hk)
          simpa [ε, R, Δ] using congrArg (fun q : ZMod m => ε * q) hmat
```

The only nontrivial `sorry` above is exactly the local theorem from §2.

---

## 6. Hidden assumptions / warnings

1. **Base orbit must be a full `ZMod m` orbit.**  
   The low-prefix reindexing needs the map induced by `u ↦ ((prefixCountFirstHitReturnBaseStep C c)^[u]) 0` to be bijective modulo `m`.  If this step is translation by `C.zero c`, you need a lemma like

   ```lean
   theorem PrefixCount.Parts.Admissible.isUnit_zero_zmod
       {d m : Nat} [NeZero m] {C : PrefixCount.Parts d}
       (hC : C.Admissible m) (c : Fin d) :
     IsUnit ((C.zero c : ZMod m))
   ```

   or an equivalent base-orbit permutation theorem.  `Odd m` alone is not enough for composite `m`.

2. **`d ≤ m` is needed for low-rank residue injectivity.**  
   The rho-event specifications need that the low rank residues `0,1,...,d-1` do not collide in `ZMod m`.

3. **The pure first-hit counts do not need `Odd m` or primality.**  
   They only use `[NeZero m]` and `(m : ZMod m) = 0`.

4. **The old unsigned target is false.**  
   The surviving layer-symbol expression is

   ```lean
   (-1 : ZMod m) ^ (k + 1) *
     (M c (k+2) - M c 1)
   ```

   not just `M c (k+2) - M c 1`.

5. **Do not rewrite `rho = k+1` as “some hit” propositionally.**  
   The Delta event is “first hit exactly at the last tested coordinate”.  Its modulo-`m` count equals the “some hit” count, but the predicates are not equal.