Below is the helper API I would add.  The key choice is to make the fixed-`t` residual the **prefix-integrated residual**

\[
r_i = b_u - t + \sum_{j<i} z_j,\qquad i=0,\dots,k,
\]

where `b_u` is the base iterate and `z` is the low `Fin k` fiber prefix after the skew iterate.  Then zeros of `r` are exactly the first-hit tests, and the map `(x,u) ↦ r` factors through the already-closed low-prefix bijection and base-cycle reindexing.

```lean
namespace RoundComposite.Concrete

open scoped BigOperators

/-- Prefix-integrate a base residual `a` and `k` low fiber increments. -/
def prefixCountLowResidualOf {m k : Nat} [NeZero m]
    (a : ZMod m) (z : Fin k → ZMod m) :
    Fin (k + 1) → ZMod m :=
  fun i =>
    a + ∑ j : Fin i.1,
      z ⟨j.1, by
        have hi : i.1 ≤ k := Nat.le_of_lt_succ (by simpa [Nat.succ_eq_add_one] using i.2)
        exact Nat.lt_of_lt_of_le j.2 hi⟩

/-- The low `Fin k` fiber prefix after the skew iterate. -/
def prefixCountFirstHitReturnLowFiber
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) {k : Nat} (hk : k < d - 2)
    (u : Nat) (x : Fin k → ZMod m) :
    Fin k → ZMod m :=
  Shared.zmodVectorTake (Nat.le_of_lt hk)
    (Shared.skewFiberIterate
      (prefixCountFirstHitReturnBaseStep (m := m) C c)
      (prefixCountFirstHitReturnFiberStep hd2 L c)
      u (0 : ZMod m)
      (Shared.zmodVectorExtendZero (Nat.le_of_lt hk) x))

/-- The fixed-`t` low residual vector used for the local first-hit count. -/
def prefixCountFirstHitReturnLowResidual
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) {k : Nat} (hk : k < d - 2)
    (t u : Nat) (x : Fin k → ZMod m) :
    Fin (k + 1) → ZMod m :=
  prefixCountLowResidualOf
    ((((prefixCountFirstHitReturnBaseStep (m := m) C c)^[u]) (0 : ZMod m))
      - (t : ZMod m))
    (prefixCountFirstHitReturnLowFiber hd2 L c hk u x)
```

The reindexing theorem should be stated directly as a sum theorem:

```lean
theorem prefixCountFirstHitReturnLowResidual_sum_reindex
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d}
    (hodd_d : Odd d) (hd5 : 5 ≤ d) (hodd_m : Odd m) (hdm : d ≤ m)
    (hC : C.Admissible m)
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) {k : Nat} (hk : k < d - 2) (t : Nat)
    (F : (Fin (k + 1) → ZMod m) → ZMod m) :
    (∑ x : Fin k → ZMod m,
      ∑ u ∈ Finset.range m,
        F (prefixCountFirstHitReturnLowResidual hd2 L c hk t u x))
    =
    ∑ r : Fin (k + 1) → ZMod m, F r := by
  classical
  /-
  Proof skeleton:

  1. Swap the `x` and `u` sums.

  2. For fixed `u`, reindex
       x ↦ prefixCountFirstHitReturnLowFiber hd2 L c hk u x
     using the closed theorem

       prefixCountFirstHitSkewFiberIterate_lowPrefix_bijective

     plus `Equiv.ofBijective`.

  3. Reindex the base residual
       u ↦ ((baseStep^[u]) 0) - t
     over `Finset.range m` using

       prefixCountFirstHitReturnBaseStep_sum_range_iterate

     and the translation equivalence on `ZMod m`.

  4. Reindex
       (a, z) ↦ prefixCountLowResidualOf a z
     using the elementary prefix-sum/difference equivalence with inverse
       r ↦ (r 0, fun i => r (Fin.succ i) - r (Fin.castSucc i)).
  -/
  sorry
```

For step 4 it is useful to package the elementary equivalence once:

```lean
noncomputable def prefixCountLowResidualEquiv
    (m k : Nat) [NeZero m] :
    (ZMod m × (Fin k → ZMod m)) ≃ (Fin (k + 1) → ZMod m) :=
by
  classical
  refine
  { toFun := fun p => prefixCountLowResidualOf p.1 p.2
    invFun := fun r =>
      (r (0 : Fin (k + 1)),
       fun i : Fin k => r (Fin.succ i) - r (Fin.castSucc i))
    left_inv := ?_
    right_inv := ?_ }
  · intro p
    ext i <;>
      -- telescope using
      -- `prefixCountLowResidualOf 0 = a`
      -- and `prefixCountLowResidualOf (Fin.succ i)
      --      = prefixCountLowResidualOf (Fin.castSucc i) + z i`.
      sorry
  · intro r
    ext i
    -- induction on `i : Fin (k+1)` / telescope.
    sorry
```

Now expose the local zero-pattern predicates.  These should either match the existing closed `pc...` lemmas definitionally, or be reducible by `simp`.

```lean
def prefixCountPcNoZeroEvent {m k : Nat} [NeZero m]
    (r : Fin (k + 1) → ZMod m) : Prop :=
  ∀ i : Fin (k + 1), r i ≠ 0

def prefixCountPcSomeZeroEvent {m k : Nat} [NeZero m]
    (r : Fin (k + 1) → ZMod m) : Prop :=
  ∃ i : Fin (k + 1), r i = 0

def prefixCountPcExactLastZeroEvent {m k : Nat} [NeZero m]
    (r : Fin (k + 1) → ZMod m) : Prop :=
  r ⟨k, Nat.lt_succ_self k⟩ = 0 ∧
    ∀ i : Fin k, r (Fin.castSucc i) ≠ 0

def prefixCountPcHitBeforeLastZeroEvent {m k : Nat} [NeZero m]
    (r : Fin (k + 1) → ZMod m) : Prop :=
  ∃ i : Fin k, r (Fin.castSucc i) = 0
```

Then define the three local symbol cases by copying the two nonzero branch tests already used by `prefixCountReturnTailSignedCoeff`.

```lean
inductive PrefixCountReturnTailLocalCase
  | delta
  | step
  | zero

/-- Fill these by reusing the branch tests from `prefixCountReturnTailSignedCoeff`. -/
def prefixCountReturnTailIsDeltaColumn
    {d : Nat} (hd2 : 2 ≤ d) {k : Nat} (hk : k < d - 2)
    (s : Fin d) : Prop :=
  -- e.g. `s = prefixCountReturnTailDeltaColumn hd2 hk`
  by
    exact False -- placeholder

def prefixCountReturnTailIsStepColumn
    {d : Nat} (hd2 : 2 ≤ d) {k : Nat} (hk : k < d - 2)
    (s : Fin d) : Prop :=
  -- e.g. `s = prefixCountReturnTailStepColumn hd2 hk`
  by
    exact False -- placeholder

def prefixCountReturnTailLocalCaseOf
    {d : Nat} (hd2 : 2 ≤ d) {k : Nat} (hk : k < d - 2)
    (s : Fin d) : PrefixCountReturnTailLocalCase :=
  if prefixCountReturnTailIsDeltaColumn hd2 hk s then
    .delta
  else if prefixCountReturnTailIsStepColumn hd2 hk s then
    .step
  else
    .zero

def prefixCountReturnTailLocalEvent
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {k : Nat} (hk : k < d - 2)
    (s : Fin d) (r : Fin (k + 1) → ZMod m) : Prop :=
  match prefixCountReturnTailLocalCaseOf hd2 hk s with
  | .delta => prefixCountPcNoZeroEvent r
  | .step  => prefixCountPcExactLastZeroEvent r
  | .zero  => prefixCountPcHitBeforeLastZeroEvent r
```

The pointwise hit-condition rewrite should have this shape:

```lean
theorem prefixCountFirstHitReturnFiberHitCondition_iff_localEvent
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) {k : Nat} (hk : k < d - 2)
    (t u : Nat) (x : Fin k → ZMod m) :
    prefixCountFirstHitReturnFiberHitCondition hd2 L c
      (((prefixCountFirstHitReturnBaseStep (m := m) C c)^[u]) (0 : ZMod m))
      (Shared.skewFiberIterate
        (prefixCountFirstHitReturnBaseStep (m := m) C c)
        (prefixCountFirstHitReturnFiberStep hd2 L c)
        u (0 : ZMod m)
        (Shared.zmodVectorExtendZero (Nat.le_of_lt hk) x))
      ⟨k, hk⟩ t
    ↔
    prefixCountReturnTailLocalEvent hd2 hk
      (L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c)
      (prefixCountFirstHitReturnLowResidual hd2 L c hk t u x) := by
  classical
  /-
  Use:
    prefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal

  Then unfold the hit condition and split on the local layer symbol.

  Expected branches:
    delta column : no residual coordinate is zero;
    step column  : the last residual is the first zero;
    zero columns : some zero occurs before the last coordinate.

  This should be a `simp` proof once the delta/step branch predicates are
  definitionally aligned with `prefixCountReturnTailSignedCoeff`.
  -/
  sorry
```

The counting bridge to `prefixCountReturnTailSignedCoeff` is then local and independent of `L`, `C`, `c`, and `t`:

```lean
theorem prefixCountReturnTailLocalEvent_indicator_sum
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {k : Nat} (hk : k < d - 2) (s : Fin d) :
    (∑ r : Fin (k + 1) → ZMod m,
      if prefixCountReturnTailLocalEvent hd2 hk s r then (1 : ZMod m) else 0)
    =
    prefixCountReturnTailSignedCoeff hd2 hk s := by
  classical
  unfold prefixCountReturnTailLocalEvent prefixCountReturnTailLocalCaseOf
  by_cases hδ : prefixCountReturnTailIsDeltaColumn hd2 hk s
  · -- delta/no-zero branch
    simp [hδ]
    simpa [prefixCountPcNoZeroEvent, prefixCountReturnTailSignedCoeff, hδ]
      using prefixCountPcNoZeroIndicatorSum (m := m) (k := k)
  · by_cases hs : prefixCountReturnTailIsStepColumn hd2 hk s
    · -- step/exact-last-zero branch
      simp [hδ, hs]
      simpa [prefixCountPcExactLastZeroEvent, prefixCountReturnTailSignedCoeff, hδ, hs]
        using prefixCountPcExactLastZeroIndicatorSum (m := m) (k := k)
    · -- zero-contribution branch
      simp [hδ, hs]
      simpa [prefixCountPcHitBeforeLastZeroEvent, prefixCountReturnTailSignedCoeff, hδ, hs]
        using prefixCountPcHitBeforeLastZeroIndicatorSum (m := m) (k := k)
```

If the unfolded step branch is coarser as `SomeZero` instead of `ExactLastZero`, replace the step branch by

```lean
| .step => prefixCountPcSomeZeroEvent r
```

and use

```lean
prefixCountPcSomeZeroIndicatorSum (m := m) (k := k)
```

in the corresponding branch.  The `ExactLastZero`/`HitBeforeLastZero` split is usually better for the first-hit proof, while `SomeZero` is the convenient coarse count.

Finally the fixed-`t` theorem is just:

```lean
theorem prefixCountFirstHitReturnTailLocalHitConditionSum_fixed_t
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d) {C : PrefixCount.Parts d}
    (hodd_d : Odd d) (hd5 : 5 ≤ d) (hodd_m : Odd m) (hdm : d ≤ m)
    (hC : C.Admissible m)
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) (k : Nat) (hk : k < d - 2)
    (t : Nat) (_ht : t ∈ Finset.range m) :
    (∑ x : Fin k → ZMod m,
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
        then (1 : ZMod m) else 0)
    =
    prefixCountReturnTailSignedCoeff hd2 hk
      (L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c) := by
  classical
  let s : Fin d :=
    L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c

  calc
    (∑ x : Fin k → ZMod m,
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
        then (1 : ZMod m) else 0)
        =
      ∑ x : Fin k → ZMod m,
      ∑ u ∈ Finset.range m,
        if prefixCountReturnTailLocalEvent hd2 hk s
            (prefixCountFirstHitReturnLowResidual hd2 L c hk t u x)
        then (1 : ZMod m) else 0 := by
          subst s
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro u _
          exact by
            rw [if_congr
              (prefixCountFirstHitReturnFiberHitCondition_iff_localEvent
                hd2 L c hk t u x)
              rfl rfl]
    _ =
      ∑ r : Fin (k + 1) → ZMod m,
        if prefixCountReturnTailLocalEvent hd2 hk s r
        then (1 : ZMod m) else 0 := by
          simpa [s] using
            prefixCountFirstHitReturnLowResidual_sum_reindex
              hd2 hodd_d hd5 hodd_m hdm hC L c hk t
              (fun r =>
                if prefixCountReturnTailLocalEvent hd2 hk s r
                then (1 : ZMod m) else 0)
    _ =
      prefixCountReturnTailSignedCoeff hd2 hk s := by
        exact prefixCountReturnTailLocalEvent_indicator_sum hd2 hk s
    _ =
      prefixCountReturnTailSignedCoeff hd2 hk
        (L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c) := by
        rfl
```

So the remaining Lean work is concentrated in exactly three helper facts:

1. `prefixCountFirstHitReturnLowResidual_sum_reindex`;
2. `prefixCountFirstHitReturnFiberHitCondition_iff_localEvent`;
3. `prefixCountReturnTailLocalEvent_indicator_sum`.

The first uses the closed low-prefix and base-cycle reindexing lemmas.  The second is a `simp`/case split after `prefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal`.  The third is exactly the closed `pc...IndicatorSum` lemmas plus the defining branches of `prefixCountReturnTailSignedCoeff`.