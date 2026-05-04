# GPT-5.5 Pro response: return-tail hit condition and unit carry

- response_id: `resp_0db37919e35976200069f8bc2d05408192981ff22f53fe7f37`
- status: `completed`
- output_items: `2`
- text_chars: `20983`

---

Below is the proof route I would implement.  I use the notation

```lean
-- row = color c, column = symbol s
M(c,s) := (((C.toMatrix hd2) c s : Nat) : ZMod m)
δ      := (⟨1, _⟩ : Fin d)
σ k    := (⟨k + 2, _⟩ : Fin d)
```

The exact total carry is

```lean
M(c, σ k) - M(c, δ)
```

i.e. symbol `k+2` count minus the `Δ`/symbol-`1` count.

---

## A. Hit-condition locality

### A0. Canonical rho prefix characterization

This is the key definitional lemma.  It should be proved by unfolding `prefixCountCanonicalRho`.

```lean
theorem prefixCountCanonicalRho_not_lt_iff_rootPrefix_eq
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    (a : ZMod m) (v : Fin (d - 1) → ZMod m)
    {q : Nat} (hq0 : 1 ≤ q) (hqd : q ≤ d - 1) :
    ¬ (prefixCountCanonicalRho d m hd2 a v).val < q ↔
      ∀ i : Fin (q - 1), v ⟨i.val, by omega⟩ = a := by
  -- unfold prefixCountCanonicalRho
  -- `rho ≥ q` means the first `q - 1` root-prefix coordinates hit `a`.
```

Useful corollary:

```lean
theorem prefixCountCanonicalRho_lt_of_rootTake_eq
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    (a : ZMod m)
    {n q : Nat} (hn : n ≤ d - 1) (hq0 : 1 ≤ q) (hqd : q ≤ d - 1)
    (hqn : q ≤ n + 1)
    {v w : Fin (d - 1) → ZMod m}
    (hvw : Shared.zmodVectorTake hn v = Shared.zmodVectorTake hn w) :
    (prefixCountCanonicalRho d m hd2 a v).val < q ↔
      (prefixCountCanonicalRho d m hd2 a w).val < q := by
  -- Use A0 on both sides.
  -- The predicate in A0 only reads coordinates `< q - 1`, and
  -- `q - 1 ≤ n`.
```

Also prove the positive-rho / zero-lambda helper if not already present:

```lean
theorem prefixCountCanonicalRho_pos
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    (a : ZMod m) (v : Fin (d - 1) → ZMod m) :
    0 < (prefixCountCanonicalRho d m hd2 a v).val := by
  -- A0 with q = 1 gives `¬ rho.val < 1`.

theorem prefixCountLambdaRho_val_eq_zero_iff_of_rho_pos
    {d : Nat} (rho s : Fin d) (hrho : 0 < rho.val) :
    (prefixCountLambdaRho d rho s).val = 0 ↔ s.val = 0 := by
  -- unfold prefixCountLambdaRho, or use the existing positive-coordinate
  -- characterization plus Fin value cases.
```

### A1. Prefix maps are unitriangular on root-prefix coordinates

Prove first for one layer, then induct over `prefixMap`.

```lean
theorem prefixCountFirstHitCanonicalSchedule_layerMap_incrementDependsOnTake
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) (t : Nat) :
    Shared.ZModVectorIncrementDependsOnTake
      ((prefixCountFirstHitCanonicalSchedule hd2 L).layerMap c t) := by
  -- Coordinate formula for layerMap:
  -- output i = input i + if lambdaRho rho s has value i then 1 else 0.
  -- For i = 0, use `prefixCountLambdaRho_val_eq_zero_iff_of_rho_pos`.
  -- For i > 0, use existing
  --   prefixCountLambdaRho_val_eq_pos_iff
  -- and A0/A0-corollaries to show the condition `lambda = i`
  -- depends only on root coordinates `< i`.
```

Then:

```lean
theorem prefixCountFirstHitCanonicalSchedule_prefixMap_incrementDependsOnTake
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) (t : Nat) :
    Shared.ZModVectorIncrementDependsOnTake
      ((prefixCountFirstHitCanonicalSchedule hd2 L).prefixMap c t) := by
  -- Induct on t using the prefixMap recursion.
  -- Use Shared.zmodVectorIncrementDependsOnTake_id at 0 and
  -- Shared.zmodVectorIncrementDependsOnTake_comp at succ.
  -- The step input is A1 layerMap.
```

### A2. Direct hit-condition congruence from rho cutoffs

This lemma is just propositional bookkeeping around the three cases in
`prefixCountFirstHitReturnFiberHitCondition`.

```lean
theorem prefixCountFirstHitReturnFiberHitCondition_congr_rho_cutoffs
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) (z : ZMod m)
    (x y : Fin (d - 2) → ZMod m)
    (k : Nat) (hk : k < d - 2) (t : Nat)
    (hlt₁ :
      (let ρx :=
        prefixCountCanonicalRho d m hd2 ((t : Nat) : ZMod m)
          ((prefixCountFirstHitCanonicalSchedule hd2 L).prefixMap c t
            ((prefixCountRootStateHeadTailEquiv d m hd2).symm (z, x)))
       let ρy :=
        prefixCountCanonicalRho d m hd2 ((t : Nat) : ZMod m)
          ((prefixCountFirstHitCanonicalSchedule hd2 L).prefixMap c t
            ((prefixCountRootStateHeadTailEquiv d m hd2).symm (z, y)))
       ρx.val < k + 1 ↔ ρy.val < k + 1))
    (hlt₂ :
      (let ρx :=
        prefixCountCanonicalRho d m hd2 ((t : Nat) : ZMod m)
          ((prefixCountFirstHitCanonicalSchedule hd2 L).prefixMap c t
            ((prefixCountRootStateHeadTailEquiv d m hd2).symm (z, x)))
       let ρy :=
        prefixCountCanonicalRho d m hd2 ((t : Nat) : ZMod m)
          ((prefixCountFirstHitCanonicalSchedule hd2 L).prefixMap c t
            ((prefixCountRootStateHeadTailEquiv d m hd2).symm (z, y)))
       ρx.val < k + 2 ↔ ρy.val < k + 2)) :
    prefixCountFirstHitReturnFiberHitCondition hd2 L c z x ⟨k, hk⟩ t ↔
      prefixCountFirstHitReturnFiberHitCondition hd2 L c z y ⟨k, hk⟩ t := by
  -- Derive `ρx.val = k+1 ↔ ρy.val = k+1` from hlt₁/hlt₂ by omega.
  -- Unfold prefixCountFirstHitReturnFiberHitCondition.
  -- The symbol `s` is identical on both sides.
  -- Case 1 uses equality `rho = k+1`.
  -- Case 2 rewrites `s.val = k+1` and uses hlt₁.
  -- Case 3 rewrites `s.val = k+2` and uses hlt₂ under negation.
```

### A3. Smaller theorem closing the field

This is strictly smaller than the field: it does not use `Odd d`, `5 ≤ d`, `Odd m`,
`d ≤ m`, or `C.Admissible m`.

```lean
theorem prefixCountFirstHitReturnFiberHitCondition_dependsOnTake
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) (z : ZMod m)
    (x y : Fin (d - 2) → ZMod m)
    (k : Nat) (hk : k < d - 2)
    (hxy :
      Shared.zmodVectorTake (Nat.le_of_lt hk) x =
        Shared.zmodVectorTake (Nat.le_of_lt hk) y)
    (t : Nat) :
    prefixCountFirstHitReturnFiberHitCondition hd2 L c z x ⟨k, hk⟩ t ↔
      prefixCountFirstHitReturnFiberHitCondition hd2 L c z y ⟨k, hk⟩ t := by
  -- Let X,Y be the two root states after prefixMap c t.
  -- From head equality and hxy, root-takes of length k+1 agree before prefixMap.
  -- Use A1 prefixMap_incrementDependsOnTake and
  -- Shared.zmodVectorTake_apply_eq_of_incrementDependsOnTake
  -- to get root-takes of length k+1 agree after prefixMap.
  -- Apply A0-corollary with q = k+1 and q = k+2.
  -- Finish with A2.
```

Then the exposed goal is immediate:

```lean
theorem prefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal :
    PrefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal := by
  intro d m _inst hd2 C hdodd hd5 hmodd hdm hC L c z x y k hk hxy t ht
  exact
    prefixCountFirstHitReturnFiberHitCondition_dependsOnTake
      (hd2 := hd2) L c z x y k hk hxy t
```

---

## B/C. Exact total carry and unitness

### B0. Layer symbol count

Use a symbol-count def independent of matrix orientation details.

```lean
noncomputable def prefixCountFirstHitLayerSymbolCount
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c s : Fin d) : ZMod m :=
  ∑ t ∈ Finset.range m,
    if L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c = s
    then (1 : ZMod m) else 0
```

Layer-count decomposition gives:

```lean
theorem prefixCountFirstHitLayerSymbolCount_eq_toMatrix
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c s : Fin d) :
    prefixCountFirstHitLayerSymbolCount hd2 L c s =
      (((C.toMatrix hd2) c s : Nat) : ZMod m) := by
  -- unfold prefixCountFirstHitLayerSymbolCount
  -- rewrite the sum of indicators as the card of the filter
  -- use the count field of LayerPermCounts.
```

### B1. Admissible projection lemmas

Add these projection lemmas once.  Their proofs should just unfold `Parts.Admissible`
and `Parts.toMatrix`.

```lean
theorem PrefixCount.Parts.Admissible.toMatrix_zero_unit
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (hC : C.Admissible m) (c : Fin d) :
    IsUnit ((((C.toMatrix hd2) c ⟨0, by omega⟩ : Nat) : ZMod m)) := by
  -- existing admissible zero/M₀ unit field

theorem PrefixCount.Parts.Admissible.toMatrix_deltaDiff_unit
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (hC : C.Admissible m) (c s : Fin d) (hs : 2 ≤ s.val) :
    IsUnit
      ((((C.toMatrix hd2) c s : Nat) : ZMod m) -
       (((C.toMatrix hd2) c ⟨1, by omega⟩ : Nat) : ZMod m)) := by
  -- existing admissible tail-difference field:
  -- M_s - M_Δ is a unit for s.val ≥ 2.
  -- If stored as M_Δ - M_s, use `.neg`.
```

### B2. Local rho counts

Define a local model hit condition on a low-prefix vector.

```lean
def prefixCountFirstHitLocalHitCondition
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    (a : ZMod m) (s : Fin d)
    (k : Nat) (hk : k < d - 2)
    (p : Fin (k + 1) → ZMod m) : Prop :=
  let v : Fin (d - 1) → ZMod m :=
    Shared.zmodVectorExtendZero (by omega : k + 1 ≤ d - 1) p
  let ρ := prefixCountCanonicalRho d m hd2 a v
  (s.val = 1 ∧ ρ.val = k + 1) ∨
    (s.val = k + 1 ∧ 1 < s.val ∧ ρ.val < s.val) ∨
    (s.val = k + 2 ∧ ¬ ρ.val < s.val)
```

Then prove the arithmetic count:

```lean
theorem prefixCountFirstHitLocalHitCondition_sum
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    (a : ZMod m) (s : Fin d)
    (k : Nat) (hk : k < d - 2) :
    (∑ p : Fin (k + 1) → ZMod m,
      if prefixCountFirstHitLocalHitCondition hd2 a s k hk p
      then (1 : ZMod m) else 0)
    =
      (if s = ⟨k + 2, by omega⟩ then (1 : ZMod m) else 0) -
      (if s = ⟨1, by omega⟩ then (1 : ZMod m) else 0) := by
  -- Use A0 specialized to v = extendZero p.
  -- Needed facts:
  --   ρ.val = k+1 iff first k entries of p equal a and last entry ≠ a.
  --   ρ.val < k+1 iff first k entries of p are not all equal a.
  --   ¬ ρ.val < k+2 iff all k+1 entries of p equal a.
  --
  -- Counts in ZMod m:
  --   sum [ρ = k+1]        = m - 1 = -1
  --   sum [ρ < k+1]        = 0
  --   sum [¬ ρ < k+2]      = 1
  --
  -- Use Shared.zmodVectorSnocEquiv to split p into
  --   (Fin k → ZMod m) × ZMod m.
```

This is where the sign is fixed: symbol `1` contributes `-1`, symbol `k+2`
contributes `+1`, symbol `k+1` contributes `0`.

### B3. Bijection of low prefixes before a layer

Define the low prefix seen at layer `t` during the return-tail monodromy.

```lean
noncomputable def prefixCountFirstHitReturnLowPrefixBeforeLayer
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) (k : Nat) (hk : k < d - 2)
    (u : Fin m) (x : Fin k → ZMod m) (t : Nat) :
    Fin (k + 1) → ZMod m :=
  Shared.zmodVectorTake (by omega : k + 1 ≤ d - 1)
    ((prefixCountFirstHitCanonicalSchedule hd2 L).prefixMap c t
      ((prefixCountRootStateHeadTailEquiv d m hd2).symm
        (((prefixCountFirstHitReturnBaseStep (m := m) C c)^[u.val]) (0 : ZMod m),
          Shared.skewFiberIterate
            (prefixCountFirstHitReturnBaseStep (m := m) C c)
            (prefixCountFirstHitReturnFiberStep hd2 L c)
            u.val (0 : ZMod m)
            (Shared.zmodVectorExtendZero (Nat.le_of_lt hk) x))))
```

Prove:

```lean
theorem prefixCountFirstHitReturnLowPrefixBeforeLayer_bijective
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (hdodd : Odd d) (hd5 : 5 ≤ d) (hmodd : Odd m) (hdm : d ≤ m)
    (hC : C.Admissible m)
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) (k : Nat) (hk : k < d - 2) (t : Nat) :
    Function.Bijective
      (fun ux : Fin m × (Fin k → ZMod m) =>
        prefixCountFirstHitReturnLowPrefixBeforeLayer hd2 L c k hk ux.1 ux.2 t) := by
  -- Ingredients:
  -- 1. Base orbit u ↦ baseStep^[u] 0 is bijective on ZMod m.
  --    Use PrefixCount.Parts.Admissible.toMatrix_zero_unit and the base-step formula.
  --
  -- 2. For each fixed u, the map
  --      x ↦ take k (skewFiberIterate ... u 0 (extendZero x))
  --    is bijective.
  --    Use A3 through
  --      prefixCountFirstHitReturnFiberIncrementDependsOnTakeGoal_of_hitCondition
  --    and then Shared.zmodVectorIncrementDependsOnTake_skewFiberIterate.
  --
  -- 3. The truncated prefixMap on the first k+1 root coordinates is bijective.
  --    Use A1 plus the generic triangular bijection lemma:
  --      Shared.zmodVectorIncrementDependsOnTake_truncate_bijective.
  --
  -- Compose these bijections.
```

If the generic triangular bijection lemma is not exposed, add:

```lean
theorem Shared.zmodVectorIncrementDependsOnTake_truncate_bijective
    {m r n : Nat}
    {F : (Fin r → ZMod m) → (Fin r → ZMod m)}
    (hF : Shared.ZModVectorIncrementDependsOnTake F)
    (hn : n ≤ r) :
    Function.Bijective
      (fun x : Fin n → ZMod m =>
        Shared.zmodVectorTake hn (F (Shared.zmodVectorExtendZero hn x))) := by
  -- prove by induction on n using zmodVectorSnocEquiv.
```

### B4. Actual hit condition equals local model after low-prefix projection

```lean
theorem prefixCountFirstHitReturnFiberHitCondition_eq_local
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) (k : Nat) (hk : k < d - 2)
    (u : Fin m) (x : Fin k → ZMod m) (t : Nat) :
    prefixCountFirstHitReturnFiberHitCondition hd2 L c
      (((prefixCountFirstHitReturnBaseStep (m := m) C c)^[u.val]) (0 : ZMod m))
      (Shared.skewFiberIterate
        (prefixCountFirstHitReturnBaseStep (m := m) C c)
        (prefixCountFirstHitReturnFiberStep hd2 L c)
        u.val (0 : ZMod m)
        (Shared.zmodVectorExtendZero (Nat.le_of_lt hk) x))
      ⟨k, hk⟩ t
    ↔
    prefixCountFirstHitLocalHitCondition hd2 ((t : Nat) : ZMod m)
      (L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c)
      k hk
      (prefixCountFirstHitReturnLowPrefixBeforeLayer hd2 L c k hk u x t) := by
  -- Unfold both.
  -- The local model has the same first k+1 root coordinates as the actual
  -- state before layer t.
  -- Use A0-corollary for q = k+1 and q = k+2, then the same case split as A2.
```

### B5. One-layer summed contribution

```lean
theorem prefixCountFirstHitReturnTailCocycle_layer_sum
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (hdodd : Odd d) (hd5 : 5 ≤ d) (hmodd : Odd m) (hdm : d ≤ m)
    (hC : C.Admissible m)
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) (k : Nat) (hk : k < d - 2) (t : Nat) :
    (∑ ux : Fin m × (Fin k → ZMod m),
      if prefixCountFirstHitReturnFiberHitCondition hd2 L c
        (((prefixCountFirstHitReturnBaseStep (m := m) C c)^[ux.1.val]) (0 : ZMod m))
        (Shared.skewFiberIterate
          (prefixCountFirstHitReturnBaseStep (m := m) C c)
          (prefixCountFirstHitReturnFiberStep hd2 L c)
          ux.1.val (0 : ZMod m)
          (Shared.zmodVectorExtendZero (Nat.le_of_lt hk) ux.2))
        ⟨k, hk⟩ t
      then (1 : ZMod m) else 0)
    =
      (if L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c =
          ⟨k + 2, by omega⟩ then (1 : ZMod m) else 0) -
      (if L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c =
          ⟨1, by omega⟩ then (1 : ZMod m) else 0) := by
  -- Reindex the sum by the bijection from B3.
  -- Replace actual hit condition by local condition using B4.
  -- Apply B2.
```

### B6. Cocycle expansion and exact total carry

First expand cocycle as a sum of return-step hit indicators.

```lean
theorem prefixCountFirstHitReturnTailCocycle_eq_sum_hitCondition
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) (k : Nat) (hk : k < d - 2)
    (x : Fin k → ZMod m) :
    prefixCountFirstHitReturnTailCocycle hd2 L c k hk x =
      ∑ u : Fin m,
        ∑ t ∈ Finset.range m,
          if prefixCountFirstHitReturnFiberHitCondition hd2 L c
            (((prefixCountFirstHitReturnBaseStep (m := m) C c)^[u.val]) (0 : ZMod m))
            (Shared.skewFiberIterate
              (prefixCountFirstHitReturnBaseStep (m := m) C c)
              (prefixCountFirstHitReturnFiberStep hd2 L c)
              u.val (0 : ZMod m)
              (Shared.zmodVectorExtendZero (Nat.le_of_lt hk) x))
            ⟨k, hk⟩ t
          then (1 : ZMod m) else 0 := by
  -- unfold prefixCountFirstHitReturnTailCocycle
  -- rw [prefixCountFirstHitReturnTailMonodromy_eq_fiberIterate]
  -- induct over m return steps, using
  -- prefixCountFirstHitReturnFiberStep_apply_hitCondition.
  -- Initial coordinate k of extendZero is 0.
```

Then the exact carry:

```lean
theorem prefixCountFirstHitReturnTailCocycle_sum_eq_symbolCount_diff
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (hdodd : Odd d) (hd5 : 5 ≤ d) (hmodd : Odd m) (hdm : d ≤ m)
    (hC : C.Admissible m)
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) (k : Nat) (hk : k < d - 2) :
    (∑ x : Fin k → ZMod m,
      prefixCountFirstHitReturnTailCocycle hd2 L c k hk x)
    =
      prefixCountFirstHitLayerSymbolCount hd2 L c ⟨k + 2, by omega⟩ -
      prefixCountFirstHitLayerSymbolCount hd2 L c ⟨1, by omega⟩ := by
  -- Use B6 cocycle expansion.
  -- Commute sums to put ∑ t outside.
  -- For each t, apply B5.
  -- Fold back to prefixCountFirstHitLayerSymbolCount.
```

Convert to matrix counts:

```lean
theorem prefixCountFirstHitReturnTailCocycle_sum_eq_toMatrix_diff
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (hdodd : Odd d) (hd5 : 5 ≤ d) (hmodd : Odd m) (hdm : d ≤ m)
    (hC : C.Admissible m)
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) (k : Nat) (hk : k < d - 2) :
    (∑ x : Fin k → ZMod m,
      prefixCountFirstHitReturnTailCocycle hd2 L c k hk x)
    =
      ((((C.toMatrix hd2) c ⟨k + 2, by omega⟩ : Nat) : ZMod m) -
       (((C.toMatrix hd2) c ⟨1, by omega⟩ : Nat) : ZMod m)) := by
  rw [prefixCountFirstHitReturnTailCocycle_sum_eq_symbolCount_diff
    (hd2 := hd2) hdodd hd5 hmodd hdm hC L c k hk]
  rw [prefixCountFirstHitLayerSymbolCount_eq_toMatrix]
  rw [prefixCountFirstHitLayerSymbolCount_eq_toMatrix]
```

### B7. Close the unit field

```lean
theorem prefixCountFirstHitReturnTailCocycle_sum_isUnit
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (hdodd : Odd d) (hd5 : 5 ≤ d) (hmodd : Odd m) (hdm : d ≤ m)
    (hC : C.Admissible m)
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) (k : Nat) (hk : k < d - 2) :
    IsUnit
      (∑ x : Fin k → ZMod m,
        prefixCountFirstHitReturnTailCocycle hd2 L c k hk x) := by
  rw [prefixCountFirstHitReturnTailCocycle_sum_eq_toMatrix_diff
    (hd2 := hd2) hdodd hd5 hmodd hdm hC L c k hk]
  exact
    PrefixCount.Parts.Admissible.toMatrix_deltaDiff_unit
      (hd2 := hd2) hC c ⟨k + 2, by omega⟩ (by omega)
```

Then:

```lean
theorem prefixCountFirstHitReturnTailCocycleUnitGoal :
    PrefixCountFirstHitReturnTailCocycleUnitGoal := by
  intro d m _inst hd2 C hdodd hd5 hmodd hdm hC L c k hk
  exact
    prefixCountFirstHitReturnTailCocycle_sum_isUnit
      (hd2 := hd2) hdodd hd5 hmodd hdm hC L c k hk
```

---

## Exact arithmetic value

For every `k < d - 2`,

```lean
∑ x : Fin k → ZMod m,
  prefixCountFirstHitReturnTailCocycle hd2 L c k hk x
=
M(c, ⟨k + 2, _⟩) - M(c, ⟨1, _⟩)
```

where

```lean
M(c,s) = (((C.toMatrix hd2) c s : Nat) : ZMod m).
```

So the sign is positive:

```lean
symbol (k+2) count - Δ count
```

Use these admissible fields/projection lemmas:

1. `toMatrix_zero_unit`: unitness of the symbol `0` count.
   This is needed only to prove the base head orbit is bijective.

2. `toMatrix_deltaDiff_unit`: unitness of
   `M(c,s) - M(c,Δ)` for `2 ≤ s.val`.
   Apply with `s = ⟨k+2, by omega⟩`.

If the existing `Admissible` stores the opposite difference
`M(c,Δ) - M(c,s)`, close by `simpa [sub_eq_add_neg] using h.neg`.

---

## Warnings / false strengthenings

* Do **not** drop the head coordinate `z` in A.  The hit condition depends on
  `z` and tail coordinates `< k`.

* Do **not** claim locality for different heads.  The correct statement fixes
  the same `z`.

* Do **not** compute the unit carry from one return-fiber step.  The unit value
  appears after the full tail monodromy and summing over `Fin k`.

* Do **not** replace `C.Admissible m` by `Odd m`.  Odd composite moduli have
  nonzero nonunits.  The proof needs the admissible unit fields.

* Do **not** state the exact value as a color-independent raw `C.part`.
  The Lean-safe value is the row entry difference of `C.toMatrix hd2`:
  `M(c,k+2) - M(c,1)`.  Only after unfolding `Parts.toMatrix` may this become
  a named `C.parts` difference, possibly with a row permutation.

* The layer-count equality only holds over `Finset.range m`.  Avoid silently
  strengthening it to arbitrary `t`-ranges.