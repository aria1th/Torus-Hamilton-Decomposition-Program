# GPT-5.5 Pro Return-Tail Orbit Response

Date: 2026-05-04.

Response id: `resp_027f823c07feb7000069f8a28fa85481a188b9e57ef6926c33`.

Status: `completed`.

---

Below is the Lean-facing route I would use.  The key point is: do **not** try to prove the orbit goal directly.  Prove that the first-hit return tail map is a lower-triangular skew odometer whose carry cocycle has **unit total** at every rank.

---

## 1. Odometer shape of the monodromy

Let

```lean
abbrev ZTail (m r : Nat) := Fin r → ZMod m
```

Use tail coordinates in increasing odometer significance: coordinate `0` is least significant, coordinate `k` carries after the first `k` coordinates complete a cycle.

Useful projections:

```lean
namespace ZTail

def take {m r k : Nat} (hk : k ≤ r) (x : ZTail m r) : ZTail m k :=
  fun i => x ⟨i.val, lt_of_lt_of_le i.isLt hk⟩

def extendZero {m k r : Nat} (hk : k ≤ r) (x : ZTail m k) : ZTail m r :=
  fun i => if h : i.val < k then x ⟨i.val, h⟩ else 0

def init {m k : Nat} (x : ZTail m (k + 1)) : ZTail m k :=
  fun i => x (Fin.castSucc i)

def last {m k : Nat} (x : ZTail m (k + 1)) : ZMod m :=
  x (Fin.last k)

end ZTail
```

For the concrete first-hit return map define the rank-`k` cocycle by zero-extending lower coordinates:

```lean
noncomputable def prefixCountFirstHitReturnTailCocycle
    {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) (k : Nat) (hk : k < d - 2) :
    ZTail m k → ZMod m :=
  fun x =>
    prefixCountFirstHitReturnTailMonodromy hd2 L c
      (ZTail.extendZero (Nat.le_of_lt hk) x) ⟨k, hk⟩
```

The triangular statement to prove is:

```lean
def PrefixCountFirstHitReturnTailTriangularGoal : Prop :=
  forall {d m : Nat} [NeZero m] (hd2 : 2 <= d)
      {C : PrefixCount.Parts d},
    Odd d -> 5 <= d -> Odd m -> d <= m ->
    C.Admissible m ->
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) ->
    forall c : Fin d,
    forall tail : ZTail m (d - 2),
    forall k : Nat, forall hk : k < d - 2,
      prefixCountFirstHitReturnTailMonodromy hd2 L c tail ⟨k, hk⟩ =
        tail ⟨k, hk⟩ +
          prefixCountFirstHitReturnTailCocycle hd2 L c k hk
            (ZTail.take (Nat.le_of_lt hk) tail)
```

Equivalently, for `r = d - 2`, the monodromy is

\[
T(x)_k = x_k + \gamma_k(x_0,\dots,x_{k-1}),
\]

where

\[
\gamma_k : (\mathbb Z/m)^k \to \mathbb Z/m.
\]

This is exactly the triangular/skew odometer form.

---

## 2. Carry/unit lemma needed at rank `k`

The skew-product induction only needs the **total carry** over the lower `k` coordinates to be a unit:

```lean
def PrefixCountFirstHitReturnTailCocycleUnitGoal : Prop :=
  forall {d m : Nat} [NeZero m] (hd2 : 2 <= d)
      {C : PrefixCount.Parts d},
    Odd d -> 5 <= d -> Odd m -> d <= m ->
    C.Admissible m ->
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) ->
    forall c : Fin d,
    forall k : Nat, forall hk : k < d - 2,
      IsUnit
        (∑ x : ZTail m k,
          prefixCountFirstHitReturnTailCocycle hd2 L c k hk x)
```

This is the essential unit lemma.  Pointwise single-carry form is stronger but unnecessary.  If the count branch proves an exact value, use a theorem of the form:

```lean
theorem prefixCountFirstHitReturnTailCocycle_sum_eq_countBranch
    {d m : Nat} [NeZero m] (hd2 : 2 <= d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) (k : Nat) (hk : k < d - 2) :
    (∑ x : ZTail m k,
      prefixCountFirstHitReturnTailCocycle hd2 L c k hk x)
      =
    PrefixCount.firstHitPrimitiveCarry hd2 C L c k hk := by
  -- finite-sum/layer-count proof
  sorry

theorem PrefixCount.firstHitPrimitiveCarry_isUnit
    {d m : Nat} [NeZero m] (hd2 : 2 <= d)
    {C : PrefixCount.Parts d}
    (hdodd : Odd d) (hd5 : 5 <= d) (hmodd : Odd m) (hdm : d <= m)
    (hC : C.Admissible m)
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2))
    (c : Fin d) (k : Nat) (hk : k < d - 2) :
    IsUnit (PrefixCount.firstHitPrimitiveCarry hd2 C L c k hk) := by
  -- count-branch primitivity/admissibility
  sorry
```

Then the unit goal follows immediately.

If the count branch returns `±1`, this is immediate.  If it returns `±2`, close using `Odd m`, since `2` is a unit in `ZMod m` for odd `m`.

---

## 3. Lambda/rho specialization for tail rank `k`

For rank `k`, the relevant positive layer is `l = k + 1`.  Since `hk : k < d - 2`, we have `0 < k + 1` and `k + 2 < d`.  Package the existing lemma into this specialization:

```lean
def prefixCountTailLayer {d : Nat} (hd2 : 2 <= d)
    {k : Nat} (hk : k < d - 2) : Fin d :=
  ⟨k + 1, by omega⟩

def prefixCountTailNextLayer {d : Nat} (hd2 : 2 <= d)
    {k : Nat} (hk : k < d - 2) : Fin d :=
  ⟨k + 2, by omega⟩

def prefixCountOneLayer {d : Nat} (hd2 : 2 <= d) : Fin d :=
  ⟨1, by omega⟩

theorem prefixCountLambdaRho_tailLayer_iff
    {d : Nat} (hd2 : 2 <= d)
    {k : Nat} (hk : k < d - 2)
    (rho s : Fin d) :
    (prefixCountLambdaRho d rho s).val = k + 1 <->
      (s = prefixCountOneLayer hd2 /\
        rho = prefixCountTailLayer hd2 hk) \/
      (s = prefixCountTailLayer hd2 hk /\
        1 < k + 1 /\ rho.val < k + 1) \/
      (s = prefixCountTailNextLayer hd2 hk /\
        k + 2 <= rho.val) := by
  -- use prefixCountLambdaRho_val_eq_pos_iff with l = k + 1
  -- and then clean Fin equalities by ext/omega
  sorry
```

This is the exact case split needed for the finite layer sums.  The total cocycle at rank `k` should be reduced to the three blocks:

1. `s = 1`, `rho = k + 1`;
2. `s = k + 1`, `rho < k + 1`;
3. `s = k + 2`, `rho >= k + 2`.

That is the count-branch primitive carry.

---

## 4. General skew-product cycle theorem

Add this once in `Shared`.

```lean
theorem Shared.CycleCoordinate.skewProduct_zmod_unit
    {N m : Nat} [NeZero N] [NeZero m]
    {α : Type*} [Fintype α] [DecidableEq α]
    {f : α → α}
    (hf : Shared.CycleCoordinate N f)
    (g : α → ZMod m)
    (hunit : IsUnit (∑ a : α, g a)) :
    Shared.CycleCoordinate (N * m)
      (fun p : α × ZMod m => (f p.1, p.2 + g p.1)) := by
  -- Standard proof:
  -- after N base steps, fiber advances by U = ∑ a, g a;
  -- U is a unit, so translation by U is an m-cycle.
  -- Equivalently construct mixed-radix rank using a coboundary correction.
  sorry
```

Then specialize to triangular maps on `Fin (k+1) → ZMod m`:

```lean
theorem Shared.CycleCoordinate.finSucc_skew_unit
    {m k N : Nat} [NeZero m] [NeZero N]
    {F : ZTail m k → ZTail m k}
    {G : ZTail m (k + 1) → ZTail m (k + 1)}
    (γ : ZTail m k → ZMod m)
    (hF : Shared.CycleCoordinate N F)
    (hinit :
      forall x : ZTail m (k + 1),
        ZTail.init (G x) = F (ZTail.init x))
    (hlast :
      forall x : ZTail m (k + 1),
        ZTail.last (G x) =
          ZTail.last x + γ (ZTail.init x))
    (hγ : IsUnit (∑ x : ZTail m k, γ x)) :
    Shared.CycleCoordinate (N * m) G := by
  -- conjugate by ZTail (k+1) ≃ ZTail k × ZMod m
  -- then apply skewProduct_zmod_unit
  sorry
```

Finally, the lower-triangular induction theorem:

```lean
theorem Shared.CycleCoordinate.of_lowerTriangularUnit
    {m r : Nat} [NeZero m]
    (F : ZTail m r → ZTail m r)
    (γ : forall k : Nat, k < r → ZTail m k → ZMod m)
    (hcoord :
      forall x : ZTail m r,
      forall k : Nat, forall hk : k < r,
        F x ⟨k, hk⟩ =
          x ⟨k, hk⟩ + γ k hk (ZTail.take (Nat.le_of_lt hk) x))
    (hunit :
      forall k : Nat, forall hk : k < r,
        IsUnit (∑ x : ZTail m k, γ k hk x)) :
    Shared.CycleCoordinate (m ^ r) F := by
  -- Induct on r.
  -- Base r = 0: singleton.
  -- Step: split ZTail m (k+1) as ZTail m k × ZMod m.
  -- Use finSucc_skew_unit with N = m^k.
  sorry
```

This theorem is the clean wrapper for the whole first-hit return-tail proof.

---

## 5. Concrete wrapper to the requested target

Once the triangular and unit goals are proved, the cycle-coordinate target follows:

```lean
theorem prefixCountFirstHitReturnTailCycleCoordinateGoal_of_triangular_unit
    (hTri : PrefixCountFirstHitReturnTailTriangularGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal) :
    PrefixCountFirstHitReturnTailCycleCoordinateGoal := by
  intro d m hm hd2 C hdodd hd5 hmodd hdm hC L c
  let F := prefixCountFirstHitReturnTailMonodromy hd2 L c
  let γ :=
    fun k hk =>
      prefixCountFirstHitReturnTailCocycle hd2 L c k hk
  exact
    Shared.CycleCoordinate.of_lowerTriangularUnit F γ
      (by
        intro tail k hk
        exact hTri hd2 hdodd hd5 hmodd hdm hC L c tail k hk)
      (by
        intro k hk
        exact hUnit hd2 hdodd hd5 hmodd hdm hC L c k hk)
```

Then use the existing bridge chain:

```lean
theorem prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_triangular_unit
    (hTri : PrefixCountFirstHitReturnTailTriangularGoal)
    (hUnit : PrefixCountFirstHitReturnTailCocycleUnitGoal) :
    PrefixCountFirstHitReturnTailMonodromyOrbitGoal :=
  prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_rank
    (prefixCountFirstHitReturnTailRankGoal_of_rankEquiv
      (prefixCountFirstHitReturnTailRankEquivGoal_of_cycleCoordinate
        (prefixCountFirstHitReturnTailCycleCoordinateGoal_of_triangular_unit
          hTri hUnit)))
```

So the remaining concrete Lean work is exactly:

1. prove `PrefixCountFirstHitReturnTailTriangularGoal`;
2. prove `PrefixCountFirstHitReturnTailCocycleUnitGoal`.

---

## 6. Warning: unit is necessary, nonzero is not enough

The bijectivity of the monodromy is not enough.  Already for one coordinate,

```lean
T : ZMod 9 → ZMod 9
T x = x + 3
```

is bijective, but its orbits have size `3`, not `9`.  Thus the carry sum must be a **unit** in `ZMod m`, not merely nonzero or odd.  For composite odd `m`, an odd value like `3` may fail to be a unit.

So if the v7 count branch only proves nonvanishing, the current target is too strong.  The right count conclusion is precisely:

```lean
IsUnit (∑ x : ZTail m k, prefixCountFirstHitReturnTailCocycle hd2 L c k hk x)
```

for every rank `k`.  If the count branch gives `±1` or `±2`, this closes immediately under `Odd m`.
