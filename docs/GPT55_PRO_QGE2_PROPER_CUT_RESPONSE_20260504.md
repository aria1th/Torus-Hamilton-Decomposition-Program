I would add **one ordinary-row black box**, not an arbitrary-row packing theorem.  The cleanest interface is an all-cuts, column-first version with the dummy `C` removed.

```lean
namespace RoundComposite.PrefixCount

/-- External finite HEG/submodular-flow theorem for exactly the ordinary
q ≥ 2 signed trellis instance.  This is intentionally *not* an arbitrary
`R : Fin n → Int` statement. -/
def OrdinaryQge2SignedTrellisHoffmanGoal : Prop :=
  ∀ {n r : Nat},
    Even n → 4 ≤ n → Odd r → r < n → 0 < r →
    ∀ (a : Fin n → Nat) (epsBit : Fin n → Nat) (c : Fin (n - 1) → Nat),
      (∀ i : Fin n, a i = 1 ∨ a i = 2) →
      (∀ i : Fin n, epsBit i = 0 ∨ epsBit i = 1) →
      (∀ k : Fin (n - 1), c k = 1 ∨ c k = 2) →
      (∑ i : Fin n, epsBit i) = r →
      (∑ i : Fin n, a i) = (∑ k : Fin (n - 1), c k) →
      (∀ J : Finset (Fin n),
        (∑ i ∈ J, ((r : Int) - (a i : Int)
            - (n : Int) * (epsBit i : Int)))
          ≤ ∑ k : Fin (n - 1), qge2ColumnCapacity n J.card (c k)) →
      ∃ X : Fin (n - 1) → Fin n → Int,
        (∀ k i, IsSignedVal (X k i)) ∧
        (∀ k : Fin (n - 1), (∑ i : Fin n, X k i) = - (c k : Int)) ∧
        (∀ i : Fin n,
          (∑ k : Fin (n - 1), X k i)
            = (r : Int) - (a i : Int) - (n : Int) * (epsBit i : Int))
```

Then prove the existing all-cut seed closure goal from it by only transposing the matrix and deriving `∑ a = ∑ c` from the two equalities to `C`.

```lean
theorem ordinaryQge2SignedSeedClosureGoal_of_signedTrellisHoffman
    (H : OrdinaryQge2SignedTrellisHoffmanGoal) :
    OrdinaryQge2SignedSeedClosureGoal := by
  classical
  intro n C r hn h4 hr hlt hpos a epsBit c ha heps hc hsumA hsumE hsumC hcut
  have hsumAC :
      (∑ i : Fin n, a i) = (∑ k : Fin (n - 1), c k) :=
    hsumA.trans hsumC.symm
  rcases H (n := n) (r := r) hn h4 hr hlt hpos
      a epsBit c ha heps hc hsumE hsumAC hcut with
    ⟨X, hXval, hXcol, hXrow⟩
  refine ⟨fun i k => X k i, ?_, ?_, ?_⟩
  · intro i k
    exact hXval k i
  · intro i
    simpa using hXrow i
  · intro k
    simpa using hXcol k
```

Now use your existing empty/full-cut equivalence to close the proper-cut goal.

```lean
theorem ordinaryQge2SignedSeedProperCutClosureGoal_of_signedTrellisHoffman
    (H : OrdinaryQge2SignedTrellisHoffmanGoal) :
    OrdinaryQge2SignedSeedProperCutClosureGoal := by
  exact ordinaryQge2SignedSeedClosureGoal_iff_properCutClosure.mp
    (ordinaryQge2SignedSeedClosureGoal_of_signedTrellisHoffman H)
```

This assumes `#check ordinaryQge2SignedSeedClosureGoal_iff_properCutClosure` has orientation

```lean
OrdinaryQge2SignedSeedClosureGoal ↔
  OrdinaryQge2SignedSeedProperCutClosureGoal
```

If your local theorem is oriented the other way, replace `.mp` by `.mpr`.

To leave exactly one external theorem open, add either:

```lean
axiom ordinaryQge2SignedTrellisHoffman :
  OrdinaryQge2SignedTrellisHoffmanGoal
```

and close the active field by

```lean
exact ordinaryQge2SignedSeedProperCutClosureGoal_of_signedTrellisHoffman
  ordinaryQge2SignedTrellisHoffman
```

or, with the absolute smallest diff, assume the already-existing all-cut goal directly:

```lean
axiom ordinaryQge2SignedSeedClosureGoal_HEG :
  OrdinaryQge2SignedSeedClosureGoal

theorem ordinaryQge2SignedSeedProperCutClosureGoal_HEG :
    OrdinaryQge2SignedSeedProperCutClosureGoal := by
  exact ordinaryQge2SignedSeedClosureGoal_iff_properCutClosure.mp
    ordinaryQge2SignedSeedClosureGoal_HEG
```

The `OrdinaryQge2SignedTrellisHoffmanGoal` version is preferable because it removes the dummy `C` and exposes the intended column/path decomposition theorem.

Why not ordinary Hall alone: the tempting arbitrary-row theorem is false.  For example with `n = 4`, three columns all having `c = 2`, and row target

```text
R = (6, 0, -6, -6),
```

the row-subset inequalities hold: for one `c = 2`, the capacities are

```text
U₂(0), U₂(1), U₂(2), U₂(3), U₂(4) = 0, 2, 2, 0, -2,
```

so for three columns the bounds are `0,6,6,0,-6`, and `R` satisfies them.  But no signed matrix exists: row sum `6` across three entries forces all entries in that row to be `2`; row sums `-6` force all entries in those rows to be `-2`; then each column already sums to `-2`, so the remaining row would have to contribute `0`, impossible since `0 ∉ signedVals`.

The ordinary theorem avoids this because the row demands are not arbitrary: they are exactly

```lean
(r : Int) - (a i : Int) - (n : Int) * (epsBit i : Int)
```

with `a_i ∈ {1,2}`, `eps_i ∈ {0,1}`, `∑ eps = r`, and `∑ a = ∑ c`.  So do not state a black box quantifying over arbitrary `R`.

Implementation order:

1. Add `OrdinaryQge2SignedTrellisHoffmanGoal`.
2. Add `ordinaryQge2SignedSeedClosureGoal_of_signedTrellisHoffman`.
3. Add `ordinaryQge2SignedSeedProperCutClosureGoal_of_signedTrellisHoffman`.
4. Add one external theorem/axiom proving `OrdinaryQge2SignedTrellisHoffmanGoal`.
5. Use the final wrapper to fill the q≥2 proper-cut signed closure field.

The remaining external theorem is precisely the finite integral Hoffman/Edmonds-Giles/submodular-flow instance for the ordinary signed trellis; the wrapper itself needs no new arithmetic lemmas because your existing proper/all-cut equivalence handles empty and full cuts.