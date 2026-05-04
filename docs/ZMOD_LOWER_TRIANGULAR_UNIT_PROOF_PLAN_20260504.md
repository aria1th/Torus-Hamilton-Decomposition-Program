# ZMod Lower-Triangular Unit Odometer Proof Note

Date: 2026-05-04.

Target:

```lean
Shared.ZModVectorLowerTriangularUnitCycleCoordinateGoal
```

This generic theorem is now Lean-closed.  It is needed by the return-tail
triangular/unit route:
if a map on `Fin r -> ZMod m` has lower-triangular form

```lean
F x k = x k + gamma k (x restricted to lower coordinates)
```

and every total carry

```lean
∑ x : (Fin k -> ZMod m), gamma k x
```

is a unit in `ZMod m`, then `F` admits a rank equivalence to
`ZMod (m^r)` incremented by `1`.

## Lean Progress

The final theorem is closed in `Shared/Monodromy.lean`:

```lean
theorem Shared.zmodVectorLowerTriangularUnitCycleCoordinate :
    Shared.ZModVectorLowerTriangularUnitCycleCoordinateGoal
```

The unit one-coordinate additive facts are now Lean-closed:

```lean
theorem Shared.zmod_add_single_cycle_of_unit
    {m : Nat} [NeZero m] {a : ZMod m} (ha : IsUnit a) :
    Shared.IsSingleCycleMap (fun x : ZMod m => x + a)

noncomputable def Shared.CycleCoordinate.zmodAddConstOfUnit
    {m : Nat} [NeZero m] {a : ZMod m} (ha : IsUnit a) :
    Shared.CycleCoordinate m (fun x : ZMod m => x + a)
```

The unit-carry skew-product analogues are also Lean-closed:

```lean
theorem Shared.sectionReturn_skewProductMap_zmod_add_single_cycle_of_unit
theorem Shared.single_cycle_of_skewProduct_zmod_additive_unit_carry

noncomputable def
  Shared.sectionReturn_skewProductMap_zmod_add_cycleCoordinate_of_unit
noncomputable def
  Shared.cycleCoordinate_of_skewProduct_zmod_additive_unit_carry
```

These avoid converting a `ZMod m` unit carry into a natural-number coprime
witness.  This matters for composite odd moduli: the relevant hypothesis is
unit carry, not merely nonzero carry.

The vector split needed for the induction step is now Lean-closed:

```lean
def Shared.zmodVectorSnocEquiv (n m : Nat) :
    (Fin (n + 1) -> ZMod m) ≃ (Fin n -> ZMod m) × ZMod m

theorem Shared.zmodVectorTake_snoc
theorem Shared.zmodVectorTake_snoc_self
```

These express that `take` ignores the final coordinate of `Fin.snoc`.

The ranked-base period and orbit-cover lemmas are now Lean-closed:

```lean
theorem Shared.zmod_rank_iterate_period
theorem Shared.zmod_rank_orbit_cover_lt
```

The finite carry-sum and ranked-base skew-product wrappers are now Lean-closed:

```lean
theorem Shared.skewFiberAdditiveCarry_eq_sum_range
theorem Shared.skewFiberAdditiveCarry_eq_univ_sum_of_rank_step

theorem
  Shared.single_cycle_of_skewProduct_zmod_additive_carry_of_rank_unit_sum

noncomputable def
  Shared.cycleCoordinate_of_skewProduct_zmod_additive_carry_of_rank_unit_sum
```

These say that a ranked base odometer together with a unit total carry gives a
single cycle, or a `CycleCoordinate`, for the additive skew product.

## Closed Proof Assembly

The full proof lives in `Shared/Monodromy.lean`, not
`Shared/TorusCayley.lean`, because the target is defined in `TorusCayley` while
the proof needs the skew-product API from `Monodromy`.

The theorem:

```lean
theorem Shared.zmodVectorLowerTriangularUnitCycleCoordinate :
    Shared.ZModVectorLowerTriangularUnitCycleCoordinateGoal
```

The proof is by induction on `r`.

Base `r = 0`: use `Shared.zmodVectorPowerEquiv 0 m`; the step equation is
trivial because both sides live over `ZMod 1`.

Step `r = n + 1`: split the vector into

```lean
(Fin n -> ZMod m) × ZMod m
```

using `Shared.zmodVectorSnocEquiv`.  Define the base map by taking the lower
`n` coordinates of `F` after zero-extending the last coordinate, and define the
last-coordinate carry as `gamma n`.

The induction hypothesis gives a rank equivalence for the base map.  The
current ranked-base unit-carry skew-product lemmas then close the
last-coordinate extension.

With these helpers, the remaining induction should be a conjugation of `F` to

```lean
Shared.skewProductMap baseStep (fun u z => z + carry u)
```

followed by the unit-carry skew-product theorem above.  This is now the actual
Lean proof shape.

## Remaining Return-Tail Fields

The generic vector theorem is no longer an external field.  For the first-hit
return-tail route, the remaining Lean obligations are now only:

```lean
PrefixCountFirstHitReturnTailTriangularGoal
PrefixCountFirstHitReturnTailCocycleUnitGoal
```

Lean packages those two fields as:

```lean
def PrefixCountFirstHitReturnTailTriangularCocycleBlocksGoal : Prop :=
  PrefixCountFirstHitReturnTailTriangularGoal ∧
  PrefixCountFirstHitReturnTailCocycleUnitGoal

theorem prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_triangularCocycleBlocks
    (hBlocks : PrefixCountFirstHitReturnTailTriangularCocycleBlocksGoal) :
    PrefixCountFirstHitReturnTailMonodromyOrbitGoal
```
