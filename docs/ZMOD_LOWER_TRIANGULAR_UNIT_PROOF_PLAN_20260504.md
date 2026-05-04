# ZMod Lower-Triangular Unit Odometer Proof Plan

Date: 2026-05-04.

Target:

```lean
Shared.ZModVectorLowerTriangularUnitCycleCoordinateGoal
```

This is the generic theorem needed by the return-tail triangular/unit route:
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

## Remaining Helper Lemmas

The full proof should live in `Shared/Monodromy.lean`, not
`Shared/TorusCayley.lean`, because the target is defined in `TorusCayley` while
the proof needs the skew-product API from `Monodromy`.

The intended theorem:

```lean
noncomputable theorem Shared.zmodVectorLowerTriangularUnitCycleCoordinate :
    Shared.ZModVectorLowerTriangularUnitCycleCoordinateGoal
```

The proof is by induction on `r`.

Base `r = 0`: use `Shared.zmodVectorPowerEquiv 0 m`; the step equation is
trivial because both sides live over `ZMod 1`.

Step `r = n + 1`: split the vector into

```lean
(Fin n -> ZMod m) × ZMod m
```

by a `Fin.snoc` equivalence.  Define the base map by taking the lower `n`
coordinates of `F` after zero-extending the last coordinate, and define the
last-coordinate carry as `gamma n`.

The induction hypothesis gives a rank equivalence for the base map.  The
current unit-carry skew-product lemmas then close the last-coordinate extension
once the section-return carry is identified with the finite sum over all base
states.

Still needed:

```lean
def Shared.zmodVectorSnocEquiv (n m : Nat) :
    (Fin (n + 1) -> ZMod m) ≃ (Fin n -> ZMod m) × ZMod m
```

with simp lemmas for projection and inverse.

```lean
theorem Shared.zmodVectorTake_snoc
theorem Shared.zmodVectorTake_snoc_self
```

to express that `take` ignores the final coordinate.

```lean
theorem Shared.zmod_rank_iterate_period
theorem Shared.zmod_rank_orbit_cover_lt
```

for a map whose rank into `ZMod N` increments by `1`.

```lean
theorem Shared.skewFiberAdditiveCarry_eq_univ_sum_of_rank_step
```

showing that one full ranked base cycle accumulates exactly the finite sum of
the carry over all base states.

With these helpers, the remaining induction should be a conjugation of `F` to

```lean
Shared.skewProductMap baseStep (fun u z => z + carry u)
```

followed by the unit-carry skew-product theorem above.
