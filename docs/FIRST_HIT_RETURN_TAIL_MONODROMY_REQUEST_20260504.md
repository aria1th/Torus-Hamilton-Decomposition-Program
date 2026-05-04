# First-Hit Return-Tail Monodromy Request

Date: 2026-05-04.

## Purpose

This is the current high-modulus cyclicity request for the all-dimensional
odd-modulus Lean goal.  It supersedes the older schedule-wide request as the
preferred target for the first-hit canonical high branch.

The point is to prove only the monodromy that remains after Lean has already
constructed the first-hit schedule, proved row-Latin/layer-bijective facts, and
reduced the root-flat return to a head-tail skew product.

## Files To Read

1. `RoundComposite/OddCore.lean`
2. `RoundComposite/PrefixCount.lean`
3. `Shared/Monodromy.lean`
4. `Shared/RootFlat.lean`
5. `docs/ODD_TORI_CURRENT_GOAL_V3_3_20260504.md`
6. Optional legacy context: `docs/D11_ODD_WORKING_CERTIFICATE_NOTE_20260502.md`
7. Optional older request: `docs/ROOT_FLAT_CANONICAL_SCHEDULE_REQUEST_20260504.md`

## Preferred Lean Target

```lean
def RoundComposite.Concrete
  .PrefixCountFirstHitReturnTailMonodromyOrbitGoal : Prop :=
  forall {d m : Nat} [NeZero m] (hd2 : 2 <= d)
      {C : PrefixCount.Parts d},
    Odd d -> 5 <= d -> Odd m -> d <= m ->
    C.Admissible m ->
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) ->
    forall c : Fin d, forall tail1 tail2 : Fin (d - 2) -> ZMod m,
      exists n : Nat,
        (prefixCountFirstHitReturnTailMonodromy hd2 L c)^[n] tail1 =
          tail2
```

where:

```lean
noncomputable def RoundComposite.Concrete
  .prefixCountFirstHitReturnTailMonodromy
    {d m : Nat} [NeZero m] (hd2 : 2 <= d)
    {C : PrefixCount.Parts d}
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) (c : Fin d) :
    (Fin (d - 2) -> ZMod m) -> (Fin (d - 2) -> ZMod m)
```

is the tail projection of the `m`-fold root-flat return, started at head
coordinate `0`.

## Already Lean-Closed Bridges

Lean proves the bijective part of the tail monodromy automatically:

```lean
theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnTailMonodromy_bijective :
    Function.Bijective (prefixCountFirstHitReturnTailMonodromy hd2 L c)
```

Therefore the preferred orbit target is enough for the full tail-monodromy
target:

```lean
theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnTailMonodromyGoal_of_orbit
    (hOrbit : PrefixCountFirstHitReturnTailMonodromyOrbitGoal) :
    PrefixCountFirstHitReturnTailMonodromyGoal
```

If the proof naturally constructs an odometer coordinate, the alternate target
is:

```lean
def RoundComposite.Concrete
  .PrefixCountFirstHitReturnTailRankGoal : Prop :=
  forall {d m : Nat} [NeZero m] (hd2 : 2 <= d) {C : PrefixCount.Parts d},
    Odd d -> 5 <= d -> Odd m -> d <= m ->
    C.Admissible m ->
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) ->
    forall c : Fin d,
      exists rank :
          ((Fin (d - 2) -> ZMod m) -> ZMod (m ^ (d - 2))),
        Function.Bijective rank /\
        forall tail : Fin (d - 2) -> ZMod m,
          rank (prefixCountFirstHitReturnTailMonodromy hd2 L c tail) =
            rank tail + 1
```

Lean proves `PrefixCountFirstHitReturnTailMonodromyOrbitGoal` from this rank
goal using `Shared.single_cycle_of_zmod_rank`.

If the odometer coordinate is naturally an equivalence, use this still smaller
variant:

```lean
def RoundComposite.Concrete
  .PrefixCountFirstHitReturnTailRankEquivGoal : Prop :=
  forall {d m : Nat} [NeZero m] (hd2 : 2 <= d) {C : PrefixCount.Parts d},
    Odd d -> 5 <= d -> Odd m -> d <= m ->
    C.Admissible m ->
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) ->
    forall c : Fin d,
      exists e :
          ((Fin (d - 2) -> ZMod m) ≃ ZMod (m ^ (d - 2))),
        forall tail : Fin (d - 2) -> ZMod m,
          e (prefixCountFirstHitReturnTailMonodromy hd2 L c tail) =
            e tail + 1
```

Lean proves the plain rank goal from this using `Equiv.bijective`.

The generic cardinality/equivalence facts for the tail space are already
available in `Shared/TorusCayley.lean`:

```lean
theorem Shared.card_zmodVector (n m : Nat) [NeZero m] :
    Fintype.card (Fin n -> ZMod m) = m ^ n

noncomputable def Shared.zmodVectorPowerEquiv (n m : Nat) [NeZero m] :
    (Fin n -> ZMod m) ≃ ZMod (m ^ n)
```

The full tail-monodromy target is enough for the previous section-monodromy
target:

```lean
theorem RoundComposite.Concrete
  .prefixCountFirstHitHeadTailSectionMonodromyGoal_of_returnTailMonodromy
    (hTail : PrefixCountFirstHitReturnTailMonodromyGoal) :
    PrefixCountFirstHitHeadTailSectionMonodromyGoal
```

It also proves the definitional bridge:

```lean
theorem RoundComposite.Concrete
  .prefixCountFirstHitSectionReturn_eq_returnTailMonodromy :
    Shared.sectionReturn
        (Shared.skewProductMap
          (prefixCountFirstHitReturnBaseStep C c)
          (prefixCountFirstHitReturnFiberStep hd2 L c))
        (0 : ZMod m) m =
      prefixCountFirstHitReturnTailMonodromy hd2 L c
```

The tail monodromy is also identified with the generic fiber iterate:

```lean
theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnTailMonodromy_eq_fiberIterate :
    prefixCountFirstHitReturnTailMonodromy hd2 L c =
      Shared.skewFiberIterate
        (prefixCountFirstHitReturnBaseStep C c)
        (prefixCountFirstHitReturnFiberStep hd2 L c)
        m (0 : ZMod m)
```

The one-return fiber coordinate formula is named:

```lean
theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnFiberStep_apply :
    prefixCountFirstHitReturnFiberStep hd2 L c z tail j =
      tail j +
        sum_over_layers_of_the_first_hit_direction_equaling_j_plus_one
```

The right side is written in Lean as a `Finset.range m` sum using
`prefixCountLambdaRho`, `prefixCountCanonicalRho`, and `L.layer`.  This is the
first lemma to rewrite when extracting the coordinate carry.

For one-coordinate skew extensions over `ZMod m`, the reusable carry lemmas
are already in `Shared/Monodromy.lean`:

```lean
theorem Shared.sectionReturn_skewProductMap_zmod_add :
    Shared.sectionReturn
        (Shared.skewProductMap baseStep (fun b z => z + carry b))
        base period =
      fun fiber : ZMod m =>
        fiber + Shared.skewFiberAdditiveCarry baseStep carry period base

theorem Shared.single_cycle_of_skewProduct_zmod_additive_carry :
    Nat.Coprime a m ->
    Shared.skewFiberAdditiveCarry baseStep carry period base = (a : ZMod m) ->
    Shared.IsSingleCycleMap
      (Shared.skewProductMap baseStep (fun b z => z + carry b))
```

and the final high-branch/final-theorem adapters:

```lean
theorem RoundComposite.Concrete
  .oddCoreHighModulusPrefixCountGoal_of_v4_highReturnTailOrbit
    (hQge2Proper :
      PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hOrbit : PrefixCountFirstHitReturnTailMonodromyOrbitGoal) :
    OddCoreHighModulusPrefixCountGoal

theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_v4_returnTailOrbit
    (hQge2Proper :
      PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal)
    (hOrbit : PrefixCountFirstHitReturnTailMonodromyOrbitGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

## Mathematical Shape Expected

For fixed color `c`, the first return on the head-tail coordinates has the
form:

```text
(head, tail) |-> (head + C.zero c, fiberStep head tail)
```

The head map is already Lean-closed as a single cycle from:

```lean
C.Admissible m
```

and specifically `Nat.Coprime (C.zero c) m`.

The requested theorem should prove that the full-round tail monodromy over one
head cycle is orbit-transitive on:

```lean
Fin (d - 2) -> ZMod m
```

Lean already supplies bijectivity, so orbit-transitivity is enough to recover
`Shared.IsSingleCycleMap`.

The expected route is triangular/skew:

1. Choose a tail-coordinate order compatible with the first-hit rule.
2. Prove the induced return on each next coordinate is a skew extension over
   the previously proved prefix.
3. Compute the total carry for each extension from `C.Admissible`.
4. Use `Shared.single_cycle_of_skewProduct_base_orbit_monodromy` or the
   lower-level skew-cycle lemma already available in `Shared/Monodromy.lean`.

The carry should ultimately be controlled by the primitive row data in
`PrefixCount.Parts.Admissible`, especially the signed primitive differences
that enter through `C.toMatrix hd2`.

## Desired Output

The most useful response is a Lean-oriented proof plan plus the smallest
auxiliary theorem list.  If code is attempted, prioritize the following:

1. A named coordinate formula for
   `prefixCountFirstHitReturnTailMonodromy hd2 L c tail j`.
2. A triangular/skew decomposition theorem for that map.
3. A total-carry theorem reducing the `j`th carry to the corresponding
   primitive field in `C.Admissible`.
4. A reusable induction theorem that turns those carries into
   `Shared.IsSingleCycleMap`.

Avoid reproving row-Latin, layer bijectivity, or the final torus lift; Lean
already routes those once the tail monodromy target is proved.
