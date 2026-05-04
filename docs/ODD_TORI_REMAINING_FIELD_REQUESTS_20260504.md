# Odd Tori Remaining Field Requests

Date: 2026-05-04.

This note is a proof-request companion to
`docs/ODD_TORI_CURRENT_GOAL_V3_4_20260504.md`.  It gives the exact remaining
Lean fields for the current preferred endpoint and the recommended prompt for
asking a separate mathematical proof attempt.

Current endpoint:

```lean
theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_v4_returnTailCocycleSumTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hSum : PrefixCountFirstHitReturnTailCocycleSumGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

Remaining fields:

```lean
PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal
PrefixCountFirstHitReturnTailCocycleSumGoal
OddSuccessorSmallModulusBaseTailGoal
```

The hit-condition locality field is now Lean-closed as
`prefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal`.  The remaining
exact cocycle sum field implies the unit field via `C.Admissible.prim_step`,
and then implies the older orbit field through a Lean-closed skew-iterate
preservation theorem, increment-to-triangular bridge, and generic
lower-triangular odometer theorem:

```lean
theorem Shared.zmodVectorLowerTriangularUnitCycleCoordinate :
    Shared.ZModVectorLowerTriangularUnitCycleCoordinateGoal

theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_hitConditionUnitBlocks
    (hBlocks : PrefixCountFirstHitReturnFiberHitConditionUnitBlocksGoal) :
    PrefixCountFirstHitReturnTailMonodromyOrbitGoal
```

Equivalently, one may still request
`PrefixCountFirstHitReturnTailMonodromyOrbitGoal` directly.

## Request 1: q>=2 Proper-Cut Signed Closure

### Files To Read

1. `RoundComposite/PrefixCount.lean`
2. `docs/ODD_TORI_CURRENT_GOAL_V3_4_20260504.md`
3. `docs/GPT55_PRO_SIGNED_TRANSPORT_COUNT_BRANCH_RESPONSE_20260503.md`

### Exact Lean Target

The preferred target is now the smaller ordinary signed-trellis Hoffman field,
which Lean wraps into the torus-shaped proper-cut closure:

```lean
def RoundComposite.PrefixCount
  .OrdinaryQge2SignedTrellisHoffmanGoal : Prop := ...

theorem RoundComposite.PrefixCount
  .ordinaryQge2SignedSeedProperCutClosureGoal_of_signedTrellisHoffman
    (hHoffman : OrdinaryQge2SignedTrellisHoffmanGoal) :
    OrdinaryQge2SignedSeedProperCutClosureGoal
```

The older sufficient target is the torus-shaped ordinary q>=2 signed closure:

```lean
def RoundComposite.PrefixCount
  .OrdinaryQge2SignedSeedProperCutClosureGoal : Prop :=
  ∀ {n C r : Nat},
    Even n → 4 ≤ n → Odd r → r < n → 0 < r →
    ∀ (a : Fin n → Nat) (epsBit : Fin n → Nat)
      (c : Fin (n - 1) → Nat),
      (∀ i : Fin n, a i = 1 ∨ a i = 2) →
      (∀ i : Fin n, epsBit i = 0 ∨ epsBit i = 1) →
      (∀ k : Fin (n - 1), c k = 1 ∨ c k = 2) →
      (∑ i : Fin n, a i) = C →
      (∑ i : Fin n, epsBit i) = r →
      (∑ k : Fin (n - 1), c k) = C →
      (∀ J : Finset (Fin n), J.Nonempty →
        J ≠ (Finset.univ : Finset (Fin n)) →
        (∑ i ∈ J, ((r : Int) - (a i : Int)
            - (n : Int) * (epsBit i : Int)))
          ≤ ∑ k : Fin (n - 1),
              qge2ColumnCapacity n J.card (c k)) →
      ∃ S : Fin n → Fin (n - 1) → Int,
        (∀ i k, IsSignedVal (S i k)) ∧
        (∀ i : Fin n,
          (∑ k : Fin (n - 1), S i k)
            = (r : Int) - (a i : Int)
                - (n : Int) * (epsBit i : Int)) ∧
        (∀ k : Fin (n - 1), (∑ i : Fin n, S i k) = - (c k : Int))
```

Do not target the broader arbitrary-row theorem
`RoundComposite.PrefixCount.Qge2SignedColumnPackingGoal`: Lean now proves
`PrefixCount.not_qge2SignedColumnPackingGoal` by a small `n = 4` counterexample.
The cut upper bounds alone do not characterize arbitrary row targets; the
ordinary row shape above is still the active field.

The audit script
`scripts/verify_qge2_proper_cut_small.py` reproduces this counterexample and
checks the active ordinary-row/proper-cut target over small even `n`.  Its
default run checks `n=4`; `--max-n 6` performs a slower exhaustive pass through
`n=6`.

### Already Lean-Closed

Lean proves that empty and full row cuts are automatic:

```lean
ordinaryQge2SignedSeedClosureGoal_iff_properCutClosure
```

Lean also exposes direct wrappers from the proper-cut theorem to the q>=2
matrix/core branch:

```lean
ordinaryQge2SignedMatrixGoal_of_properCutClosure
ordinaryQge2SignedCoreGoal_of_properCutClosure
```

Lean also proves the single-column necessary capacity bound:

```lean
theorem PrefixCount.qge2ColumnCapacity_upper_bound
    {n c : Nat} {v : Fin n -> Int}
    (hv : forall i : Fin n, IsSignedVal (v i))
    (hsum : (sum i : Fin n, v i) = - (c : Int))
    (J : Finset (Fin n)) :
    (sum i in J, v i) <= qge2ColumnCapacity n J.card c
```

This records that `qge2ColumnCapacity` is the correct upper envelope for a
single signed column with total sum `-c`.

Summing those single-column bounds gives the matrix-level necessary cut
condition:

```lean
theorem PrefixCount.qge2SignedMatrix_row_cut_bound
    {n r : Nat}
    {a epsBit : Fin n -> Nat} {c : Fin (n - 1) -> Nat}
    {S : Fin n -> Fin (n - 1) -> Int}
    (hSigned : forall i k, IsSignedVal (S i k))
    (hRow :
      forall i : Fin n,
        (sum k : Fin (n - 1), S i k)
          = (r : Int) - (a i : Int)
              - (n : Int) * (epsBit i : Int))
    (hCol :
      forall k : Fin (n - 1),
        (sum i : Fin n, S i k) = - (c k : Int))
    (J : Finset (Fin n)) :
    (sum i in J, ((r : Int) - (a i : Int)
        - (n : Int) * (epsBit i : Int)))
      <= sum k : Fin (n - 1), qge2ColumnCapacity n J.card (c k)
```

Thus the remaining q>=2 field is the sufficiency direction: given exactly these
cut inequalities and the row/column sum data, construct the signed matrix.

The target can therefore focus only on nonempty proper cuts.

### Prompt

Prove the finite signed-column decomposition theorem
`OrdinaryQge2SignedSeedProperCutClosureGoal`.  Treat it as a standalone
integral Hoffman/Rado-Edmonds style transportation theorem.  The rows have
prescribed integer sums

```lean
(r : Int) - (a i : Int) - (n : Int) * (epsBit i : Int)
```

and the columns have prescribed negative sums `-(c k)`.  Every entry must lie
in `{ -2, -1, 1, 2 }`, represented by `IsSignedVal`.

Please provide either:

1. a Lean-friendly theorem reducing this exact target to a standard finite
   flow/circulation or polymatroid theorem;
2. a direct constructive proof using the special hypotheses
   `a_i,c_k ∈ {1,2}` and `epsBit_i ∈ {0,1}`;
3. or a concrete counterexample if the stated cut condition is insufficient.

The most useful output is a sequence of auxiliary Lean theorem statements with
proof outlines and exact points where existing `PrefixCount` lemmas apply.

## Request 2: First-Hit Return-Tail Cocycle Sum

### Files To Read

1. `RoundComposite/OddCore.lean`
2. `RoundComposite/PrefixCount.lean`
3. `Shared/Monodromy.lean`
4. `Shared/RankCycle.lean`
5. `Shared/TorusCayley.lean`
6. `Shared/RootFlat.lean`
7. `docs/FIRST_HIT_RETURN_TAIL_MONODROMY_REQUEST_20260504.md`
8. `docs/ODD_TORI_CURRENT_GOAL_V3_4_20260504.md`
9. `docs/GPT55_PRO_RETURN_TAIL_ORBIT_RESPONSE_20260504.md`
10. `docs/ZMOD_LOWER_TRIANGULAR_UNIT_PROOF_PLAN_20260504.md`
11. `docs/GPT55_PRO_RETURN_TAIL_HIT_CONDITION_UNIT_REQUEST_20260504.md`
12. `docs/GPT55_PRO_RETURN_TAIL_HIT_CONDITION_UNIT_RESPONSE_20260504.md`
    for the completed exact-sum proof route

### Exact Lean Target

The one-step hit-condition dependency is now Lean-closed:

```lean
theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal :
    PrefixCountFirstHitReturnFiberHitConditionDependsOnTakeGoal
```

The unit-carry field is now Lean-reduced from the exact sum target:

```lean
theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnTailCocycleUnitGoal_of_sum
    (hSum : PrefixCountFirstHitReturnTailCocycleSumGoal) :
    PrefixCountFirstHitReturnTailCocycleUnitGoal
```

The preferred remaining target for the first-hit return-tail monodromy is:

```lean
def RoundComposite.Concrete
  .PrefixCountFirstHitReturnTailCocycleSumGoal : Prop :=
  forall {d m : Nat} [NeZero m] (hd2 : 2 <= d) {C : PrefixCount.Parts d},
    Odd d -> 5 <= d -> Odd m -> d <= m ->
    C.Admissible m ->
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) ->
    forall c : Fin d, forall k : Nat, forall hk : k < d - 2,
      (∑ x : (Fin k -> ZMod m),
        prefixCountFirstHitReturnTailCocycle hd2 L c k hk x)
        =
        ((-1 : ZMod m) ^ (k + 1)) *
          (((C.step c ⟨k, hk⟩ : Int) - (C.delta c : Int)) : ZMod m)

theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_hitConditionUnitBlocks
    (hBlocks : PrefixCountFirstHitReturnFiberHitConditionUnitBlocksGoal) :
    PrefixCountFirstHitReturnTailMonodromyOrbitGoal
```

Closed `Shared` helpers for this route:

```lean
Shared.zmod_add_single_cycle_of_unit
Shared.CycleCoordinate.zmodAddConstOfUnit
Shared.sectionReturn_skewProductMap_zmod_add_single_cycle_of_unit
Shared.sectionReturn_skewProductMap_zmod_add_cycleCoordinate_of_unit
Shared.single_cycle_of_skewProduct_zmod_additive_unit_carry
Shared.cycleCoordinate_of_skewProduct_zmod_additive_unit_carry
Shared.zmodVectorSnocEquiv
Shared.zmodVectorTake_snoc
Shared.zmodVectorTake_snoc_self
Shared.ZModVectorIncrementDependsOnTake
Shared.zmodVectorIncrementDependsOnTake_skewFiberIterate
Shared.zmod_rank_iterate_period
Shared.zmod_rank_orbit_cover_lt
Shared.skewFiberAdditiveCarry_eq_sum_range
Shared.skewFiberAdditiveCarry_eq_univ_sum_of_rank_step
Shared.single_cycle_of_skewProduct_zmod_additive_carry_of_rank_unit_sum
Shared.cycleCoordinate_of_skewProduct_zmod_additive_carry_of_rank_unit_sum
```

The generic `Shared` proof is already closed as:

```lean
theorem Shared.zmodVectorLowerTriangularUnitCycleCoordinate :
    Shared.ZModVectorLowerTriangularUnitCycleCoordinateGoal
```

This route avoids proving orbit transitivity directly.  It asks for:

```text
every rank cocycle has the exact total carry `C.step c k - C.delta c`
up to the canonical prefix sign `(-1)^(k+1)`.
```

The older GPT-5.5 Pro response established the triangular/unit route and led
to the now-closed generic lower-triangular odometer theorem.  The narrower
follow-up response is complete; after local Lean progress its useful target is
the exact cocycle-sum calculation:

```text
docs/GPT55_PRO_RETURN_TAIL_HIT_CONDITION_UNIT_REQUEST_20260504.md
response id: resp_0db37919e35976200069f8bc2d05408192981ff22f53fe7f37
response doc: docs/GPT55_PRO_RETURN_TAIL_HIT_CONDITION_UNIT_RESPONSE_20260504.md
```

Important correction after local finite verification: the exact target has the
canonical prefix sign `(-1)^(k+1)`.  A small direct evaluator of the Lean
definitions found `d=5,m=5` admissible examples where the unsigned equality is
false, while

```lean
sum = ((-1 : ZMod m) ^ (k + 1)) *
  (((C.step c ⟨k, hk⟩ : Int) - (C.delta c : Int)) : ZMod m)
```

matches the observed values.  The sign is harmless for the unit-carry wrapper,
because `(-1)^(k+1)` is a unit.

The older response identifies the unsigned row-entry difference

```lean
(((C.toMatrix hd2) c ⟨k + 2, _⟩ : Nat) : ZMod m) -
(((C.toMatrix hd2) c ⟨1, _⟩ : Nat) : ZMod m)
```

as the primitive row quantity.  In the current Lean target this row quantity
must be multiplied by the prefix sign above, and should only then be converted
to the named `C.step c ⟨k, hk⟩ - C.delta c` expression after unfolding the
local `Parts.toMatrix` definitions.

Lean now has the cocycle expansion and matrix-projection endpoints for this
route:

```lean
prefixCountFirstHitReturnTailCocycle_eq_sum_hitCondition
prefixCountLayerCount_range_eq_matrix_zmod
prefixCount_toMatrix_rawStep_sub_delta_zmod
prefixCountNoHitSubtypeCard
prefixCountNoHitIndicatorSum
prefixCountHasHitIndicatorSum
prefixCountFirstHitReturnBaseStep_sum_fin_iterate
prefixCountFirstHitReturnBaseStep_sum_range_iterate
Shared.zmodVectorTake_extendZero_apply_bijective_of_incrementDependsOnTake
prefixCountFirstHitSkewFiberIterate_lowPrefix_bijective
```

So the open return-tail proof request should focus on the low-prefix
reindexing across the actual nested `u,t,x` sum and the split by layer symbol.
The raw no-hit/has-hit cardinalities modulo `m`, the base-orbit `u`-sum
reindexing, and the projected-low-prefix bijections are now Lean-closed.

### Already Lean-Closed

Lean already builds the first-hit schedule, proves the row-Latin and
layer-bijective parts, reduces the root-flat return to head-tail monodromy, and
proves bijectivity of the tail map, preservation of this increment-dependency
under `Shared.skewFiberIterate`, and the generic lower-triangular odometer
theorem.  It now also proves the one-step first-hit hit-condition locality and
the reduction from exact sum to unit carry.  The remaining request is the exact
cocycle-sum calculation, with the `(-1)^(k+1)` factor included.

Useful closed bridges:

```lean
theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnTailMonodromy_bijective :
    Function.Bijective (prefixCountFirstHitReturnTailMonodromy hd2 L c)

theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnTailMonodromyGoal_of_orbit
    (hOrbit : PrefixCountFirstHitReturnTailMonodromyOrbitGoal) :
    PrefixCountFirstHitReturnTailMonodromyGoal

theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_rank
    (hRank : PrefixCountFirstHitReturnTailRankGoal) :
    PrefixCountFirstHitReturnTailMonodromyOrbitGoal

theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnTailRankGoal_of_rankEquiv
    (hEquiv : PrefixCountFirstHitReturnTailRankEquivGoal) :
    PrefixCountFirstHitReturnTailRankGoal

theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnTailRankEquivGoal_of_cycleCoordinate
    (hCycle : PrefixCountFirstHitReturnTailCycleCoordinateGoal) :
    PrefixCountFirstHitReturnTailRankEquivGoal

theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_hitConditionUnitBlocks
    (hBlocks : PrefixCountFirstHitReturnFiberHitConditionUnitBlocksGoal) :
    PrefixCountFirstHitReturnTailMonodromyOrbitGoal

theorem Shared.single_cycle_of_zmod_rank
    (f : alpha -> alpha) (rank : alpha -> ZMod N)
    (hrank : Function.Bijective rank)
    (hstep : forall x, rank (f x) = rank x + 1) :
    Shared.IsSingleCycleMap f

theorem Shared.single_cycle_of_zmod_rank_equiv
    (f : alpha -> alpha) (rank : alpha ≃ ZMod N)
    (hstep : forall x, rank (f x) = rank x + 1) :
    Shared.IsSingleCycleMap f

noncomputable def Shared.zmodVectorPowerEquiv (n m : Nat) [NeZero m] :
    (Fin n -> ZMod m) ≃ ZMod (m ^ n)

theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnTailMonodromy_eq_fiberIterate :
    prefixCountFirstHitReturnTailMonodromy hd2 L c =
      Shared.skewFiberIterate
        (prefixCountFirstHitReturnBaseStep C c)
        (prefixCountFirstHitReturnFiberStep hd2 L c)
        m (0 : ZMod m)

theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnFiberStep_apply :
    prefixCountFirstHitReturnFiberStep hd2 L c z tail j =
      tail j +
        ∑ t ∈ Finset.range m,
          if (prefixCountLambdaRho d
              (prefixCountCanonicalRho d m hd2 ((t : Nat) : ZMod m)
                ((prefixCountFirstHitCanonicalSchedule hd2 L).prefixMap c t
                  ((prefixCountRootStateHeadTailEquiv d m hd2).symm
                    (z, tail))))
              (L.layer (prefixCountLayerIndex ((t : Nat) : ZMod m)) c)).val
              = j.val + 1
          then (1 : ZMod m) else 0
```

### Prompt

Prove the high-modulus first-hit return-tail exact cocycle-sum field:

```lean
PrefixCountFirstHitReturnTailCocycleSumGoal
```

This is now preferred over proving
`PrefixCountFirstHitReturnTailMonodromyOrbitGoal` directly.  It is still
sufficient to prove the orbit field, either rank target, or the
`CycleCoordinate` target.

The proof should focus on the tail map

```lean
prefixCountFirstHitReturnTailMonodromy hd2 L c :
  (Fin (d - 2) -> ZMod m) -> (Fin (d - 2) -> ZMod m)
```

for fixed color `c`.  The preferred proof should show that each one-step fiber
map

```lean
prefixCountFirstHitReturnFiberStep hd2 L c z
```

has coordinate increments depending only on `Shared.zmodVectorTake ... tail`,
and that the finite sum of each rank cocycle is a unit in `ZMod m`.  If one
instead chooses a rank proof, construct an odometer coordinate

```lean
rank :
  (Fin (d - 2) -> ZMod m) -> ZMod (m ^ (d - 2))
```

or equivalence

```lean
e : (Fin (d - 2) -> ZMod m) ≃ ZMod (m ^ (d - 2))
```

such that the monodromy increments that coordinate by `1`.  Equivalently, a
forward odometer proof may provide:

```lean
K : Shared.CycleCoordinate (m ^ (d - 2))
      (prefixCountFirstHitReturnTailMonodromy hd2 L c)
```

The expected mathematical route is:

1. choose a tail-coordinate order compatible with the first-hit rule;
2. prove each next coordinate is a skew extension over the previous prefix;
3. compute the total carry from the primitive row data in `C.Admissible`,
   including the canonical `(-1)^(k+1)` prefix sign;
4. invoke `prefixCountFirstHitReturnTailMonodromyOrbitGoal_of_hitConditionUnitBlocks`.

Do not spend effort on the generic lower-triangular odometer theorem, row-Latin,
layer bijectivity, root-flat schedule construction, or the final torus lift.
Those bridges are already Lean-closed.  The one-step hit-condition dependency
and the reduction from exact sum to unit carry are also Lean-closed; the open
return-tail field is now exactly the signed total cocycle-sum formula above.

## Request 3: Successor Small-Modulus Base-Tail Branch

### Files To Read

1. `RoundComposite/OddCore.lean`
2. `RoundComposite/SeedSemigroup.lean`
3. `RoundComposite/ActiveHall.lean`
4. `Shared/RootFlat.lean`
5. `docs/ACTIVE_HALL_TOKEN_LINEAR_REQUEST_20260504.md`
6. `docs/GPT55_PRO_ACTIVE_HALL_TOKEN_LINEAR_RESPONSE_20260504.md`
7. `docs/ODD_TORI_CURRENT_GOAL_V3_4_20260504.md`
8. `docs/GPT55_PRO_SUCCESSOR_SMALL_BASE_TAIL_RESPONSE_20260504.md`

### Exact Lean Target

Minimal theorem:

```lean
def RoundComposite.Concrete.OddSuccessorSmallModulusBaseTailGoal : Prop :=
  ∀ {b m : Nat},
    5 ≤ b →
    Odd m → 3 ≤ m →
    m < 2 * b + 1 →
    StandardCayleySolved b m →
    StandardCayleySolved (2 * b + 1) m
```

Certificate-facing sufficient theorem:

```lean
def RoundComposite.Concrete
  .OddSuccessorSmallModulusSlackPacketLiftAddGoal : Prop :=
  ∀ {b m T : Nat},
    5 ≤ b →
    Odd m → 3 ≤ m → m < b + T →
    StandardCayleySolved b m →
    (packets : List (List Nat)) →
    packets.length = b →
    (packets.map List.length).sum = b + T →
    (∀ packet, packet ∈ packets → packet.sum = m) →
    (∀ packet, packet ∈ packets →
      ∀ a, a ∈ packet → 0 < a ∧ a < m ∧ Nat.Coprime a m) →
    T = b + 1 →
    m ^ b > m * (b + T) * T →
    StandardCayleySolved (b + T) m
```

Lean already proves:

```lean
oddSuccessorSmallModulusBaseTailGoal_of_slackPacketLiftAdd
oddSuccessorSmallModulusBaseTailGoal_of_baseTailGeometryFromHall
oddSuccessorSmallModulusBaseTailGoal_of_baseTailGeometryFromHoffman
successor_hall_slack
unitCarryPackets_spec
ActiveHall.symbolingWithResidues_iff_feasible_of_eraseLastHallCuts
ActiveHall.symbolingWithResidues_iff_feasible_of_eraseLastHallCutsSelection
ActiveHall.symbolingWithResidues_iff_feasible_of_eraseLastHallCutsChoice
ActiveHall.symbolingWithResidues_iff_feasible_of_eraseLastHallCutsSlackChoice
ActiveHall.symbolingWithResidues_iff_feasible_of_eraseLastHallCutsNontrivialSlackChoice
ActiveHall.symbolingWithResidues_iff_feasible_of_eraseLastHallCutsLinearChoice
ActiveHall.symbolingWithResidues_iff_feasible_of_eraseLastHallCutsTokenLinearChoice
ActiveHall.eraseLastHallCutsTokenLinearChoiceGoal_of_selection
ActiveHall.eraseLastHallCutsSelectionGoal_iff_tokenLinearChoiceGoal
```

So it is enough to prove the additive packet-lift theorem.
Alternatively, prove `OddSuccessorSmallModulusBaseTailGeometryFromHallGoal`
and supply `ActiveHall.HallRealizationGoal`, or prove
`OddSuccessorSmallModulusBaseTailGeometryFromHoffmanGoal` and supply
`ActiveHall.HoffmanOrderedSDRGoal`.

The GPT-5.5 Pro response recommends the following internal split for the Hall
geometry route:

```text
cylinder expansion from StandardCayleySolved b m and UnitSlackPackets
+ active symboling with residues, using ActiveHall.HallRealizationGoal once
+ pure base-tail lift from valid cylinder and active symboling
```

It also warns that the successor hypothesis `T = b + 1` should remain in this
target unless packet-prefix sums are strengthened.  Unit entries alone do not
force all proper packet-prefix sums to be units for composite odd moduli.

### Prompt

Prove the successor small-modulus base-tail branch.  You may target either
`OddSuccessorSmallModulusBaseTailGoal` directly or the sufficient additive
packet theorem `OddSuccessorSmallModulusSlackPacketLiftAddGoal`.

The proof should explain:

1. how a `StandardCayleySolved b m` base decomposition is lifted to dimension
   `b + T` with `T = b + 1`;
2. how the packet data assigns tail carry units;
3. where `ActiveHall.SymbolingWithResidues` or `ActiveHall.HallRealizationGoal`
   is used to realize the active tail symboling;
4. how the resulting root-flat/layered construction yields
   `StandardCayleySolved (b + T) m`.

Do not spend effort on the arithmetic slack inequality or packet existence for
the successor case: Lean already proves these via `successor_hall_slack` and
`unitCarryPackets_spec`.

## Priority Recommendation

The likely fastest order is:

1. First-hit return-tail rank/equivalence, if the canonical return proof from
   the paper already contains an explicit odometer.
2. q>=2 proper-cut signed closure, if a standard finite flow theorem can be
   imported or stated cleanly.
3. successor small branch, because it combines the base-tail construction with
   the Active-Hall realization layer.

If proving `ActiveHall.HallRealizationGoal` separately, use
`docs/ACTIVE_HALL_TOKEN_LINEAR_REQUEST_20260504.md`; it is the current sharp
abstract combinatorics request for that layer.  Lean now exposes named `iff`
wrappers from `HallRealizationGoal` to the erase-last choice, slack, linear,
and token-linear formulations.  It also exposes residue-level iff wrappers from
each erase-last formulation to
`ActiveHall.SymbolingWithResidues I R <-> ActiveHall.FeasibleWithResidues I R`,
so an external proof can target whichever equivalent statement is most natural.

## Mathlib Hall Survey

A local mathlib check found the standard finite Hall theorem:

```lean
Finset.all_card_le_biUnion_card_iff_exists_injective
```

and the graph-facing wrappers:

```lean
SimpleGraph.exists_isMatching_of_forall_ncard_le
SimpleGraph.exists_isPerfectMatching_of_forall_ncard_le
```

These are in:

```text
Mathlib/Combinatorics/Hall/Basic.lean
Mathlib/Combinatorics/Hall/Finite.lean
Mathlib/Combinatorics/SimpleGraph/Hall.lean
```

No direct Hoffman ordered-SDR or capacitated bipartite edge-coloring theorem was
found in the local mathlib tree.  Ordinary Hall is already used inside
`RoundComposite.ActiveHall` for one-symbol token matching and column filling.
The remaining Active-Hall gap is precisely the strengthening from these
column-wise matchings to a row-Latin ordered symboling.
