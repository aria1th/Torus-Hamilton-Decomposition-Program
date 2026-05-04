# Odd Tori Remaining Field Requests

Date: 2026-05-04.

This note is a proof-request companion to
`docs/ODD_TORI_CURRENT_GOAL_V3_4_20260504.md`.  It gives the three exact
remaining Lean fields for the current preferred endpoint and the recommended
prompt for asking a separate mathematical proof attempt.

Current endpoint:

```lean
theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_v4_returnTailOrbit_blocks
    (hBlocks : OddModulusToriV4ReturnTailOrbitBlocksGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

Remaining fields:

```lean
PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal
PrefixCountFirstHitReturnTailMonodromyOrbitGoal
OddSuccessorSmallModulusBaseTailGoal
```

## Request 1: q>=2 Proper-Cut Signed Closure

### Files To Read

1. `RoundComposite/PrefixCount.lean`
2. `docs/ODD_TORI_CURRENT_GOAL_V3_4_20260504.md`
3. `docs/GPT55_PRO_SIGNED_TRANSPORT_COUNT_BRANCH_RESPONSE_20260503.md`

### Exact Lean Target

The active target is the torus-shaped ordinary q>=2 signed closure:

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

## Request 2: First-Hit Return-Tail Orbit / Rank Route

### Files To Read

1. `RoundComposite/OddCore.lean`
2. `RoundComposite/PrefixCount.lean`
3. `Shared/Monodromy.lean`
4. `Shared/RankCycle.lean`
5. `Shared/TorusCayley.lean`
6. `Shared/RootFlat.lean`
7. `docs/FIRST_HIT_RETURN_TAIL_MONODROMY_REQUEST_20260504.md`
8. `docs/ODD_TORI_CURRENT_GOAL_V3_4_20260504.md`

### Exact Lean Target

The preferred target is the orbit/transitivity part of the first-hit
return-tail monodromy:

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

If an odometer coordinate is more natural, any of the following sufficient
targets is preferable:

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

def RoundComposite.Concrete
  .PrefixCountFirstHitReturnTailCycleCoordinateGoal : Prop :=
  forall {d m : Nat} [NeZero m] (hd2 : 2 <= d) {C : PrefixCount.Parts d},
    Odd d -> 5 <= d -> Odd m -> d <= m ->
    C.Admissible m ->
    (L : PrefixCount.LayerPermCounts d m (C.toMatrix hd2)) ->
    forall c : Fin d,
      Shared.CycleCoordinate (m ^ (d - 2))
        (prefixCountFirstHitReturnTailMonodromy hd2 L c)
```

### Already Lean-Closed

Lean already builds the first-hit schedule, proves the row-Latin and
layer-bijective parts, reduces the root-flat return to head-tail monodromy, and
proves bijectivity of the tail map.  The remaining request is only the orbit
or odometer part.

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

Prove the high-modulus first-hit return-tail orbit theorem
`PrefixCountFirstHitReturnTailMonodromyOrbitGoal`.  It is also sufficient to
prove either rank target above, or the `CycleCoordinate` target.

The proof should focus on the tail map

```lean
prefixCountFirstHitReturnTailMonodromy hd2 L c :
  (Fin (d - 2) -> ZMod m) -> (Fin (d - 2) -> ZMod m)
```

for fixed color `c`.  Lean already proves bijectivity, so it is enough to show
that every tail reaches every other tail under iteration.  A rank proof should
construct an odometer coordinate

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

The expected mathematical route is triangular/skew:

1. choose a tail-coordinate order compatible with the first-hit rule;
2. prove each next coordinate is a skew extension over the previous prefix;
3. compute the total carry from the primitive row data in `C.Admissible`;
4. use the existing `Shared/Monodromy.lean` and `Shared/RankCycle.lean`
   cycle criteria.

Do not spend effort on row-Latin, layer bijectivity, root-flat schedule
construction, or the final torus lift.  Those bridges are already Lean-closed;
the open field is exactly the tail orbit/rank argument.

## Request 3: Successor Small-Modulus Base-Tail Branch

### Files To Read

1. `RoundComposite/OddCore.lean`
2. `RoundComposite/SeedSemigroup.lean`
3. `RoundComposite/ActiveHall.lean`
4. `Shared/RootFlat.lean`
5. `docs/ACTIVE_HALL_TOKEN_LINEAR_REQUEST_20260504.md`
6. `docs/GPT55_PRO_ACTIVE_HALL_TOKEN_LINEAR_RESPONSE_20260504.md`
7. `docs/ODD_TORI_CURRENT_GOAL_V3_4_20260504.md`

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
