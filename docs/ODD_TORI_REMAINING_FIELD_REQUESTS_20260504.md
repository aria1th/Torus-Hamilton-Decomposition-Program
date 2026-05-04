# Odd Tori Remaining Field Requests

Date: 2026-05-04.

This note is a proof-request companion to
`docs/ODD_TORI_MINIMAL_BLOCKS_COMPLETION_AUDIT_20260504.md`.  It gives the
three exact remaining Lean fields for the current minimal endpoint and the
recommended prompt for asking a separate mathematical proof attempt.

Current endpoint:

```lean
theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_v4_minimal_blocks
    (hBlocks : OddModulusToriV4MinimalBlocksGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

Remaining fields:

```lean
PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal
PrefixCountRootFlatCanonicalScheduleCriterionGoal
OddSuccessorSmallModulusBaseTailGoal
```

## Request 1: q>=2 Proper-Cut Signed Closure

### Files To Read

1. `RoundComposite/PrefixCount.lean`
2. `docs/ODD_TORI_MINIMAL_BLOCKS_COMPLETION_AUDIT_20260504.md`
3. `docs/GPT55_PRO_SIGNED_TRANSPORT_COUNT_BRANCH_RESPONSE_20260503.md`

### Exact Lean Target

The cleanest current target is the pure signed-column packing theorem in the
exact ordinary q>=2 branch shape:

```lean
def RoundComposite.PrefixCount.Qge2SignedColumnPackingGoal : Prop :=
  forall {n : Nat}, 4 <= n ->
    forall (R : Fin n -> Int) (c : Fin (n - 1) -> Nat),
    (forall k : Fin (n - 1), c k = 1 ∨ c k = 2) ->
    (sum i : Fin n, R i) =
      - (sum k : Fin (n - 1), (c k : Int)) ->
    (forall J : Finset (Fin n),
      (sum i in J, R i)
        <= sum k : Fin (n - 1), qge2ColumnCapacity n J.card (c k)) ->
    exists S : Fin n -> Fin (n - 1) -> Int,
      (forall i k, IsSignedVal (S i k)) ∧
      (forall i : Fin n, (sum k : Fin (n - 1), S i k) = R i) ∧
      (forall k : Fin (n - 1),
        (sum i : Fin n, S i k) = - (c k : Int))
```

The `n - 1` column count and `4 <= n` hypothesis are intentional.  A completely
free column count would be too strong: for very small or single-column cases,
the cut upper bounds alone do not characterize entrywise nonzero signed columns.

Lean proves the adapter:

```lean
theorem ordinaryQge2SignedSeedClosureGoal_of_columnPacking
    (hPacking : Qge2SignedColumnPackingGoal) :
    OrdinaryQge2SignedSeedClosureGoal
```

Together with
`ordinaryQge2SignedSeedClosureGoal_iff_properCutClosure`, this is sufficient
for the q>=2 field in the minimal odd-tori endpoint.

Lean also exposes direct odd-tori endpoints consuming this packing theorem:

```lean
theorem RoundComposite.Concrete
  .oddSuccessorClosureGoal_of_v4_columnPackingSchedule
    (hPacking : PrefixCount.Qge2SignedColumnPackingGoal)
    (hSchedule : PrefixCountRootFlatCanonicalScheduleCriterionGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddSuccessorClosureGoal

theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_v4_columnPackingSchedule
    (hPacking : PrefixCount.Qge2SignedColumnPackingGoal)
    (hSchedule : PrefixCountRootFlatCanonicalScheduleCriterionGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m

theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_v4_columnPackingSchedule_blocks
    (hBlocks : OddModulusToriV4ColumnPackingScheduleBlocksGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

The torus-shaped target is:

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

### Already Lean-Closed

Lean proves that empty and full row cuts are automatic:

```lean
ordinaryQge2SignedSeedClosureGoal_iff_properCutClosure
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

## Request 2: Root-Flat Canonical Schedule Criterion

### Files To Read

1. `Shared/RootFlat.lean`
2. `RoundComposite/OddCore.lean`
3. `RoundComposite/PrefixCount.lean`
4. `docs/ODD_TORI_MINIMAL_BLOCKS_COMPLETION_AUDIT_20260504.md`

### Exact Lean Target

```lean
def RoundComposite.Concrete
  .PrefixCountRootFlatCanonicalScheduleCriterionGoal : Prop :=
  ∀ {d m : Nat} [NeZero m] (hd2 : 2 ≤ d)
      {C : PrefixCount.Parts d},
    Odd d → 5 ≤ d → Odd m → d ≤ m →
    C.Admissible m →
    PrefixCount.LayerPermCounts d m (C.toMatrix hd2) →
    ∃ S : Shared.RootFlatSchedule
        (Fin d) (Fin d) (PrefixCountRootState d m) m,
      S.step = prefixCountRootStep d m ∧
      S.rowLatin ∧ S.layerBijective ∧ S.returnsSingleCycle
```

### Already Lean-Closed

The generic lift is done.  If this target supplies a schedule with the stated
properties, Lean converts it to the return certificate and then to the torus
Hamilton decomposition:

```lean
prefixCountRootFlatCanonicalReturnGoal_iff_scheduleCriterion
Shared.rootFlatLayeredDecomposition_of_schedule
standardCayleySolved_of_rootFlatLayered_standardStep
```

### Prompt

Construct the canonical root-flat schedule from admissible prefix counts and a
layer permutation decomposition.  The schedule must use

```lean
S.step = prefixCountRootStep d m
```

and prove:

1. `S.rowLatin`;
2. `S.layerBijective`;
3. `S.returnsSingleCycle`.

The expected proof should identify the exact rule assigning directions from the
prefix-count columns, show that `LayerPermCounts` supplies the layer-wise Latin
permutations, and prove the first-return maps are single cycles from the
primitive row conditions in `C.Admissible`.

Please avoid reproving the final torus lift; `Shared/RootFlat.lean` already
handles that once the schedule properties are established.

## Request 3: Successor Small-Modulus Base-Tail Branch

### Files To Read

1. `RoundComposite/OddCore.lean`
2. `RoundComposite/SeedSemigroup.lean`
3. `RoundComposite/ActiveHall.lean`
4. `Shared/RootFlat.lean`
5. `docs/ACTIVE_HALL_TOKEN_LINEAR_REQUEST_20260504.md`
6. `docs/GPT55_PRO_ACTIVE_HALL_TOKEN_LINEAR_RESPONSE_20260504.md`
7. `docs/ODD_TORI_MINIMAL_BLOCKS_COMPLETION_AUDIT_20260504.md`

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

1. Root-flat schedule criterion, if the canonical return proof from the paper is
   already sufficiently explicit.
2. q>=2 proper-cut signed closure, if a standard finite flow theorem can be
   imported or stated cleanly.
3. successor small branch, because it combines the base-tail construction with
   the Active-Hall realization layer.

If proving `ActiveHall.HallRealizationGoal` separately, use
`docs/ACTIVE_HALL_TOKEN_LINEAR_REQUEST_20260504.md`; it is the current sharp
abstract combinatorics request for that layer.

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
