# Odd Tori Remaining Field Requests

Date: 2026-05-04.

This note is a proof-request companion to
`docs/ODD_TORI_CURRENT_GOAL_V3_4_20260504.md`.  It gives the exact remaining
Lean fields for the current preferred endpoint and the recommended prompt for
asking a separate mathematical proof attempt.

Current endpoint:

```lean
def RoundComposite.Concrete
  .OddModulusToriV4ReturnTailClosedTrellisBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal ∧
  OddSuccessorSmallModulusBaseTailGoal

theorem RoundComposite.Concrete
  .oddModulusToriAllDimensionsGoal_of_v4_returnTailClosedTrellis_blocks
    (hBlocks : OddModulusToriV4ReturnTailClosedTrellisBlocksGoal) :
    OddModulusToriAllDimensionsGoal
```

```lean
theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_v4_returnTailClosedTrellis
    (hQge2Trellis : PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

Lean now also exposes the fully split endpoint:

```lean
def RoundComposite.Concrete
  .OddModulusToriV4ReturnTailClosedFullSupportTrellisBlocksGoal : Prop :=
  (PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal ∧
   PrefixCount.OrdinaryQge2IndicatorToFullSupportGoal) ∧
  OddSuccessorSmallModulusBaseTailGoal

theorem RoundComposite.Concrete
  .oddModulusToriAllDimensionsGoal_of_v4_returnTailClosedFullSupportTrellis
    (hFull : PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal)
    (hLift : PrefixCount.OrdinaryQge2IndicatorToFullSupportGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal) :
    OddModulusToriAllDimensionsGoal
```

Lean also exposes the fully split small-branch endpoint:

```lean
def ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal : Prop := ...
def ActiveHall.FiniteHoffman.ExactEdgeColoringGoal : Prop := ...
def ActiveHall.FiniteHoffman.CompatibleDeWerraGoal : Prop := ...

theorem ActiveHall.FiniteHoffman.exactEdgeColoringGoal_of_raw
    (hRaw : ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal) :
    ActiveHall.FiniteHoffman.ExactEdgeColoringGoal

theorem ActiveHall.FiniteHoffman.rawExactEdgeColoringGoal_of_compatibleDeWerra
    (hDW : ActiveHall.FiniteHoffman.CompatibleDeWerraGoal) :
    ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal

def RoundComposite.Concrete
  .OddSuccessorSmallModulusBaseTailGeometryExactEdgeColoringGoal : Prop :=
  OddSuccessorSmallModulusBaseTailGeometryFromHallGoal ∧
  ActiveHall.FiniteHoffman.ExactEdgeColoringGoal

theorem RoundComposite.Concrete
  .oddModulusToriAllDimensionsGoal_of_v4_returnTailClosedFullSupportTrellisGeometryRawEdge
    (hFull : PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal)
    (hLift : PrefixCount.OrdinaryQge2IndicatorToFullSupportGoal)
    (hGeom : OddSuccessorSmallModulusBaseTailGeometryFromHallGoal)
    (hRaw : ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal) :
    OddModulusToriAllDimensionsGoal
```

Remaining fields for the most split endpoint:

```lean
PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal
PrefixCount.OrdinaryQge2IndicatorToFullSupportGoal
OddSuccessorSmallModulusBaseTailGeometryFromHallGoal
ActiveHall.FiniteHoffman.CompatibleDeWerraGoal
```

Equivalently, the first two fields can be replaced by the coarser field
`PrefixCount.OrdinaryQge2SignedTrellisHoffmanGoal`, and the last two fields can
be replaced by the coarser field `OddSuccessorSmallModulusBaseTailGoal`.  The
raw ActiveHall field can be used instead of
`ActiveHall.FiniteHoffman.CompatibleDeWerraGoal`; the slightly coarser field
`ActiveHall.FiniteHoffman.ExactEdgeColoringGoal` is also sufficient.

After the completed q>=2 GPT-5.5 Pro response, Lean now exposes a sharper
standard finite-Hoffman split for the first field:

```lean
def PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal : Prop := ...
def PrefixCount.OrdinaryQge2IndicatorToFullSupportGoal : Prop := ...

theorem PrefixCount.ordinaryQge2SignedTrellisHoffmanGoal_of_fullSupport
    (hFull : OrdinaryQge2SignedFullSupportTrellisGoal)
    (hLift : OrdinaryQge2IndicatorToFullSupportGoal) :
    OrdinaryQge2SignedTrellisHoffmanGoal
```

The preferred q>=2 proof route is now: prove the full-support signed trellis
Hoffman theorem, then prove that the ordinary indicator cuts imply the
full-support inequalities.

The hit-condition locality field, residual reindex field, exact signed
cocycle-sum field, and unit-carry field are now Lean-closed internally.  The
closed unit field still implies the older orbit field through a Lean-closed
skew-iterate preservation theorem, increment-to-triangular bridge, and generic
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
`PrefixCountFirstHitReturnTailMonodromyOrbitGoal` directly, but it is no
longer needed for the current endpoint.

## Request 1: q>=2 Full-Support Signed Trellis

### Files To Read

1. `RoundComposite/PrefixCount.lean`
2. `docs/ODD_TORI_CURRENT_GOAL_V3_4_20260504.md`
3. `docs/GPT55_PRO_SIGNED_TRANSPORT_COUNT_BRANCH_RESPONSE_20260503.md`
4. `docs/GPT55_PRO_QGE2_TRELLIS_HOFFMAN_PROOF_RESPONSE_20260504.md`

### Exact Lean Target

The endpoint still consumes the ordinary signed-trellis Hoffman field:

```lean
def RoundComposite.PrefixCount
  .OrdinaryQge2SignedTrellisHoffmanGoal : Prop := ...

theorem RoundComposite.PrefixCount
  .ordinaryQge2SignedSeedProperCutClosureGoal_of_signedTrellisHoffman
    (hHoffman : OrdinaryQge2SignedTrellisHoffmanGoal) :
    OrdinaryQge2SignedSeedProperCutClosureGoal
```

The preferred proof split for this field is now:

```lean
def RoundComposite.PrefixCount
  .OrdinaryQge2SignedFullSupportTrellisGoal : Prop := ...

def RoundComposite.PrefixCount
  .OrdinaryQge2IndicatorToFullSupportGoal : Prop := ...

theorem RoundComposite.PrefixCount
  .ordinaryQge2SignedTrellisHoffmanGoal_of_fullSupport
    (hFull : OrdinaryQge2SignedFullSupportTrellisGoal)
    (hLift : OrdinaryQge2IndicatorToFullSupportGoal) :
    OrdinaryQge2SignedTrellisHoffmanGoal
```

The full-support interface uses these Lean definitions:

```lean
def RoundComposite.PrefixCount.qge2OrdinaryRowTarget
    (n r : Nat) (a epsBit : Fin n -> Nat) (i : Fin n) : Int := ...

def RoundComposite.PrefixCount.qge2SignedColumnFinset
    (n c : Nat) : Finset (Fin n -> SignedValInt) := ...

noncomputable def RoundComposite.PrefixCount.qge2SignedColumnSupport
    (n c : Nat) (w : Fin n -> Int) : Int := ...
```

For the lifting half, Lean also exposes the separation formulation:

```lean
def RoundComposite.PrefixCount
  .OrdinaryQge2SupportViolationGivesIndicatorCutGoal : Prop := ...

theorem RoundComposite.PrefixCount
  .ordinaryQge2IndicatorToFullSupportGoal_of_separation
    (hSep : OrdinaryQge2SupportViolationGivesIndicatorCutGoal) :
    OrdinaryQge2IndicatorToFullSupportGoal
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
cut inequalities and the row/column sum data, construct the signed matrix.  The
preferred external proof can now target the pair
`OrdinaryQge2SignedFullSupportTrellisGoal` and
`OrdinaryQge2IndicatorToFullSupportGoal`; Lean wraps those into
`OrdinaryQge2SignedTrellisHoffmanGoal`, and then into the older proper-cut
closure field.

### Prompt

Prove the finite signed-column decomposition theorem through the new
full-support split.  The main target is
`OrdinaryQge2SignedFullSupportTrellisGoal`, treated as the ordinary trellis
instance of integral Hoffman/Rado-Edmonds style transportation.  The rows have
prescribed integer sums

```lean
(r : Int) - (a i : Int) - (n : Int) * (epsBit i : Int)
```

and the columns have prescribed negative sums `-(c k)`.  Every entry must lie
in `{ -2, -1, 1, 2 }`, represented by `IsSignedVal`.

Then prove `OrdinaryQge2IndicatorToFullSupportGoal`, preferably through
`OrdinaryQge2SupportViolationGivesIndicatorCutGoal`: any violated full-support
inequality should expose a violated ordinary indicator cut.

Please provide either:

1. a Lean-friendly theorem reducing this exact target to a standard finite
   flow/circulation or polymatroid theorem;
2. a direct constructive proof using the special hypotheses
   `a_i,c_k ∈ {1,2}` and `epsBit_i ∈ {0,1}`;
3. or a concrete counterexample if the stated cut condition is insufficient.

The most useful output is a sequence of auxiliary Lean theorem statements with
proof outlines and exact points where existing `PrefixCount` lemmas apply.

### Active GPT-5.5 Pro Request

```text
request doc: docs/GPT55_PRO_QGE2_TRELLIS_HOFFMAN_PROOF_REQUEST_20260504.md
response id: resp_0078009c9235b49c0069f8dc9d25548194b2b94fd491d49cd7
response doc: docs/GPT55_PRO_QGE2_TRELLIS_HOFFMAN_PROOF_RESPONSE_20260504.md
latest status: completed on 2026-05-04
```

Follow-up q>=2 cut-completion request:

```text
request doc: docs/GPT55_PRO_QGE2_INDICATOR_TO_FULL_SUPPORT_REQUEST_20260504.md
response id: resp_0c636bbdc33191c10069f8e747ade0819c8ef13cac38681513
response doc: docs/GPT55_PRO_QGE2_INDICATOR_TO_FULL_SUPPORT_RESPONSE_20260504.md
latest status: in_progress on 2026-05-04
```

Follow-up q>=2 full-support trellis request:

```text
request doc: docs/GPT55_PRO_QGE2_FULL_SUPPORT_TRELLIS_REQUEST_20260504.md
response id: resp_0bcd9e078159726f0069f8ebcb1594819db42229b737abe499
response doc: docs/GPT55_PRO_QGE2_FULL_SUPPORT_TRELLIS_RESPONSE_20260504.md
latest status: in_progress on 2026-05-04
```

## Closed Record: First-Hit Return-Tail Cocycle Sum

This branch is no longer a remaining proof request.  Lean now closes the full
return-tail cocycle chain:

```lean
theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnLowResidualReindexGoal :
    PrefixCountFirstHitReturnLowResidualReindexGoal

theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnTailLocalHitConditionSumGoal :
    PrefixCountFirstHitReturnTailLocalHitConditionSumGoal

theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnTailCocycleSumGoal :
    PrefixCountFirstHitReturnTailCocycleSumGoal

theorem RoundComposite.Concrete
  .prefixCountFirstHitReturnTailCocycleUnitGoal :
    PrefixCountFirstHitReturnTailCocycleUnitGoal
```

The signed formula remains the correct mathematical statement:

```lean
(∑ x : (Fin k -> ZMod m),
  prefixCountFirstHitReturnTailCocycle hd2 L c k hk x)
  =
  ((-1 : ZMod m) ^ (k + 1)) *
    (((C.step c ⟨k, hk⟩ : Int) - (C.delta c : Int)) : ZMod m)
```

The sign is harmless for the unit-carry route because `(-1)^(k+1)` is a unit.
The final residual-reindex proof uses the low-fiber bijection, the base-cycle
reindex, `Shared.zmodVectorConsEquiv`, and the prefix-map low-residual sum
theorem.

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

Active GPT-5.5 Pro requests:

```text
successor small geometry response:
  docs/GPT55_PRO_SUCCESSOR_SMALL_BASE_TAIL_RESPONSE_20260504.md

ActiveHall ordered-SDR proof request:
  request doc: docs/GPT55_PRO_ACTIVE_HALL_ORDERED_SDR_PROOF_REQUEST_20260504.md
  response id: resp_050d642997a6ebc00069f8dceccb388192ae6b3842da834279
  response doc: docs/GPT55_PRO_ACTIVE_HALL_ORDERED_SDR_PROOF_RESPONSE_20260504.md
  latest status: completed on 2026-05-04
```

After this response, Lean now also exposes the copied-edge finite Hoffman
interface and adapters:

```lean
def ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal : Prop := ...
def ActiveHall.FiniteHoffman.ExactEdgeColoringGoal : Prop := ...
def ActiveHall.FiniteHoffman.CompatibleDeWerraGoal : Prop := ...

theorem ActiveHall.FiniteHoffman.rawExactEdgeColoringGoal_of_compatibleDeWerra
    (hDW : ActiveHall.FiniteHoffman.CompatibleDeWerraGoal) :
    ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal

theorem ActiveHall.FiniteHoffman.exactEdgeColoringGoal_of_raw
    (hRaw : ActiveHall.FiniteHoffman.RawExactEdgeColoringGoal) :
    ActiveHall.FiniteHoffman.ExactEdgeColoringGoal

theorem ActiveHall.hoffmanOrderedSDRGoal_of_exactEdgeColoring
    (hEdge : ActiveHall.FiniteHoffman.ExactEdgeColoringGoal) :
    ActiveHall.HoffmanOrderedSDRGoal

theorem ActiveHall.hallRealizationGoal_of_exactEdgeColoring
    (hEdge : ActiveHall.FiniteHoffman.ExactEdgeColoringGoal) :
    ActiveHall.HallRealizationGoal

theorem ActiveHall.eraseLastHallCutsTokenLinearChoiceGoal_of_exactEdgeColoring
    (hEdge : ActiveHall.FiniteHoffman.ExactEdgeColoringGoal) :
    ActiveHall.EraseLastHallCutsTokenLinearChoiceGoal
```

Follow-up exact edge-colouring proof request:

```text
request doc: docs/GPT55_PRO_ACTIVE_HALL_EXACT_EDGE_COLORING_REQUEST_20260504.md
response id: resp_0cd087a6b2f8d1cf0069f8e8faaf4881a0beb65e653ae30d4c
response doc: docs/GPT55_PRO_ACTIVE_HALL_EXACT_EDGE_COLORING_RESPONSE_20260504.md
latest status: completed on 2026-05-04
```

Follow-up successor-small geometry request:

```text
request doc: docs/GPT55_PRO_SUCCESSOR_SMALL_GEOMETRY_FROM_HALL_REQUEST_20260504.md
response id: resp_01731cacc08aae120069f8eb3bbeec819d8a723b1647b82643
response doc: docs/GPT55_PRO_SUCCESSOR_SMALL_GEOMETRY_FROM_HALL_RESPONSE_20260504.md
latest status: in_progress on 2026-05-04
```

Thus the abstract ActiveHall part can now be supplied by the more standard
copied-edge prescribed colouring theorem instead of directly proving the
`Symboling` formulation.

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
