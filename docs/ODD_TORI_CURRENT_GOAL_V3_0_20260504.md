# Odd-Modulus Tori Current Goal v3.0

Date: 2026-05-04.

## Target Theorem

Formalize the all-dimensional odd-modulus closure theorem:

```lean
theorem odd_modulus_tori_all_dimensions
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

## Minimal Proof Spine

### 1. Closure Dispatcher

Generate every `d >= 2` from the solved dimensions `2`, `3`, `5`, `7`,
product closure, and the successor closure `b -> 2*b + 1`.

Lean interface:

```lean
def RoundComposite.Concrete.OddSuccessorClosureGoal : Prop :=
  forall {b m : Nat},
    5 <= b ->
    Odd m -> 3 <= m ->
    StandardCayleySolved b m ->
    StandardCayleySolved (2*b + 1) m
```

Dispatcher endpoint:

```lean
theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_357_and_successor
    (hSucc : OddSuccessorClosureGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

Status: Lean-closed in `RoundComposite/ConcreteEndpoints.lean`.

### 2. Successor Closure

Prove the uniform successor theorem:

```lean
theorem odd_successor_closure
    {b m : Nat}
    (hb5 : 5 <= b)
    (hmodd : Odd m) (hm3 : 3 <= m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2*b + 1) m
```

It is assembled from two construction branches:

```text
m >= 2*b + 1: OddCoreHighModulusPrefixCountGoal
m <  2*b + 1: OddSuccessorSmallModulusBaseTailGoal
```

Status: the conditional branch-split theorem is Lean-closed in
`RoundComposite/OddCore.lean`:

```lean
theorem RoundComposite.Concrete
  .odd_successor_closure_of_high_and_successorSmall
    (hHigh : OddCoreHighModulusPrefixCountGoal)
    (hSmall : OddSuccessorSmallModulusBaseTailGoal)
    {b m : Nat}
    (hb5 : 5 <= b)
    (hmodd : Odd m) (hm3 : 3 <= m)
    (hb : StandardCayleySolved b m) :
    StandardCayleySolved (2*b + 1) m
```

### 3. Construction Blocks

Close the two branch interfaces consumed by successor closure.

High-modulus count branch:

```lean
def RoundComposite.Concrete.OddCoreHighModulusPrefixCountGoal : Prop :=
  forall {d m : Nat}, Odd d -> 5 <= d -> Odd m -> d <= m ->
    StandardCayleySolved d m
```

Preferred Lean inputs for this branch:

```lean
PrefixCount.OrdinaryQge2SignedSeedClosureGoal
PrefixCount.OrdinaryQeq1CanonicalCorrectionGoal
PrefixCount.MarginTransportQge2CompatibleGoal
PrefixCount.MarginTransportQeq1CompatibleGoal
PrefixCountRootFlatCanonicalReturnGoal
```

Root-flat coordinate support now includes the direction-step bijectivity lemmas
`RoundComposite.Concrete.prefixCountRootStepSucc_bijective` and
`RoundComposite.Concrete.prefixCountRootStep_bijective`.  These close the
`layerBijective` side of the eventual canonical certificate once the schedule
and return-cycle proof are supplied.

The `q >= 2` seed choice is now closed in Lean:

```lean
PrefixCount.ordinaryQge2SeedGoal
PrefixCount.ordinaryQge2PlanGoal
PrefixCount.qge2ColumnCapacity
PrefixCount.ordinaryQge2PlanData_row_cut_capacity
PrefixCount.OrdinaryQge2SignedSeedClosureGoal
PrefixCount.ordinaryQge2SignedMatrixGoal_of_signedSeedClosure
```

It chooses a power of two in `[n, 2*n - 2]`; since `m` is odd, that choice is
coprime to `m`, then packages the `1/2` row and column plan.  Lean also proves
the ordinary branch row-cut inequality against the appendix capacity
`min(2*j, 2*(n-j)-c)`.  Thus the remaining q>=2 signed-column theorem is the
Hoffman/Rado-Edmonds integral decomposition input itself, not the surrounding
cut arithmetic.  The v4 ordinary signed-core data now has Lean bridges:

```lean
PrefixCount.ordinaryQge2PlanGoal_of_seed
PrefixCount.ordinaryQge2SignedMatrixGoal_of_signedSeedClosure
PrefixCount.ordinaryQge2SignedCoreGoal_of_plan_and_matrix
PrefixCount.ordinaryQeq1SignedCoreGoal_of_plan_and_matrix
PrefixCount.ordinaryQeq1SignedCoreGoal_of_canonicalMatrix
PrefixCount.OrdinaryQeq1AuxDegreeMatrixData
PrefixCount.OrdinaryQeq1AuxDegreeMatrixGoal
PrefixCount.ordinaryQeq1AuxDegree
PrefixCount.UniformColumnDegreeMatrixData
PrefixCount.UniformColumnDegreeMatrixGoal
PrefixCount.UniformColumnDegreeResidueCountGoal
PrefixCount.UniformColumnDegreeIntervalPartitionGoal
PrefixCount.uniformColumnDegreeCellMap_injective
PrefixCount.uniformColumnDegreeMatrix_row_sum
PrefixCount.uniformColumnDegreeMatrixGoal_of_residueCount
PrefixCount.uniformColumnDegreeBlockResidueSum
PrefixCount.uniformColumnDegreeRangeResidueSum_mul
PrefixCount.uniformColumnDegreeResidueCountGoal_of_intervalPartition
PrefixCount.uniformColumnDegreeIntervalCellMap
PrefixCount.uniformColumnDegreeIntervalCellSet
PrefixCount.uniformColumnDegreeShiftedCellSet
PrefixCount.uniformColumnDegreeIntervalCellMap_injective
PrefixCount.uniformColumnDegreeIntervalCellResidueSum
PrefixCount.uniformColumnDegreePrefix_succ
PrefixCount.uniformColumnDegreeShiftedIntervalPartition
PrefixCount.uniformColumnDegreeIntervalPartitionGoal
PrefixCount.OrdinaryQeq1AuxDegreeArithmeticGoal
PrefixCount.OrdinaryQeq1AuxDegreeTotalGoal
PrefixCount.ordinaryQeq1AuxDegreeTotalGoal
PrefixCount.ordinaryQeq1AuxDegreeMatrixGoal_of_uniformColumnDegree
PrefixCount.ordinaryQeq1AuxDegreeArithmeticGoal_of_total
PrefixCount.ordinaryQeq1AuxMatrixGoal_of_degreeMatrix
PrefixCount.OrdinaryQeq1AuxMatrixData
PrefixCount.OrdinaryQeq1SpecialMatchingData
PrefixCount.OrdinaryQeq1AuxMatrixData.posCols
PrefixCount.OrdinaryQeq1AuxMatrixData.posRows
PrefixCount.OrdinaryQeq1AuxMatrixData.sum_row_eq_two_posCols_card_sub
PrefixCount.OrdinaryQeq1AuxMatrixData.sum_col_eq_two_posRows_card_sub
PrefixCount.OrdinaryQeq1AuxMatrixData.posRows_card
PrefixCount.OrdinaryQeq1AuxMatrixData.posCols_card
PrefixCount.OrdinaryQeq1AuxMatrixData.lowCols
PrefixCount.OrdinaryQeq1AuxMatrixData.lowCols_card
PrefixCount.OrdinaryQeq1AuxMatrixData.exists_distinguished_low_neg
PrefixCount.OrdinaryQeq1AuxSpecialMatchingData
PrefixCount.OrdinaryQeq1AuxMatrixGoal
PrefixCount.OrdinaryQeq1SpecialMatchingGoal
PrefixCount.OrdinaryQeq1AuxSpecialMatchingDataGoal
PrefixCount.OrdinaryQeq1SpecialMatchingCounterexample.aux
PrefixCount.OrdinaryQeq1SpecialMatchingCounterexample.no_specialMatching
PrefixCount.not_ordinaryQeq1SpecialMatchingGoal
PrefixCount.OrdinaryQeq1CanonicalCorrectionData
PrefixCount.OrdinaryQeq1CanonicalCorrectionDataGoal
PrefixCount.ordinaryQeq1CanonicalCorrectionDataGoal_of_auxMatrix_and_specialMatching
PrefixCount.ordinaryQeq1CanonicalCorrectionDataGoal_of_auxSpecialMatchingData
PrefixCount.ordinaryQeq1CanonicalCorrectionGoal_of_dataGoal
PrefixCount.ordinaryQeq1CanonicalMatrixGoal_of_correction
PrefixCount.ordinaryQeq1PlanGoal
PrefixCount.marginTransportQge2CompatibleGoal_of_ordinaryQge2SignedCore
PrefixCount.marginTransportQeq1CompatibleGoal_of_ordinaryQeq1SignedCore
RoundComposite.Concrete
  .oddCoreHighModulusPrefixCountGoal_of_qge2PlanMatrix_qeq1Matrix_and_geometry
RoundComposite.Concrete
  .oddCoreHighModulusPrefixCountGoal_of_qge2SeedMatrix_qeq1Matrix_and_geometry
RoundComposite.Concrete
  .oddCoreHighModulusPrefixCountGoal_of_qge2Matrix_qeq1Matrix_and_geometry
RoundComposite.Concrete
  .oddCoreHighModulusPrefixCountGoal_of_qge2Matrix_qeq1Core_and_geometry
RoundComposite.Concrete
  .oddCoreHighModulusPrefixCountGoal_of_qge2Matrix_qeq1Core_and_rootFlatCanonical
RoundComposite.Concrete
  .oddCoreHighModulusPrefixCountGoal_of_qge2Matrix_qeq1Canonical_and_geometry
RoundComposite.Concrete
  .oddCoreHighModulusPrefixCountGoal_of_qge2Matrix_qeq1Canonical_and_rootFlatCanonical
RoundComposite.Concrete
  .oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1Canonical_and_geometry
RoundComposite.Concrete
  .oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1Canonical_and_rootFlatCanonical
RoundComposite.Concrete
  .oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1Correction_and_geometry
RoundComposite.Concrete
  .oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1Correction_and_rootFlatCanonical
RoundComposite.Concrete
  .oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1CorrectionData_and_rootFlatCanonical
RoundComposite.Concrete
  .oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1AuxMatching_and_rootFlatCanonical
RoundComposite.Concrete
  .oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1DegreeMatching_and_rootFlatCanonical
RoundComposite.Concrete
  .oddCoreHighModulusPrefixCountGoal_of_planMatrixSignedCores_and_geometry
RoundComposite.Concrete
  .oddCoreHighModulusPrefixCountGoal_of_qge2PlanMatrix_qeq1Core_and_geometry
RoundComposite.Concrete
  .oddCoreHighModulusPrefixCountGoal_of_ordinarySignedCores_and_geometry
RoundComposite.Concrete
  .oddCoreHighModulusPrefixCountGoal_of_ordinarySignedCores_and_rootFlatCanonical
RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_ordinarySignedCores_geometry_and_slackPacketLift
RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_ordinarySignedCores_rootFlatCanonical_and_slackPacketLift
RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_qge2Matrix_qeq1Core_geometry_and_slackPacketLift
RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_qge2Matrix_qeq1Core_rootFlatCanonical_and_slackPacketLift
RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_qge2Matrix_qeq1Canonical_geometry_and_slackPacketLift
RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_qge2Matrix_qeq1Canonical_rootFlatCanonical_and_slackPacketLift
RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1Canonical_geometry_and_slackPacketLift
RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1Canonical_rootFlatCanonical_and_slackPacketLift
RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1Correction_rootFlatCanonical_and_slackPacketLift
RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1CorrectionData_rootFlatCanonical_and_slackPacketLift
RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_qge2SeedClosure_qeq1AuxMatching_rootFlatCanonical_and_slackPacketLift
RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_qeq1DegreeMatching
RoundComposite.Concrete
  .OddModulusToriV4ConstructionBlocksGoal
RoundComposite.Concrete
  .OddModulusToriV4JointMatchingBlocksGoal
RoundComposite.Concrete
  .OddModulusToriV4DegreeMatchingBlocksGoal
RoundComposite.Concrete
  .OddModulusToriV4UniformDegreeBlocksGoal
RoundComposite.Concrete
  .OddModulusToriV4UniformTotalBlocksGoal
RoundComposite.Concrete
  .OddModulusToriV4PostUniformBlocksGoal
RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_v4_construction_blocks
RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_v4_joint_matching_blocks
RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_v4_degree_matching_blocks
RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_v4_uniform_degree_blocks
RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_v4_uniform_total_blocks
RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_v4_post_uniform_blocks
RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_qge2Matrix_qeq1Matrix_geometry_and_slackPacketLift
RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_qge2Matrix_qeq1Matrix_rootFlatCanonical_and_slackPacketLift
```

so the `q >= 2` ordinary plan is reduced to the signed-column closure theorem
alone.  The restricted `q = 1` construction is now exposed in its paper-facing
form as `PrefixCount.OrdinaryQeq1CanonicalCorrectionGoal`: it constructs the
canonical matching-correction matrix only in the relevant case `m = n + r`.
The gate still carries the needed odd-modulus hypothesis as `Odd (n + r)`,
matching the manuscript's `r`-odd restricted branch when `n + 1` is odd.
Lean then derives the more general compatibility-facing matrix interface through
`PrefixCount.ordinaryQeq1CanonicalMatrixGoal_of_correction`.  Thus
`OddModulusToriV4ConstructionBlocksGoal` consumes the data-level correction
theorem, not the broader arbitrary-`m` matrix gate.  The `geometry` variants are available
if the count-matrix/root-flat criterion is proved directly, while the
`rootFlatCanonical` variants consume the current canonical-return interface.
Both ordinary branches are now further split into easy plan data and the hard
signed-column/matching-correction matrix closure.  The `q = 1` plan data is
Lean-closed as `PrefixCount.ordinaryQeq1PlanGoal`, so that branch now only needs
the restricted canonical matching-correction theorem.

The arithmetic lowering from the paper's auxiliary `±1` matrix plus corrected
matching output is Lean-closed as
`PrefixCount.ordinaryQeq1CanonicalCorrectionGoal_of_dataGoal`.  Consequently the
remaining q=1 mathematical input can be stated as the data-level existence
theorem `PrefixCount.OrdinaryQeq1CanonicalCorrectionDataGoal`, whose content is
the Gale-Ryser auxiliary matrix and special Hall matching construction.
This has a joint paper-facing interface
`PrefixCount.OrdinaryQeq1AuxSpecialMatchingDataGoal`, which packages the
auxiliary `±1` matrix and its special matching together and Lean-lowers to
correction data through
`PrefixCount.ordinaryQeq1CanonicalCorrectionDataGoal_of_auxSpecialMatchingData`.
The stronger universal split would use
`PrefixCount.OrdinaryQeq1AuxMatrixGoal` and
`PrefixCount.OrdinaryQeq1SpecialMatchingGoal`; when both are available, their
combination is Lean-closed through
`PrefixCount.ordinaryQeq1CanonicalCorrectionDataGoal_of_auxMatrix_and_specialMatching`.
The finite `(n,r)=(8,5)` witness
`PrefixCount.OrdinaryQeq1SpecialMatchingCounterexample.aux` proves
`PrefixCount.not_ordinaryQeq1SpecialMatchingGoal`, so the universal
arbitrary-auxiliary matching interface is stronger than the paper construction
needs.  The current q=1 request should use the joint data interface unless the
auxiliary matrix is canonically fixed.
The auxiliary matrix side is split once more at the Gale-Ryser output level:
`PrefixCount.OrdinaryQeq1AuxDegreeMatrixGoal` asks only for the `0/1`
degree matrix, and Lean closes the conversion to the signed `±1` matrix through
`PrefixCount.ordinaryQeq1AuxMatrixGoal_of_degreeMatrix`.
For the remaining q=1 special matching theorem, Lean now exposes the matching
incidence carried by an arbitrary auxiliary `±1` matrix: `posCols` and `posRows`
count the `+1` entries, `posCols_card` recovers the paper row degrees,
`posRows_card` proves every column has `(n - 2) / 2` positive entries, and
`exists_distinguished_low_neg` isolates the required negative low column in the
distinguished row.  Thus the remaining q=1 matching work is now the Hall
selection of the `P` rows against the high columns plus one such low column.
That degree-matrix side is now split into the row-degree arithmetic and the
generic uniform-column `0/1` matrix realization:
`PrefixCount.OrdinaryQeq1AuxDegreeArithmeticGoal` plus
`PrefixCount.UniformColumnDegreeMatrixGoal` imply
`PrefixCount.OrdinaryQeq1AuxDegreeMatrixGoal` through
`PrefixCount.ordinaryQeq1AuxDegreeMatrixGoal_of_uniformColumnDegree`.
The bounds and positivity part of that arithmetic is Lean-closed from the single
total-degree identity `PrefixCount.OrdinaryQeq1AuxDegreeTotalGoal` through
`PrefixCount.ordinaryQeq1AuxDegreeArithmeticGoal_of_total`.
The total-degree identity itself is Lean-closed as
`PrefixCount.ordinaryQeq1AuxDegreeTotalGoal`.
The generic uniform-column matrix realization has also been lowered to the
cyclic-interval residue count theorem
`PrefixCount.UniformColumnDegreeResidueCountGoal`; Lean closes the row side and
the bridge to `PrefixCount.UniformColumnDegreeMatrixGoal` through
`PrefixCount.uniformColumnDegreeMatrixGoal_of_residueCount`.
The residue count has then been lowered once more to the interval-partition
identity `PrefixCount.UniformColumnDegreeIntervalPartitionGoal`.  This identity
is now Lean-closed as `PrefixCount.uniformColumnDegreeIntervalPartitionGoal`.
The proof uses shifted cyclic intervals
`PrefixCount.uniformColumnDegreeShiftedCellSet`, the injectivity and residue
sum lemmas for each interval cell, and
`PrefixCount.uniformColumnDegreeShiftedIntervalPartition`; combined with
`PrefixCount.uniformColumnDegreeRangeResidueSum_mul` and
`PrefixCount.uniformColumnDegreeResidueCountGoal_of_intervalPartition`, the
uniform-column component is no longer an external block.

Small-modulus successor branch:

```lean
def RoundComposite.Concrete.OddSuccessorSmallModulusBaseTailGoal : Prop :=
  forall {b m : Nat},
    5 <= b ->
    Odd m -> 3 <= m ->
    m < 2*b + 1 ->
    StandardCayleySolved b m ->
    StandardCayleySolved (2*b + 1) m
```

Lean reduces this branch to the broader slack-packet theorem:

```lean
def RoundComposite.Concrete.OddCoreSmallModulusSlackPacketLiftGoal : Prop
```

## Current Working Endpoint

The current all-dimensional endpoint is the v4 construction-block packet:

```lean
theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_v4_construction_blocks
    (hBlocks : OddModulusToriV4ConstructionBlocksGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

where

```lean
def RoundComposite.Concrete.OddModulusToriV4ConstructionBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCount.OrdinaryQeq1CanonicalCorrectionDataGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal
```

The preferred q=1 matching-facing endpoint keeps the auxiliary matrix and its
special matching in one joint data block:

```lean
def RoundComposite.Concrete.OddModulusToriV4JointMatchingBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCount.OrdinaryQeq1AuxSpecialMatchingDataGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_v4_joint_matching_blocks
    (hBlocks : OddModulusToriV4JointMatchingBlocksGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

The paper-facing endpoint with the `q = 1` auxiliary degree matrix split is:

```lean
def RoundComposite.Concrete.OddModulusToriV4DegreeMatchingBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCount.OrdinaryQeq1AuxDegreeMatrixGoal ∧
  PrefixCount.OrdinaryQeq1SpecialMatchingGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_v4_degree_matching_blocks
    (hBlocks : OddModulusToriV4DegreeMatchingBlocksGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

The endpoint with the auxiliary degree matrix split into arithmetic plus generic
uniform-column realization is:

```lean
def RoundComposite.Concrete.OddModulusToriV4UniformDegreeBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCount.OrdinaryQeq1AuxDegreeArithmeticGoal ∧
  PrefixCount.UniformColumnDegreeMatrixGoal ∧
  PrefixCount.OrdinaryQeq1SpecialMatchingGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_v4_uniform_degree_blocks
    (hBlocks : OddModulusToriV4UniformDegreeBlocksGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

The endpoint where the arithmetic side is lowered to the total-degree identity is:

```lean
def RoundComposite.Concrete.OddModulusToriV4UniformTotalBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCount.OrdinaryQeq1AuxDegreeTotalGoal ∧
  PrefixCount.UniformColumnDegreeMatrixGoal ∧
  PrefixCount.OrdinaryQeq1SpecialMatchingGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_v4_uniform_total_blocks
    (hBlocks : OddModulusToriV4UniformTotalBlocksGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

Since `PrefixCount.ordinaryQeq1AuxDegreeTotalGoal` is now Lean-closed, the
current minimal endpoint removes the total-degree identity from the requested
block packet:

```lean
def RoundComposite.Concrete.OddModulusToriV4PostTotalBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCount.UniformColumnDegreeMatrixGoal ∧
  PrefixCount.OrdinaryQeq1SpecialMatchingGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_v4_post_total_blocks
    (hBlocks : OddModulusToriV4PostTotalBlocksGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

The current minimal endpoint further replaces the generic uniform-column matrix
realization by its cyclic-interval residue-count form:

```lean
def RoundComposite.Concrete.OddModulusToriV4ResidueBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCount.UniformColumnDegreeResidueCountGoal ∧
  PrefixCount.OrdinaryQeq1SpecialMatchingGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_v4_residue_blocks
    (hBlocks : OddModulusToriV4ResidueBlocksGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

The interval-partition endpoint was:

```lean
def RoundComposite.Concrete.OddModulusToriV4IntervalBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCount.UniformColumnDegreeIntervalPartitionGoal ∧
  PrefixCount.OrdinaryQeq1SpecialMatchingGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_v4_interval_blocks
    (hBlocks : OddModulusToriV4IntervalBlocksGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

Since `PrefixCount.uniformColumnDegreeIntervalPartitionGoal` is now Lean-closed,
the current minimal endpoint removes the entire uniform-column component from
the requested block packet:

```lean
def RoundComposite.Concrete.OddModulusToriV4PostUniformBlocksGoal : Prop :=
  PrefixCount.OrdinaryQge2SignedSeedClosureGoal ∧
  PrefixCount.OrdinaryQeq1SpecialMatchingGoal ∧
  PrefixCountRootFlatCanonicalReturnGoal ∧
  OddCoreSmallModulusSlackPacketLiftGoal

theorem RoundComposite.Concrete
  .odd_modulus_tori_all_dimensions_of_v4_post_uniform_blocks
    (hBlocks : OddModulusToriV4PostUniformBlocksGoal)
    {d m : Nat} (hd2 : 2 <= d)
    (hmodd : Odd m) (hm3 : 3 <= m) :
    Shared.CayleyHamiltonDecomposition d m
```

Thus the concrete Lean work is exactly:

1. prove the q>=2 signed-column closure theorem;
2. prove the q=1 special matching theorem;
3. prove the prefix-count root-flat canonical return certificate;
4. prove the base-tail Hall-slack packet lift.

## Active Hall Current Boundary

The finite Active Hall realization has been reduced to one narrower selection
interface.  As of the latest Lean state, this is best viewed at the
choice-function level:

```lean
def RoundComposite.ActiveHall.EraseLastHallCutsGoal : Prop
def RoundComposite.ActiveHall.EraseLastHallCutsSelectionGoal : Prop
def RoundComposite.ActiveHall.EraseLastHallCutsChoiceGoal : Prop
def RoundComposite.ActiveHall.EraseLastHallCutsSlackChoiceGoal : Prop
def RoundComposite.ActiveHall.EraseLastHallCutsNontrivialSlackChoiceGoal : Prop
def RoundComposite.ActiveHall.EraseLastHallCutsLinearChoiceGoal : Prop
def RoundComposite.ActiveHall.EraseLastHallCutsTokenLinearChoiceGoal : Prop
def RoundComposite.ActiveHall.HoffmanOrderedSDRGoal : Prop
def RoundComposite.ActiveHall.ColumnFillingUpgradeGoal : Prop

theorem RoundComposite.ActiveHall
  .hallRealizationGoal_of_hoffmanOrderedSDR
    (hHoffman : HoffmanOrderedSDRGoal) :
    HallRealizationGoal

theorem RoundComposite.ActiveHall
  .hoffmanOrderedSDRGoal_of_hallRealization
    (hRealize : HallRealizationGoal) :
    HoffmanOrderedSDRGoal

theorem RoundComposite.ActiveHall
  .hallRealizationGoal_iff_hoffmanOrderedSDRGoal :
    HallRealizationGoal <-> HoffmanOrderedSDRGoal

theorem RoundComposite.ActiveHall
  .hallRealizationGoal_of_columnFillingUpgrade
    (hUpgrade : ColumnFillingUpgradeGoal) :
    HallRealizationGoal

theorem RoundComposite.ActiveHall
  .columnFillingUpgradeGoal_of_hallRealization
    (hRealize : HallRealizationGoal) :
    ColumnFillingUpgradeGoal

theorem RoundComposite.ActiveHall
  .hallRealizationGoal_iff_columnFillingUpgradeGoal :
    HallRealizationGoal <-> ColumnFillingUpgradeGoal

theorem RoundComposite.ActiveHall
  .hallRealizationGoal_of_eraseLastHallCuts
    (hErase : EraseLastHallCutsGoal) :
    HallRealizationGoal

theorem RoundComposite.ActiveHall
  .symbolingWithResidues_of_feasible_and_eraseLastHallCuts
    (hErase : EraseLastHallCutsGoal)
    (hFeasible : FeasibleWithResidues I R) :
    SymbolingWithResidues I R

theorem RoundComposite.ActiveHall
  .symbolingWithResidues_of_feasible_and_hoffmanOrderedSDR
    (hHoffman : HoffmanOrderedSDRGoal)
    (hFeasible : FeasibleWithResidues I R) :
    SymbolingWithResidues I R

theorem RoundComposite.ActiveHall
  .symbolingWithResidues_of_feasible_and_columnFillingUpgrade
    (hUpgrade : ColumnFillingUpgradeGoal)
    (hFeasible : FeasibleWithResidues I R) :
    SymbolingWithResidues I R

theorem RoundComposite.ActiveHall
  .eraseLastHallCutsGoal_of_choice
    (hChoice : EraseLastHallCutsChoiceGoal) :
    EraseLastHallCutsGoal

theorem RoundComposite.ActiveHall
  .eraseLastHallCutsChoiceGoal_of_slackChoice
    (hSlackChoice : EraseLastHallCutsSlackChoiceGoal) :
    EraseLastHallCutsChoiceGoal

theorem RoundComposite.ActiveHall
  .eraseLastHallCutsGoal_of_slackChoice
    (hSlackChoice : EraseLastHallCutsSlackChoiceGoal) :
    EraseLastHallCutsGoal

theorem RoundComposite.ActiveHall
  .eraseLastHallCutsSlackChoiceGoal_of_nontrivial
    (hNontriv : EraseLastHallCutsNontrivialSlackChoiceGoal) :
    EraseLastHallCutsSlackChoiceGoal

theorem RoundComposite.ActiveHall
  .eraseLastHallCutsGoal_of_nontrivialSlackChoice
    (hNontriv : EraseLastHallCutsNontrivialSlackChoiceGoal) :
    EraseLastHallCutsGoal

theorem RoundComposite.ActiveHall
  .eraseLastHallCutsNontrivialSlackChoiceGoal_of_linear
    (hLinear : EraseLastHallCutsLinearChoiceGoal) :
    EraseLastHallCutsNontrivialSlackChoiceGoal

theorem RoundComposite.ActiveHall
  .eraseLastHallCutsLinearChoiceGoal_of_tokenLinear
    (hToken : EraseLastHallCutsTokenLinearChoiceGoal) :
    EraseLastHallCutsLinearChoiceGoal

theorem RoundComposite.ActiveHall
  .eraseLastHallCutsTokenLinearChoiceGoal_of_hallRealization
    (hRealize : HallRealizationGoal) :
    EraseLastHallCutsTokenLinearChoiceGoal

theorem RoundComposite.ActiveHall
  .eraseLastHallCutsGoal_of_linearChoice
    (hLinear : EraseLastHallCutsLinearChoiceGoal) :
    EraseLastHallCutsGoal

theorem RoundComposite.ActiveHall
  .eraseLastHallCutsGoal_of_tokenLinearChoice
    (hToken : EraseLastHallCutsTokenLinearChoiceGoal) :
    EraseLastHallCutsGoal

theorem RoundComposite.ActiveHall
  .hallRealizationGoal_of_eraseLastHallCutsChoice
    (hChoice : EraseLastHallCutsChoiceGoal) :
    HallRealizationGoal

theorem RoundComposite.ActiveHall
  .hallRealizationGoal_of_eraseLastHallCutsSlackChoice
    (hSlackChoice : EraseLastHallCutsSlackChoiceGoal) :
    HallRealizationGoal

theorem RoundComposite.ActiveHall
  .hallRealizationGoal_of_eraseLastHallCutsNontrivialSlackChoice
    (hNontriv : EraseLastHallCutsNontrivialSlackChoiceGoal) :
    HallRealizationGoal

theorem RoundComposite.ActiveHall
  .hallRealizationGoal_of_eraseLastHallCutsLinearChoice
    (hLinear : EraseLastHallCutsLinearChoiceGoal) :
    HallRealizationGoal

theorem RoundComposite.ActiveHall
  .hallRealizationGoal_of_eraseLastHallCutsTokenLinearChoice
    (hToken : EraseLastHallCutsTokenLinearChoiceGoal) :
    HallRealizationGoal

theorem RoundComposite.ActiveHall
  .hallRealizationGoal_iff_eraseLastHallCutsTokenLinearChoiceGoal :
    HallRealizationGoal <-> EraseLastHallCutsTokenLinearChoiceGoal

theorem RoundComposite.ActiveHall
  .eraseLastHallCutsTokenLinearChoiceGoal_of_hoffmanOrderedSDR
    (hHoffman : HoffmanOrderedSDRGoal) :
    EraseLastHallCutsTokenLinearChoiceGoal

theorem RoundComposite.ActiveHall
  .symbolingWithResidues_of_feasible_and_eraseLastHallCutsChoice
    (hChoice : EraseLastHallCutsChoiceGoal)
    (hFeasible : FeasibleWithResidues I R) :
    SymbolingWithResidues I R

theorem RoundComposite.ActiveHall
  .symbolingWithResidues_of_feasible_and_eraseLastHallCutsSlackChoice
    (hSlackChoice : EraseLastHallCutsSlackChoiceGoal)
    (hFeasible : FeasibleWithResidues I R) :
    SymbolingWithResidues I R

theorem RoundComposite.ActiveHall
  .symbolingWithResidues_of_feasible_and_eraseLastHallCutsNontrivialSlackChoice
    (hNontriv : EraseLastHallCutsNontrivialSlackChoiceGoal)
    (hFeasible : FeasibleWithResidues I R) :
    SymbolingWithResidues I R

theorem RoundComposite.ActiveHall
  .symbolingWithResidues_of_feasible_and_eraseLastHallCutsLinearChoice
    (hLinear : EraseLastHallCutsLinearChoiceGoal)
    (hFeasible : FeasibleWithResidues I R) :
    SymbolingWithResidues I R

theorem RoundComposite.ActiveHall
  .symbolingWithResidues_of_feasible_and_eraseLastHallCutsTokenLinearChoice
    (hToken : EraseLastHallCutsTokenLinearChoiceGoal)
    (hFeasible : FeasibleWithResidues I R) :
    SymbolingWithResidues I R
```

The choice-level form asks for a function `choice : X -> C` selecting one active
color at each vertex, with the prescribed last-column degrees, such that every
lower-symbol cut has enough existing Hall slack to absorb exactly the low-hit
loss introduced by erasing `choice`.  The preferred remaining interface is now
the slack form:

```lean
Incidence.choiceLowHitCount I choice U S
  <= M.cutSlack U (S.image Fin.castSucc)
```

The nontrivial-cut form is even narrower: the above inequality only has to be
checked for `U.Nonempty`, `U != Finset.univ`, and `S.Nonempty`.  The cases
`U = empty`, `U = univ`, and `S = empty` are Lean-closed because their
low-hit count is zero.

The current smallest interface is the linear form, using

```lean
Incidence.lowCutSet I U S
Incidence.choiceDegreeOn (Incidence.lowCutSet I U S) choice c
```

and requiring

```lean
sum c in U,
  Incidence.choiceDegreeOn (Incidence.lowCutSet I U S) choice c
<= M.cutSlack U (S.image Fin.castSucc)
```

for the same nontrivial cuts.

After the token-load bridge, an even cleaner equivalent target is the
token-linear form:

```lean
def EraseLastHallCutsTokenLinearChoiceGoal : Prop :=
  forall I M, M.HallCuts ->
    exists f : (Sigma fun c => Fin (M.val c (Fin.last T))) ≃ X,
      (forall q, q.1 ∈ I.active (f q)) ∧
        forall U S,
          U.Nonempty -> U != Finset.univ -> S.Nonempty ->
            Incidence.tokenLoadOn f (Incidence.lowCutSet I U S) U
              <= M.cutSlack U (S.image Fin.castSucc)
```

Here `f` places the last-column tokens directly into vertices.  The induced
choice is `fun x => (f.symm x).1`, so the prescribed degrees follow from the
token bijection, and the linear cut inequality follows from:

```lean
Incidence.tokenLoadOn_eq_sum_choiceDegreeOn
```

Thus the preferred remaining Active Hall request is now
`EraseLastHallCutsTokenLinearChoiceGoal`.

Closed support includes:

```lean
theorem RoundComposite.ActiveHall.hallRealization_zero
theorem RoundComposite.ActiveHall.hallRealization_one
theorem RoundComposite.ActiveHall.eraseLastHallCuts_zero
theorem RoundComposite.ActiveHall.eraseLastHallCutsChoice_zero
theorem RoundComposite.ActiveHall.eraseLastHallCutsSlackChoice_zero
theorem RoundComposite.ActiveHall.eraseLastHallCutsNontrivialSlackChoice_zero
theorem RoundComposite.ActiveHall.eraseLastHallCutsLinearChoice_zero
theorem RoundComposite.ActiveHall.eraseLastHallCutsTokenLinearChoice_zero
noncomputable def RoundComposite.ActiveHall.Symboling.extendLast
theorem RoundComposite.ActiveHall.Symboling.color_mem_active
theorem RoundComposite.ActiveHall.Symboling.count_eq_choiceDegree
theorem RoundComposite.ActiveHall.Symboling
  .extendLast_realizes_eraseLastCountMatrix
theorem RoundComposite.ActiveHall.Symboling
  .local_castSucc_cut_count_add_last_low_indicator_le_cap
theorem RoundComposite.ActiveHall.Symboling
  .cutMass_eq_sum_local_of_realizes
theorem RoundComposite.ActiveHall.Symboling
  .cutMass_image_castSucc_add_choiceLowHitCount_le_cutCap_of_realizes
def RoundComposite.ActiveHall.Incidence.eraseChoice
def RoundComposite.ActiveHall.CountMatrix.eraseLastCountMatrix
def RoundComposite.ActiveHall.CountMatrix.cutSlack
theorem RoundComposite.ActiveHall.CountMatrix.cutMass_add_le_iff_le_cutSlack
def RoundComposite.ActiveHall.Incidence.choiceDegreeOn
def RoundComposite.ActiveHall.Incidence.choiceHitCountOn
def RoundComposite.ActiveHall.Incidence.lowCutSet
def RoundComposite.ActiveHall.Incidence.choiceLowHitCount
theorem RoundComposite.ActiveHall.Incidence.choiceDegreeOn_le_card
theorem RoundComposite.ActiveHall.Incidence.choiceDegreeOn_mono_set
theorem RoundComposite.ActiveHall.Incidence.choiceDegreeOn_le_choiceDegree
theorem RoundComposite.ActiveHall.Incidence.choiceDegreeOn_univ
theorem RoundComposite.ActiveHall.Incidence.choiceHitCountOn_le_card
theorem RoundComposite.ActiveHall.Incidence.choiceHitCountOn_mono_set
theorem RoundComposite.ActiveHall.Incidence.choiceHitCountOn_mono_colors
theorem RoundComposite.ActiveHall.Incidence.choiceHitCountOn_le_choiceHitCount
theorem RoundComposite.ActiveHall.Incidence.choiceHitCountOn_univ
theorem RoundComposite.ActiveHall.Incidence.lowCutSet_mono_symbols
theorem RoundComposite.ActiveHall.Incidence.lowCutSet_mono_symbols_of_subset
theorem RoundComposite.ActiveHall.Incidence.lowCutSet_colors_empty
theorem RoundComposite.ActiveHall.Incidence.lowCutSet_colors_univ
theorem RoundComposite.ActiveHall.Incidence
  .choiceLowHitCount_eq_choiceHitCountOn_lowCutSet
theorem RoundComposite.ActiveHall.Incidence
  .sum_choiceDegreeOn_on
theorem RoundComposite.ActiveHall.Incidence
  .sum_choiceDegreeOn_on_le_card
theorem RoundComposite.ActiveHall.Incidence
  .sum_choiceDegreeOn_on_le_choiceHitCount
theorem RoundComposite.ActiveHall.Incidence
  .sum_choiceDegreeOn_on_le_sum_choiceDegree
theorem RoundComposite.ActiveHall.Incidence
  .sum_choiceDegreeOn_on_mono_set
theorem RoundComposite.ActiveHall.Incidence
  .sum_choiceDegreeOn_on_mono_colors
def RoundComposite.ActiveHall.Incidence.tokenLoadOn
theorem RoundComposite.ActiveHall.Incidence
  .tokenLoadOn_eq_choiceHitCountOn
theorem RoundComposite.ActiveHall.Incidence
  .tokenLoadOn_eq_sum_choiceDegreeOn
theorem RoundComposite.ActiveHall.Incidence
  .tokenLoadOn_le_card
theorem RoundComposite.ActiveHall.Incidence
  .tokenLoadOn_mono_set
theorem RoundComposite.ActiveHall.Incidence
  .tokenLoadOn_mono_colors
theorem RoundComposite.ActiveHall.Incidence
  .tokenLoadOn_set_empty
theorem RoundComposite.ActiveHall.Incidence
  .tokenLoadOn_colors_empty
theorem RoundComposite.ActiveHall.Incidence
  .tokenLoadOn_colors_univ
theorem RoundComposite.ActiveHall.Incidence
  .choiceLowHitCount_eq_sum_choiceDegreeOn_lowCutSet
theorem RoundComposite.ActiveHall.Incidence
  .choiceLowHitCount_symbols_empty
theorem RoundComposite.ActiveHall.Incidence
  .choiceLowHitCount_colors_empty
theorem RoundComposite.ActiveHall.Incidence
  .choiceLowHitCount_colors_univ
theorem RoundComposite.ActiveHall.Incidence
  .choiceLowHitCount_le_choiceHitCount
theorem RoundComposite.ActiveHall.CountMatrix.eraseLastCountMatrix_cutMass
theorem RoundComposite.ActiveHall.CountMatrix.cutMass_last_eq_choiceHitCount
theorem RoundComposite.ActiveHall.CountMatrix
  .cutMass_image_castSucc_insert_last_eq_eraseLast_add_choiceHitCount
theorem RoundComposite.ActiveHall.CountMatrix
  .eraseLastCountMatrix_hallCuts_of_cutCap_slack
theorem RoundComposite.ActiveHall.CountMatrix
  .eraseLastCountMatrix_hallCuts_of_cutSlack
theorem RoundComposite.ActiveHall.Incidence.sum_choiceDegree_on
theorem RoundComposite.ActiveHall.Incidence
  .eraseChoice_active_inter_card_add_indicator
theorem RoundComposite.ActiveHall.Incidence.cutCap_image_castSucc
theorem RoundComposite.ActiveHall.Incidence.cutCap_image_castSucc_insert_last
theorem RoundComposite.ActiveHall.Incidence
  .cutCap_image_castSucc_eq_eraseChoice_cutCap_add_choiceLowHitCount
theorem RoundComposite.ActiveHall.Incidence
  .exists_choiceDegree_bijective_token_matching
structure RoundComposite.ActiveHall.CountMatrix.ColumnFilling
theorem RoundComposite.ActiveHall.CountMatrix
  .exists_columnFilling_of_hallCuts
def RoundComposite.ActiveHall.Symboling.toColumnFilling
```

Remaining Active Hall proof obligation:

```lean
HoffmanOrderedSDRGoal
```

This is Lean-equivalent to all of the following interfaces:

```lean
HallRealizationGoal
ColumnFillingUpgradeGoal
EraseLastHallCutsTokenLinearChoiceGoal
```

The token-linear form is a degree-constrained active token placement theorem
with the cut condition

```lean
Incidence.tokenLoadOn f (Incidence.lowCutSet I U S) U
<= M.cutSlack U (S.image Fin.castSucc)
```

for every nonempty proper color cut `U` and nonempty lower-symbol cut `S`.

Plain Hall matching now gives the weaker `CountMatrix.ColumnFilling`: each
symbol column can be filled with active colors and the prescribed column
counts.  This does not enforce the row-Latin condition that, at each vertex,
the `T` chosen colors are all distinct.  This remaining strengthening is
isolated as:

```lean
ColumnFillingUpgradeGoal
```

It is Lean-equivalent to `HallRealizationGoal`, so the true abstract finite
combinatorics blocker is Hoffman's ordered-SDR theorem, equivalently the
capacitated upgrade from column-wise fillings to genuine `Symboling`s.
