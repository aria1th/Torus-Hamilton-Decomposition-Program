# Route E v3.6 Analysis

Date: 2026-05-06.

Source bundle:

- `/data/angel/repos/etc/routeE_proof_bundle_v3_6_20260506.zip`

Working branch:

- `route-e-v3-6-20260506`

This note records the current repo comparison and the first Lean-facing
formalization slice.  The bundle is useful proof evidence, but it is not a
Lean formalization and it does not yet claim the full D5 even Route-E theorem.

## Current Target

Formalize Route E as a branch/menu proof, starting with the B20 branch:

```text
m = 24*q + 20 = 6*c + 2
c = 4*q + 3
h = m/2 = 12*q + 10
nu = (c, 4*c + 1, 0, c, 0)
```

The proof route is the all-pair section:

```text
P_all = {0} union {(i,j,a) : 0 <= i < j <= 4, 1 <= a < m}
```

For a closed branch, the required pieces are:

1. exact first return on `P_all`;
2. no early return before that first hit;
3. one-cycle induced map;
4. total return-time mass `sum tau = m^4`;
5. adapter into the existing `RouteETheta*` / `D5EvenRouteE*` Lean endpoints.

## Lean Slice Added

`D5Odd/EvenRouteE.lean` now records the B20 v3.6 all-pair label time-mass
surface in namespace `RouteEB20`.

New arithmetic names include:

- `quarter`
- `modulus_eq_four_quarter`
- `half_eq_two_quarter`
- `allPairTimeZ`
- `allPairTime01`
- `allPairTime02`
- `allPairTime03Target`
- `allPairTime04Target`
- `allPairTime12`
- `allPairTime13`
- `allPairTime14`
- `allPairTime23`
- `allPairTime24`
- `allPairTime34`
- `AllPairLabel`
- `allPairTimeMass`
- `allPairTimeMassTotal`
- `allPairRowCountTarget`
- `allPairLabelCountTarget`
- `allPairLabelCountTarget_sum_eq_allPairRowCountTarget`
- `BoundaryQuotientFormulaTarget`
- `BoundaryQuotientOneCycleTarget`
- `boundaryQuotient`
- `boundaryQuotient_A_h`
- `boundaryQuotient_A_h_succ`
- `boundaryQuotient_B_h_sub_one`
- `boundaryQuotient_B_last`
- `boundaryQuotient_B_close`
- `boundaryQuotient_C_one`
- `boundaryQuotient_C_h`
- `boundaryQuotient_C_last`
- `boundaryQuotient_A_even`
- `boundaryQuotient_A_odd_shift`
- `boundaryQuotient_B_odd`
- `boundaryQuotient_B_two`
- `boundaryQuotient_B_even_shift`
- `boundaryQuotient_C_generic`
- `boundaryQuotient_formulaTarget`
- `card_boundaryNode_eq_three_modulus_sub_two`
- `boundaryCycleLength`
- `boundaryCycleLength_eq_card`
- `boundaryCycleLength_eq_twelve_quarter_sub_two`
- `boundaryCycleB2BridgeStart_eq_modulus_add_two`
- `boundaryCycleFirstOddStart_eq_modulus_add_three`
- `boundaryCycleALastBridgeStart_eq_two_modulus_add_one`
- `boundaryCycleSecondOddStart_eq_two_modulus_add_two`
- `boundaryCycleSecondEvenStart_eq_two_modulus_add_half_add_one`
- `boundaryCycleSecondEvenEnd_eq_length`
- `boundaryCycleSpineNode`
- `boundaryCycleSpineNode_zero`
- `boundaryCycleSpineNode_one`
- `boundaryCycleSpineNode_two`
- `boundaryCycleSpineNode_three`
- `boundaryCycleSpineNode_four`
- `boundaryCycleSpine_step_zero`
- `boundaryCycleSpine_step_one`
- `boundaryCycleSpine_step_two`
- `boundaryCycleSpine_step_three`
- `boundaryCycleSpine_step_four`
- `boundaryCycleSpineNode_C_run`
- `boundaryCycleSpine_step_C_run`
- `boundaryCycleSpine_step_C_last`
- `boundarySpineCValue_succ`
- `boundarySpineCParam_pred_eq`
- `boundarySpineCValue_last`
- `boundarySpineCParam_last_eq_half`
- `RouteENonzeroSeam.ofNat_val`
- `routeEBoundaryNodeOfNat`
- `boundaryFirstEvenValue_range`
- `boundaryCycleFirstEvenTailIndex`
- `boundaryCycleFirstEvenTailNode`
- `boundaryCycleFirstEvenTail_step_even`
- `boundaryCycleFirstEvenTail_step_odd`
- `boundaryCycleSpine_to_firstEvenTail`
- `boundaryCycleFirstEvenTail_to_B2Bridge`
- `boundaryFirstOddValue_range`
- `boundaryCycleFirstOddLaneCount`
- `boundaryCycleFirstOddLaneNode`
- `boundaryCycleFirstOddLane_step_even`
- `boundaryCycleFirstOddLane_step_odd`
- `boundaryCycleB2Bridge_to_firstOddLane`
- `boundaryCycleFirstOddLane_to_BSubOne`
- `boundaryCycleFirstOddBSubOne_to_CRun`
- `boundaryCycleFirstOddCRun_step`
- `boundaryCycleFirstOddCRun_to_ALast`
- `boundaryFirstOddParam_shift_succ`
- `boundarySecondOddValue_range`
- `boundaryCycleSecondOddLaneCount`
- `boundaryCycleSecondOddLaneNode`
- `boundaryCycleSecondOddLane_step_even`
- `boundaryCycleSecondOddLane_step_odd`
- `boundaryCycleALastBridge_to_secondOddLane`
- `boundaryCycleSecondOddLane_to_final`
- `boundarySecondOddParam_shift_succ`
- `boundarySecondEvenValue_range`
- `boundaryCycleSecondEvenTailIndex`
- `boundaryCycleSecondEvenTailNode`
- `boundaryCycleSecondEvenTail_step_even`
- `boundaryCycleSecondEvenTail_step_odd`
- `boundaryCycleSecondOddFinal_to_secondEvenTail`
- `boundaryCycleSecondEvenTail_to_zero`
- `boundarySecondEvenParam_shift_succ`
- `boundaryCycleNodeAt`
- `boundaryCycleNode`
- `boundaryCycleNodeAt_last`
- `boundaryCycleNode_last_to_zero`
- `boundaryCycleNodeAt_succ_spine`
- `boundaryCycleNodeAt_spine_to_firstEven`
- `boundaryCycleNodeAt_succ_firstEven`
- `boundaryCycleNodeAt_firstEven_to_B2Bridge`
- `boundaryCycleNodeAt_B2Bridge_to_firstOdd`
- `boundaryCycleNodeAt_succ_firstOddLane`
- `boundaryCycleNodeAt_firstOddLane_to_BSubOne`
- `boundaryCycleNodeAt_BSubOne_to_CRun`
- `boundaryCycleNodeAt_succ_firstOddCRun`
- `boundaryCycleNodeAt_firstOddCRun_to_ALast`
- `boundaryCycleNodeAt_ALast_to_secondOdd`
- `boundaryCycleNodeAt_succ_secondOddLane`
- `boundaryCycleNodeAt_secondOddLane_to_final`
- `boundaryCycleNodeAt_secondOddFinal_to_secondEven`
- `boundaryCycleNodeAt_succ_secondEven`
- `boundaryCycleNodeAt_succ`
- `boundaryCycleNode_step`
- `boundaryCycleNode_injective`
- `boundaryCycleNode_bijective`
- `boundaryQuotientCycleEnumeration`
- `boundaryQuotient_singleCycle`
- `boundaryQuotient_oneCycleTarget`
- `BoundaryQuotientCycleEnumeration`
- `BoundaryQuotientCycleEnumeration.singleCycle`
- `BoundaryQuotientCycleEnumeration.oneCycleTarget`
- `boundaryFirstEvenParam_val`
- `boundaryFirstEvenParam_shift_succ`
- `boundaryFirstOddParam_val`
- `boundarySecondOddParam_val`
- `boundarySecondEvenParam_val`
- `boundaryCycleHandCountTotal_eq_card`
- `boundaryShiftParam`
- `boundaryPredParam`
- `boundaryParamOne`
- `boundaryParamTwo`
- `boundaryParamHalfSubTwo`
- `boundaryParamHalfSubOne`
- `boundaryParamHalf`
- `boundaryParamHalfAddOne`
- `boundaryParamHalfAddTwo`
- `boundaryParamPenultimate`
- `boundaryParamLast`
- `allPairTime01_eq_three_quarter_sq`
- `allPairTimeZ_eq_half_add_three`
- `allPairTime02_lane_sum_eq`
- `allPairTime12_lane_sum_eq`
- `allPairTime13_two_clock_eq`
- `allPairTime34_boundary_defect_eq`
- `allPairTime03Target_add_allPairTime04Target`
- `allPairTimeMassTotal_eq_modulus_pow_four`
- `allPairTimeMass_sum_eq_modulus_pow_four`

The same Lean file also now exposes an all-pair adapter surface:

- `RouteEBoundaryLabel`
- `RouteEBoundaryNode`
- `card_routeEBoundaryNode`
- `RouteEAllPairVecSupport`
- `RouteEAllPairSectionPoint`
- `RouteEAllPairSection`
- `RouteEAllPairSectionCertificate`
- `RouteEAllPairSectionCertificate.toSmallSeamCertificate`
- `RouteEAllPairSectionCertificate.seamRootReturn_single_cycle`
- `RouteEAllPairSectionCertificate.orbitTarget`
- `RouteEAllPairSectionCertificate.toHamiltonDecomposition`
- `RouteEAllPairSectionCertificate.toTorusHamiltonDecomposition`
- `RouteEAllPairSectionCertificate.toCayleyHamiltonDecomposition`
- `RouteEAllPairLabelTraceTarget`
- `RouteEAllPairLabelTraceTarget.returnTime_sum`
- `RouteEAllPairLabelTraceTarget.toSectionCertificate`
- `RouteEAllPairIndexedLabelTraceTarget`
- `RouteEAllPairIndexedLabelTraceTarget.toLabelTraceTarget`
- `RouteEAllPairIndexedLabelTraceTarget.toSectionCertificate`
- `RouteEAllPairLabelFiber`
- `RouteEAllPairCanonicalRow`
- `card_routeEAllPairCanonicalRow`
- `RouteEAllPairCanonicalLabelDstTraceTarget`
- `RouteEAllPairCanonicalLabelDstTraceTarget.toLabelDstTraceTarget`
- `RouteEAllPairCanonicalLabelDstTraceTarget.toSectionCertificate`
- `RouteEBoundaryFirstReturnTarget`
- `RouteEBoundaryFirstReturnTarget.boundaryMap_singleCycle`
- `RouteEB20.AllPairLabelTraceTarget`
- `RouteEB20.AllPairLabelTraceTarget.returnTime_sum`
- `RouteEB20.allPairSectionCertificateOfLabelTraceTarget`
- `RouteEB20.symbolicAllPairBranchTarget_of_labelTraceTarget`
- `RouteEB20.finiteM20AllPairTarget_of_labelTraceTarget`
- `RouteEB20.allPairBranchTarget_of_labelTraceTargets`
- `RouteEB20.hamiltonTarget_of_labelTraceTargets`
- `RouteEB20.torusTarget_of_labelTraceTargets`
- `RouteEB20.cayleyTarget_of_labelTraceTargets`
- `RouteEB20.AllPairIndexedLabelTraceTarget`
- `RouteEB20.AllPairIndexedLabelTraceTarget.toLabelTraceTarget`
- `RouteEB20.allPairSectionCertificateOfIndexedLabelTraceTarget`
- `RouteEB20.symbolicAllPairBranchTarget_of_indexedLabelTraceTarget`
- `RouteEB20.finiteM20AllPairTarget_of_indexedLabelTraceTarget`
- `RouteEB20.allPairBranchTarget_of_indexedLabelTraceTargets`
- `RouteEB20.hamiltonTarget_of_indexedLabelTraceTargets`
- `RouteEB20.torusTarget_of_indexedLabelTraceTargets`
- `RouteEB20.cayleyTarget_of_indexedLabelTraceTargets`

This is the root-flat / prefix-count return adapter for the all-pair proof
route: once a branch supplies exact all-pair first-return equations,
minimality/no-early witnesses, a one-cycle section map, and time exhaustion,
the existing `RouteESmallSeamCertificate` machinery carries it to the current
D5 even Hamilton, torus, and Cayley endpoints.  The branch-independent
`RouteEAllPairLabelTraceTarget` adapter reduces time exhaustion to per-label
fiber sums.  `RouteEAllPairLabelDstTraceTarget` refines this to the
`src_label -> dst_label` sums emitted by the closure verifiers, and the indexed
variants match verifier rows (`idx`, `dst_idx`, labels, `time`) through a
bijection to `RouteEAllPairSection`.  The canonical-row variant fixes the
verifier row shape as `{Z} union labels x nonzero seam`, proves cardinal
`1 + 10*(m-1)`, and then transports a branch-supplied row-to-section bijection
to the same label-destination certificate surface.  B20 keeps its original
branch-local target names, while B16/R14e now reuse the generic adapters with
their own count vectors and time-mass polynomials.

B16 and R14e branch surfaces are now also named in Lean:

- `RouteEB16.modulus`
- `RouteEB16.counts_sum`
- `RouteEB16.routeCounts`
- `RouteEB16.allPairTimeMassTarget`
- `RouteEB16.allPairLabelDstTimeMassTarget`
- `RouteEB16.allPairLabelDstTimeMassTarget_sum_by_src`
- `RouteEB16.allPairLabelDstCountTarget`
- `RouteEB16.allPairLabelDstCountTarget_sum_by_src`
- `RouteEB16.allPairLabelDstCountBySrcTarget_sum_eq_allPairRowCountTarget`
- `RouteEB16.allPairTimeMassTarget_sum_eq_total`
- `RouteEB16.allPairTimeMassTarget_sum_eq_modulus_pow_four`
- `RouteEB16.allPairTimeMassTotalTarget_eq_modulus_pow_four`
- `RouteEB16.BoundaryMacroNode`
- `RouteEB16.BoundaryQuotientFormulaTarget`
- `RouteEB16.BoundaryQuotientOneCycleTarget`
- `RouteEB16.SymbolicBoundaryQuotientOneCycleTarget`
- `RouteEB16.boundaryQuotientOneCycleTarget_of_formula_and_macro`
- `RouteEB16.symbolicBoundaryQuotientOneCycleTarget_of_formula_and_macro`
- `RouteEB16.BoundaryMacroReturnTarget`
- `RouteEB16.BoundaryMacroReturnTarget.boundaryQuotient_singleCycle`
- `RouteEB16.SymbolicBoundaryMacroReturnTarget`
- `RouteEB16.FiniteM16BoundaryQuotientTarget`
- `RouteEB16.boundaryMacroLengthTotalTarget_eq_boundary_card`
- `RouteEB16.AllPairLabelTraceTarget`
- `RouteEB16.AllPairIndexedLabelTraceTarget`
- `RouteEB16.AllPairLabelDstTraceTarget`
- `RouteEB16.AllPairIndexedLabelDstTraceTarget`
- `RouteEB16.allPairSectionCertificateOfLabelTraceTarget`
- `RouteEB16.allPairSectionCertificateOfIndexedLabelTraceTarget`
- `RouteEB16.allPairSectionCertificateOfLabelDstTraceTarget`
- `RouteEB16.allPairSectionCertificateOfIndexedLabelDstTraceTarget`
- `RouteEB16.SymbolicAllPairBranchTarget`
- `RouteEB16.FiniteM16AllPairTarget`
- `RouteEB16.AllPairBranchTarget`
- `RouteEB16.allPairBranchTarget_of_labelDstTraceTargets`
- `RouteEB16.allPairBranchTarget_of_indexedLabelDstTraceTargets`
- `RouteEB16.hamiltonTarget_of_labelTraceTargets`
- `RouteEB16.torusTarget_of_labelTraceTargets`
- `RouteEB16.cayleyTarget_of_labelTraceTargets`
- `RouteEB16.hamiltonTarget_of_indexedLabelTraceTargets`
- `RouteEB16.torusTarget_of_indexedLabelTraceTargets`
- `RouteEB16.cayleyTarget_of_indexedLabelTraceTargets`
- `RouteER14e.modulus`
- `RouteER14e.counts_sum`
- `RouteER14e.routeCounts`
- `RouteER14e.allPairTimeMassTarget`
- `RouteER14e.allPairLabelDstTimeMassTarget`
- `RouteER14e.allPairLabelDstTimeMassTarget_sum_by_src`
- `RouteER14e.allPairLabelDstCountTarget`
- `RouteER14e.allPairLabelDstCountTarget_sum_by_src`
- `RouteER14e.allPairLabelDstCountBySrcTarget_sum_eq_allPairRowCountTarget`
- `RouteER14e.allPairTimeMassTarget_sum_eq_total`
- `RouteER14e.allPairTimeMassTarget_sum_eq_modulus_pow_four`
- `RouteER14e.allPairTimeMassTotalTarget_eq_modulus_pow_four`
- `RouteER14e.BoundaryMacroNode`
- `RouteER14e.BoundaryQuotientFormulaTarget`
- `RouteER14e.BoundaryQuotientOneCycleTarget`
- `RouteER14e.SymbolicBoundaryQuotientOneCycleTarget`
- `RouteER14e.boundaryQuotientOneCycleTarget_of_formula_and_macro`
- `RouteER14e.symbolicBoundaryQuotientOneCycleTarget_of_formula_and_macro`
- `RouteER14e.BoundaryMacroReturnTarget`
- `RouteER14e.BoundaryMacroReturnTarget.boundaryQuotient_singleCycle`
- `RouteER14e.SymbolicBoundaryMacroReturnTarget`
- `RouteER14e.FiniteM14BoundaryMacroReturnTarget`
- `RouteER14e.boundaryMacroLengthTotalTarget_eq_boundary_card`
- `RouteER14e.insertionBoundaryCountTarget_eq_boundary_card`
- `RouteER14e.insertionWeightedCountTarget_eq_allPairRowCountTarget`
- `RouteER14e.AllPairLabelTraceTarget`
- `RouteER14e.AllPairIndexedLabelTraceTarget`
- `RouteER14e.AllPairLabelDstTraceTarget`
- `RouteER14e.AllPairIndexedLabelDstTraceTarget`
- `RouteER14e.allPairSectionCertificateOfLabelTraceTarget`
- `RouteER14e.allPairSectionCertificateOfIndexedLabelTraceTarget`
- `RouteER14e.allPairSectionCertificateOfLabelDstTraceTarget`
- `RouteER14e.allPairSectionCertificateOfIndexedLabelDstTraceTarget`
- `RouteER14e.SymbolicAllPairBranchTarget`
- `RouteER14e.FiniteM14AllPairTarget`
- `RouteER14e.AllPairBranchTarget`
- `RouteER14e.allPairBranchTarget_of_labelDstTraceTargets`
- `RouteER14e.allPairBranchTarget_of_indexedLabelDstTraceTargets`
- `RouteER14e.hamiltonTarget_of_labelTraceTargets`
- `RouteER14e.torusTarget_of_labelTraceTargets`
- `RouteER14e.cayleyTarget_of_labelTraceTargets`
- `RouteER14e.hamiltonTarget_of_indexedLabelTraceTargets`
- `RouteER14e.torusTarget_of_indexedLabelTraceTargets`
- `RouteER14e.cayleyTarget_of_indexedLabelTraceTargets`

These theorem names still do not instantiate the branch maps.  They provide two
proof-facing endpoints.  First, a boundary quotient plus first-return
macro-section data feeds `RouteEBoundaryFirstReturnTarget` and yields
`IsSingleCycleMap` for the quotient.  Second, a concrete label,
label-destination, or indexed all-pair trace target, plus the finite exceptional
case (`m = 16` or `m = 14`), yields a `RouteEAllPairSectionCertificate` and
then Hamilton/torus/Cayley endpoints.  The
`RouteE_three_branch_status_package_20260506.zip` package promotes B16 and
R14e to proof-facing closure on paper/verifier evidence, but the boundary
quotient derivations, all-pair first-return equations, no-early facts, and
finite exceptional tables are not yet Lean instances.

The file checks with:

```bash
lake env lean D5Odd/EvenRouteE.lean
```

This slice intentionally does not assert that the all-pair time masses are
already first-return theorems.  The `03` and `04` entries are named as
`Target` formulas because the bundle explicitly leaves their boundary-clock
derivation as the remaining B20 symbolic time gap.

## Bundle Arithmetic Correction

The v3.6 proof draft prints:

```text
T_03 + T_04 = 10368*q^3 + 24426*q^2 + 19079*q + 5038
```

But the two displayed target polynomials are:

```text
T_03 = 5184*q^3 + 12528*q^2 + 10080*q + 2703
T_04 = 5184*q^3 + 11898*q^2 +  9099*q + 2335
```

Adding them gives:

```text
T_03 + T_04 = 10368*q^3 + 24426*q^2 + 19179*q + 5038
```

The corrected coefficient `19179` is also forced by the Lean theorem
`RouteEB20.allPairTimeMassTotal_eq_modulus_pow_four`.  Using `19079` leaves a
residual error of `100*q` in the B20 total time budget.

Lean now records both sides of this correction:

- `RouteEB20.allPairTime03Target_add_allPairTime04Target_v36_draft_defect`
  proves the bundle-text value is short by `100*q`.
- `RouteEB20.allPairTime03Target_add_allPairTime04Target_ne_v36_draft`
  rules out the printed coefficient for every `q > 0`.

## B20 Status

Closed or proof-facing in the bundle:

- count admissibility;
- 02 and 12 lane time masses;
- 01 and 13 two-clock time masses;
- 14, 23, and 24 residual-core time masses;
- 34 finite-defect boundary time mass;
- boundary quotient formula target for the B20 v1.8 candidate.
- boundary quotient one-cycle target for the B20 v1.8 candidate.
- a boundary-clock mass adapter:
  `RouteEB20.BoundaryClockMassTarget` plus
  `RouteEB20.allPairTimeMassFromBoundaryClocks_sum_eq_modulus_pow_four`.
  This lets a future pointwise derivation of the `03` and `04` clock functions
  close the all-pair time exhaustion without changing the endpoint theorem.
- pointwise boundary-clock formula surfaces for the stable symbolic range:
  `RouteEB20.boundaryClockTime03Formula`,
  `RouteEB20.boundaryClockTime04Formula`,
  `RouteEB20.BoundaryClockPointwiseFormulaTarget`,
  `RouteEB20.BoundaryClockSymbolicMassTarget`, and
  `RouteEB20.BoundaryClockSymbolicMassTarget.toBoundaryClockMassTarget`.
  These names isolate the `q > 0` formula proof from the finite `q = 0`
  certificate row; `RouteEB20.allPairTimeMassFromSymbolicBoundaryClocks_sum_eq_modulus_pow_four`
  then feeds the symbolic clock target into the all-pair time exhaustion.
- recovered `03` and `04` boundary-clock aggregate masses:
  `RouteEB20.allPairTime03BoundaryClockBranchMassTotal_eq_target`,
  `RouteEB20.allPairTime04BoundaryClockBranchMassTotal_eq_target`,
  `RouteEB20.allPairTime04BoundaryClockModClassMassTotal_eq_target`, and
  `RouteEB20.allPairTime0304BoundaryClockBranchMassTotal_eq_target_sum`.
  These encode the branch-mass decomposition found by exact all-pair samples
  and the B20 closure package.
- the B20 closure package separates the symbolic proof range `q >= 1` from
  the finite `q = 0`/`m = 20` certificate.  The aggregate polynomials still
  evaluate correctly at `q = 0`, but the stabilized `04` recurrence is only
  claimed for `q >= 1`.
- B20 symbolic/finite dispatcher endpoints:
  `RouteEB20.SymbolicAllPairBranchTarget`,
  `RouteEB20.FiniteM20AllPairTarget`,
  `RouteEB20.AllPairBranchTarget`,
  `RouteEB20.allPairBranchTarget_of_symbolic_and_m20`, the
  `RouteEB20.AllPairLabelTraceTarget` and
  `RouteEB20.AllPairIndexedLabelTraceTarget` adapters, and the Hamilton/Torus/
  Cayley projection theorems from that branch target.
- the boundary one-cycle hand proof's segment count and orbit segment
  endpoints, whose total is `Fintype.card (RouteEBoundaryNode (modulus q))`.
- the first five nodes of the explicit spine enumeration and the first four
  successor checks for `boundaryQuotient`.
- the C-run predecessor equality and terminal C_h identification needed to
  extend the spine successor proof; the spine successor proof is now closed
  through `C_h -> B_h`; every segment-level successor case of the combined
  `boundaryCycleNodeAt` adapter is now connected through the second-even tail,
  packaged as the `Fin`-indexed global step `boundaryCycleNode_step`, and
  closed as `boundaryQuotient_oneCycleTarget`.
- numeric nonzero seam constructors and range lemmas for the four modular
  residue chains used by the explicit boundary-cycle orbit enumeration.

Remaining B20 obligations:

- promote the recovered `T_03` pointwise formula and the `T_04` stabilized
  mod-class recurrences from
  `RouteEB20.BoundaryClockPointwiseFormulaTarget` to boundary-clock proofs;
- add or connect the finite `m = 20` all-pair table certificate;
- turn the no-early package into Lean-level hypotheses or lemmas;
- instantiate `RouteEB20.AllPairIndexedLabelTraceTarget` or
  `RouteEB20.AllPairLabelTraceTarget` for the B20 section map, which then
  yields `RouteEAllPairSectionCertificate`.

## B16 and R14e Status

B16:

- direct count-admissible;
- `B16_closure_package_20260506.zip` and
  `RouteE_three_branch_status_package_20260506.zip` record a proof-facing
  boundary quotient, macro-return one-cycle, boundary insertion compression,
  label-wise and label-destination time masses, and finite `m = 16`
  exceptional target;
- Lean now has B16 closed boundary formula and boundary macro-return targets,
  plus label/indexed and label-destination all-pair adapters.  The formula+macro
  adapter is
  `RouteEB16.boundaryQuotientOneCycleTarget_of_formula_and_macro`, and the
  checked macro length identity is
  `RouteEB16.boundaryMacroLengthTotalTarget_eq_boundary_card`; the
  label-destination mass check is
  `RouteEB16.allPairLabelDstTimeMassTarget_sum_by_src`, and the
  label-destination row-count check extracted from the case count table is
  `RouteEB16.allPairLabelDstCountBySrcTarget_sum_eq_allPairRowCountTarget`;
- remaining Lean work is to instantiate the concrete boundary quotient map and
  macro-return data, then supply all-pair first-return/no-early equations and
  the finite `m = 16` table.

R14e:

- direct count-admissible;
- `R14e_closure_package_20260506.zip` and
  `RouteE_three_branch_status_package_20260506.zip` record a proof-facing
  boundary quotient, macro-return one-cycle, insertion distribution, label-wise
  and label-destination time masses, and finite `m = 14` two-node macro target;
- Lean now has R14e closed boundary formula and boundary macro-return targets,
  insertion-count arithmetic, and label/indexed plus label-destination all-pair
  adapters.  The
  formula+macro adapter is
  `RouteER14e.boundaryQuotientOneCycleTarget_of_formula_and_macro`; the
  insertion weighted count is connected to the verifier row count target by
  `RouteER14e.insertionWeightedCountTarget_eq_allPairRowCountTarget`; the
  label-destination mass check is
  `RouteER14e.allPairLabelDstTimeMassTarget_sum_by_src`, and the
  label-destination row-count check is
  `RouteER14e.allPairLabelDstCountBySrcTarget_sum_eq_allPairRowCountTarget`;
- remaining Lean work is to instantiate the concrete boundary quotient map and
  macro-return data, then derive/instantiate the insertion distribution,
  all-pair first-return/no-early equations, and the finite `m = 14` table.

## Reproduction Caveat

The bundle Python scripts `routeE_B20_twoclock_time_pass_v3_6.py` and
`routeE_B20_time_mass_pass_v3_5.py` currently expect absolute CSV inputs under
`/mnt/data` and are not self-contained from the zip extraction alone.  The JSON
evidence and proof drafts are still readable and useful, but script
reproduction needs either the missing CSV dumps or a small path/input adapter.

## Next Divisible Implementation Slices

1. B20 boundary time slice:
   formalize the boundary quotient formula for labels `03`, `04`, and `34`,
   then prove the corrected `T_03 + T_04` target from boundary clocks.

2. B20 no-early slice:
   introduce a Lean structure for all-pair first-return certificates with
   explicit minimality/no-early fields, then instantiate its arithmetic side
   with the newly recorded B20 time masses.

3. B20 residual-core slice:
   formalize the shared `S(s,b,l)` macro theorem for hard labels `14`, `23`,
   and `24`, separating entrance lemmas, macro transitions, exit
   classification, and calendar sums.

4. B16/R14e instantiation slice:
   turn the new closure packages into concrete
   `RouteEB16.AllPairIndexedLabelDstTraceTarget` and
   `RouteER14e.AllPairIndexedLabelDstTraceTarget` instances, separating
   symbolic `q/k > 0` derivations from finite `m = 16` and `m = 14` table
   witnesses.

5. Branch-menu slice:
   after B20/B16/R14e target instances exist, decide whether the final all-even
   route should be a finite branch menu or a unified direct core-certificate
   theorem.  The next package-recommended search target is the R38/symmetric
   family, since the naive symmetric theorem is known false.
