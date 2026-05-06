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
- `boundaryCycleNode`
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

This is the root-flat / prefix-count return adapter for the all-pair proof
route: once a branch supplies exact all-pair first-return equations,
minimality/no-early witnesses, a one-cycle section map, and time exhaustion,
the existing `RouteESmallSeamCertificate` machinery carries it to the current
D5 even Hamilton, torus, and Cayley endpoints.

B16 and R14e branch surfaces are now also named in Lean:

- `RouteEB16.modulus`
- `RouteEB16.counts_sum`
- `RouteEB16.routeCounts`
- `RouteEB16.allPairTimeMassTarget`
- `RouteEB16.allPairTimeMassTarget_sum_eq_total`
- `RouteEB16.allPairTimeMassTarget_sum_eq_modulus_pow_four`
- `RouteEB16.allPairTimeMassTotalTarget_eq_modulus_pow_four`
- `RouteER14e.modulus`
- `RouteER14e.counts_sum`
- `RouteER14e.routeCounts`
- `RouteER14e.allPairTimeMassTarget`
- `RouteER14e.allPairTimeMassTarget_sum_eq_total`
- `RouteER14e.allPairTimeMassTarget_sum_eq_modulus_pow_four`
- `RouteER14e.allPairTimeMassTotalTarget_eq_modulus_pow_four`

These theorem names intentionally stop at count admissibility and symbolic
time-mass target identities.  The label-indexed mass functions package the
same target polynomials over `RouteEB20.AllPairLabel`; they are not
first-return theorems.  The bundle still marks the B16 boundary one-cycle
proof and the R14e boundary formula/one-cycle proof as not yet fully
symbolic.

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

## B20 Status

Closed or proof-facing in the bundle:

- count admissibility;
- 02 and 12 lane time masses;
- 01 and 13 two-clock time masses;
- 14, 23, and 24 residual-core time masses;
- 34 finite-defect boundary time mass;
- boundary quotient formula target for the B20 v1.8 candidate.
- the boundary one-cycle hand proof's segment count and orbit segment
  endpoints, whose total is `Fintype.card (RouteEBoundaryNode (modulus q))`.
- the first five nodes of the explicit spine enumeration and the first four
  successor checks for `boundaryQuotient`.
- the C-run predecessor equality and terminal C_h identification needed to
  extend the spine successor proof; the spine successor proof is now closed
  through `C_h -> B_h`, and the first-even tail is connected through both
  boundary bridges.
- numeric nonzero seam constructors and range lemmas for the four modular
  residue chains used by the explicit boundary-cycle orbit enumeration.

Remaining B20 obligations:

- prove the B20 boundary quotient candidate is a single cycle, beyond the
  currently Lean-checked segment count;
- derive `T_03` and `T_04` from the boundary-clock formulas, not only from
  sample-verified target polynomials;
- turn the no-early package into Lean-level hypotheses or lemmas;
- instantiate `RouteEAllPairSectionCertificate` for the B20 section map.

## B16 and R14e Status

B16:

- direct count-admissible;
- boundary quotient formula and time-mass evidence are extracted and
  sample-verified;
- residual-core symbolic depth is still behind B20.

R14e:

- direct count-admissible;
- 03/04/34 boundary formulas are extracted and sample-verified;
- symbolic one-cycle proof and time-mass derivation remain pending.

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

4. Branch-menu slice:
   compare B16/R14e branch data against the B20 interfaces and decide whether
   the final all-even route should be a finite branch menu or a unified direct
   core-certificate theorem.
