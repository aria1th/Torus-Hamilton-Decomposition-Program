# Route E v3.6 Completion Audit

Date: 2026-05-06.

Goal being audited:

```text
Route E v3.6 proof bundle analysis and Lean formalization:
create an isolated branch, compare routeE_proof_bundle_v3_6_20260506.zip
against the current repo, formalize the branch-wise Route E proof surfaces in
Lean, and either close branches or expose precise counterexample/positive
search blockers with stable build verification.
```

This audit is not a completion claim.  It records current evidence and the
remaining gaps.

## Artifact Checklist

| Requirement | Current evidence | Status |
| --- | --- | --- |
| Isolated branch | `route-e-v3-6-20260506`; commits `dfcf5e6`, `5bf2ce0`, `3d15fb3`, `c958d41`, `cf03adf` | done |
| Bundle read and compared | `docs/ROUTE_E_V3_6_ANALYSIS_20260506.md` records bundle scope, B20/B16/R14e status, and reproduction caveat | done |
| B20 count surface | `RouteEB20.routeCounts`, existing `RouteEB20.counts_sum` | done |
| B20 small-seam surface | Existing `RouteEB20.returnTimeFormula`, `RouteEB20.seamMap`, `RouteEB20.ThetaPointwiseTraceTarget` | pre-existing, still useful |
| B20 all-pair time target | `RouteEB20.allPairTimeMassTotal_eq_modulus_pow_four` and `RouteEB20.allPairTimeMass_sum_eq_modulus_pow_four` | done as arithmetic target |
| B20 lane-sum arithmetic | `RouteEB20.allPairTimeZ_eq_half_add_three`, `allPairTime02_lane_sum_eq`, `allPairTime12_lane_sum_eq`, `allPairTime13_two_clock_eq`, `allPairTime34_boundary_defect_eq` | partially done |
| B20 bundle inconsistency check | `T_03 + T_04` coefficient corrected from bundle text `19079` to `19179`; `RouteEB20.allPairTime03Target_add_allPairTime04Target_v36_draft_defect` proves the old value is short by `100*q`, and `RouteEB20.allPairTime03Target_add_allPairTime04Target_ne_v36_draft` rejects it for `q > 0` | blocker exposed |
| B20 boundary-clock mass adapter | `RouteEB20.BoundaryClockMassTarget`, `RouteEB20.allPairTimeMassFromBoundaryClocks_eq`, `RouteEB20.allPairTimeMassFromBoundaryClocks_sum_eq_modulus_pow_four` | endpoint surface added |
| B20 boundary-clock pointwise formulas | `RouteEB20.boundaryClockTime03Formula`, `RouteEB20.boundaryClockTime04Formula`, `RouteEB20.BoundaryClockPointwiseFormulaTarget`, `RouteEB20.BoundaryClockSymbolicMassTarget`, `RouteEB20.BoundaryClockSymbolicMassTarget.toBoundaryClockMassTarget`, `RouteEB20.allPairTimeMassFromSymbolicBoundaryClocks_sum_eq_modulus_pow_four` | symbolic `q > 0` formula surface added |
| B20 `03`/`04` boundary-clock branch masses | `RouteEB20.allPairTime03BoundaryClockBranchMassTotal_eq_target`, `RouteEB20.allPairTime04BoundaryClockBranchMassTotal_eq_target`, `RouteEB20.allPairTime04BoundaryClockModClassMassTotal_eq_target`, `RouteEB20.allPairTime0304BoundaryClockBranchMassTotal_eq_target_sum`; the B20 closure package supports the symbolic `q >= 1` formulas and separates finite `m=20` | aggregate targets added |
| B20 symbolic/finite dispatcher | `RouteEB20.SymbolicAllPairBranchTarget`, `RouteEB20.FiniteM20AllPairTarget`, `RouteEB20.AllPairBranchTarget`, `RouteEB20.allPairBranchTarget_of_symbolic_and_m20`, plus Hamilton/Torus/Cayley projections | endpoint split added |
| Boundary quotient type | `RouteEBoundaryLabel`, `RouteEBoundaryNode`, `card_routeEBoundaryNode` formalize `{Z} union {03,04,34} x {1,...,m-1}` and cardinal `3m-2` | done |
| B20 boundary quotient formula | `RouteEB20.boundaryQuotient` encodes the v1.8 map candidate; special-gate and generic rewrite lemmas are proved; `RouteEB20.boundaryQuotient_formulaTarget` proves `BoundaryQuotientFormulaTarget q (boundaryQuotient q)` | formula closed |
| B20 boundary one-cycle hand count | `RouteEB20.boundaryCycleLength_eq_card`, `RouteEB20.boundaryCycleSecondEvenEnd_eq_length`, `RouteEB20.boundaryCycleHandCountTotal_eq_card` | count and segment endpoints closed |
| B20 boundary spine segment | `RouteEB20.boundaryCycleSpineNode`, `RouteEB20.boundaryCycleSpine_step_zero`, `RouteEB20.boundaryCycleSpine_step_one`, `RouteEB20.boundaryCycleSpine_step_two`, `RouteEB20.boundaryCycleSpine_step_three`, `RouteEB20.boundaryCycleSpine_step_four`, `RouteEB20.boundaryCycleSpine_step_C_run`, `RouteEB20.boundaryCycleSpine_step_C_last` | full spine successor segment closed |
| B20 boundary residue chains | `RouteEB20.boundaryFirstEvenValue_range`, `RouteEB20.boundaryFirstEvenParam_shift_succ`, `RouteEB20.boundaryCycleFirstEvenTail_step_even`, `RouteEB20.boundaryCycleFirstEvenTail_step_odd`, `RouteEB20.boundaryCycleSpine_to_firstEvenTail`, `RouteEB20.boundaryCycleFirstEvenTail_to_B2Bridge`, `RouteEB20.boundaryFirstOddParam_shift_succ`, `RouteEB20.boundaryCycleFirstOddLane_step_even`, `RouteEB20.boundaryCycleFirstOddLane_step_odd`, `RouteEB20.boundaryCycleB2Bridge_to_firstOddLane`, `RouteEB20.boundaryCycleFirstOddLane_to_BSubOne`, `RouteEB20.boundaryCycleFirstOddBSubOne_to_CRun`, `RouteEB20.boundaryCycleFirstOddCRun_step`, `RouteEB20.boundaryCycleFirstOddCRun_to_ALast`, `RouteEB20.boundarySecondOddParam_shift_succ`, `RouteEB20.boundaryCycleALastBridge_to_secondOddLane`, `RouteEB20.boundaryCycleSecondOddLane_step_even`, `RouteEB20.boundaryCycleSecondOddLane_step_odd`, `RouteEB20.boundaryCycleSecondOddLane_to_final`, `RouteEB20.boundarySecondEvenParam_shift_succ`, `RouteEB20.boundaryCycleSecondOddFinal_to_secondEvenTail`, `RouteEB20.boundaryCycleSecondEvenTail_step_even`, `RouteEB20.boundaryCycleSecondEvenTail_step_odd`, `RouteEB20.boundaryCycleSecondEvenTail_to_zero` | all listed B20 boundary successor segments from zero back to zero are Lean-checked |
| B20 boundary one-cycle adapter | `RouteEB20.boundaryCycleNodeAt`, `RouteEB20.boundaryCycleNode`, `RouteEB20.boundaryCycleNode_last_to_zero`, `RouteEB20.boundaryCycleNodeAt_succ`, `RouteEB20.boundaryCycleNode_step`, `RouteEB20.boundaryCycleNode_injective`, `RouteEB20.boundaryCycleNode_bijective`, `RouteEB20.boundaryQuotientCycleEnumeration`, `RouteEB20.boundaryQuotient_singleCycle`, `RouteEB20.boundaryQuotient_oneCycleTarget`, `RouteEB20.BoundaryQuotientCycleEnumeration.singleCycle`, `RouteEB20.BoundaryQuotientCycleEnumeration.oneCycleTarget` | combined enumeration, global successor semiconjugacy, injectivity, bijectivity, and one-cycle target closed |
| All-pair adapter to endpoints | `RouteEAllPairSectionCertificate.toSmallSeamCertificate` and Hamilton/torus/Cayley projection theorems | done |
| B20 label-fiber all-pair adapter | `RouteEB20.AllPairLabelTraceTarget`, `RouteEB20.AllPairLabelTraceTarget.returnTime_sum`, `RouteEB20.allPairSectionCertificateOfLabelTraceTarget`, `RouteEB20.symbolicAllPairBranchTarget_of_labelTraceTarget`, `RouteEB20.finiteM20AllPairTarget_of_labelTraceTarget`, `RouteEB20.allPairBranchTarget_of_labelTraceTargets` | CSV/verifier-shaped target added |
| B20 indexed all-pair adapter | `RouteEB20.AllPairIndexedLabelTraceTarget`, `RouteEB20.AllPairIndexedLabelTraceTarget.toLabelTraceTarget`, `RouteEB20.allPairSectionCertificateOfIndexedLabelTraceTarget`, `RouteEB20.symbolicAllPairBranchTarget_of_indexedLabelTraceTarget`, `RouteEB20.finiteM20AllPairTarget_of_indexedLabelTraceTarget`, `RouteEB20.allPairBranchTarget_of_indexedLabelTraceTargets` | row-indexed package target added |
| B16 count surface | `RouteEB16.routeCounts`, `RouteEB16.counts_sum` | done |
| B16 time target | `RouteEB16.allPairTimeMassTarget_sum_eq_modulus_pow_four`, `RouteEB16.allPairTimeMassTotalTarget_eq_modulus_pow_four` | done as label-indexed target |
| R14e count surface | `RouteER14e.routeCounts`, `RouteER14e.counts_sum` | done |
| R14e time target | `RouteER14e.allPairTimeMassTarget_sum_eq_modulus_pow_four`, `RouteER14e.allPairTimeMassTotalTarget_eq_modulus_pow_four` | done as label-indexed target |
| Stable Lean verification | `lake env lean D5Odd/EvenRouteE.lean`; `lake env lean D5Odd/EvenRouteEM4.lean` | done |
| Branch closure theorem | No `RouteEAllPairSectionCertificate` instance for B20/B16/R14e yet | open |
| Final all-even theorem | No new all-even dispatcher theorem from Route E v3.6 branches | open |

## Verified Commands

```bash
lake env lean D5Odd/EvenRouteE.lean
lake env lean D5Odd/EvenRouteEM4.lean
```

Both commands completed successfully after the current Lean edits.

The B20 closure package dumper was also regenerated locally under
`/tmp/b20_closure_repro` for
`m = 20,44,68,92,116,140,164`.  Each generated all-pair map had one section
cycle from index `0`, node count `1 + 10*(m-1)`, and total first-return time
`m^4`.  The regenerated `T_03/T_04` sums were:

| m | q | T_03 | T_04 |
| ---: | ---: | ---: | ---: |
| 20 | 0 | 2703 | 2335 |
| 44 | 1 | 30495 | 28516 |
| 68 | 2 | 114447 | 109597 |
| 92 | 3 | 285663 | 276682 |
| 116 | 4 | 575247 | 560875 |
| 140 | 5 | 1014303 | 993280 |
| 164 | 6 | 1633935 | 1605001 |

## Current Blockers

1. B20 `T_03` and `T_04` now have Lean arithmetic branch-mass endpoints and
   proof-facing clock formula surfaces
   (`RouteEB20.BoundaryClockPointwiseFormulaTarget` and
   `RouteEB20.BoundaryClockSymbolicMassTarget`).  They are still not
   first-principles boundary-clock derivations inside Lean.  The closure package
   states the symbolic clock formulas for `q >= 1` and separates the finite
   `m=20` certificate.

2. No branch currently instantiates `RouteEAllPairSectionCertificate`.  The
   adapter now includes `RouteEB20.AllPairLabelTraceTarget` and
   `RouteEB20.AllPairIndexedLabelTraceTarget`, which derive certificate-level
   time exhaustion from per-label fiber sums and can match the package
   `idx`/`dst_idx` row format.  Exact all-pair first-return equations,
   no-early minimality, a section one-cycle proof, and the concrete
   return-time/label function still need to be supplied.

3. B20 has the boundary quotient map candidate `RouteEB20.boundaryQuotient`,
   and `BoundaryQuotientFormulaTarget q (boundaryQuotient q)` is now supplied
   by `RouteEB20.boundaryQuotient_formulaTarget`.  The hand proof's segment
   count, segment endpoints, the spine successor segment, the first-even tail
   successor segment, the first-odd tail through `A_last`, the second-odd tail
   through `A_(half-2)`, the second-even tail back to zero, and residue-chain
   range lemmas are Lean-checked.  The boundary one-cycle target is now closed
   by `RouteEB20.boundaryQuotient_oneCycleTarget`.

4. B16 has a boundary quotient formula and time target in the bundle, but the
   boundary formula, formula-induced one-cycle proof, and lane/core time
   derivation are not Lean proofs.

5. R14e has only transition-count and time-mass evidence at this stage.  The
   bundle explicitly says a closed node-level boundary formula analogous to
   B20/B16 remains to be extracted.

6. The v3.6 bundle reproduction scripts for the B20 time passes expect CSV
   inputs under `/mnt/data`; the B20 closure package includes the C++ dumper and
   compact verifier scripts, so exact maps can be regenerated locally.

## Next Concrete Slice

The next best Lean implementation slice is the B20 symbolic/finite split:

1. promote the recovered `T_03` pointwise clock formulas and `T_04` stabilized
   mod-class recurrences to Lean boundary-clock lemmas for `q >= 1`;
2. add or connect a finite all-pair table certificate for `m=20`;
3. turn the no-early package into Lean-level hypotheses or lemmas;
4. instantiate `RouteEAllPairSectionCertificate` for the B20 section map.
