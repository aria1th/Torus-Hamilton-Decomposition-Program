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
| B20 bundle inconsistency check | `T_03 + T_04` coefficient corrected from bundle text `19079` to `19179`; old value fails total time by `100*q` | blocker exposed |
| Boundary quotient type | `RouteEBoundaryLabel`, `RouteEBoundaryNode`, `card_routeEBoundaryNode` formalize `{Z} union {03,04,34} x {1,...,m-1}` and cardinal `3m-2` | done |
| B20 boundary quotient formula | `RouteEB20.boundaryQuotient` encodes the v1.8 map candidate; special-gate and generic rewrite lemmas are proved; `RouteEB20.boundaryQuotient_formulaTarget` proves `BoundaryQuotientFormulaTarget q (boundaryQuotient q)` | formula closed, one-cycle open |
| B20 boundary one-cycle hand count | `RouteEB20.boundaryCycleLength_eq_card`, `RouteEB20.boundaryCycleSecondEvenEnd_eq_length`, `RouteEB20.boundaryCycleHandCountTotal_eq_card` | count and segment endpoints closed, rank/orbit proof open |
| B20 boundary spine segment | `RouteEB20.boundaryCycleSpineNode`, `RouteEB20.boundaryCycleSpine_step_zero`, `RouteEB20.boundaryCycleSpine_step_one`, `RouteEB20.boundaryCycleSpine_step_two`, `RouteEB20.boundaryCycleSpine_step_three`, `RouteEB20.boundaryCycleSpine_step_C_run`, `RouteEB20.boundaryCycleSpine_step_C_last` | full spine successor segment closed, remaining orbit open |
| B20 boundary residue chains | `RouteEB20.boundaryFirstEvenValue_range`, `RouteEB20.boundaryFirstEvenParam_shift_succ`, `RouteEB20.boundaryCycleFirstEvenTail_step_even`, `RouteEB20.boundaryCycleFirstEvenTail_step_odd`, `RouteEB20.boundaryCycleSpine_to_firstEvenTail`, `RouteEB20.boundaryCycleFirstEvenTail_to_B2Bridge`, `RouteEB20.boundaryFirstOddParam_shift_succ`, `RouteEB20.boundaryCycleFirstOddLane_step_even`, `RouteEB20.boundaryCycleFirstOddLane_step_odd`, `RouteEB20.boundaryCycleB2Bridge_to_firstOddLane`, `RouteEB20.boundaryCycleFirstOddLane_to_BSubOne`, `RouteEB20.boundaryCycleFirstOddBSubOne_to_CRun`, `RouteEB20.boundaryCycleFirstOddCRun_step`, `RouteEB20.boundaryCycleFirstOddCRun_to_ALast`, `RouteEB20.boundarySecondOddParam_shift_succ`, `RouteEB20.boundaryCycleALastBridge_to_secondOddLane`, `RouteEB20.boundaryCycleSecondOddLane_step_even`, `RouteEB20.boundaryCycleSecondOddLane_step_odd`, `RouteEB20.boundaryCycleSecondOddLane_to_final`, plus second-even range lemmas | first-even segment, first-odd tail through `A_last`, and second-odd tail through `A_(half-2)` closed; remaining second-even chain and bijection proof open |
| All-pair adapter to endpoints | `RouteEAllPairSectionCertificate.toSmallSeamCertificate` and Hamilton/torus/Cayley projection theorems | done |
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

## Current Blockers

1. B20 `T_03` and `T_04` are still target polynomials, not boundary-clock
   derivations.  The corrected sum is now Lean-checked, but the first-principles
   derivation remains open.

2. No branch currently instantiates `RouteEAllPairSectionCertificate`.  The
   adapter exists, but exact all-pair first-return equations, no-early
   minimality, a section one-cycle proof, and the concrete return-time function
   still need to be supplied.

3. B20 has the boundary quotient map candidate `RouteEB20.boundaryQuotient`,
   and `BoundaryQuotientFormulaTarget q (boundaryQuotient q)` is now supplied
   by `RouteEB20.boundaryQuotient_formulaTarget`.  The hand proof's segment
   count, segment endpoints, the spine successor segment, the first-even tail
   successor segment, the first-odd tail through `A_last`, the second-odd tail
   through `A_(half-2)`, and residue-chain range lemmas are Lean-checked, but
   the remaining second-even chain and bijection parts of the rank/orbit proof
   remain open.

4. B16 has a boundary quotient formula and time target in the bundle, but the
   boundary formula, formula-induced one-cycle proof, and lane/core time
   derivation are not Lean proofs.

5. R14e has only transition-count and time-mass evidence at this stage.  The
   bundle explicitly says a closed node-level boundary formula analogous to
   B20/B16 remains to be extracted.

6. The bundle reproduction scripts for the B20 time passes expect CSV inputs
   under `/mnt/data`; the zip extraction alone does not contain those CSVs.
   This blocks script-level reproduction unless the dumps are restored or the
   scripts are adapted.

## Next Concrete Slice

The next best Lean implementation slice is B20 boundary one-cycle:

1. define `boundaryCycleNode q : Fin (boundaryCycleLength q) →
   RouteEBoundaryNode (modulus q)` by extending the checked spine, first-even
   tail, and first-odd lane segments across the remaining residue-chain
   segments;
2. prove the remaining successor compatibility with
   `RouteEB20.boundaryQuotient`;
3. prove the enumeration is bijective, then conjugate to `finRotate`;
4. after the quotient cycle is closed, return to the boundary-clock derivation
   of `T_03` and `T_04` using the corrected combined coefficient `19179`.
