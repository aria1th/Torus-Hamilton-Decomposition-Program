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
| All-pair adapter to endpoints | `RouteEAllPairSectionCertificate.toSmallSeamCertificate` and Hamilton/torus/Cayley projection theorems | done |
| B16 count surface | `RouteEB16.routeCounts`, `RouteEB16.counts_sum` | done |
| B16 time target | `RouteEB16.allPairTimeMassTotalTarget_eq_modulus_pow_four` | done as target |
| R14e count surface | `RouteER14e.routeCounts`, `RouteER14e.counts_sum` | done |
| R14e time target | `RouteER14e.allPairTimeMassTotalTarget_eq_modulus_pow_four` | done as target |
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

3. B16 has a boundary quotient formula and time target in the bundle, but the
   boundary formula, formula-induced one-cycle proof, and lane/core time
   derivation are not Lean proofs.

4. R14e has only transition-count and time-mass evidence at this stage.  The
   bundle explicitly says a closed node-level boundary formula analogous to
   B20/B16 remains to be extracted.

5. The bundle reproduction scripts for the B20 time passes expect CSV inputs
   under `/mnt/data`; the zip extraction alone does not contain those CSVs.
   This blocks script-level reproduction unless the dumps are restored or the
   scripts are adapted.

## Next Concrete Slice

The next best Lean implementation slice is B20 boundary time:

1. define the B20 boundary quotient node type `{Z} union {03,04,34} x
   {1,...,m-1}`;
2. encode the v1.8 quotient formula as a function;
3. prove the formula one-cycle, or isolate the exact arithmetic sub-lemma
   where the proof fails;
4. derive `T_03` and `T_04` from the boundary clocks, using the corrected
   combined coefficient `19179`.

