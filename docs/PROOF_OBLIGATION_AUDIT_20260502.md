# Proof Obligation Audit

Date: 2026-05-02.

This audit records what the current Lean/program artifacts actually prove for
the active D7/D5-even research goal.  It is deliberately not a completion
claim: the finite manifests and green builds below are evidence for specific
interfaces, not substitutes for the remaining uniform theorems.

## Goal-To-Artifact Map

| Goal item | Current artifact | What is covered | What is not covered |
|---|---|---|---|
| Keep closed D7 odd torus/Cayley endpoint as regression target | `D7Odd/Cayley.lean`, `D7Odd/Torus.lean`, `D7Odd/Handoff/Additive4Plus2Goal.lean` | The existing odd D7 endpoint remains closed in Lean.  The additive bridge can lower to the same torus/Cayley endpoint once the bridge certificate target is supplied. | This does not by itself prove the new structural `4+2` explanation uniformly for all odd `m`. |
| D7 odd additive `A7 ~= A5 x A3` bridge | `D7Odd/Handoff/Additive4Plus2*.lean` | Root-state product chart, local bridge schedule, row/layer local facts, and endpoint adapters are formalized. | Uniform construction of the all-odd bridge data remains open. |
| D7 Target A base rank-step | `D7Odd/Handoff/Additive4Plus2ConcreteGoal.lean`, `D7Odd/Handoff/TargetASeamQuotient.lean`, `scripts/verify_targetA_23_32_seam_quotient.py`, `scripts/verify_targetA_exceptional_phase_splice.py`, `docs/A5_EXCEPTIONAL_PHASE_SPLICE_BUNDLE_V0_4_20260502.md` | `BridgeConcreteFullRankPackage` names the Lean-facing base rank `A5 -> ZMod (m^4)` and derives base orbit coverage from rank step.  The `23/32` seam quotient arithmetic is closed in Lean for `h >= 6`; the verifier checks Q-hitting, Q-first-return formulas, and length sums over the tested range.  The exceptional phase-splice bundle reduces the bad class `m = 10*t+7` to a five-lane system and identifies `00` as a correction block with an explicit phase table.  The new exceptional verifier recomputes that phase table from the A5 state dynamics for `m = 17,27,37`. | Lean still needs actual Q-hitting and length-sum proofs, small-modulus packaging, a formal exceptional `00` phase table, a correction word or row-family insertion schedule whose reduced lane map is one cycle, the lift of that splice proof back to the base return/rank package, and a seven-row column exact-cover family.  The current `23/32` branch covers the good class structurally, not the full Target-A row-family problem. |
| D7 Target B' fiber rank-step | `D7Odd/Handoff/Additive4Plus2ConcreteGoal.lean`, `D7Odd/Handoff/Additive4Plus2TargetB.lean`, `scripts/verify_zero_set_k_cert.py`, `scripts/verify_d7_4plus2_rank_fingerprints.py` | `BridgeConcreteFullRankPackage` names the fiber rank `A3 -> ZMod (m^2)` and derives monodromy single-cycle from rank step.  `Additive4Plus2TargetB.lean` proves the triangular A3 scalar criterion: a clock/carry map `(s,x) |-> (s+A, x+phi(s))` is one `m^2` cycle when the clock scalar `A`, full-round carry scalar `E`, and round-return equation are supplied with `A,E` units.  It combines this with the base `m^4` rank-step as `BridgeConcreteScalarMonodromyPackage`, and now also names the zero-set-only specialization `ZeroSetKappaFamily` / `BridgeConcreteZeroSetScalarMonodromyPackage`, lowering Target-B' data to the bridge torus/Cayley endpoints.  The `m=9` scalar zero-set-only `K(Z)` certificate now checks scalar units, extracts finite `phi(s)` tables, verifies the triangular `roundAtZero` equations, and runs the full finite bridge replay.  Compact `m=11,13,17` witnesses have committed base/fiber rank fingerprints. | No uniform zero-set-only or congruence-family `K_m(Z)` theorem is proved.  The remaining Lean gap is to construct a `ZeroSetKappaFamily` or congruence-family replacement and derive the triangular round-return equation and scalar units from the selected row schedule. |
| D5 even Route-E periodic-excursion track | `D5Odd/EvenRouteE.lean`, `D5Odd/EvenRouteEM4.lean`, `scripts/verify_d5_even_routeE.py`, `scripts/verify_d5_routeE_nonopen_bundle.py`, `scripts/verify_d5_routeE_small_seam_rank_certs.py`, `scripts/verify_d5_routeE_b20_branch.py`, `docs/D5_EVEN_ROUTE_E_BRANCH_EXTRACTION_V0_7_20260502.md` | The finite `m=4` branch is closed.  The canonical `Theta_s` small-seam certificate lowers to D5 Hamilton/Torus/Cayley endpoints, and `D5Odd/EvenRouteEM4.lean` now gives unconditional adapters from the ranked, piecewise, and ranked-piecewise all-large Route-E targets to the all-even Hamilton/Torus/Cayley endpoints.  The ranked piecewise certificate derives the seam one-cycle from a rank into `ZMod (m-1)`.  The open-port section normal form is now Lean-named: the section-pair map is conjugate by `(a,b) |-> (a+b,a)` to `H(sigma,a)=(sigma-C,a+A+1-1_{sigma=0})`, `RouteEOpenPortAffineChartCertificate` records the rank-step hook for that `m^2` section map, `routeEOpenPortFinSquareSucc_single_cycle` closes the finite base-`m` odometer spine for explicit chart ranks, and `RouteEOpenPortFiniteOdometerCertificate` lowers a chart equivalence plus step law to the section cycle.  The canonical uniform-triple chart `routeEOpenPortCanonicalChartIdx(s,a)=(-a-s,-1-s)` now has its carry law closed as `RouteEOpenPortCanonicalChartStepTarget.unconditional`, yielding `routeEOpenPortCanonicalH_single_cycle` and `routeEOpenPortCanonicalSectionPairMap_single_cycle`.  The finite `m=6,8,...,60` bundle table is checked against the repo table and verifier transcript; the rank/block certs verify rank step, maximal translation blocks, and return-time sum.  The v0.7 branch extraction shifts the proof search toward a finite residue-branch menu and isolates B20, `m == 20 mod 24`, with counts `(r,0,0,h+r,r)` and an apparent two-block seam map, as the first symbolic branch target.  The B20 verifier checks this formula, the two-block map, the pointwise return-time partition, and the return-time sum for selected moduli.  Lean now records `RouteEB20.counts_sum` and `RouteEB20.returnTimeWeightedSum_eq_modulus_pow_four`, closing the arithmetic sum after the extracted distribution is proved.  Lean also records the expected B20 seam map as index addition on the nonzero seam and proves `RouteEB20.seamMap_single_cycle`, the two translation-block formulas, and the `RouteEB20.seamBlocks_*` cover/disjoint/translation packaging. | The all-even symbolic proof is still open: a finite count/slot branch menu covering all even `m >= 6`, branch first-return equations/minimality, uniform seam rank formulas, full-return proofs beyond the open-port section, and return-time sums must be proved.  For B20 specifically, the missing theorem is the symbolic port-time proof that the small-seam first return equals the closed expected seam map, no earlier return occurs, and the pointwise return-time partition holds. |
| D7 even separate track | `D7Odd/Even.lean` | The even D7 target remains isolated behind the `RootFlatSchedule` certificate interface and endpoint adapters. | A new uniform D7-even certificate family is not supplied here. |
| Composite/root-flat/local bridge/monodromy infrastructure | `Shared/*.lean`, `RoundComposite.lean`, `RoundComposite/ConcreteEndpoints.lean` | The shared root-flat lift, monodromy/rank-cycle lemmas, and graph-level composite endpoints build.  New D7/D5 propositions are intended to plug into these interfaces. | No new prime-odd or even certificate is created by the composite infrastructure alone. |

## Current Verification Snapshot

Lean builds rerun on 2026-05-02:

```text
lake build D7Odd.Handoff.TargetASeamQuotient D7Odd.Handoff.Additive4Plus2ConcreteGoal
=> Build completed successfully (8378 jobs).

lake build D7Odd.Handoff.Additive4Plus2TargetB D7Odd.Handoff
=> Build completed successfully (8384 jobs).

lake build D5Odd.EvenRouteE D5Odd.EvenRouteEM4 D7Odd.Even
=> Build completed successfully (8379 jobs).

lake build RoundComposite.ConcreteEndpoints
=> Build completed successfully (8375 jobs).
```

Program regressions rerun on 2026-05-02:

```text
python3 scripts/verify_d7_4plus2_rank_fingerprints.py \
  --json-out /tmp/d7_4plus2_rank_fingerprint_current.json
=> witnesses 3 all_ok True missing [] extra []

python3 scripts/verify_zero_set_k_cert.py \
  certs/d7_m9_zero_set_K_scalar_cert.json \
  --triangular-manifest certs/d7_m9_zero_set_K_triangular_obligations.json \
  --json-out /tmp/d7_m9_zero_set_K_scalar_triangular_full.json
=> m=9 scalar_ok=True triangular_ok=True table_ok=True provided_kappa=absent expanded_valid=True full_ok=True
=> triangular_manifest_ok True mismatches []

python3 scripts/verify_zero_set_k_cert.py \
  certs/d7_m9_zero_set_K_full_bridge_cert.json \
  certs/d7_m9_zero_set_K_scalar_cert.json \
  --allow-missing-scalar \
  --json-out /tmp/d7_m9_zero_set_K_full_and_scalar_verify.json
=> m=9 scalar_ok=False triangular_ok=False table_ok=True provided_kappa=True expanded_valid=True full_ok=True
=> m=9 scalar_ok=True triangular_ok=True table_ok=True provided_kappa=absent expanded_valid=True full_ok=True
=> all_ok=True

python3 scripts/verify_4plus2_allN_bridge_cert.py \
  --cert-json certs/d7_m9_zero_set_K_full_bridge_cert.json
=> verified m=9 product_states=531441 rows=7 base_rank_steps=ok section_rank_steps=ok return_cycles=single

python3 scripts/verify_targetA_23_32_seam_quotient.py \
  --moduli 13,15,17,19,21,23,25,27,29,31,33,35,37,39,41 \
  --phi-max 200 \
  --manifest certs/d7_targetA_23_32_seam_quotient_manifest.json \
  --json-out /tmp/d7_targetA_23_32_seam_quotient_current.json
=> phi_all_ok=True, all_ok=True
=> manifest_ok True mismatches []

python3 scripts/verify_targetA_exceptional_phase_splice.py \
  --moduli 17,27,37 \
  --json-out /tmp/d7_targetA_exceptional_phase_splice_17_37.json
=> all_ok=True

python3 scripts/summarize_d5_routeE_small_seam_blocks.py \
  --json-out /tmp/d5_routeE_small_seam_block_summary_current.json
=> cases 28 all_ok True return_sums_ok True

python3 scripts/verify_d5_routeE_b20_branch.py \
  --moduli 20,44 \
  --json-out /tmp/d5_routeE_b20_branch_20_44.json
=> all_ok=True

python3 scripts/analyze_d5_routeE_small_seam_families.py \
  --manifest certs/d5_routeE_small_seam_family_scan_manifest.json \
  --json-out /tmp/d5_routeE_small_seam_family_scan_current.json
=> manifest_ok True mismatches []

python3 scripts/verify_d5_even_routeE.py --mode section \
  --count-scan-moduli 6,8,10,12 \
  --count-scan-limit 20 \
  --json-out /tmp/d5_count_scan_6_12_limit20.json
python3 scripts/analyze_d5_routeE_small_seam_families.py \
  --manifest certs/d5_routeE_small_seam_family_scan_manifest.json \
  --count-scan-json /tmp/d5_count_scan_6_12_limit20.json \
  --score-count-scan-small-seam \
  --json-out /tmp/d5_routeE_small_seam_family_scan_with_count_hits.json
=> count_scan summaries:
=> m=6: first_hits=10 distinct=2 open_hits=0 known_present=True alternatives=1
=> m=8: first_hits=10 distinct=2 open_hits=0 known_present=True alternatives=1
=> m=10: first_hits=20 distinct=9 open_hits=6 known_present=True alternatives=8
=> m=12: first_hits=20 distinct=12 open_hits=2 known_present=True alternatives=11
=> scored min-block examples:
=> m=10: (0,0,8,1,0), blocks=7, open=True
=> m=12: (1,2,1,7,0), blocks=7, open=False

python3 scripts/verify_d5_even_routeE.py --mode section \
  --count-scan-moduli 14,16 \
  --count-scan-limit 20 \
  --json-out /tmp/d5_count_scan_14_16_limit20.json
python3 scripts/analyze_d5_routeE_small_seam_families.py \
  --manifest certs/d5_routeE_small_seam_family_scan_manifest.json \
  --count-scan-json /tmp/d5_count_scan_14_16_limit20.json \
  --score-count-scan-small-seam \
  --json-out /tmp/d5_routeE_count_hit_scores_14_16.json
=> m=14: first_hits=20 distinct=20 open_hits=1 known_present=True alternatives=19
=> m=16: first_hits=20 distinct=20 open_hits=0 known_present=True alternatives=19
=> scored min-block examples:
=> m=14: (2,2,6,3,0), blocks=7, open=False
=> m=16: (1,13,0,1,0), blocks=11, open=False, known=True

python3 scripts/search_d5_routeE_small_seam_candidates.py \
  --mode open-port \
  --moduli 6,8,10,12,14,16,18,20 \
  --hit-limit 2 \
  --json-out /tmp/d5_open_port_small_seam_search_6_20.json
=> open-port small-seam hits at m=10,12,14,18,20
=> no open-port hit in this search at m=6,8,16

python3 scripts/search_d5_routeE_small_seam_candidates.py \
  --mode support \
  --max-support 3 \
  --moduli 6,8,10,12,14,16 \
  --hit-limit 3 \
  --json-out /tmp/d5_support3_small_seam_search_6_16.json
python3 scripts/search_d5_routeE_small_seam_candidates.py \
  --mode support \
  --max-support 3 \
  --moduli 18,20,22 \
  --hit-limit 3 \
  --candidate-limit 1200 \
  --json-out /tmp/d5_support3_small_seam_search_18_22.json
=> support<=3 min-block examples:
=> m=14: (1,3,0,9,0), blocks=8
=> m=18: (5,7,0,5,0), blocks=9
=> m=22: (3,1,0,17,0), blocks=10
=> The searcher also supports exploratory return caps, but capped misses are
=> not proof evidence; candidates used downstream must be rerun without caps.

python3 scripts/search_d5_routeE_small_seam_candidates.py \
  --mode support \
  --max-support 3 \
  --support-pattern 0,1,3 \
  --moduli 14,16,18,20 \
  --hit-limit 0 \
  --json-out /tmp/d5_support013_small_seam_fullhits_14_20.json
python3 scripts/search_d5_routeE_small_seam_candidates.py \
  --mode support \
  --max-support 3 \
  --support-pattern 0,1,3 \
  --moduli 22 \
  --hit-limit 0 \
  --json-out /tmp/d5_support013_small_seam_fullhits_22.json
python3 scripts/search_d5_routeE_small_seam_candidates.py \
  --mode support \
  --max-support 3 \
  --support-pattern 0,1,3 \
  --moduli 24 \
  --hit-limit 0 \
  --json-out /tmp/d5_support013_small_seam_fullhits_24.json
python3 scripts/search_d5_routeE_small_seam_candidates.py \
  --mode support --max-support 3 --support-pattern 0,1,3 \
  --moduli 26 --hit-limit 0 \
  --json-out /tmp/d5_support013_small_seam_fullhits_26.json
python3 scripts/search_d5_routeE_small_seam_candidates.py \
  --mode support --max-support 3 --support-pattern 0,1,3 \
  --moduli 28 --hit-limit 0 \
  --json-out /tmp/d5_support013_small_seam_fullhits_28.json
python3 scripts/search_d5_routeE_small_seam_candidates.py \
  --mode support --max-support 3 --support-pattern 0,1,3 \
  --moduli 30 --hit-limit 0 \
  --json-out /tmp/d5_support013_small_seam_fullhits_30.json
=> full support-pattern (a,b,0,c,0) min-block examples:
=> m=14: (1,3,0,9,0), blocks=8
=> m=16: (1,13,0,1,0), blocks=11
=> m=18: (5,7,0,5,0), blocks=9
=> m=20: (3,13,0,3,0), blocks=7
=> m=22: (11,3,0,7,0), blocks=7
=> m=24: (5,13,0,5,0), blocks=11
=> m=26: (13,5,0,7,0), blocks=8
=> m=28: (3,5,0,19,0), blocks=8
=> m=30: (11,7,0,11,0), blocks=8
=> The same pattern at m=32,34 was stopped after about two minutes without
=> a JSON result, so the current exact support-pattern evidence is m=14..30.

python3 scripts/verify_d5_routeE_nonopen_bundle.py \
  /data/angel/repos/etc/d5_even_routeE_nonopen_small_seam_v0_4.zip \
  --json-out /tmp/d5_routeE_nonopen_bundle_check.json
=> cases 28 tsv_matches_repo True report_matches_tsv True python_recompute_all_ok True all_ok True

python3 scripts/verify_d5_even_routeE.py --mode section \
  --section-scan-moduli 6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,50,52,54,56,58,60 \
  --section-scan-limit 1 \
  --full-scan-moduli 6,8,10,12,14,16,18,20 \
  --full-scan-limit 1 \
  --manifest certs/d5_routeE_open_port_manifest.json \
  --json-out /tmp/d5_routeE_open_port_manifest_verify.json
=> manifest_ok True mismatches []

python3 scripts/verify_d5_routeE_small_seam_rank_certs.py \
  --cert certs/d5_routeE_small_seam_rank_certs.json \
  --json-out /tmp/d5_routeE_small_seam_rank_cert_current.json
=> cases 28 all_ok True missing [] extra []
```

The D5 build replays existing `D5Odd.ReturnCycle` linter warnings.  They are
not new proof gaps for this audit, but they remain cleanup debt.

## Current Blocking Propositions

The sharpest remaining propositions are:

1. **D7 Target A, row family.**  Produce seven all-zero-set base row words for
   every odd `m >= 5`, prove column exact-cover, and prove the canonical
   folded base return admits a bijective rank into `ZMod (m^4)` stepping by
   `+1`.
2. **D7 Target A, good-class `23/32` proof completion.**  Formalize the
   Q-hitting, Q-first-return, and length-sum obligations currently verified by
   `verify_targetA_23_32_seam_quotient.py`, and package the small moduli.
3. **D7 Target A, exceptional splice.**  Formalize the five-lane `00` phase
   table for `m = 10*t+7`, choose a correction word or insertion schedule,
   prove the reduced lane map is one cycle, and lift the result back through
   Q-hitting and length-sum/excursion coverage.
4. **D7 Target B'.**  Generalize the finite `m=9` zero-set-only scalar
   certificate as a `ZeroSetKappaFamily`, or replace it by a congruence-family
   `K_m(Z)`, then prove that the selected row schedule and `K_m(Z)` produce the
   triangular A3 round-return equation and unit scalars needed by
   `A3TriangularScalarCertificate`.
5. **D5 even Route-E.**  Find a finite residue-branch menu of count/slot
   families covering every even `m >= 6`; prove each branch's induced
   `Theta_s` first-return equations and minimality; prove seam rank formulas
   into `ZMod (m-1)`; and prove `sum tau = m^4`.  The first branch-level
   target is B20, `m == 20 mod 24`, with
   `nu=(r,0,0,h+r,r)` and a two-block seam map.  Its count-sum, weighted
   return-time arithmetic, expected seam-map translations, and expected
   seam-map single-cycle theorem are now recorded in Lean, and
   `RouteEB20.ThetaTraceTarget` names the exact trace certificate still to be
   constructed.  Its adapter
   `RouteEB20.thetaPiecewiseCertificateOfTraceTarget` already packages such a
   trace certificate as a `RouteEThetaPiecewiseTranslationCertificate`, so the
   remaining B20 work is the symbolic trace theorem: first-return equations,
   no-earlier-return, and pointwise return-time partition.  The pointwise
   form is now named as `RouteEB20.returnTimeFormula` and
   `RouteEB20.ThetaPointwiseTraceTarget`, with the final arithmetic routed
   through `RouteEB20.returnTimeWeightedSum_eq_modulus_pow_four`.  The canonical
   open-port carry law is a checked section-level lemma, not the final
   all-even return theorem; the remaining work is the full Route-E symbolic
   small-seam certificate.
6. **D7 even.**  Keep the RootFlatSchedule route separate and supply a
   certificate family only on that track.

## Practical Next Checks

When another bundle arrives, the first comparison should ask whether it
supplies one of the missing propositions above rather than just another finite
cycle witness.  In particular:

- For D7 odd, look for row-family exact-cover formulas, explicit base/fiber
  rank formulas, or a uniform `K_m(Z)` scalar proof.
- For D5 even, look for residue-class count/slot families and symbolic
  one-dimensional small-seam proofs, not only additional finite moduli.
- For D7 even, reject anything that silently mixes into the D7 odd `4+2`
  bridge; it belongs behind the separate root-flat certificate interface.
