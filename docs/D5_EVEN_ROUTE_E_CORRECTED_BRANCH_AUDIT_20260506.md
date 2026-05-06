# D5 Even Route E Corrected Branch Audit

Date: 2026-05-06.

This audit records the current state of the goal:

```text
Fill the corrected D5 even Route-E branch dispatcher as far as possible, and
promote finite witness evidence toward symbolic proof artifacts by scripts,
docs, verification, and commits.
```

The goal is not complete as an all-even proof.  It is currently complete only
as a branch-taxonomy and evidence-preservation pass.

## Deliverable Checklist

| requirement | artifact | current status |
| --- | --- | --- |
| Correct the branch taxonomy after the sign audit | `docs/D5_EVEN_ROUTE_E_CORRECTED_BRANCH_DISPATCHER_20260506.md` | done |
| Remove impossible even prefix-count branch | same dispatcher doc | done, recorded as `X1` |
| Remove cyclic bulk + RF2-preserving adjacent-Kempe branch | same dispatcher doc plus `docs/D5_EVEN_ROUTE_E_ADJACENT_KEMPE_NO_GO_20260506.md` | done, recorded as `X2` |
| Audit discarded X1/X2 mechanisms | `scripts/verify_routeE_no_go_branches.py`, `certs/routeE_no_go_branch_verification.json` | done |
| Add color-by-color sign vector and repeated-block screens | `scripts/audit_routeE_color_sign_screens.py`, `certs/routeE_color_sign_screen_audit.json` | done |
| Preserve `m=2` full-layered boundary certificate | `certs/d5_routeE_m2_full_layered_boundary.json` | done |
| Verify `m=2` RF1/RF2/sign/nested returns | `scripts/summarize_d5_routeE_corrected_branches.py` | done |
| Preserve `m=4` finite certificate status | summary script via `export_d5_even_routeE_layers.py` | done |
| Preserve `m=6..60` small-seam evidence window | `certs/d5_routeE_small_seam_rank_certs.json` and branch summary cert | done |
| Distinguish rank/block verification from table presence | `scripts/summarize_d5_routeE_corrected_branches.py --verify-rank-certs` | done |
| Distinguish seam recomputation from rank cert verification | `--verify-small-seam` and `--verify-rank-certs` options | done |
| Turn Lambda_E local mask counts into symbolic formulas | `scripts/derive_d5_lambdaE_mask_polynomials.py`, `certs/d5_lambdaE_mask_polynomials.json`, and `docs/D5_EVEN_ROUTE_E_PROOF_PROGRESS_20260506.md` | done |
| Verify Lambda_E symbolic mask-count artifact by recomputation | `scripts/verify_d5_lambdaE_mask_polynomials.py`, `certs/d5_lambdaE_mask_polynomials_verification.json` | done |
| Preserve first Type-A B20 branch evidence | `certs/d5_routeE_b20_branch_verify_m20_44_68.json` | done, covers `m=20,44,68,92` despite filename |
| Check B20 sample branch verifier in completion audit | `scripts/audit_routeE_corrected_goal.py` | done |
| Preserve Type-A B16/R14e package evidence without raw CSV | `scripts/summarize_routeE_typeA_closure_packages.py`, `certs/routeE_typeA_closure_package_summary.json`, `certs/routeE_typeA_symbolic_skeleton.json` | done |
| Verify Type-A symbolic skeleton identities without `sympy` | `scripts/verify_routeE_typeA_symbolic_skeleton.py`, `certs/routeE_typeA_symbolic_skeleton_verification.json` | done |
| Record Type-A residue coverage and next target | `scripts/summarize_routeE_typeA_residue_coverage.py`, `certs/routeE_typeA_residue_coverage.json` | done |
| Preserve all-pair portfolio sample coverage | `certs/routeE_allpair_portfolio_samples_v1_1.json`, `scripts/summarize_routeE_allpair_portfolio.py`, `certs/routeE_allpair_portfolio_summary.json` | done, samples cover all even residues but are not proofs |
| Fit all-pair portfolio samples by residue | `scripts/analyze_routeE_allpair_portfolio_fits.py`, `certs/routeE_allpair_portfolio_fit_summary.json` | done, `42 mod 48` is next affine portfolio-only candidate |
| Initialize R42 affine branch record | `scripts/init_routeE_r42_affine_branch_record.py`, `certs/routeE_r42_affine_branch_record.json` | done, branch remains open |
| Reproduce R42 affine samples with all-pair checker | `scripts/routeE_allpair_cpp_v1_2.cpp`, `scripts/verify_routeE_r42_affine_samples.py`, `certs/routeE_r42_affine_samples_verification.json` | done, sample-verified but not symbolic |
| Summarize R42 boundary quotient | `scripts/summarize_routeE_r42_boundary_quotient.py`, `certs/routeE_r42_boundary_quotient_summary.json` | done, q>=1 block profile stable |
| Verify R42 compact boundary summary | `scripts/verify_routeE_r42_boundary_summary.py`, `certs/routeE_r42_boundary_summary_verification.json` | done, internal affine/block consistency verified |
| Recheck R38 symmetric next-target evidence | `certs/routeE_r38_symmetric_probe_summary.json` and raw small probe JSONs | done, negative-control only |
| Make C++ residue branch search timeout-safe | `scripts/search_d5_routeE_cpp_residue_branches.py --timeout`, `certs/routeE_r38_m182_cpp_screen_timeout.json` | done |
| Run broad open-residue C++ smoke screen | `certs/routeE_open_residue_cpp_smoke_20260506.json`, `certs/routeE_open_residue_cpp_smoke_summary_20260506.json` | done, all timed out |
| Initialize R38 gate-transducer branch record | `scripts/init_routeE_r38_gate_transducer_record.py`, `certs/routeE_r38_gate_transducer_branch_record.json` | done, branch remains open |
| Scan finite small-seam window for simple affine branch laws | `scripts/analyze_d5_routeE_small_seam_families.py`, `certs/routeE_small_seam_family_scan_manifest.json` | done, no robust law found |
| Verify finite small-seam family scan by recomputation | `scripts/verify_routeE_small_seam_family_scan.py`, `certs/routeE_small_seam_family_scan_verification.json` | done |
| Machine-check the goal completion status | `scripts/audit_routeE_corrected_goal.py`, `certs/routeE_corrected_goal_audit.json` | done, reports incomplete |
| Visualize current Route E progress | `docs/ROUTE_E_LATEST_COMMITS_VISUALIZATION_20260506.md` | done |
| Connect B20 to Lean-facing open fields | dispatcher doc, references `RouteEB20.ThetaPointwiseTraceTarget` | done |
| Prove generic all-even E-gen theorem | none | open |

## Commands Checked

Fast branch summary:

```bash
python3 scripts/summarize_d5_routeE_corrected_branches.py
```

Full branch-window verification:

```bash
python3 scripts/summarize_d5_routeE_corrected_branches.py \
  --verify-rank-certs \
  --verify-small-seam \
  --json-out certs/d5_routeE_corrected_branch_summary.json
```

Rank certificate verifier:

```bash
python3 scripts/verify_d5_routeE_small_seam_rank_certs.py \
  --cert certs/d5_routeE_small_seam_rank_certs.json
```

Result:

```text
cases 28 all_ok True missing [] extra []
```

Discarded branch no-go verifier:

```bash
python3 scripts/verify_routeE_no_go_branches.py \
  --json-out certs/routeE_no_go_branch_verification.json
```

Result:

```text
all_ok=True
X1 even prefix-count contradiction=True
X2 adjacent-Kempe-only sign contradiction=True
```

Color sign vector and repeated-block screen:

```bash
python3 scripts/audit_routeE_color_sign_screens.py \
  --json-out certs/routeE_color_sign_screen_audit.json
```

Result:

```text
all_recorded_color_sign_screens_ok True
one_lambda_records 49
explicit_records 2
stationary_branch_discarded True
```

This strengthens the old global sign screen.  The recorded necessary condition
is now

```text
(Omega_0,Omega_1,Omega_2,Omega_3,Omega_4)=(-,-,-,-,-),
```

where `Omega_kappa = product_t sign(P_{t,kappa})`.  The same artifact records
the repeated-block screen: if `R_kappa = B_kappa^h`, then `gcd(h,m)=1` is
necessary; stationary seams have `h=m` and are discarded.

Lambda_E symbolic mask counts:

```bash
python3 scripts/derive_d5_lambdaE_mask_polynomials.py \
  --json-out certs/d5_lambdaE_mask_polynomials.json
```

The script derives exact shifted-zero mask polynomials by inclusion-exclusion
over the 5-cycle equality arrangement and recovers the modal/nonmodal/rank
totals used by the finite witnesses.

The recorded symbolic totals are:

```text
modal_count    = m^4 - 5*m^3 + 10*m^2 - 10*m + 5
nonmodal_count = 5*m^3 - 10*m^2 + 10*m - 5
rank_0_total   = 3*m^3 + m^2 - 3*m - 1
rank_1_total   = 3*m^3 + 2*m^2 - 5*m
rank_2_total   = 3*m^3 - 4*m + 1
rank_3_total   = 2*m^3 - 2*m
```

Verification:

```bash
python3 scripts/verify_d5_lambdaE_mask_polynomials.py \
  --json-out certs/d5_lambdaE_mask_polynomials_verification.json
```

Result:

```text
ok True masks 32 reachable 27 unreachable 5
```

B20 branch verifier:

```bash
python3 scripts/verify_d5_routeE_b20_branch.py \
  --moduli 20,44,68,92 \
  --json-out certs/d5_routeE_b20_branch_verify_m20_44_68.json
```

Result:

```text
all_ok=True
```

Type-A package summary:

```bash
python3 scripts/summarize_routeE_typeA_closure_packages.py \
  --json-out certs/routeE_typeA_closure_package_summary.json \
  --symbolic-out certs/routeE_typeA_symbolic_skeleton.json
```

Result:

```text
b16 [16, 40, 64, 88, 112, 136, 160] macro_all_ok True r14e [14, 62, 110, 158, 206] all_recorded_flags_ok True
```

The symbolic skeleton preserves:

```text
B16: 11 label-polynomial entries and 29 destination-label polynomial entries;
R14e: 11 label-polynomial entries, 33 destination-label polynomial entries,
      and insertion macro identities.
```

Type-A symbolic skeleton verification without `sympy`:

```bash
python3 scripts/verify_routeE_typeA_symbolic_skeleton.py \
  --json-out certs/routeE_typeA_symbolic_skeleton_verification.json
```

Result:

```text
all_ok True
```

The checker uses a small standard-library one-variable polynomial parser.  It
verifies the B16/R14e label totals, destination-label totals, R14e
destination-count total, insertion boundary count, insertion weighted count,
and `m^4` identities.

Type-A residue coverage:

```bash
python3 scripts/summarize_routeE_typeA_residue_coverage.py \
  --json-out certs/routeE_typeA_residue_coverage.json
```

Result:

```text
covered residues mod 48: 14,16,20,40,44
open residues mod 48: 0,2,4,6,8,10,12,18,22,24,26,28,30,32,34,36,38,42,46
next target: R42 affine all-pair/boundary family
```

All-pair portfolio sample coverage from the v3.6 proof bundle:

```bash
python3 scripts/summarize_routeE_allpair_portfolio.py \
  --json-out certs/routeE_allpair_portfolio_summary.json
```

Result:

```text
samples=81
covered_residues=24/24 even residue classes mod 48
portfolio_only_residues=19
```

These are zero-event checked all-pair candidates, not symbolic branch theorems.
The audit keeps this evidence separate from proof-facing Type-A coverage.

Portfolio affine-fit scan:

```bash
python3 scripts/analyze_routeE_allpair_portfolio_fits.py \
  --json-out certs/routeE_allpair_portfolio_fit_summary.json
```

Result:

```text
affine_xz_residues=[14,16,20,40,42,44]
portfolio_only_affine_xz_residues=[42]
```

Thus the next simple symbolic-promotion candidate from the portfolio is
`m = 48q + 42` with the observed symmetric affine law `x = z = 6q + 5`.

R42 branch record:

```bash
python3 scripts/init_routeE_r42_affine_branch_record.py \
  --json-out certs/routeE_r42_affine_branch_record.json
```

Result:

```text
branch R42 status sample_verified_open_symbolic_candidate
law x=z=6*q+5
sample_moduli=[42,90,138,186,234]
boundary_verification_ok=True
color_sign_screen_ok=True
block24 q>=2 tail alpha=4*q+3 beta=12*q+10
```

R42 sample verification:

```bash
python3 scripts/verify_routeE_r42_affine_samples.py \
  --json-out certs/routeE_r42_affine_samples_verification.json
```

Result:

```text
all_passed=True
q=0,1,2,3,4 verified by scripts/routeE_allpair_cpp_v1_2.cpp
```

R42 boundary quotient summary:

```bash
python3 scripts/summarize_routeE_r42_boundary_quotient.py \
  --json-out certs/routeE_r42_boundary_quotient_summary.json
```

Result:

```text
q>=1: boundary_nodes = 3*m - 2, one boundary cycle, 29 blocks
block_count_by_label = {Z:1, 03:7, 04:13, 34:8}
transition fits include Z->03 = 1 and 34->34 = 12*q + 10
representative_q1_block_table has 29 compact blocks
run-normalized block formula fits: stable_structural_keys=True, blocks=29
raw_csv_preserved=False
```

R42 compact boundary summary verification:

```bash
python3 scripts/verify_routeE_r42_boundary_summary.py \
  --json-out certs/routeE_r42_boundary_summary_verification.json
```

Result:

```text
ok True
q_ge_1_transition_fits_verified True
q_ge_1_transition_symbolics_verified True
q1_representative_block_formulas_verified True
q1_representative_null_formula_field_count 2
q1_null_fields_have_q_ge_2_tail_formulas True
stability_verified True
```

The transition affine formulas now also verify symbolically:

```text
row totals    = {Z:1, 03:48*q+41, 04:48*q+41, 34:48*q+41}
column totals = {Z:1, 03:48*q+41, 04:48*q+41, 34:48*q+41}
total         = 144*q + 124 = 3*(48*q+42)-2
positive-edge support is strongly connected
```

The two remaining null formula fields are terminal affine fields in the
representative block table.  They are recorded as q=1 boundary compression
debt, not as a mismatch; both now have q>=2 tail affine formulas in the compact
summary.

R38 symmetric recheck:

```bash
python3 scripts/search_d5_routeE_symmetric_packets.py \
  --moduli 38,86,134 --x-values 5,23 --timeout 20 --jobs 3 \
  --json-out certs/routeE_r38_symmetric_probe_recheck.json

python3 scripts/search_d5_routeE_symmetric_packets.py \
  --moduli 182,230 --x-values 5,23 --timeout 30 --jobs 2 \
  --json-out certs/routeE_r38_symmetric_probe_recheck_182_230.json

python3 scripts/search_d5_routeE_symmetric_packets.py \
  --moduli 182 --x-values 1:89:2 --timeout 8 --jobs 8 \
  --json-out certs/routeE_r38_symmetric_probe_m182_oddx.json
```

Summary:

```text
hits: m=38,x=5; m=86,x=23; m=134,x=5
negative control: m=134,x=23 splits as 38,38,57 despite time sum m^4
m=182 quick probe: no full certificate; x=21,63 have one section cycle but fail time exhaustion
```

Timeout-safe C++ screen:

```bash
python3 scripts/search_d5_routeE_cpp_residue_branches.py \
  --moduli 182 \
  --patterns '0,1,3;0,3,4;1,3,4;0,1,4;2,3,4' \
  --hit-limit 3 --candidate-limit 8000 --cap-m3-factor 1.0 \
  --jobs 5 --timeout 8 \
  --json-out certs/routeE_r38_m182_cpp_screen_timeout.json
```

Result:

```text
all five tested support patterns timed out with no partial hits.
```

This is not a mathematical obstruction.  It is a search-control artifact that
prevents future broad mining runs from requiring manual process kills.

Open-residue C++ smoke screen:

```bash
python3 scripts/search_d5_routeE_cpp_residue_branches.py \
  --moduli 48,50,52,54,56,58,60,66,70,72,74,76,78,80,82,84,86,90,94 \
  --patterns '0,1,3;0,3,4;1,3,4' \
  --hit-limit 1 --candidate-limit 1500 --cap-m3-factor 0.25 \
  --jobs 8 --timeout 4 \
  --json-out certs/routeE_open_residue_cpp_smoke_20260506.json
```

Result:

```text
tasks=57 hits=0 timeouts=57
```

This is again search-control evidence only.  It says this shallow broad screen
does not immediately fill open Type-A residues.

R38 gate-transducer branch record:

```bash
python3 scripts/init_routeE_r38_gate_transducer_record.py \
  --json-out certs/routeE_r38_gate_transducer_branch_record.json
```

Result:

```text
branch R38 status open_gate_transducer_target
target residues [38]
positive seeds {'134': [5], '38': [5], '86': [23]}
```

The record fixes the proof-facing data that a future R38 candidate must supply:
closed packet/count law, finite gate transitions, section return one-cycle,
no-early/minimality, insertion distribution, time-mass polynomials, and
finite boundary cases.

Finite small-seam family scan:

```bash
python3 scripts/analyze_d5_routeE_small_seam_families.py \
  --periods 6,8,12,16,24,48 \
  --json-out certs/routeE_small_seam_family_scan_6_60.json \
  --write-manifest certs/routeE_small_seam_family_scan_manifest.json
```

Result:

```text
periods 6,8,12,16,24 have bad affine residue classes;
period 48 has no bad non-singleton classes but is nonrobust
because 20 of 24 residue classes are singleton in m=6..60.
```

Thus the existing finite window is not enough to infer a uniform affine count
law.  It is branch-finding evidence only.

Verification:

```bash
python3 scripts/verify_routeE_small_seam_family_scan.py \
  --json-out certs/routeE_small_seam_family_scan_verification.json
```

Result:

```text
ok True periods [6, 8, 12, 16, 24, 48]
bad [6, 8, 12, 16, 24]
nonrobust [48]
```

Machine completion audit:

```bash
python3 scripts/audit_routeE_corrected_goal.py \
  --json-out certs/routeE_corrected_goal_audit.json
```

Result:

```text
goal_complete False
missing_count 2
missing: Type-A residue coverage is complete
missing: E-gen-symbolic branch is closed
```

The audit is intentionally conservative: proof-facing evidence does not count
as a closed branch theorem unless the branch is actually covered and the
generic symbolic endpoint is no longer open.

Hygiene:

```bash
python3 -m py_compile scripts/summarize_d5_routeE_corrected_branches.py
python3 -m py_compile scripts/summarize_routeE_typeA_closure_packages.py
python3 -m py_compile scripts/summarize_routeE_typeA_residue_coverage.py
python3 -m py_compile scripts/summarize_routeE_allpair_portfolio.py
python3 -m py_compile scripts/analyze_routeE_allpair_portfolio_fits.py
python3 -m py_compile scripts/init_routeE_r42_affine_branch_record.py
python3 -m py_compile scripts/verify_routeE_typeA_symbolic_skeleton.py
python3 -m py_compile scripts/search_d5_routeE_cpp_residue_branches.py
python3 -m py_compile scripts/init_routeE_r38_gate_transducer_record.py
python3 -m py_compile scripts/audit_routeE_corrected_goal.py
python3 -m py_compile scripts/analyze_d5_routeE_small_seam_families.py
python3 -m py_compile scripts/verify_routeE_small_seam_family_scan.py
python3 -m py_compile scripts/derive_d5_lambdaE_mask_polynomials.py
python3 -m py_compile scripts/verify_d5_lambdaE_mask_polynomials.py
git diff --check
```

## Current Branch Summary

Regenerated by:

```bash
python3 scripts/summarize_d5_routeE_corrected_branches.py \
  --verify-rank-certs --verify-small-seam
```

```text
| branch | range | status | check |
| --- | --- | --- | --- |
| O | odd m | external_existing_odd_branch | existing odd branch |
| X1 | even prefix-count | removed_by_column_parity_obstruction | discarded branch |
| X2 | adjacent-Kempe only | removed_by_sign_obstruction | discarded branch |
| E0 | m=2 | filled_boundary_certificate | RF1=True RF2=True sign=True colors=True |
| E-small | m=4 | filled_finite_C_E_O_schedule | RF1=True RF2=True sign=True colors=True |
| E-gen-window | 6..60 even | finite_small_seam_evidence_window | cases=28 rank_cert=True moduli_match=True rank_verified=True seam_verified=True |
| E-gen-symbolic | all large even m | open | B20 samples=[20, 44, 68, 92] ok=True; TypeA B16=[16, 40, 64, 88, 112, 136, 160] R14e=[14, 62, 110, 158, 206] ok=True; uniform template still needed |
```

## Commits In This Pass

```text
b860772 Verify R42 transition mass symbolics
0c3d0a0 Index R42 verification artifacts in branch record
090d7ae Update Type-A next target to R42
a700cc9 Record R42 qge2 tail block fit
965bf91 Verify R42 compact boundary summary
b7760a9 Add Route E color sign screen audit
0993311 Fit R42 run-normalized boundary blocks
19c9990 Refresh Route E ledger after progress visualization
0cd8204 Refresh Route E ledger after R42 stability note
da0916c Add Route E progress visualization
8ea8eea Record R42 block table stability limits
2d2b6cb Preserve R42 representative boundary block table
6dd7d40 Add Route E no-go branch audit
8ca7cb6 Add Route E R42 boundary transition fits
f438d04 Summarize Route E R42 boundary quotient
5ac3ac1 Extend Route E R42 sample verification
327fe6c Verify Route E R42 affine samples
1538fa5 Initialize Route E R42 affine branch record
b32434a Analyze Route E portfolio affine fits
7cb945b Summarize Route E all-pair portfolio coverage
045cdec Refresh Route E audit ledger after B20 audit
ee7a2e6 Audit B20 Route E branch verifier
1bfa4a2 Verify Route E small-seam family scan
5b7d8c3 Record Route E open-residue smoke screen
d1d6987 Verify LambdaE mask polynomial artifact
4b3bce3 Preserve LambdaE mask polynomial artifact
a716056 Record Route E small-seam family scan
4204b58 Refresh Route E audit commit list
60476dd Verify Route E Type-A symbolic skeleton
d3311f5 Add Route E corrected goal audit
990005f Refresh Route E corrected branch audit
b516772 Initialize Route E R38 gate-transducer record
4b504ec Make Route E residue search timeout-safe
7be1745 Record Route E R38 symmetric probe
fd4ff1c Record Route E Type-A residue coverage
a3bc306 Extract Route E Type-A symbolic skeleton
5a91a94 Preserve Route E Type-A package evidence
9d22bcd Audit corrected Route E branch progress
c1dfa2c Extend B20 Route E evidence to m92
c2036ef Add B20 corrected branch evidence
c75debc Strengthen Route E branch window verification
f6dcfa6 Record corrected Route E branch dispatcher
c1434bf Refine Route E corrected branch target
```

Earlier supporting commits in the same branch include:

```text
05e1182 Isolate Route E adjacent Kempe no-go
f0805ee Refine Route E ansatz verdict
16073ee Record Route E parity-changing defect layer
caae490 Extract Route E layer switch structure
```

## Remaining Open Proof Obligations

The all-even symbolic theorem is still open.

For the generic full layered branch one still needs:

```text
1. a finite count/slot branch menu covering every even m >= 6;
2. closed layer coloring formulas for each branch;
3. RF1/RF2 proofs for those formulas;
4. color sign vector proofs `Omega_kappa=-1` for all colors;
5. pointwise first-return equations;
6. no-earlier-return/minimality proofs;
7. quotient or splice one-cycle proofs;
8. sum tau = m^4 time-exhaustion identities;
9. finite exception integration.
```

For B20 specifically, Lean already records the seam map, block cover, cycle
proof, and return-time weighted sum.  The remaining fields are:

```text
RouteEB20.ThetaPointwiseTraceTarget.firstReturn_equation
RouteEB20.ThetaPointwiseTraceTarget.firstReturn_minimal
```

Thus B20 is a proof-facing branch target, not a closed theorem.

The B16/R14e package summary now adds two more Type-A proof-facing branches:

```text
B16:  m=24q+16, q=0..6, package flags all true;
R14e: m=48k+14, k=0..4, package flags all true.
```

The package hashes are stored in
`certs/routeE_typeA_closure_package_summary.json`, and the symbolic polynomial
skeleton is stored in `certs/routeE_typeA_symbolic_skeleton.json`, so the
evidence can be checked against the original zip artifacts without preserving
large CSV files in the repository.

The Type-A residue coverage cert records that the promoted branch set covers
five even residue classes modulo `48`: `14,16,20,40,44`.  The next package
target is `R38`, but this is explicitly a gate-transducer mining target because
the naive symmetric `x=z` branch law has a recorded failure.

The R38 symmetric recheck strengthens that caution.  It reproduces early hits,
but it does not produce a branch theorem and it shows that the tempting
`x=5/23` continuation already fails to give a simple law.

## Conclusion

The corrected dispatcher is now executable and evidence-preserving.  The
impossible branches are excluded, finite boundary/window artifacts are stored,
the B20/B16/R14e Type-A branches are preserved as proof-facing evidence, and
the R38 next-target record is initialized.  The goal should remain active until
the `E-gen-symbolic` branch obtains a uniform full layered parity-changing
template or is replaced by a different finite branch cover.
