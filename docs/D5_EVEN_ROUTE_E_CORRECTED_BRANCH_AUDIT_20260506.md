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
| Preserve `m=2` full-layered boundary certificate | `certs/d5_routeE_m2_full_layered_boundary.json` | done |
| Verify `m=2` RF1/RF2/sign/nested returns | `scripts/summarize_d5_routeE_corrected_branches.py` | done |
| Preserve `m=4` finite certificate status | summary script via `export_d5_even_routeE_layers.py` | done |
| Preserve `m=6..60` small-seam evidence window | `certs/d5_routeE_small_seam_rank_certs.json` and branch summary cert | done |
| Distinguish rank/block verification from table presence | `scripts/summarize_d5_routeE_corrected_branches.py --verify-rank-certs` | done |
| Distinguish seam recomputation from rank cert verification | `--verify-small-seam` and `--verify-rank-certs` options | done |
| Turn Lambda_E local mask counts into symbolic formulas | `scripts/derive_d5_lambdaE_mask_polynomials.py` and `docs/D5_EVEN_ROUTE_E_PROOF_PROGRESS_20260506.md` | done |
| Preserve first Type-A B20 branch evidence | `certs/d5_routeE_b20_branch_verify_m20_44_68.json` | done, covers `m=20,44,68,92` despite filename |
| Preserve Type-A B16/R14e package evidence without raw CSV | `scripts/summarize_routeE_typeA_closure_packages.py`, `certs/routeE_typeA_closure_package_summary.json`, `certs/routeE_typeA_symbolic_skeleton.json` | done |
| Verify Type-A symbolic skeleton identities without `sympy` | `scripts/verify_routeE_typeA_symbolic_skeleton.py`, `certs/routeE_typeA_symbolic_skeleton_verification.json` | done |
| Record Type-A residue coverage and next target | `scripts/summarize_routeE_typeA_residue_coverage.py`, `certs/routeE_typeA_residue_coverage.json` | done |
| Recheck R38 symmetric next-target evidence | `certs/routeE_r38_symmetric_probe_summary.json` and raw small probe JSONs | done, negative-control only |
| Make C++ residue branch search timeout-safe | `scripts/search_d5_routeE_cpp_residue_branches.py --timeout`, `certs/routeE_r38_m182_cpp_screen_timeout.json` | done |
| Initialize R38 gate-transducer branch record | `scripts/init_routeE_r38_gate_transducer_record.py`, `certs/routeE_r38_gate_transducer_branch_record.json` | done, branch remains open |
| Scan finite small-seam window for simple affine branch laws | `scripts/analyze_d5_routeE_small_seam_families.py`, `certs/routeE_small_seam_family_scan_manifest.json` | done, no robust law found |
| Machine-check the goal completion status | `scripts/audit_routeE_corrected_goal.py`, `certs/routeE_corrected_goal_audit.json` | done, reports incomplete |
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

Lambda_E symbolic mask counts:

```bash
python3 scripts/derive_d5_lambdaE_mask_polynomials.py
```

The script derives exact shifted-zero mask polynomials by inclusion-exclusion
over the 5-cycle equality arrangement and recovers the modal/nonmodal/rank
totals used by the finite witnesses.

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
next target: R38 / symmetric-or-near-symmetric family
```

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
python3 -m py_compile scripts/verify_routeE_typeA_symbolic_skeleton.py
python3 -m py_compile scripts/search_d5_routeE_cpp_residue_branches.py
python3 -m py_compile scripts/init_routeE_r38_gate_transducer_record.py
python3 -m py_compile scripts/audit_routeE_corrected_goal.py
python3 -m py_compile scripts/analyze_d5_routeE_small_seam_families.py
python3 -m py_compile scripts/derive_d5_lambdaE_mask_polynomials.py
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
4. product_t Lambda_t = -1 sign proofs;
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
