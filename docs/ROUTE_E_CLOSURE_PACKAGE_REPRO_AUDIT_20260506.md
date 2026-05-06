# Route E Closure Package Reproduction Audit

Date: 2026-05-06.

This note records the current reproducibility status of the B16 and R14e
closure packages relative to the Lean Route-E targets.

## Packages

- `/data/angel/repos/etc/RouteE/B16_closure_package_20260506.zip`
- `/data/angel/repos/etc/RouteE/R14e_closure_package_20260506.zip`

The packages were extracted to `/tmp/routee_next`.

## Package Contents

B16 contains:

- `B16_complete_routeE_certificate_note_20260506.md`
- `b16_complete_verifier.py`
- `b16_complete_verifier_output.json`
- `b16_label_dst_q6_verify.out`
- `b16_mine_subsums.out`
- `b16_complete_verifier_rerun_clean.stdout`

R14e contains:

- `R14e_complete_routeE_certificate_note_20260506.md`
- `r14e_complete_verifier.py`
- `r14e_complete_verifier_output.json`
- `r14e_insertion_macro_verifier_output.json`
- `r14e_complete_verifier_stdout.txt`
- `map_R14e_m206_x1_z101_full.csv`
- `map_R14e_m206_x1_z101_full_reconstructed.csv`
- `r14e_macro_Dr_check_out.json`

## Local Rerun Attempts

Commands:

```bash
python3 /tmp/routee_next/B16/b16_complete_verifier.py
python3 /tmp/routee_next/R14e/r14e_complete_verifier.py
```

Both currently fail before reading data:

```text
ModuleNotFoundError: No module named 'sympy'
```

This checkout's current Python environment therefore cannot rerun the verifier
scripts as-is.

After installing `sympy` in a temporary virtual environment, the same rerun was
attempted from a fresh extraction under `/tmp/routee_closure_reaudit_20260506`.
The scripts execute, but the missing-data issue remains.

B16 output:

```text
poly_bad_count = 0
label_total_equals_m4 = true
label_dst_total_equals_m4 = true
bad_macro_cases = []
case_summary = []
```

The empty `case_summary` is the key point: the script found no finite
`map_B16_*.csv` inputs, so it checked polynomial identities but did not rerun
any concrete branch map.

R14e output:

```text
cases = [{ k = 4, m = 206, complete = true, single_cycle = true,
           total_equals_m4 = true, boundary_step_sum_ok = true }]
label_total_equals_m4 = false
dst_total_equals_m4 = false
label_dst_count_equals_allpair_size = false
insertion_weighted_equals_allpair_size = true
```

Thus the included `m=206` R14e CSV still gives positive finite cycle evidence,
but the package does not contain enough cases for the recorded interpolation
aggregate to rerun successfully.

## Self-Containment Check

Even with `sympy` installed, the packages are not fully self-contained rerun
bundles.

B16:

- `b16_complete_verifier.py` globs `/mnt/data/map_B16_m*_x1_z*.csv`.
- The B16 zip contains no `map_B16_*.csv` files.
- The included JSON/stdout are evidence artifacts, but the script cannot
  regenerate them from this zip alone.

R14e:

- `r14e_complete_verifier.py` globs `/mnt/data/map_R14e_m*_x1_z*.csv`.
- The R14e zip contains only the `m=206` full/reconstructed CSV pair.
- The recorded verifier output covers `m=14,62,110,158,206`, so the package is
  missing the other finite CSV inputs needed for a faithful rerun.
- The script writes `/mnt/data/r14e_complete_verifier_output.json`.

The included R14e `m=206` CSV pair does pass an independent stdlib-only finite
check:

```text
rows = expected_rows = 2051
total_time = m^4 = 1800814096
section_cycle_lengths = [2051]
boundary_step_sum = 2051
insertion_dist = {1: 409, 2: 1, 4: 50, 5: 103, 6: 51, 206: 1, 413: 1}
```

This is positive finite evidence for `m=206`, but it is not enough to rerun the
recorded interpolation/verifier output for `m=14,62,110,158,206`.

## Lean Consequence

The current Lean state should treat these packages as proof-facing evidence,
not as closed certificate instances.

The relevant Lean endpoints are now available:

- `RouteEAllPairBoundaryInsertionTarget`
- `RouteEAllPairLabelDstBoundaryTraceTarget`
- `RouteEB16.AllPairBoundaryLabelDstTraceTarget`
- `RouteER14e.AllPairBoundaryLabelDstTraceTarget`

But no `RouteEAllPairSectionCertificate` instance for B16 or R14e has been
constructed from these packages yet.  A concrete instance still requires either
the missing deterministic CSV/table artifacts or a direct Lean derivation of
the first-return equations, no-early/minimality facts, boundary insertion
coverage, and time-mass sums.
