# Route E Modular Criteria Evidence

Date: 2026-05-06.

This note records the evidence preserved from
`RouteE_modular_criteria_package_20260506.zip` and
`RouteE_branch_modular_criteria_note_20260506.md`.

The point of this audit is deliberately narrow: preserve the useful
proof-facing evidence without importing large raw tables into the repository.
The current conclusion is that B20, B16, and R14e are strong proof-facing
branches, but none of them is yet a concrete Lean
`RouteEAllPairSectionCertificate` instance.

## Input Artifacts

| artifact | sha256 |
| --- | --- |
| `/data/angel/repos/etc/RouteE_modular_criteria_package_20260506.zip` | `b4f6f6cd941b13184bbf5fc9b2f729e700698be7335d9d40df9d70ec73169916` |
| `/data/angel/repos/etc/RouteE_branch_modular_criteria_note_20260506.md` | `8bf1dbd7b133a4ed722ab752a7f196e334f3017fb1383a0c3f3e99dc7e651b94` |
| `/data/angel/repos/etc/B20_closure_package_20260506.zip` | `c9672b2088dfd3e2deaefdf541fbf7349b5052ba27a2d3a32c8457caf130c107` |
| `/data/angel/repos/etc/RouteE/B16_closure_package_20260506.zip` | `9efb26e87847c7915d04cc362bef4f033cd8a7e05198daa3e911f2daf3ffb04a` |
| `/data/angel/repos/etc/RouteE/R14e_closure_package_20260506.zip` | `5fec93c3d177485b6ede4115aec79b548d765761c996c12e8383c2c726b00d08` |
| `/data/angel/repos/etc/RouteE/RouteE_three_branch_status_package_20260506.zip` | `7c65450ed5987d75e0341881a36fa7555b303f088b51f147dfd849e810c41f51` |

`RouteE_modular_criteria_package_20260506.zip` contains only the modular
criteria note.  The branch evidence lives in the B20/B16/R14e closure
packages.

## Modular Proof Standard

The note separates a search hit from a proof-facing branch.  A branch is not
closed because a program found a one-cycle section map.  It must supply:

- parameter domain and packet admissibility;
- closed section, boundary, or macro return formulas;
- no-early/minimality statements for the relevant first returns;
- a structural one-cycle proof for the compressed quotient;
- insertion and root-flat time-exhaustion identities;
- finite exceptional cases as explicit finite certificates;
- negative controls preventing false generalizations.

The reusable lift chain is:

```text
macro one-cycle
=> boundary one-cycle
=> all-pair one-cycle
=> root-flat time exhaustion
=> Route-E Hamilton factor endpoint
```

This is the correct Lean-facing route for B20, B16, and R14e.

## Branch Status

### B20

Family:

```text
m = 24*q + 20
c = 4*q + 3
nu = (c, 4*c + 1, 0, c, 0)
```

Package evidence:

- `b20_complete_verifier_output.json` records samples
  `m = 20,44,68,92,116,140,164`.
- For every recorded sample:
  - all-pair row count is `1 + 10*(m-1)`;
  - all-pair map from index `0` is one cycle;
  - total first-return time is `m^4`;
  - boundary quotient formula has zero reported mismatches;
  - label exact sums match the listed polynomials.
- Boundary quotient cycle lengths are `3*m - 2`, recorded as
  `58,130,202,274,346,418,490`.

Local repo sanity rerun:

```bash
cd /data/angel/repos/etc/Torus-Hamilton-Decomposition-Program/scripts
python3 verify_d5_routeE_b20_branch.py \
  --moduli 20,44 \
  --json-out /tmp/routee_b20_repo_rerun_20260506.json
```

Result:

```text
m=20 small_ok=True blocks_ok=True times_ok=True time_formula_ok=True sum_ok=True
m=44 small_ok=True blocks_ok=True times_ok=True time_formula_ok=True sum_ok=True
all_ok=True
```

Rerun limitation:

- `b20_step1_formula_check.py` expects `/mnt/data/b20_map_m*_v2_8.csv`.
- Those CSV files are not in the closure package.
- The package includes a C++ all-pair dumper, so exact maps can be regenerated,
  but this audit did not store regenerated raw CSVs.

### B16

Family:

```text
m = 24*q + 16
nu = (1, 12*q + 9, 0, 12*q + 5, 0)
```

Package evidence:

- `b16_complete_verifier_output.json` records complete cases
  `q = 0,1,2,3,4,5,6`, i.e. `m = 16,40,64,88,112,136,160`.
- Every recorded case has:
  - complete all-pair table;
  - one section cycle;
  - total first-return time `m^4`;
  - zero boundary formula mismatches.
- The recorded symbolic checks have:
  - `poly_bad_count = 0`;
  - label total equals `m^4`;
  - label-destination total equals `m^4`.

Local partial rerun after installing `sympy` in a temporary venv:

```bash
python3 -m venv /tmp/routee_venv_20260506
/tmp/routee_venv_20260506/bin/pip install sympy
/tmp/routee_venv_20260506/bin/python \
  /tmp/routee_packages_20260506/b16/b16_complete_verifier.py
```

Result:

```text
poly_bad_count: 0
label_total_equals_m4: true
label_dst_total_equals_m4: true
bad_macro_cases: []
case_summary: []
```

The empty `case_summary` is expected in this checkout: the script globs
`/mnt/data/map_B16_m*_x1_z*.csv`, and the B16 zip contains no `map_B16_*.csv`
raw tables.  Thus the local rerun confirms symbolic polynomial and macro
checks, but not the recorded finite all-pair CSV checks.

### R14e

Family:

```text
m = 48*k + 14 = 6*r + 2
r = 8*k + 2
nu = (1, 24*k + 7, 0, 24*k + 5, 0)
```

Package evidence:

- `r14e_complete_verifier_output.json` records complete cases
  `k = 0,1,2,3,4`, i.e. `m = 14,62,110,158,206`.
- Every recorded case has:
  - complete all-pair table;
  - one section cycle;
  - total first-return time `m^4`;
  - boundary insertion step sum equal to the all-pair size.
- The recorded symbolic checks have:
  - insertion weighted sum equals `1 + 10*(m-1)`;
  - label total equals `m^4`;
  - label-destination total equals `m^4`;
  - label-destination count total equals all-pair size.

Local partial rerun:

```bash
cp /tmp/routee_packages_20260506/r14e/map_R14e_m206_x1_z101_full*.csv /mnt/data/
/tmp/routee_venv_20260506/bin/python \
  /tmp/routee_packages_20260506/r14e/r14e_complete_verifier.py
```

Result for the packaged `m=206` CSV:

```text
k=4, m=206
complete=true
single_cycle=true
total_equals_m4=true
boundary_step_sum_ok=true
```

The global interpolation flags are false in this partial rerun because only the
`m=206` CSV is present locally.  The recorded package output used the five
sample cases `m=14,62,110,158,206`.

## Existing Repo Sanity Check

The current Route-E scripts still verify the older non-open small-seam cases
needed for orientation:

```bash
cd /data/angel/repos/etc/Torus-Hamilton-Decomposition-Program/scripts
python3 verify_d5_even_routeE.py \
  --mode section \
  --small-seam-moduli 14,16,20,38,40,44 \
  --json-out /tmp/routee_even_section_rerun_20260506.json
```

Summary:

```text
small_seam_count = 6
small_seam_ok = true
small_moduli = [14, 16, 20, 38, 40, 44]
```

This is a sanity check for the existing seam machinery; it is not a proof of
the new modular B16/R14e all-pair branches.

## Negative Controls

The modular criteria note records three anti-criteria:

- time exhaustion alone is insufficient;
- symmetric unit parameters are insufficient;
- macro-cycles extracted only after seeing a full all-pair cycle are pattern
  evidence, not a proof.

The explicit negative control to keep visible is:

```text
m = 134, x = z = 23
```

It has time exhaustion but a split section map.  This prevents the false
generalization "symmetric unit works".

## Lean Consequence

Current proof state:

- B20 is closest.  Its boundary quotient one-cycle and several arithmetic
  surfaces are already Lean-facing.
- B16 and R14e are promoted to proof-facing closure but still need concrete
  Lean instances.
- No B20/B16/R14e branch from these packages currently instantiates a concrete
  `RouteEAllPairSectionCertificate`.

The next Lean target should not import raw search logs.  It should instantiate
the existing label-destination/boundary-insertion targets from symbolic
formulas plus finite exceptional certificates:

```text
B20: q > 0 symbolic branch + finite m=20
B16: q > 0 symbolic branch + finite m=16
R14e: k > 0 symbolic branch + finite m=14
```

## Preservation Decision

Do not commit the large JSON outputs or CSV tables from the packages.  The
stable preservation layer is:

- this audit note;
- artifact hashes above;
- the compact branch formulas and status notes already in `docs/`;
- small rerun commands;
- future Lean theorem instances.

Raw tables should remain external artifacts unless they are needed as finite
exception certificates.
