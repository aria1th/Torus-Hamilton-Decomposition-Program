# D5 Even Route E Corrected Branch Dispatcher

Date: 2026-05-06.

This note records the corrected proof target after the sign audit of the
adjacent-switch Route-E ansatz.

## Corrected Verdict

The following restricted branches are removed:

```text
even pure prefix-count branch;
cyclic bulk + RF2-preserving adjacent-rank Kempe repairs only.
```

They cannot prove even-modulus `D_5`.  The viable even branch is instead:

```text
full layered parity-changing one-layer coloring
+ nested first-return/splice certificate.
```

Here "one-layer coloring" means a proper edge-coloring of the root-flat layer
graph satisfying both outgoing and incoming Latin conditions.  It is not just a
pointwise stop transposition rule.

## One-Layer RF2 Condition

In `D_5`, write the root-flat prefix space as

```text
Q4 = (Z/mZ)^4
```

with stop vectors

```text
p0 = (0,0,0,0)
p1 = (1,0,0,0)
p2 = (1,1,0,0)
p3 = (1,1,1,0)
p4 = (1,1,1,1).
```

For a fixed layer, let

```text
c(z,r) = kappa    iff    color kappa uses stop r at root point z.
```

RF1 is:

```text
r |-> c(z,r) is a permutation of {0,1,2,3,4} for every z.
```

RF2 is equivalently:

```text
r |-> c(y + p_r, r) is a permutation of {0,1,2,3,4} for every y.
```

Thus each valid layer is a two-sided Latin object:

```text
outgoing Latin at tails + incoming Latin at heads.
```

This is the local condition any full layered branch must verify.

## Layer Sign Identity

For one layer define

```text
Lambda_t = product_kappa sign(P_{t,kappa}),
```

where `P_{t,kappa}` is the color-`kappa` root-flat layer map.  Let

```text
alpha_z : r |-> c(z,r)
beta_y  : r |-> c(y + p_r, r)
T_r(z)  = z - p_r.
```

Then:

```text
Lambda_t
 = (product_r sign(T_r))
   (product_z sign(alpha_z))
   (product_y sign(beta_y)).
```

This follows by comparing the permutation of the layer edge set in
tail-rank coordinates with the same edge set in tail-color/head-color
coordinates.

For even `m`, every prefix translation `T_r` has sign `+1` on `Q4`: nonzero
translations are products of `m^3` many `m`-cycles, and `m^3` is even.
Therefore layer parity is entirely controlled by the outgoing/incoming local
Latin signs.

## Global Sign Requirement

For even `m`, `|Q4| = m^4` is even.  If RF3 holds, every color return map is a
single `m^4`-cycle and hence has sign `-1`.  With five colors:

```text
product_kappa sign(R_kappa) = (-1)^5 = -1.
```

Since

```text
R_kappa = P_{m-1,kappa} ... P_{0,kappa},
```

any even `D_5` certificate must satisfy:

```text
product_t Lambda_t = -1.
```

Equivalently, an odd number of layers must carry negative layer parity.

## Adjacent-Kempe Branch Removal

An RF2-preserving adjacent `r/(r+1)` switch from cyclic bulk must be supported
on a set `A` satisfying

```text
A = A + e_{r+1}.
```

So the support is a union of full cycles in the affected coordinate direction.
Such a switch changes the two swapped color maps by the same sign factor, hence
does not change `Lambda_t`.  Cyclic bulk has `Lambda_t = +1`, and stacking only
these switches leaves every layer with `Lambda_t = +1`, contradicting the
global sign requirement.

Thus the old adjacent-switch-only branch is not a proof branch.  Adjacent words
remain useful only as local `S_5` descriptions of a defect layer.

## Even Prefix-Count Branch Removal

The pure prefix-count branch is also impossible for even `D_5`.  In the
prefix-count primitivity criterion every color row would need `N_0` to be a
unit modulo `m`.  When `m` is even, every unit is odd, so five color rows force

```text
sum_kappa N_{kappa,0} = odd + odd + odd + odd + odd = odd.
```

But local Latin column balance requires the stop-0 column sum to be exactly
`m`, which is even.  This contradiction removes the even prefix-count branch
before any return-map analysis.

## Remaining Even Branches

The corrected dispatcher is:

```text
Branch O:
  m odd.  Use the existing odd-modulus branch/input.

Branch X1:
  even pure prefix-count.
  Removed by the stop-0 column parity obstruction.

Branch X2:
  cyclic bulk + RF2-preserving adjacent-rank switches only.
  Removed by the layer-sign obstruction.

Branch E0:
  m = 2.  Use a full layered boundary certificate.
  Stationary seam certificates are excluded by sign/square obstructions.

Branch E-small:
  4 <= m < M.  Use finite full-layered certificates.
  Currently m=4 is filled by the embedded C/E/O schedule.

Branch E-gen:
  m even and m >= M.  Use a full layered parity-changing one-layer coloring
  template.  The template must verify RF1, RF2, product_t Lambda_t = -1, and
  the four-level nested first-return/splice certificate for RF3.
```

Within E-gen there are two proof styles:

```text
Type A:
  all-pair / boundary / macro quotient certificate.
  This is the B20/B16/R14e style and matches the Lean adapter shape.

Type B:
  four-level nested root-flat first-return certificate.
  This is valid only as a full-layered parity-changing coloring proof, not as
  an adjacent-switch-only proof.
```

Every concrete E-gen branch record should include:

```text
BranchHeader:  m >= M and m mod L = ell, or a finite m=m0.
LayerData:     closed formulas for layer colorings and RF1/RF2 proofs.
SignData:      product_t Lambda_t = -1.
ReturnData:    all-pair or nested first-return equations.
NoEarlyData:   minimality/no-early return proof.
PrimitiveData: quotient or splice graph one-cycle proof.
TimeData:      sum tau = m^4.
Exceptions:    finite boundary cases.
```

## Finite Template Reduction

If a full layered template is described by finitely many affine seam predicates,
endpoint exceptions, and quasi-affine splice block boundaries, then verification
reduces to finitely many branches:

```text
small m < M,
and generic residue classes m mod L.
```

The reason is finite: RF1/RF2 depend on finitely many local predicate patterns;
seam overlaps and inverse detection reduce to finitely many linear congruence
systems; Smith normal form makes their solvability depend on fixed gcd/residue
data; and splice boundary order types are quasi-affine in `m`.  On each residue
branch, the return-time sums become polynomial or quasi-polynomial identities.

The next extraction target from SAT/finite witnesses is therefore not an
adjacent-switch slab list.  It is a parity-changing layer type list, its layer
parity table, the generic residue modulus `L`, and the RF3 splice tables.

## Current Filled Artifacts

The current branch table can be regenerated with:

```bash
python3 scripts/summarize_d5_routeE_corrected_branches.py
```

For the slower recomputation of the recorded `m=6..60` small-seam window:

```bash
python3 scripts/summarize_d5_routeE_corrected_branches.py --verify-small-seam
```

For the proof-facing rank/block certificate check on the same window:

```bash
python3 scripts/summarize_d5_routeE_corrected_branches.py --verify-rank-certs
```

For the external Type-A closure packages (`B16`, `R14e`) without committing raw
CSV tables:

```bash
python3 scripts/summarize_routeE_typeA_closure_packages.py \
  --json-out certs/routeE_typeA_closure_package_summary.json \
  --symbolic-out certs/routeE_typeA_symbolic_skeleton.json
```

As of this note, the verified summary is:

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

The `m=2` full-layered boundary certificate is stored at:

```text
certs/d5_routeE_m2_full_layered_boundary.json
```

The `m=6..60` small-seam rank certificates are stored at:

```text
certs/d5_routeE_small_seam_rank_certs.json
```

This fills the boundary/window evidence branches but does not close the generic
all-even theorem.  The remaining symbolic proof obligation is a uniform
count/slot/splice law for the parity-changing full layered branch beyond the
recorded finite window.

The rank certificate verifier checks more than table presence: it recomputes
the Theta first-return map, verifies the seam rank step, maximal translation
blocks, and the return-time sum `m^4` for all recorded `m=6,8,...,60` cases.

The first Type-A symbolic branch candidate currently tracked is B20:

```text
m = 24*q + 20,
counts = (4*q+3, 0, 0, 16*q+13, 4*q+3).
```

Its current sample verifier artifact is:

```text
certs/d5_routeE_b20_branch_verify_m20_44_68.json
```

This artifact checks the two-block seam map, the six-value return-time
distribution, the pointwise return-time formula, and the weighted `m^4` sum for
`m=20,44,68,92`.  It does not close the B20 theorem.  In Lean terms, the
remaining B20 fields are still the pointwise first-return equation and
no-earlier-return minimality for `RouteEB20.ThetaPointwiseTraceTarget`.

The `B16` and `R14e` closure packages are summarized at:

```text
certs/routeE_typeA_closure_package_summary.json
certs/routeE_typeA_symbolic_skeleton.json
```

The summary records the source package hashes and proof-facing verifier flags
for:

```text
B16:  m = 16,40,64,88,112,136,160;
R14e: m = 14,62,110,158,206.
```

All recorded package flags are currently `true`, including B16 macro checks and
R14e insertion/macro comparisons.  This is still evidence for Type-A symbolic
branches, not a closed Lean theorem: it preserves the finite verifier outputs
and identifies the same missing Lean-facing first-return/minimality obligations.

The symbolic skeleton additionally preserves the B16/R14e label-time
polynomial tables, the destination-label polynomial tables, the `m^4` total
identities, and the R14e insertion macro identities.  This is the preferred
artifact for moving those branches into a paper appendix or Lean statement,
because it avoids storing raw all-pair CSV maps while retaining the algebraic
mass formulas.

Those identities can be checked locally without `sympy`:

```bash
python3 scripts/verify_routeE_typeA_symbolic_skeleton.py \
  --json-out certs/routeE_typeA_symbolic_skeleton_verification.json
```

The current verification output has `all_ok = true`.

The residue coverage of the promoted Type-A branches is summarized by:

```bash
python3 scripts/summarize_routeE_typeA_residue_coverage.py \
  --json-out certs/routeE_typeA_residue_coverage.json
```

Current Type-A proof-facing coverage modulo `48` is:

```text
B20:  residues 20,44;
B16:  residues 16,40;
R14e: residue 14.
```

The remaining even residues modulo `48` are:

```text
0,2,4,6,8,10,12,18,22,24,26,28,30,32,34,36,38,42,46.
```

The next recorded target is the `R38` / symmetric-or-near-symmetric family,
but the status package explicitly warns that the naive `x=z` symmetric theorem
is false.  That branch should therefore be mined as a gate-transducer family,
not as a fixed symmetric-unit law.

A small R38 symmetric recheck is stored at:

```text
certs/routeE_r38_symmetric_probe_summary.json
```

It reproduces the initial symmetric hits:

```text
m=38,  x=5;
m=86,  x=23;
m=134, x=5.
```

It also records the negative controls:

```text
m=134, x=23: time sum is m^4 but the section map splits as 38,38,57;
m=182: quick odd-x probe found no full certificate, and x=21,63 have one
       section cycle but fail time exhaustion.
```

So the R38 branch remains open and should be searched as a gate/transducer or
near-symmetric family, not as a simple two-value or fixed symmetric law.

The C++ residue search driver now supports a per-task timeout:

```bash
python3 scripts/search_d5_routeE_cpp_residue_branches.py ... --timeout 8
```

The first recorded timeout-safe screen for `m=182` is:

```text
certs/routeE_r38_m182_cpp_screen_timeout.json
```

It timed out on the tested support patterns without partial hits.  This should
be read only as search-control evidence, not as a no-go theorem.

The current R38 branch record is initialized at:

```text
certs/routeE_r38_gate_transducer_branch_record.json
```

That record fixes the next branch as an open gate-transducer target and lists
the required data before it can be promoted:

```text
closed packet/count formula;
finite gate state set and transition formula;
section return map and one-cycle proof;
no-early/minimality;
boundary/all-pair insertion distribution;
label or label-destination time mass polynomials;
sum tau = m^4;
finite boundary cases.
```

The repository-level completion status can be regenerated with:

```bash
python3 scripts/audit_routeE_corrected_goal.py \
  --json-out certs/routeE_corrected_goal_audit.json
```

At the time of this note the audit reports `goal_complete = false`, because
Type-A residue coverage is incomplete and `E-gen-symbolic` is still open.

The finite small-seam window can be scanned for simple affine count laws by:

```bash
python3 scripts/analyze_d5_routeE_small_seam_families.py \
  --periods 6,8,12,16,24,48 \
  --json-out certs/routeE_small_seam_family_scan_6_60.json \
  --write-manifest certs/routeE_small_seam_family_scan_manifest.json
```

The current manifest says that periods `6,8,12,16,24` have bad affine residue
classes, while period `48` is nonrobust: it has no bad non-singleton classes,
but `20` of `24` even residue classes are singleton in the `m=6..60` window.
This prevents the finite window from being treated as a uniform count law.

The local `Lambda_E` defect-layer counts are preserved in machine-readable
form by:

```bash
python3 scripts/derive_d5_lambdaE_mask_polynomials.py \
  --json-out certs/d5_lambdaE_mask_polynomials.json
```

This records the inclusion-exclusion mask polynomials and the adjacent-rank
switch totals for the parity-changing layer.  It is symbolic local data, not a
global all-even branch theorem.

The recorded artifact is checked by recomputation:

```bash
python3 scripts/verify_d5_lambdaE_mask_polynomials.py \
  --json-out certs/d5_lambdaE_mask_polynomials_verification.json
```
