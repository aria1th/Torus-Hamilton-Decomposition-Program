# D5 Even Route-E Non-Open Small Seam

Date: 2026-05-01.

Source bundle:

- `/data/angel/repos/etc/d5_even_routeE_nonopen_small_seam_v0_4.zip`

This note records the small-seam update for the D5 even Route-E track.  It is
an audit and research-state note, not an all-even symbolic theorem.

## Main Update

For one-`Lambda_E` schedules

```text
C_0^nu0 C_1^nu1 C_2^nu2 C_3^nu3 C_4^nu4 E_s,
sum_i nu_i = m - 1,
```

the normalized return is

```text
F_{nu,s}(w) = w + nu + e_{p_s(w)},
p_s(w) = Lambda_E(Z(w)-1)(s).
```

The non-open schedules in the bundle do not require a large origin-excursion
chart.  For each E-slot `s`, use the cyclically shifted seam

```text
Theta_s = { rho_s(0,a,0,0,-a) : a != 0 }.
```

This seam has size `m-1`.  It is a port line for coordinate

```text
j = s + 2 mod 5.
```

For example, `s = 0` gives `(0,a,0,0,-a)` and `j = 2`; `s = 4` gives
`(a,0,0,-a,0)` and `j = 1`.

## Direct Criterion

Let `V` be the first-return map of `F_{nu,s}` to `Theta_s`.  If

```text
V is a single cycle on Theta_s
sum_{theta in Theta_s} tau(theta) = m^4,
```

then `F_{nu,s}` is a single cycle on `A5(m)`.

This is the standard first-return counting argument: one seam cycle stitches
all excursions into one closed orbit, and the return-time sum equal to `m^4`
forces that orbit to cover the whole root state space.

## Verified Range

The bundle supplies one-`Lambda_E` schedules for every even
`m = 6,8,...,60`.  Each satisfies:

- every seam start has the expected port `j = s+2`;
- the first return on `Theta_s` is one cycle of length `m-1`;
- the return-time sum is `m^4`.

The schedule table from the bundle is now embedded in
`scripts/verify_d5_even_routeE.py` as `SMALL_SEAM_CASES`.

The Lean-facing target for these traces is now:

```text
D5Odd/EvenRouteE.lean
```

It defines `RouteECounts`, the nonzero parameter seam
`RouteENonzeroSeam m = {a : ZMod m // a != 0}`, and proves that this seam has
cardinality `m-1`.  It also records the explicit shifted seam point
`routeEThetaPoint slot a`, matching the bundle's
`rho_s(0,a,0,0,-a)`, and proves that both the raw `ZMod m` parametrization and
the subtype `RouteENonzeroSeam m` parametrization are injective.  The generic
`RouteESmallSeamCertificate` now derives the needed root-return orbit target
from:

- an injective seam parametrization;
- first-return equations and no-earlier-return witnesses;
- a single cycle on the induced seam map;
- the return-time sum `m^4`.

There is a coordinate convention worth making explicit.  `D5Odd/Even.lean`
uses `Vec4` as the `rootZ` projection of `Vec5`, i.e. coordinates `1..4`, not
coordinates `0..3`.  Thus the bundle point `(0,a,0,0,-a)` is represented in
Lean as `![a,0,0,-a]`.  The file now defines the underlying `Vec5` point
`routeEThetaVec slot a` and proves:

- `Root5 m (routeEThetaVec slot a)`;
- `rootZ (routeEThetaVec slot a) = routeEThetaPoint slot a`;
- `(rootOfZ (routeEThetaPoint slot a)).1 = routeEThetaVec slot a`.
- the coordinate identities `routeEThetaVec_pos_param`,
  `routeEThetaVec_neg_param`, and `routeEThetaVec_port_zero`;
- the verifier's `start_ok` port statement
  `LambdaE (zeroMaskMinusOne (routeEThetaVec slot a)) slot = slot+2 mod 5`
  for `a != 0`, as `LambdaE_routeEThetaVec` and
  `LambdaE_routeEThetaSeam`.

The Route-E zero-set table `LambdaE` is therefore no longer only an `m=4`
implementation detail: it is part of the general Route-E interface in
`D5Odd/EvenRouteE.lean`, where `LambdaE_latin` and `LambdaE_cyclic` record
its finite table invariants.  `D5Odd/EvenRouteEM4.lean` reuses that
definition.

The canonical wrapper `RouteEThetaSmallSeamCertificate` now fixes both the
seam type `RouteENonzeroSeam m` and the seam map
`routeEThetaSeamPoint slot`, i.e. the exact `Theta_s` seam from the bundle.
It lowers to `RouteENonopenSmallSeamCertificate` and then routes any completed
Route-E certificate through the existing `D5Odd.Even` seam endpoint to D5
Hamilton, torus, and Cayley decompositions.

It also records the finite-exception packaging shape.  The target
`D5EvenRouteEM4FiniteTarget` is now closed in `D5Odd/EvenRouteEM4.lean` by a
finite `C/E/O/O` four-layer schedule.  Lean verifies exact cover and Latin
conditions by finite decision, proves the five color returns are single cycles
using generated `ZMod 256` rank tables, and packages the unconditional
Hamilton witness.

With that finite branch available, Lean proves that:

- `D5EvenRouteEAllLargeEvenTarget` gives
  all even `m >= 4` Hamilton, torus, and Cayley targets;
- the same conclusion follows from the non-open specialized target
  `D5EvenRouteENonopenAllLargeEvenTarget`;
- and also from the canonical bundle-seam target
  `D5EvenRouteEThetaAllLargeEvenTarget`.

Thus the remaining D5 even Route-E obligation is isolated to the all-large
`m >= 6` small-seam proof.

The repo-side verification command used for this absorption was:

```bash
python3 scripts/verify_d5_even_routeE.py --mode section \
  --small-seam-moduli all \
  --json-out /tmp/d5_even_routeE_small_seam_all.json
```

It reported:

```text
cases = 28
range = 6..60
all_ok = True
seam_sizes_ok = True
return_sums_ok = True
```

The v0.4 bundle was also re-read directly: its
`outputs/d5_even_routeE_small_seam_extended_cases.tsv` table has the same
`28` rows as the repo's `SMALL_SEAM_CASES`, with matching `(slot, counts)` for
every even `m = 6,8,...,60`.  The standalone C++ checker compiled from
`scripts/fast_d5_routeE_small_seam_verify.cpp` reports `ok 1` for all `28`
embedded cases.

The bundle was rechecked again on 2026-05-02 after the current proof-status
update:

- the source TSV and repo `SMALL_SEAM_CASES` agree exactly on all `28` rows;
- `scripts/verify_d5_even_routeE.py --mode section --small-seam-moduli all`
  reports `all_ok=True`, `seam_sizes_ok=True`, and `return_sums_ok=True`;
- the standalone C++ checker reports `bad 0` over the same `28` rows.

The exact bundle-to-repo consistency check is now automated by:

```bash
python3 scripts/verify_d5_routeE_nonopen_bundle.py \
  /data/angel/repos/etc/d5_even_routeE_nonopen_small_seam_v0_4.zip \
  --json-out /tmp/d5_routeE_nonopen_bundle_check.json
```

On the source zip this reports:

```text
cases 28 tsv_matches_repo True report_matches_tsv True python_recompute_all_ok True all_ok True
```

The verifier now also emits proof-facing data for the induced seam map:

- `translation_blocks`: maximal intervals in `a = 1,...,m-1` on which
  `V(a)-a mod m` is constant;
- `translation_block_count`: the number of such blocks;
- `orbit_prefix_from_1`: a short prefix of the single seam cycle.

This is intended as the finite trace format for the next symbolic
block-splice proof.  For example, the recorded `m = 44` schedule has only two
translation blocks:

```text
[1,20]  -> delta 23
[21,43] -> delta 24
```

The C++ checker from the bundle is also retained as
`scripts/fast_d5_routeE_small_seam_verify.cpp`.  It verifies one recorded
`(m, slot, counts)` case at a time and gives an implementation-independent
cross-check of the same `start_ok`, one-cycle, and return-time-sum criterion.

The follow-up family scanner:

```bash
python3 scripts/analyze_d5_routeE_small_seam_families.py \
  --manifest certs/d5_routeE_small_seam_family_scan_manifest.json \
  --json-out /tmp/d5_routeE_small_seam_family_scan.json
```

tests whether the finite `m = 6,8,...,60` table is already compatible with
simple affine normalized count vectors on residue classes.  It reports that
periods `4,6,...,26` all fail exact affine fits on at least one residue class,
while periods `28` and `30` have no robust affine class because each class has
at most two samples.  Thus the current table is strong evidence for the
small-seam criterion, but it should not be treated as an extracted all-even
count formula.  The compact manifest
`certs/d5_routeE_small_seam_family_scan_manifest.json` pins this negative scan
as a regression artifact.

On 2026-05-02 the analyzer was extended to read prefix hits from the full
one-`Lambda_E` count/slot scan:

```bash
python3 scripts/verify_d5_even_routeE.py --mode section \
  --count-scan-moduli 6,8,10,12 \
  --count-scan-limit 20 \
  --json-out /tmp/d5_count_scan_6_12_limit20.json

python3 scripts/analyze_d5_routeE_small_seam_families.py \
  --manifest certs/d5_routeE_small_seam_family_scan_manifest.json \
  --count-scan-json /tmp/d5_count_scan_6_12_limit20.json \
  --score-count-scan-small-seam \
  --json-out /tmp/d5_routeE_small_seam_family_scan_with_count_hits.json
```

The prefix-hit summary is:

```text
count_scan m first_hits distinct open_hits open_distinct known_present alternatives zero_classes
6 10 2 0 0 True 1 2
8 10 2 0 0 True 1 2
10 20 9 6 2 True 8 6
12 20 12 2 1 True 11 7
```

Thus the recorded `SMALL_SEAM_CASES` are not unique even at small moduli.  The
known witness is present in these scan prefixes, but alternative normalized
count vectors are also present, and `m = 10,12` already show open-port normal
forms.  This sharpens the interpretation of the negative family scan: fitting
the recorded table may fail because the table is one validated witness choice,
not because Route-E lacks a simpler all-even count family.  The next search
should choose a canonical objective, such as low support, open-port form,
small block count, or long translation blocks, before attempting a uniform
residue theorem.

The `--score-count-scan-small-seam` option deduplicates the prefix hits by
normalized count vector and reruns the small-seam block verifier on each
distinct hit.  In the `m = 6,8,10,12` scan, the best minimum-block candidates
are the recorded witnesses for `m = 6,8`, the open-port vector
`(0,0,8,1,0)` for `m = 10`, and the non-open vector `(1,2,1,7,0)` for
`m = 12`.  A follow-up prefix scan for `m = 14,16` gives:

```text
count_scan m first_hits distinct open_hits open_distinct known_present alternatives zero_classes
14 20 20 1 1 True 19 9
16 20 20 0 0 True 19 9
```

For `m = 14`, the open-port prefix hit `(0,6,2,5,0)` has `13` singleton
translation blocks, while the best minimum-block prefix hit `(2,2,6,3,0)` has
`7` blocks.  For `m = 16`, the recorded vector `(1,13,0,1,0)` is still the
best minimum-block prefix hit in this scan, with `11` blocks.  This reinforces
that "open-port" and "proof-simple block trace" are related but not identical
search objectives.

The block-splice trace can now be summarized directly with:

```bash
python3 scripts/summarize_d5_routeE_small_seam_blocks.py \
  --json-out /tmp/d5_routeE_small_seam_block_summary.json
```

On the current `m = 6,8,...,60` table this reports `28` cases,
`all_ok=True`, and `return_sums_ok=True`.  The low block-count cases are
`m = 6,8,10,44,48,50`, while the cases with a block of length at least
`m/4` are `m = 6,8,36,44,48,50`.  In particular, the known `m = 44` witness
has exactly two blocks:

```text
[1,20]  -> delta 23
[21,43] -> delta 24
```

Equivalently, the proof-facing piecewise translation proposition for this
finite trace is:

```text
1 <= a <= 20:  V(a) = a + 23 mod 44
21 <= a <= 43: V(a) = a + 24 mod 44
```

Lean now has a named interface for this trace shape:

- `RouteESeamTranslationBlock m` records one interval
  `start <= a <= stop` and a constant translation `delta`;
- `RouteEThetaPiecewiseTranslationCertificate m` adds block cover,
  disjointness, and translation formulas to the canonical
  `RouteEThetaSmallSeamCertificate`;
- `D5EvenRouteEThetaPiecewiseAllLargeEvenTarget` is the corresponding
  all-large even target, with lowering lemmas to the existing D5 even
  Hamilton, torus, and Cayley endpoints.

The next proof-facing layer is now also named.  `RouteEThetaRankedSmallSeamCertificate`
replaces the direct `seamReturn_single` hypothesis by a bijective seam rank

```text
RouteENonzeroSeam m -> ZMod (m-1)
```

whose step under the seam return is `+1`; Lean then derives the one-cycle
property using `Shared.single_cycle_of_zmod_rank`.  The combined
`RouteEThetaRankedPiecewiseTranslationCertificate` records both the interval
translation blocks and the rank-step data.

This interface is deliberately conservative: it records the block-splice data
as proof-facing evidence, and it can derive the seam one-cycle from a rank
formula, but it still requires the return-time sum identity.  The missing
symbolic theorem is therefore sharper: produce uniform count/slot families,
prove the block translations and ranked seam cycle for each family, and prove
the return-time sum.

This does not supply a residue-class formula for all even `m`, but it gives a
small proof-facing target for the next lane/block-splice argument: explain
which normalized count families produce few-block or long-block seam maps, and
then prove the one-cycle and return-time-sum identities symbolically.
The same summary clusters by normalized zero/support positions.  On this table
there is no robust affine count fit with at least three samples in any such
cluster; only two-sample affine fits appear.  Thus the current finite table
still points more strongly to a block-splice theorem than to direct affine
interpolation of count vectors.

The finite rank/block certificate is stored as:

```text
certs/d5_routeE_small_seam_rank_certs.json
```

and verified by:

```bash
python3 scripts/verify_d5_routeE_small_seam_rank_certs.py \
  --cert certs/d5_routeE_small_seam_rank_certs.json \
  --json-out /tmp/d5_routeE_small_seam_rank_cert_verify.json
```

It records, for every bundled `m = 6,8,...,60` case, the orbit rank on the
small seam, its inverse rank table, the maximal translation blocks, and the
return-time sum.  The verification checks `rank(V(a)) = rank(a)+1 mod (m-1)`,
block cover/disjointness/maximality, and `sum tau = m^4`.

## Revised D5 Even Route-E Gap

The non-open branch should no longer be described as an unresolved
`m^4`-state chart problem.  The evidence now reduces it to a one-dimensional
small-seam first-return problem.

The remaining symbolic propositions are:

1. construct residue-class formulas for `(s,nu)` covering every even
   `m >= 6`;
2. for each residue family, prove the induced small-seam map on
   `a = 1,...,m-1` is one cycle;
3. prove the return-time sum identity `sum tau = m^4` for each family;
4. provide the Lean first-return equations/minimality witnesses needed by
   `RouteEThetaSmallSeamCertificate`.

The finite `m = 4` witness required by `D5EvenRouteEM4FiniteTarget` is now
closed separately and no longer belongs to the open symbolic gap.

This is closer to the final lane-map proof shape in the D3 even Route-E
argument than to a high-dimensional SAT/chart certificate.
