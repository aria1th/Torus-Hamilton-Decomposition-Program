# D7 Progress, Blocking, and Found Facts

Status baseline before and after the next D7/D5-even research bundles.

Date: 2026-05-01.

Additional absorbed bundles:

- `/data/angel/repos/etc/A5_to_A7_induction_hypothesis_bundle_v0_1.zip`
- `/data/angel/repos/etc/d5_even_routeE_bundle_v0_1.zip`
- `/data/angel/repos/etc/A5_to_A7_post_bundle_update_v0_2.zip`
- `/data/angel/repos/etc/A5_to_A7_current_proofs_bundle_v0_3.zip`
- `/data/angel/repos/etc/A5_to_A7_current_proofs_bundle_note_v0_3.md`
- `/data/angel/repos/etc/d5_even_routeE_nonopen_small_seam_v0_4.zip`

## Current Progress

- D7 odd remains the regression endpoint.  The torus and Cayley endpoints are
  closed in Lean, and the working regression build is
  `lake build D7Odd RoundComposite.ConcreteEndpoints`.
- The composite-dimension theorem has been raised to concrete graph-level
  Cayley/Torus endpoints through `RoundComposite.lean` and
  `RoundComposite/ConcreteEndpoints.lean`.
- The shared root-flat return criterion is available in `Shared/RootFlat.lean`:
  row Latin, layer bijective, and return single-cycle imply the layered
  Hamilton decomposition.
- The D7 structural explanation is now centered on the additive `4+2` bridge
  `A7(m) ~= A5(m) x A3(m)`.
- The concrete Lean reduction target is
  `BridgeConcreteFullRankPackage` in
  `D7Odd/Handoff/Additive4Plus2ConcreteGoal.lean`.  Supplying this package for
  all odd `m >= 5` now routes directly to the odd D7 torus and Cayley
  endpoints.
- The finite `m = 3` branch is kept separate through the small-certificate
  route; the bridge target is for odd `m >= 5`.
- D5 even and D7 even remain separate certificate tracks.  The D5 even track
  has sharpened from a generic seam-orbit search into the Route-E
  one-`Lambda_E` periodic-excursion program recorded in
  `docs/A5_TO_A7_AND_D5_EVEN_BUNDLE_ABSORPTION_20260501.md`.
  The later non-open small-seam bundle further reduces the non-open branch to
  a size `m-1` direct first-return seam, verified for the recorded even cases
  `m = 6,8,...,60`.

## Current Blocking Point

The remaining D7 odd structural gap is the uniform construction of
`BridgeConcreteFullRankPackage` for every odd `m >= 5`.  After the A5-to-A7
bundle, this should be treated as two independent targets.

Concretely, this splits into two rank-step theorems:

- Base side: construct a uniform all-zero-set row family and
  `baseRank : Color -> D5Odd.ARoot5 m -> ZMod (m ^ 4)` such that the canonical
  folded base return steps `baseRank` by `+1`.
- Fiber side: construct a D3 fiber compiler and
  `fiberRank : Color -> ARoot3 m -> ZMod (m ^ 2)` such that the section return
  over the `m^4` base period steps `fiberRank` by `+1`.

The A5-to-A7 bundle sharpens the base side into **Target A**: construct
multi-`P` all-zero-set base row schedules and prove primitiveity by a
section-splice first-return theorem on
`Sigma = {(0,a,b,0,-a-b) : a+b != 0}`.  The direct one-`P` lift of the mixed D5
schedule is obstructed by the count equation `5k = 7`.

It sharpens the fiber side into **Target B'**: once a Target-A schedule is
fixed, construct a zero-set-only `K_m(Z)` or finite congruence family and prove
that the two A3 scalar monodromy invariants are units.  In the zero-set-only
model, these scalars reduce to finite mask sums using the `A5` stratum
coefficients `4,-3,2,-1,0,1` by zero-set size.

The previous live obstruction was the bundled fiber compiler at `m = 9`,
especially color `0`.  The extracted certificate
`bridge_4plus2_allN_m9_zero_set_K_cert.json` now gives a finite zero-set-only
replacement for this case.  The remaining blocker is to explain and generalize
that `K(Z)` table, and to combine it with a uniform base-row family.

## Found Facts

### Finite Bridge Certificates

`scripts/verify_4plus2_allN_bridge_cert.py` verifies the bundled `m = 5, 7, 9`
bridge certificates:

- base returns have canonical `m^4` rank-step cycles;
- fiber section returns have canonical `m^2` rank-step cycles;
- product returns are single `m^6` cycles.

### Simple Fiber Formulas

`scripts/search_4plus2_kappa_formulas.py` finds simple bundled formulas for
`m = 5` and `m = 7`:

- `m = 5`: `r = p + 2|Z| mod 3`;
- `m = 7`: `r = 2|Z| + 2 mod 3`.

The alternate `m = 5` base cover found by the base-row analyzer also admits a
simple formula: `r = t + |Z| + 2 mod 3`.

### Bundled m = 9 Fiber Obstruction and Zero-Set K Replacement

For bundled `m = 9`, the restricted cyclic/reflected affine family has no hit.
The larger dihedral family also has no hit:

- formula family: affine rotation modulo `3` plus affine reflection bit modulo
  `2`;
- candidates checked: `1296`;
- section-return hits: `0`.

The dihedral failure summary is concentrated at color `0`:

- cycle length `27`: `664` candidates;
- cycle length `9`: `516` candidates;
- cycle length `3`: `79` candidates;
- cycle length `1`: `37` candidates.

Thus the first fiber obstruction is not a late-color compatibility issue; every
dihedral candidate already fails on the color-0 section return.

The bundled `m = 9` witness itself is also not explained by the coarse features
currently tested.  Along the color-0 section trace:

- `slot_by_layer_p_z_component`: `5/55` pure classes;
- `slot_by_layer_p_z_component_full_mod3`: `11/1235` pure classes.

This says that even after adding full coordinate residues modulo `3`, the
observed finite witness still depends on finer base-state information.

The extracted certificate `bridge_4plus2_allN_m9_zero_set_K_cert.json` changes
the picture.  It keeps the bundled `m = 9` rows, replaces the kappa table, and
passes the full verifier:

```text
verified m=9 product_states=531441 rows=7 base_rank_steps=ok section_rank_steps=ok return_cycles=single
```

The new kappa table is layer-independent and zero-set-only:

- `zero_mask`: `27/27` pure classes;
- `layer_zero_mask`: `243/243` pure classes;
- `layer_zero_mask_full_mod3`: `3033/3033` pure classes.

The certificate metadata records the table as `K(Z)` on the shifted zero-set
mask `S = Z(u)-1`:

```text
0->1, 1->3, 2->2, 3->4, 4->5, 5->3, 6->0, 7->1, 8->3,
9->0, 10->4, 11->5, 12->4, 13->4, 14->1, 16->1, 17->0,
18->3, 19->3, 20->2, 21->4, 22->3, 24->3, 25->3, 26->2,
28->1, 31->4
```

So `m = 9` is no longer evidence that the bridge needs arbitrary opaque
state-dependence.  It is evidence that the needed compiler may be a finite
zero-set table rather than a four-parameter affine formula.

Applying this exact `m = 9` table unchanged to the existing bundled `m = 5`
and `m = 7` row choices does not work: it fails at color `2` for `m = 5` and
at color `4` for `m = 7`.  So the current evidence does not yet give one
global K-table for all moduli and all existing row choices; it gives a concrete
zero-set-table target to explain and generalize.

`scripts/verify_zero_set_k_cert.py` now verifies the scalar-only version of
this certificate.  It expands the shifted zero-set mask table into the full
`kappa_perm_indices` table, checks the recorded scalar invariants

```text
A = (5,7,2,1,1,1,1)
E = (2,2,2,4,4,5,8)
```

are all units modulo `9`, and then replays the full finite bridge verifier.
This is the current Target-B' regression for zero-set-only scalar certificates.
When the non-scalar and scalar JSON files are checked together, the non-scalar
file reports `scalar_ok=False` only because it has no scalar-invariant field;
both files report `table_ok=True`, `expanded_valid=True`, and `full_ok=True`,
while the scalar file also reports `scalar_ok=True`.

### Base Row Side

The base side is also not explained by a very short uniform primitive word
family.

- The bundled row projections for `m = 5, 7, 9` are base primitive.
- Bundled base words can be reassembled as column exact covers for
  `m = 5, 7, 9`.
- For `m = 17`, no primitive base word appears up to length `4`.
- For `m = 17`, length `5` gives first examples, including
  `01121`, `01214`, `10112`, `11210`, and `12101`.
- `scripts/analyze_targetA_section.py` now audits primitive base words against
  the intended `Sigma` section-splice interface.  The bundle-mentioned
  candidates `332`, `01302`, and `4204204` are not uniform all-odd words:
  `01302` works at `m = 5`; all three work at `m = 9`; none works unchanged
  for `m = 7,11,13,15,17`.  The length-5 `m = 17` examples above all pass the
  `Sigma` section audit at `m = 17`, but do not work unchanged for smaller odd
  moduli.
- A scan through odd `m = 5,7,...,21` up to word length `5` shows `23` and
  `32` are primitive for many moduli (`5,9,11,13,15,19,21`), while `m = 7`
  and `m = 17` need different first-hit patterns in the current scan.  This
  points toward a congruence-dependent or constructive Target-A row family
  rather than one fixed short base word.
- Direct testing of `23` through odd `m <= 37` fails exactly at
  `m = 7,17,27,37` in that range.  The post-update bundle sharpens this into
  the structural class `m == 2 mod 5`, equivalently `m == 7 mod 10` among odd
  moduli.  The known `m = 7` and `m = 17` exceptional primitive words do not
  work unchanged for `m = 27` or `m = 37`.
- `scripts/search_targetA_primitive_words.cpp` provides a faster C++ search
  path for these exceptional moduli.  With random sampling at `m = 27`, it
  found primitive words `22414`, `24142`, `441144`, and `332332`; all four
  pass the `Sigma` section audit at `m = 27`.  These do not work unchanged at
  `m = 7,17,37`, and naive `m = 37` random search is already heavy.
- With orbit-only and explicit-word modes, the same helper verifies that the
  symmetry closure of the known `m = 7,17,27` words has no `m = 37` hit, and a
  length-5 exhaustive chunk scan for `m = 37` also finds no hit.  A length-6
  chunk search then finds primitive words `404432`, `044324`, `324044`,
  `432404`, and `443240`; all five pass the `Sigma` section audit at
  `m = 37`.

The post-update bundle changes how these facts should be interpreted.  The
short words `23` and `32` are now the leading generic Target-A candidates:

```text
Phi_23 and Phi_32 one-cycle on Sigma  iff  m != 2 mod 5
```

in the tested odd range, with the excursion identity `sum ell = m^4` still
holding in both good and bad classes.  In the bad class `m == 2 mod 5`, the
induced `Sigma` map splits into five cycles.  For `W = 23`, the observed
lengths are:

```text
(m^2 + 9m - 2) / 5, (m^2 - m + 3) / 5, (m^2 - m - 2) / 5,
(m^2 - 6m + 3) / 5, (m^2 - 6m - 2) / 5.
```

For `W = 32`, the observed lengths are:

```text
(m^2 + 9m - 12) / 5, (m^2 - m + 8) / 5, (m^2 - m - 2) / 5,
(m^2 - 6m + 3) / 5, (m^2 - 6m + 3) / 5.
```

The key symbolic mechanism is the transversal
`Sigma0 = {(a,0) : a != 0}`, where the return acts as `a -> a+1`.  Thus
Target A should now be attacked as a seam-connectivity theorem for the generic
class, plus a five-cycle seam-splicing theorem for `m == 2 mod 5`, rather than
as an unstructured primitive-word search.

`scripts/verify_targetA_23_32.py` now records this post-update target as a
concise finite regression: it checks the expected section-cycle criterion,
`sum ell = m^4`, the `Sigma0` return law, and the bad-class five-cycle
formulas without emitting the large diagnostics from
`scripts/analyze_targetA_section.py`.  It passes for every odd
`m = 5,7,...,51` for both `23` and `32`.

`scripts/analyze_targetA_23_32_seams.py` separates the same data into the
proof-facing seam statement.  For every tested odd `m = 5,7,...,51`, it
confirms:

- if `m != 2 mod 5`, the whole `Sigma` cycle is the component meeting
  `Sigma0`;
- if `m == 2 mod 5`, there is exactly one `Sigma0` component and four
  off-`Sigma0` cycles with the predicted lengths.

The current-proofs bundle sharpens this again.  For `W = 23` or `W = 32`,
set

```text
Q = {B_i=(i,0)} union {A_j=(0,j)}, 1 <= i,j <= m-1.
```

For odd `m = 2h+1`, `m >= 13`, the seam quotient collapses the common
`B`-chain and the alternating `A`-line to the arithmetic map

```text
phi_h(x) = x - 3  for 1 <= x <= 3,
         = x - 8  for 4 <= x <= 5,
         = x - 5  for 6 <= x <= h,
```

with residues represented in `{1,...,h}`.  The quotient theorem is

```text
phi_h is one cycle iff h != 3 mod 5 iff m != 2 mod 5.
```

When `h == 3 mod 5`, the quotient has five cycles, explaining the bad class
structurally.  `scripts/verify_targetA_23_32_seam_quotient.py` now checks the
finite regression version: `phi_h` arithmetic, Q-hitting for computed first
returns, the Q-first-return formulas, and `sum ell = m^4`.  The remaining
proof-facing lemmas are Q-hitting and length-sum, plus the small moduli
`m = 5,7,9,11`.

The arithmetic proof of `phi_h` should use the inverse map.  It is `x -> x+5`
away from the top five-point boundary, and at the boundary it changes the
residue class modulo `5` by `3-h`.  Therefore the residue quotient is
transitive exactly when `h != 3 mod 5`; when `h == 3 mod 5`, the five residue
classes are the five quotient cycles.  The verifier now records this inverse
formula and residue-cycle explanation explicitly.

`D7Odd/Handoff/TargetASeamQuotient.lean` now exposes this as a Lean proof
interface.  It defines `phi_h`, `phi_h^{-1}`, the good class, and a package
whose fields are the single-cycle theorem plus Q-hitting, Q-first-return, and
length-sum obligations for `23` and `32`.  The inverse identities and
bijectivity of `phi_h` for `h >= 6` are already proved in Lean.  The residue
gate `IsUnit (3-h : ZMod 5) ↔ h % 5 != 3` is also now proved, so the remaining
arithmetic gap is the orbit-stitching theorem from this unit gate to
`IsSingleCycleMap (phi h)`.  The Lean file also exposes branch lemmas for
`phi_h^{-1}`: the internal step is `x -> x+5`, and the top five boundary
points map to `3,4,0,1,2`.  The residue transition is now formalized as
`phiInvNat_mod_five`: internal steps preserve residue modulo `5`, while the
top-boundary jump adds `3-h`.

The next Target-A gap is independent of this section theorem: seven primitive
row words must also satisfy column exact cover.  The necessary aggregate count
condition is that each base slot `0..4` appears exactly `m` times across the
seven base words.  `scripts/analyze_4plus2_base_rows.py` now reports this
count gate.  It confirms the bundled `m = 5,7,9` rows and the alternate
`m = 5` cover `23,23,002,0111,3044,14413,43220` are balanced, while a toy
`m = 11` construction using mostly powers of `23` has the correct total length
`55` but fails the slot-count gate with counts `4,0,26,25,0`.
The primitive-pool exact-cover search now uses this count gate before trying
column placements; the recorded alternate `m = 5` cover is still found with
the count-pruned search.
`scripts/search_targetA_balanced_covers.py` is a focused version for larger
primitive pools, especially pools exported by
`scripts/search_targetA_primitive_words.cpp`.  It reads `HIT ... word=...`
lines, searches seven-word multisets satisfying the balanced count gate, and
then calls the column exact-cover placer.  It reproduces the alternate `m = 5`
cover from the six-word input pool where `23` is allowed to repeat.

The column exact-cover placer has now been rewritten as a fixed-word column
DP: at each layer it chooses which five of the seven rows consume their next
base symbol, and requires those five symbols to be a permutation of `0..4`.
The two remaining rows are then filled by `5` and `6`.  This avoids explicitly
enumerating base positions and all extra-slot assignments.

For the current temporary `m = 11` primitive pool
`/tmp/targetA_m11_primitive_words_len11.txt`, the count-vector gate is not
empty for the natural length pattern

```text
7,8,8,8,8,8,8.
```

The command

```bash
python3 scripts/search_targetA_balanced_covers.py \
  --m 11 --word-file /tmp/targetA_m11_primitive_words_len11.txt \
  --lengths 7,8,8,8,8,8,8 \
  --combo-limit 0 --count-vector-limit 3 \
  --json-out /tmp/targetA_m11_count_vector_gate.json
```

reports balanced count-vector combinations immediately.  Thus, for this pool,
the next `m = 11` obstacle is not merely aggregate slot balance; it is finding
an actual column placement, or expanding the primitive pool enough that such a
placement appears.

### A5-to-A7 Target-A/Target-B Refinement

The absorbed A5-to-A7 induction bundle records that the direct mixed D5
schedule lift is impossible in the current local bridge model: one `P`-type
bridge layer contributes five base `P` occurrences, while seven one-`P` rows
would require seven occurrences, giving the impossible equation `5k = 7`.

Thus the live route is the all-zero-set spread with multi-`P` row words.  The
base proof target is a section-splice primitiveity proof on

```text
Sigma = {(0,a,b,0,-a-b) : a+b != 0}.
```

The desired facts for a row word family are positive first return to `Sigma`,
one-cycle first-return map on `Sigma`, and total excursion length `m^4`.

The fiber proof target is no longer an arbitrary state table.  For a
zero-set-only `K_m(Z)`, the `A5` exact zero-set counts modulo `m` are determined
by `|Z|`, with coefficients:

```text
0 ->  4
1 -> -3
2 ->  2
3 -> -1
4 ->  0
5 ->  1
```

So the A3 fiber primitiveity condition becomes a finite scalar unit check for
each color and chosen row schedule.

### D5 Even Route-E Track

The absorbed D5 even bundle replaces the earlier generic seam-orbit description
with a concrete Route-E program.

- The perturbed table `Lambda_E` changes exactly two cyclic representative rows
  of the odd `Lambda_1` zero-set table.
- For `m = 4`, the bundle gives a finite `C/E/O` schedule witness.
- For tested even `m = 6,8,10,12,14,16,18,20`, the schedules have constant
  layers plus one `Lambda_E` layer, and all five returns are single `m^4`
  cycles.
- Symbolically, one-`Lambda_E` schedules reduce to
  `F_{nu,s}(w) = w + nu + e_{p_s(w)}` and color conjugacy reduces all colors
  to one return map.
- In the open-port family `s=0`, `nu=(0,A,B,C,0)`, the completed section map is
  `H_{A,C}(sigma,a) = (sigma-C, a+A+1-1_{sigma=0})`, which is a single
  `m^2` cycle when `gcd(C,m)=1`.
- `scripts/verify_d5_even_routeE.py` now has a section-scan mode.  Through
  even `m = 6,8,...,60`, it finds the uniform open-port section triple
  `(A,B,C) = (0,m-2,1)`: the section formula holds, `H` is a single `m^2`
  cycle, and the only exception point is `(m-1,2)`.  This does not prove the
  full return is primitive; it isolates the remaining obstruction in the
  origin-excursion/full-return chart.
- The same verifier now has an open-port full-cycle scan.  Through
  `m = 6,8,...,20`, the section-passing open-port triples include full
  one-cycle returns at `m = 10,12,14,18,20`, but no open-port full hit at
  `m = 6,8,16`.  Thus the all-even Route-E family cannot be closed merely by
  the easy open-port section condition; some residue classes need a
  non-open-port count/slot choice or a stronger origin-excursion chart.
- A larger one-`Lambda_E` count/slot scan now confirms that the missing
  open-port cases are not failures of the one-`Lambda_E` ansatz itself.  The
  scan finds full one-cycle hits for `m = 6,8,10,12,14,16,18,20`; for example,
  `m = 6` starts with `(slot, counts) = (0, (0,0,1,3,1))`, `m = 8` with
  `(0, (2,0,0,3,2))`, and `m = 16` with `(0, (0,0,8,3,4))`.  These hits give
  a finite-data target for extracting residue-class count/drift families
  beyond the open-port normal form.
- Count/slot scan hits now also report `normalized_counts_slot0`, obtained by
  cyclically rotating the E-slot to `0`.  This makes equivalent rotated hits
  visible: for instance, the `m = 6` hit `(1, (1,0,0,1,3))` normalizes to the
  same `(0,0,1,3,1)` count vector as the bundled `m = 6` witness.  All first
  hits currently seen at `m = 6,8,16` are outside open-port normal form after
  this normalization.
- The scan also records normalized support/zero positions and whether each hit
  matches the bundled finite schedule's normalized count vector.  For `m = 6`
  and `m = 8`, rotated copies of the bundled normalized counts appear among
  the first ten hits.  For `m = 16`, the first ten slot-0 hits are all
  different from the bundled normalized count `(1,13,0,1,0)`, so the count
  space has additional non-open-port witnesses beyond the finite table entry.
The non-open small-seam bundle reduces these non-open witnesses to a direct
seam of size `m-1`:

```text
Theta_s = { rho_s(0,a,0,0,-a) : a != 0 }.
```

If the first-return map on `Theta_s` is one cycle and the return-time sum is
`m^4`, the normalized return on `A5(m)` is a single `m^4` cycle.  The repo
verifier now checks the bundled cases for all even `m = 6,8,...,60`; the local
absorption run reported `28` cases and `all_ok=True`.  It now also emits the
maximal translation blocks of the induced seam map, i.e. intervals on which
`V(a)-a mod m` is constant.  These blocks are the finite trace data for the
next one-dimensional block-splice proof.

The D5 even open tasks are now: find residue-class count/drift families
covering every even `m >= 6`, prove the induced one-dimensional small-seam
maps and return-time sums for those families, and package `m = 4` as a finite
witness theorem.

The first residue-family scan is intentionally negative.  The script
`scripts/analyze_d5_routeE_small_seam_families.py` checks whether the recorded
small-seam table already supports simple affine normalized count vectors on
residue classes.  On the current `m = 6,8,...,60` data, tested periods
`4,6,...,26` fail exact affine fits, while periods `28` and `30` have only
one or two samples per class.  This means the table is a seam-criterion
certificate source, not yet an all-even formula source.

`D5Odd/EvenRouteE.lean` now records this as a Lean-facing certificate shape:
one-`Lambda_E` count/slot data, the nonzero seam of size `m-1`, small-seam
first-return traces, first-return minimality, and the return-time sum.  The
orbit target needed by the existing D5 even seam endpoint is derived in Lean
from the first-return counting lemma, rather than stored as an assumed field.
It also records the branch-combination theorem: a separate `m = 4` Hamilton
witness plus either the generic all-large Route-E target or the specialized
non-open small-seam target implies all even `m >= 4` Hamilton, torus, and
Cayley targets.

## Next Bundle Checklist

When new bundles arrive, compare them against this baseline:

- Do they include a finer description of the bundled `m = 9` kappa table?
- Do they explain why the zero-set-only `K(Z)` replacement gives color `0`
  section monodromy for `m = 9`?
- Do they provide a candidate invariant finer than `(layer, p, |Z|, component)`
  and full residues modulo `3`?
- Do they include a uniform or congruence-dependent base-row family that covers
  the `m = 17` length-5 onset?
- Do they prove or further compress the `23/32` first-return table, especially
  the `Sigma0` law and the `m == 2 mod 5` five-cycle decomposition?
- Do they provide a correction family for the `m == 2 mod 5` seam components?
- Do they expose explicit `baseRank` or `fiberRank` formulas compatible with
  `BridgeConcreteFullRankPackage`?
- Do they separate D5 even and D7 even certificate tracks from the D7 odd
  additive bridge?
- For D5 even, do they provide count/drift families and origin-excursion
  charts for the Route-E one-`Lambda_E` program?

## Verification Commands

Recent checks used for this baseline:

```bash
lake build D7Odd RoundComposite.ConcreteEndpoints
lake build D7Odd.Handoff.Additive4Plus2ConcreteGoal
python3 -m py_compile scripts/search_4plus2_kappa_formulas.py
python3 scripts/search_4plus2_kappa_formulas.py --only 9 \
  --formula-family dihedral --section-only --summarize-failures \
  --json-out /tmp/d7_dihedral_m9_failure_summary_check.json
python3 scripts/search_4plus2_kappa_formulas.py --only 9 \
  --diagnostics-only --section-trace-diagnostics \
  --json-out /tmp/d7_m9_section_trace_diag_check.json
python3 scripts/verify_4plus2_allN_bridge_cert.py \
  --cert-json /data/angel/repos/etc/bridge_4plus2_allN_m9_zero_set_K_cert.json
python3 scripts/search_4plus2_kappa_formulas.py \
  --cert-json /data/angel/repos/etc/bridge_4plus2_allN_m9_zero_set_K_cert.json \
  --diagnostics-only --diagnostic-profile all --section-trace-diagnostics \
  --json-out /tmp/d7_m9_zero_set_K_diag.json
python3 scripts/verify_zero_set_k_cert.py \
  /data/angel/repos/etc/bridge_4plus2_allN_m9_zero_set_K_scalar_cert.json \
  --json-out /tmp/d7_m9_zero_set_K_scalar_verify.json
python3 scripts/verify_d5_even_routeE.py --mode all \
  --json-out /tmp/d5_even_routeE_verify.json
python3 scripts/verify_d5_even_routeE.py --mode section \
  --section-scan-moduli 6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,50,52,54,56,58,60 \
  --section-scan-limit 1 \
  --json-out /tmp/d5_even_routeE_section_scan_6_60.json
python3 scripts/verify_d5_even_routeE.py --mode section \
  --full-scan-moduli 6,8,10,12,14,16,18,20 \
  --full-scan-limit 5 \
  --json-out /tmp/d5_even_routeE_open_port_full_scan.json
python3 scripts/verify_d5_even_routeE.py --mode section \
  --count-scan-moduli 6,8,10,12,14,16 \
  --count-scan-limit 5 \
  --json-out /tmp/d5_even_routeE_count_scan_6_16.json
python3 scripts/analyze_targetA_section.py \
  --moduli 5,7,9,11,13,15,17 \
  --words 332,01302,4204204 \
  --json-out /tmp/d7_targetA_section_candidates.json
g++ -O3 -std=c++17 scripts/search_targetA_primitive_words.cpp \
  -o /tmp/search_targetA_primitive_words
/tmp/search_targetA_primitive_words 27 6 10 5 2000 27
python3 scripts/analyze_targetA_section.py \
  --moduli 37 \
  --words 404432,044324,324044,432404,443240 \
  --json-out /tmp/d7_targetA_section_m37_len6_hits.json
python3 scripts/verify_targetA_23_32.py \
  --moduli 5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49,51 \
  --json-out /tmp/targetA_23_32_5_to_51.json
python3 scripts/analyze_targetA_23_32_seams.py \
  --moduli 5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49,51 \
  --json-out /tmp/targetA_23_32_seams_5_to_51.json
python3 scripts/analyze_4plus2_base_rows.py \
  --cover-from-bundled --only 5,7,9 --cover-limit 1 \
  --json-out /tmp/targetA_bundled_cover_counts.json
python3 scripts/analyze_4plus2_base_rows.py \
  --cover-m 11 \
  --cover-words 23232323,23232323,23232323,23232323,23232323,2323232323,00002 \
  --cover-limit 1 --json-out /tmp/targetA_m11_power_bad_counts.json
python3 scripts/analyze_4plus2_base_rows.py \
  --cover-primitive-m 5 --cover-primitive-max-len 5 \
  --cover-lengths 5,4,5,4,3,2,2 \
  --cover-pool-limit 200 --combo-limit 300000 --cover-limit 1 \
  --json-out /tmp/targetA_m5_primitive_cover_count_pruned.json
python3 scripts/search_targetA_balanced_covers.py \
  --m 5 --words 23,002,0111,3044,14413,43220 \
  --lengths 5,4,5,4,3,2,2 \
  --json-out /tmp/targetA_balanced_m5_inline.json
git diff --check
```

This document is not a completion certificate for the full research goal.  It
records the current open frontier before the next bundle comparison.
