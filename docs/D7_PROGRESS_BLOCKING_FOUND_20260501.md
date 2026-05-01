# D7 Progress, Blocking, and Found Facts

Status baseline before and after the next D7/D5-even research bundles.

Date: 2026-05-01.

Additional absorbed bundles:

- `/data/angel/repos/etc/A5_to_A7_induction_hypothesis_bundle_v0_1.zip`
- `/data/angel/repos/etc/d5_even_routeE_bundle_v0_1.zip`

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
  `m = 7,17,27,37` in that range, suggesting an `m ≡ 7 mod 10` exceptional
  family.  The known `m = 7` and `m = 17` exceptional primitive words do not
  work unchanged for `m = 27` or `m = 37`.

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

The D5 even open tasks are now: find residue-class count/drift families
covering every even `m >= 6`, prove origin-excursion affine chart
certificates, and package `m = 4` as a finite witness theorem.

## Next Bundle Checklist

When new bundles arrive, compare them against this baseline:

- Do they include a finer description of the bundled `m = 9` kappa table?
- Do they explain why the zero-set-only `K(Z)` replacement gives color `0`
  section monodromy for `m = 9`?
- Do they provide a candidate invariant finer than `(layer, p, |Z|, component)`
  and full residues modulo `3`?
- Do they include a uniform or congruence-dependent base-row family that covers
  the `m = 17` length-5 onset?
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
python3 scripts/verify_d5_even_routeE.py --mode all \
  --json-out /tmp/d5_even_routeE_verify.json
python3 scripts/analyze_targetA_section.py \
  --moduli 5,7,9,11,13,15,17 \
  --words 332,01302,4204204 \
  --json-out /tmp/d7_targetA_section_candidates.json
git diff --check
```

This document is not a completion certificate for the full research goal.  It
records the current open frontier before the next bundle comparison.
