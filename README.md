# Torus Hamilton Decomposition Program

Lean 4 formalization and audit artifacts for Hamilton decompositions of directed torus/Cayley digraphs.

The current formalized endpoints include the odd-modulus directed 5-torus and
7-torus constructions.  In particular, the repository proves:

```lean
theorem D5Odd.D5_odd_cayley_unconditional {m : Nat} [NeZero m]
    (hodd : Odd m) (hm3 : 3 <= m) :
    D5Odd.CayleyHamiltonDecompositionD5 m

theorem D7Odd.D7_odd_cayley_unconditional {m : Nat} [NeZero m]
    (hodd : Odd m) (hm3 : 3 <= m) :
    D7Odd.CayleyHamiltonDecompositionD7 m
```

These theorems state explicit Cayley-edge decompositions for
`Cay((ZMod m)^d, {e_0, ..., e_{d-1}})` in dimensions `d = 5` and `d = 7`
when `m` is odd and `m >= 3`.

## Repository Layout

- `D5Odd/`: Lean 4 formalization.
- `D5Odd/Cayley.lean`: final Cayley-edge wrapper and theorem.
- `D5Odd/Torus.lean`: layer/root-flat lift from return maps to full torus color cycles.
- `D5Odd/Main.lean`: model-level odd D5 endpoint.
- `D5Odd/ReturnCycle.lean`: D5 return-cycle certificates, including the
  `m = 3` root-return `CycleCoordinate` exported from the rank certificate.
- `D7Odd/`: Lean 4 formalization of the odd D7 construction.
- `D7Odd/Handoff/CanonicalFamily.lean`: canonical generic branch and root-flat D7 endpoint.
- `D7Odd/Handoff/PrimeCanonicalBridge.lean`: bridge from the prime-parametric interface back to the fixed `d = 7` canonical regression.
- `D7Odd/Handoff/Additive4Plus2.lean`: root-state coordinate equivalence `A7(m) ~= A5(m) x A3(m)`, the A3 prefix equivalence/cardinality theorem `card_ARoot3 = m^2`, the product/root-state cardinality theorems `card_ProductRoot = card_RootState7 = m^6`, D7 slot-step conjugacy, product-side certificate adapters into the D7 root-flat and shared layered-lift targets, and local/skew-return criteria for constructing product certificates.
- `D7Odd/Handoff/Additive4Plus2D5Base.lean`: concrete D5 all-zero-set base slot rule used by the bundled bridge verifier, reusing `D5Odd.ZeroSetTable.Lambda1` and the D5 exact-cover proof to expose row-Latin and layer-bijective local facts.
- `D7Odd/Handoff/Additive4Plus2D3Fiber.lean`: concrete odd-D3 affine fiber packet used by the bundled bridge verifier, including row-Latin, layer-step bijectivity, and permuted fiber-compiler proofs for moduli with `0 != 1`.
- `D7Odd/Handoff/Additive4Plus2BridgeKappa.lean`: concrete state-dependent bridge `kappa` combining the D5 base slot rule with an S3 fiber permutation, with bijectivity, concrete row-schedule row-Latin adapters, D3 compiler-to-`phi` adapters, component projection lemmas, and a packaged concrete row/layer local-facts theorem.
- `D7Odd/Handoff/Additive4Plus2BridgeChart.lean`: alternate `4+2` bridge chart matching the bundled all-zero-set model, where base non-root directions carry the forced D3 `q0` fiber move, plus bridge-chart local/skew-return certificate adapters.
- `D7Odd/Handoff/Additive4Plus2Endpoints.lean`: final torus/Cayley wrappers from direct-chart and bridge-chart `4+2` product-side certificates.
- `D7Odd/Handoff/Additive4Plus2Goal.lean`: conditional odd D7 goal theorem: the finite `m = 3` branch plus bridge-chart certificates, or the corresponding local/skew-return packages, for all odd `m >= 5` imply the handoff, torus, Cayley, and shared Cayley endpoints.
- `D7Odd/Handoff/Additive4Plus2ConcreteGoal.lean`: concrete all-zero-set bridge target: once row permutations, D3 fiber-layer/permutation data, a base-return rank step into `ZMod (m^4)`, and a fiber-monodromy rank step into `ZMod (m^2)` are supplied for the canonical folded return, the local row/layer facts, folded-return bijectivity, product-return equality, base orbit coverage, and monodromy single-cycle are filled in automatically and the odd D7 torus/Cayley endpoints follow.
- `D7Odd/Handoff/TargetASeamQuotient.lean`: Lean-facing proof target for
  the `23/32` Target-A seam quotient, defining `phi_h`, its inverse, the
  good class `h % 5 != 3`, proving the inverse identities and bijectivity for
  `h >= 6`, proving the residue-shift unit gate in `ZMod 5`, proving the
  inverse-map residue transition at the top boundary, proving
  `IsSingleCycleMap (phi h) ↔ IsSingleCycleMap (phiInv h)`, and packaging
  the remaining cycle/Q-hitting/length-sum obligations.  It also proves the
  bad-class necessary direction: if `phi h` is a single cycle, then
  `h % 5 != 3`.  In the good class it proves the quotient residue map
  `r |-> r + (3-h)` is a single cycle on `ZMod 5`, and it proves the
  internal lane traversal lemma for repeated `phiInv` steps by `+5`, plus
  the boundary-jump residue lemma between lanes and an exact low-representative
  boundary landing lemma.  The lane-top formula `laneTop` and
  `phiInv_reaches_next_low` lift one residue edge to an actual `phiInv` orbit
  segment.  A local `Reaches` relation with transitivity is available for the
  final orbit-stitching composition.
- `D7Odd/Torus.lean`: lift from root-flat D7 certificates to full torus color cycles.
- `D7Odd/Cayley.lean`: final D7 Cayley-edge wrapper and theorem.
- `D7Odd/Even.lean`: even-modulus D7 certificate targets via the
  `RootFlatSchedule` interface, with adapters to the shared layered lift and
  torus/Cayley wrappers.
- `D5Odd/Even.lean`: even-modulus D5 seam certificate target and torus/Cayley wrappers.
- `D5Odd/EvenRouteE.lean`: Lean-facing Route-E certificate interface for
  D5 even one-`Lambda_E` count/slot data and small-seam traces.  It records
  the nonzero seam of size `m-1`, the explicit shifted seam parametrization
  `a |-> rho_s(0,a,0,0,-a)` as `routeEThetaPoint`, and derives the D5 even
  seam orbit target from first-return equations, first-return minimality,
  seam single-cyclicity, and the return-time sum before routing to the
  torus/Cayley endpoints.  It also defines the underlying `Vec5` seam point
  `routeEThetaVec` and proves its `rootZ`/`rootOfZ` equivalence with
  `routeEThetaPoint`, making the bundle coordinate convention explicit.
- `D5Odd/EvenRouteEM4.lean`: finite `m = 4` Route-E branch.  It packages the
  recorded `C/E/O/O` four-layer schedule, verifies exact cover and Latin
  conditions by finite decision, proves all five color returns are single
  cycles using generated `ZMod 256` rank tables, and closes
  `D5EvenRouteEM4FiniteTarget`.
- `Shared/ReturnLift.lean`: shared return-map lift lemma used by the D5 and D7 torus lifts.
- `Shared/RankCycle.lean`: shared rank-map criterion for proving finite return maps are single cycles.
- `Shared/RootFlat.lean`: generic root-flat schedule, certificate, and
  layered full-step lift: row Latin gives edge partition, and layer bijective
  plus return single-cycle gives Hamiltonian full color steps.
- `Shared/TorusCayley.lean`: standard dimension-indexed directed torus/Cayley
  Hamilton-decomposition proposition used by the composite-reduction interface,
  block-coordinate equivalences for composite dimensions, and cycle-coordinate
  data for product lifts, including constructors from rank-equivalence data and
  finite single-cycle endpoints.
- `Shared/CayleyProduct.lean`: coordinate-bearing Cayley decompositions and the
  concrete graph-product transport theorem, including product color-direction
  edge partition, Hamiltonian conjugacy, and adapters from color-wise rank
  functions or existing single-cycle Cayley decompositions.
- `Shared/Monodromy.lean`: skew-product, base-orbit, and monodromy lemmas for additive bridge proofs.
- `Shared/AdditiveBridge.lean`: local additive bridge lemmas for state-dependent direction reindexing, row/source Latin preservation, and skew-product layer bijectivity.
- `RoundComposite.lean`: composite-dimension product reduction from pointwise expansion and prime bases, including odd-modulus variants, concrete adapters for the shared standard torus/Cayley proposition, and graph-level standard Cayley/Torus product expansions.
- `RoundComposite/ConcreteEndpoints.lean`: conditional graph-level composite
  endpoints obtained from the formalized D5/D7 odd theorems, including direct
  Cayley/Torus product endpoints for 35, 49, and nonempty products of 5/7
  factors.
- `docs/D7_PROGRESS_BLOCKING_FOUND_20260501.md`: current progress, blockers,
  and found facts for the D7 additive `4+2` bridge before the next research
  bundle comparison.
- `docs/A5_TO_A7_AND_D5_EVEN_BUNDLE_ABSORPTION_20260501.md`: absorption note
  for `A5_to_A7_induction_hypothesis_bundle_v0_1.zip` and
  `d5_even_routeE_bundle_v0_1.zip`, sharpening the D7 odd bridge into
  Target-A base rows plus Target-B' zero-set scalar fiber compiler and moving
  D5 even to the Route-E periodic-excursion track.
- `docs/A5_TO_A7_POST_BUNDLE_UPDATE_20260501.md`: absorption note for
  `A5_to_A7_post_bundle_update_v0_2.zip`, recording the `23/32` Target-A
  generic branch, the `m == 2 mod 5` five-cycle obstruction, and the revised
  seam-splicing proof obligations.
- `docs/A5_TO_A7_CURRENT_PROOFS_BUNDLE_20260501.md`: absorption note for
  `A5_to_A7_current_proofs_bundle_v0_3.zip` and its note, recording the
  symbolic seam quotient `phi_h` for the `23/32` Target-A branch and the
  reduced Q-hitting/length-sum obligations.
- `docs/D5_EVEN_ROUTE_E_NONOPEN_SMALL_SEAM_20260501.md`: absorption note for
  `d5_even_routeE_nonopen_small_seam_v0_4.zip`, recording the size `m-1`
  small-seam criterion for non-open one-`Lambda_E` schedules and the verified
  even range `m = 6,8,...,60`.
- `docs/D7_ODD_SPECIAL_THEOREM_REQUESTS.md`: D7 handoff/proof-status notes.
- `scripts/d5_odd_paper_verify.py`: audit-only Python verifier used for independent sanity checks.
- `scripts/verify_4plus2_allN_bridge_cert.py`: audit verifier for the bundled `m=5,7,9` all-zero-set `4+2` bridge certificates, including canonical base `m^4` and fiber-section `m^2` rank-step checks plus product `m^6` cycle checks.
- `scripts/analyze_4plus2_base_rows.py`: base-only search aid for the all-zero-set `4+2` bridge; it summarizes bundled row projections, reports aggregate base-slot count feasibility for exact cover, and scans short primitive A5 base words.
- `scripts/analyze_targetA_section.py`: Target-A section-return analyzer for
  candidate all-zero-set A5 base words, reporting primitiveity, first return
  to `Sigma = {(0,a,b,0,-a-b) : a+b != 0}`, excursion coverage, and coarse
  diagnostics for symbolic first-return tables.
- `scripts/verify_targetA_23_32.py`: concise verifier for the post-update
  Target-A `23/32` theorem candidate, checking section cycles, `sum ell =
  m^4`, the `Sigma0` return law, and the bad-class five-cycle formulas.
- `scripts/analyze_targetA_23_32_seams.py`: seam-decomposition reporter for
  the same `23/32` target, separating the `Sigma0` component from off-`Sigma0`
  bad-class cycles and checking the good-class connectivity/bad-class
  decomposition gates.
- `scripts/verify_targetA_23_32_seam_quotient.py`: verifier for the current
  `23/32` seam quotient proof target, checking the arithmetic `phi_h` cycle
  theorem, finite Q-hitting, Q-first-return formulas, and length sums.
- `scripts/search_targetA_primitive_words.cpp`: faster C++ primitive-word
  search for Target-A exceptional moduli where the Python exhaustive scan is
  too slow.
- `scripts/search_targetA_balanced_covers.py`: balanced Target-A row-family
  search over a primitive-word pool, accepting C++ `HIT ... word=...` output,
  enforcing aggregate slot counts `(m,m,m,m,m)`, then calling the column
  exact-cover placer.  It can also report balanced count-vector combinations
  separately from column placement.
- `scripts/search_4plus2_kappa_formulas.py`: fiber-compiler search aid for zero-set cyclic/reflected kappa formulas of the form `a*t + b*p(Z) + c*|Z| + d mod 3`, a larger dihedral `rotation mod 3 + reflection mod 2` family, and dependency diagnostics for bundled or generated kappa tables.
- `scripts/verify_zero_set_k_cert.py`: Target-B' verifier for scalar
  zero-set-only `K(Z)` certificates; it expands mask tables into full kappa
  tables, checks scalar unit invariants, and can run the full bridge verifier.
- `scripts/d7_bridge_snapshot.py`: compact JSON snapshot tool for bridge bundles or extracted certificate JSON files, used to compare new research bundles against the current baseline.
- `scripts/d5_even_seam_sat_search.py`: SAT witness search for the D5 even seam certificate target.
- `scripts/verify_d5_even_routeE.py`: audit verifier for the absorbed D5 even
  Route-E bundle, checking the finite schedule table, normalized core
  first-return formula, open-port section formula/cycle examples, and the
  non-open small-seam criterion from the later small-seam bundle.
- `scripts/fast_d5_routeE_small_seam_verify.cpp`: standalone C++ verifier for
  one recorded D5 Route-E small-seam case, kept as an independent check of the
  `m-1` seam criterion.
- `ANCILLARY.md`: description of the source bundle supplied with the manuscript.

## Build

Install Lean with `elan`, then run:

```bash
lake build D5Odd D7Odd
lake build RoundComposite Shared
lake build RoundComposite.ConcreteEndpoints
```

The project currently uses:

```text
leanprover/lean4:v4.30.0-rc2
mathlib v4.30.0-rc2
```

Optional D5 audit script:

```bash
python3 scripts/d5_odd_paper_verify.py 3 5 7 9
```

Expected output:

```text
m=3: matching=81, G-cycle=81
m=5: matching=625, G-cycle=625
m=7: matching=2401, G-cycle=2401
m=9: matching=6561, G-cycle=6561
```

Optional `4+2` additive bridge audit script, using
`D7_current_research_note_bundle_v1_1.zip` from the parent workspace:

```bash
python3 scripts/verify_4plus2_allN_bridge_cert.py
```

For formula search, the same verifier can export compact rank fingerprints and
orbit prefixes:

```bash
python3 scripts/verify_4plus2_allN_bridge_cert.py \
  --rank-summary-json /tmp/d7_4plus2_rank_summary.json
```

The base-row side can be inspected separately:

```bash
python3 scripts/analyze_4plus2_base_rows.py \
  --scan-moduli 5,7,9,11,13,15,17 --max-len 3 \
  --cover-from-bundled \
  --json-out /tmp/d7_4plus2_base_rows.json
```

Candidate Target-A base words can also be audited against the intended
section-splice proof interface:

```bash
python3 scripts/analyze_targetA_section.py \
  --moduli 5,7,9,11,13,15,17 \
  --words 332,01302,4204204 \
  --json-out /tmp/d7_targetA_section_candidates.json
```

The current generic Target-A candidates from the post-update bundle are
`23` and `32`.  Use the focused verifier for this theorem candidate:

```bash
python3 scripts/verify_targetA_23_32.py \
  --json-out /tmp/d7_targetA_23_32.json
```

It checks the expected one-cycle pattern outside `m == 2 mod 5`, the
bad-class five-cycle formulas, the `Sigma0` return law, and `return_time_sum =
m^4`.  A larger comparison matching the post-update bundle range is:

```bash
python3 scripts/verify_targetA_23_32.py \
  --moduli 5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49,51 \
  --json-out /tmp/d7_targetA_23_32_5_to_51.json
```

The corresponding seam decomposition can be inspected with:

```bash
python3 scripts/analyze_targetA_23_32_seams.py \
  --moduli 5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49,51 \
  --json-out /tmp/d7_targetA_23_32_seams_5_to_51.json
```

The current proof bundle further reduces the `23/32` branch to a seam quotient
on `Q={B_i=(i,0)} union {A_j=(0,j)}` and the arithmetic map `phi_h`.  Check
that quotient with:

```bash
python3 scripts/verify_targetA_23_32_seam_quotient.py \
  --moduli 13,15,17,19,21,23,25,27,29,31,33,35,37,39,41 \
  --phi-max 200 \
  --json-out /tmp/d7_targetA_23_32_seam_quotient.json
```

The verifier also records the inverse-map explanation for the arithmetic:
`phi_h^{-1}` walks by `+5` inside residue classes and crosses the top boundary
with residue shift `3-h mod 5`.  The Lean target now proves this residue
transition as `phiInvNat_mod_five`.

The corresponding Lean proof target is exposed by:

```bash
lake build D7Odd.Handoff.TargetASeamQuotient
```

For larger exceptional moduli, compile the faster C++ search helper:

```bash
g++ -O3 -std=c++17 scripts/search_targetA_primitive_words.cpp \
  -o /tmp/search_targetA_primitive_words
/tmp/search_targetA_primitive_words 27 6 10 5 2000 27
```

The helper also accepts explicit candidate words after the mode argument, which
is useful for parallel chunk checks or testing symmetry closures.

It can also try bounded exact-cover assembly from the primitive-word pool:

```bash
python3 scripts/analyze_4plus2_base_rows.py \
  --cover-primitive-m 5 --cover-primitive-max-len 5 \
  --cover-lengths 5,4,5,4,3,2,2 \
  --cover-pool-limit 200 --combo-limit 300000 \
  --test-with-bundled-kappa \
  --json-out /tmp/d7_4plus2_base_pool_search.json
```

For larger primitive pools exported by the C++ helper, use the balanced-cover
search:

```bash
python3 scripts/search_targetA_balanced_covers.py \
  --m 5 --words 23,002,0111,3044,14413,43220 \
  --lengths 5,4,5,4,3,2,2 \
  --json-out /tmp/d7_targetA_balanced_m5_inline.json
```

For larger moduli, the count-vector gate can be inspected before running the
full word-multiset search:

```bash
python3 scripts/search_targetA_balanced_covers.py \
  --m 11 --word-file /tmp/targetA_m11_primitive_words_len11.txt \
  --lengths 7,8,8,8,8,8,8 \
  --combo-limit 0 --count-vector-limit 3 \
  --json-out /tmp/targetA_m11_count_vector_gate.json
```

This separates the necessary aggregate-count question from the harder column
placement question.

The restricted zero-set kappa formula family can be checked separately:

```bash
python3 scripts/search_4plus2_kappa_formulas.py --only 5,7,9 \
  --json-out /tmp/d7_4plus2_kappa_formula_search.json
```

The same script can check the larger dihedral family by using the monodromy
section-return criterion without replaying the full product-cycle audit:

```bash
python3 scripts/search_4plus2_kappa_formulas.py --only 5,7 \
  --formula-family dihedral --section-only \
  --json-out /tmp/d7_4plus2_dihedral_section_search.json
```

This reproduces the `m=5` and `m=7` hits with constant reflection bit.  Running
the same command with `--only 9` checks all `1296` dihedral candidates and finds
no section-return hit.  With `--summarize-failures`, all bundled `m=9`
dihedral candidates fail already at color `0`; the first section-cycle lengths
are `27` for `664` candidates, `9` for `516`, `3` for `79`, and `1` for `37`.
With `--section-trace-diagnostics`, the bundled `m=9` witness itself is also
seen to require finer state dependence along the color-0 trace:
`slot_by_layer_p_z_component` has only `5/55` pure classes, and adding full
coordinate residues modulo `3` gives only `11/1235` pure classes.

To inspect an existing kappa table without running the formula search:

```bash
python3 scripts/search_4plus2_kappa_formulas.py --only 9 \
  --diagnostics-only \
  --diagnostic-profile all \
  --json-out /tmp/d7_kappa_diag_m9.json
```

For the bundled `m=9` table, the current diagnostics show no pure classes for
`zero_mask`, `zero_count`, `p`, `p_zero_count`,
`layer_mod3_pmod3_zmod3`, or `layer_mod3_zero_mask`; `layer_zero_mask` has
only `9/243` pure classes, with majority fraction `0.188843`.  In the residue
profile, `layer_full_mod3` also has `0/729` pure classes, and even
`layer_zero_mask_full_mod3` has only `44/3033` pure classes.  This is not an
impossibility proof, but it records why the bundled table should be treated as
opaque relative to these coarse features.

Extracted certificate JSON files can be inspected directly.  For example,
`bridge_4plus2_allN_m9_zero_set_K_cert.json` verifies as a full bridge
certificate and its kappa table is pure on `zero_mask`:

```bash
python3 scripts/verify_4plus2_allN_bridge_cert.py \
  --cert-json /data/angel/repos/etc/bridge_4plus2_allN_m9_zero_set_K_cert.json
python3 scripts/search_4plus2_kappa_formulas.py \
  --cert-json /data/angel/repos/etc/bridge_4plus2_allN_m9_zero_set_K_cert.json \
  --diagnostics-only --diagnostic-profile all --section-trace-diagnostics \
  --json-out /tmp/d7_m9_zero_set_K_diag.json
python3 scripts/d7_bridge_snapshot.py \
  --cert-json /data/angel/repos/etc/bridge_4plus2_allN_m9_zero_set_K_cert.json \
  --include-full-verify --include-section-trace \
  --json-out /tmp/d7_m9_zero_set_K_snapshot.json
```

The snapshot records whether a certificate-provided `K(Z)` table matches the
shifted zero-set mask encoding used by the finite kappa table.

For scalar-only `K(Z)` certificates, expand the mask table and check the A3
unit invariants directly:

```bash
python3 scripts/verify_zero_set_k_cert.py \
  /data/angel/repos/etc/bridge_4plus2_allN_m9_zero_set_K_scalar_cert.json \
  --json-out /tmp/d7_m9_zero_set_K_scalar_verify.json
```

It can also test row solutions exported by the base analyzer:

```bash
python3 scripts/search_4plus2_kappa_formulas.py \
  --cover-json /tmp/d7_4plus2_base_pool_search.json --only 5 \
  --emit-hit-cert-dir /tmp/d7_4plus2_formula_certs \
  --json-out /tmp/d7_4plus2_base_pool_kappa_formula_search.json
```

Expected output:

```text
verified m=5 product_states=15625 rows=7 base_rank_steps=ok section_rank_steps=ok return_cycles=single
verified m=7 product_states=117649 rows=7 base_rank_steps=ok section_rank_steps=ok return_cycles=single
verified m=9 product_states=531441 rows=7 base_rank_steps=ok section_rank_steps=ok return_cycles=single
```

The D5 even SAT search requires `python-sat`; it is a witness/debugging tool
for the seam target, not a Lean proof artifact.  The current seam encoding
returns `unsat` for the small `m=2` smoke check.

The absorbed D5 even Route-E bundle has an independent verifier:

```bash
python3 scripts/verify_d5_even_routeE.py --mode all \
  --json-out /tmp/d5_even_routeE_verify.json
```

It checks the recorded finite schedules for `m = 4,6,...,20`, the normalized
Route-E core first-return table through `m = 20`, and the open-port section
formula/cycle examples.  It is an audit artifact for the current Route-E
program, not an all-even symbolic theorem.

The open-port section search can also be scanned separately:

```bash
python3 scripts/verify_d5_even_routeE.py --mode section \
  --section-scan-moduli 6,8,10,12,14,16,18,20,22,24,26,28,30 \
  --section-scan-limit 1 \
  --json-out /tmp/d5_even_routeE_section_scan.json
```

To distinguish section-only hits from full one-`Lambda_E` cycles in the
open-port subfamily, add the full scan:

```bash
python3 scripts/verify_d5_even_routeE.py --mode section \
  --full-scan-moduli 6,8,10,12,14,16,18,20 \
  --full-scan-limit 5 \
  --json-out /tmp/d5_even_routeE_open_port_full_scan.json
```

To scan the larger one-`Lambda_E` count/slot family directly:

```bash
python3 scripts/verify_d5_even_routeE.py --mode section \
  --count-scan-moduli 6,8,10,12,14,16 \
  --count-scan-limit 5 \
  --json-out /tmp/d5_even_routeE_count_scan.json
```

The count scan reports both the raw `(slot, counts)` and
`normalized_counts_slot0`, obtained by cyclically rotating the E-slot to `0`.
It also reports the normalized support/zero positions and, when a bundled
finite schedule exists for that modulus, whether a hit matches its normalized
count vector.

The later non-open small-seam bundle can be checked with:

```bash
python3 scripts/verify_d5_even_routeE.py --mode section \
  --small-seam-moduli all \
  --json-out /tmp/d5_even_routeE_small_seam_all.json
```

This verifies the recorded even cases `m = 6,8,...,60`: each first-return map
on the size `m-1` seam is a single cycle and has return-time sum `m^4`.  The
same output includes maximal translation blocks for the induced seam map,
which are the finite traces for the next one-dimensional block-splice proof.
The Lean target also includes `RouteEThetaSmallSeamCertificate`, specialized
to the canonical bundle seam
`Theta_s = {rho_s(0,a,0,0,-a) : a != 0}` via
`routeEThetaSeamPoint`.  It lowers to the more general
`RouteENonopenSmallSeamCertificate` and proves that such a certificate gives
the existing D5 even Hamilton, torus, and Cayley endpoints.
It also fixes the branch combinatorics: a separate
`D5EvenRouteEM4FiniteTarget` plus the all-large Route-E certificate target
implies all even `m >= 4` Hamilton, torus, and Cayley targets.
That finite branch is now closed unconditionally in
`D5Odd/EvenRouteEM4.lean`; the remaining D5 even Route-E obligation is the
all-large symbolic certificate for even `m >= 6`.

The same table can be spot-checked through the standalone C++ verifier:

```bash
python3 - <<'PY' >/tmp/d5_even_routeE_small_seam_cases.tsv
from scripts.verify_d5_even_routeE import SMALL_SEAM_CASES
for m, data in sorted(SMALL_SEAM_CASES.items()):
    print(m, data["slot"], *data["counts"])
PY
g++ -std=c++17 -O2 scripts/fast_d5_routeE_small_seam_verify.cpp \
  -o /tmp/fast_d5_routeE_small_seam_verify
while read -r m slot n0 n1 n2 n3 n4; do
  /tmp/fast_d5_routeE_small_seam_verify "$m" "$slot" "$n0" "$n1" "$n2" "$n3" "$n4" |
    head -1
done < /tmp/d5_even_routeE_small_seam_cases.tsv
```

The finite small-seam table can be scanned for residue-family count formulas:

```bash
python3 scripts/analyze_d5_routeE_small_seam_families.py \
  --json-out /tmp/d5_routeE_small_seam_family_scan.json
```

This is a research aid.  On the current table, simple affine normalized count
vectors fail for tested periods up to `26`; periods `28` and above are too
sparse to give robust family evidence.

The corresponding Lean target interface builds with:

```bash
lake build D5Odd.EvenRouteE
lake build D5Odd.EvenRouteEM4
```

## Citation

If you use this formalization, cite the repository using `CITATION.cff`.

Paper drafts may link to:

```text
https://github.com/aria1th/Torus-Hamilton-Decomposition-Program
```

## Notes

The Python verifier is retained as an audit and illustration tool.  The formal proof artifact is the Lean 4 development.
