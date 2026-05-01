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
- `D7Odd/Handoff/Additive4Plus2ConcreteGoal.lean`: concrete all-zero-set bridge target: once row permutations, D3 fiber-layer/permutation data, a base-return rank step into `ZMod (m^4)`, and a fiber-monodromy rank step into `ZMod (m^2)` are supplied for the canonical folded return, the local row/layer facts, folded-return bijectivity, product-return equality, base orbit coverage, and monodromy single-cycle are filled in automatically and the odd D7 endpoint follows.
- `D7Odd/Torus.lean`: lift from root-flat D7 certificates to full torus color cycles.
- `D7Odd/Cayley.lean`: final D7 Cayley-edge wrapper and theorem.
- `D7Odd/Even.lean`: even-modulus D7 certificate targets via the
  `RootFlatSchedule` interface, with adapters to the shared layered lift and
  torus/Cayley wrappers.
- `D5Odd/Even.lean`: even-modulus D5 seam certificate target and torus/Cayley wrappers.
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
- `docs/D7_ODD_SPECIAL_THEOREM_REQUESTS.md`: D7 handoff/proof-status notes.
- `scripts/d5_odd_paper_verify.py`: audit-only Python verifier used for independent sanity checks.
- `scripts/verify_4plus2_allN_bridge_cert.py`: audit verifier for the bundled `m=5,7,9` all-zero-set `4+2` bridge certificates, including canonical base `m^4` and fiber-section `m^2` rank-step checks plus product `m^6` cycle checks.
- `scripts/analyze_4plus2_base_rows.py`: base-only search aid for the all-zero-set `4+2` bridge; it summarizes bundled row projections and scans short primitive A5 base words.
- `scripts/d5_even_seam_sat_search.py`: SAT witness search for the D5 even seam certificate target.
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

It can also try bounded exact-cover assembly from the primitive-word pool:

```bash
python3 scripts/analyze_4plus2_base_rows.py \
  --cover-primitive-m 5 --cover-primitive-max-len 5 \
  --cover-lengths 5,4,5,4,3,2,2 \
  --cover-pool-limit 200 --combo-limit 300000 \
  --test-with-bundled-kappa \
  --json-out /tmp/d7_4plus2_base_pool_search.json
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

## Citation

If you use this formalization, cite the repository using `CITATION.cff`.

Paper drafts may link to:

```text
https://github.com/aria1th/Torus-Hamilton-Decomposition-Program
```

## Notes

The Python verifier is retained as an audit and illustration tool.  The formal proof artifact is the Lean 4 development.
