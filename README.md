# Torus Hamilton Decomposition Program

Lean 4 formalization and audit artifacts for Hamilton decompositions of directed torus/Cayley digraphs.

The current formalized endpoints include the directed 2-torus seed and the
odd-modulus directed 5-torus and 7-torus constructions.  In particular, the
repository proves:

```lean
theorem Shared.D2.shared_cayley_uniform :
    ∀ {m : Nat}, 3 <= m -> Odd m ->
      Shared.CayleyHamiltonDecomposition 2 m

theorem D5Odd.D5_odd_cayley_unconditional {m : Nat} [NeZero m]
    (hodd : Odd m) (hm3 : 3 <= m) :
    D5Odd.CayleyHamiltonDecompositionD5 m

theorem D7Odd.D7_odd_cayley_unconditional {m : Nat} [NeZero m]
    (hodd : Odd m) (hm3 : 3 <= m) :
    D7Odd.CayleyHamiltonDecompositionD7 m
```

These theorems state explicit Cayley-edge decompositions for
`Cay((ZMod m)^d, {e_0, ..., e_{d-1}})` in dimensions `d = 2, 5, 7`
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
- `D7Odd/Handoff/Additive4Plus2TargetB.lean`: Lean-facing Target-B'
  scalar interface for the A3 fiber engine.  It defines the clock/carry
  equivalence `A3(m) ~= (ZMod m)^2` and proves that a triangular map
  `(s,x) |-> (s+A, x+phi(s))` is a single `m^2` cycle once the clock scalar
  `A`, the full-round carry scalar `E`, and the recorded round return are
  supplied with `A` and `E` units.  It also packages this with the base
  `m^4` rank-step into `BridgeConcreteScalarMonodromyPackage`, lowering the
  scalar Target-B' data to the existing bridge torus/Cayley endpoint adapters.
  The `ZeroSetKappaFamily` and
  `BridgeConcreteZeroSetScalarMonodromyPackage` wrappers specialize this target
  to zero-set-only `K(Z)` tables.
- `D7Odd/Handoff/TargetASeamQuotient.lean`: Lean-facing proof target for
  the `23/32` Target-A seam quotient, defining `phi_h`, its inverse, the
  good class `h % 5 != 3`, proving the inverse identities and bijectivity for
  `h >= 6`, proving the residue-shift unit gate in `ZMod 5`, proving the
  inverse-map residue transition at the top boundary, proving
  `IsSingleCycleMap (phi h) ↔ IsSingleCycleMap (phiInv h)`, and packaging
  the remaining Q-hitting/length-sum obligations.  The seam quotient
  arithmetic package itself is now closed for `h >= 6` via
  `TargetASeamQuotientArithmetic.ofSixLe`; in particular,
  `phi_single_cycle_iff_goodPhiClass` proves
  `IsSingleCycleMap (phi h) ↔ h % 5 != 3`.  Its proof combines the bad-class
  obstruction, the good-class residue cycle
  `r |-> r + (3-h)` on `ZMod 5`, internal `+5` lane traversal for `phiInv`,
  exact low-representative boundary landings, and a lifted residue-path
  composition via the local `Reaches` relation.  The wrapper
  `TargetASeamQuotientRemaining.toPackage` now fills the arithmetic field of
  the older package automatically from `m = 2h+1` and `m >= 13`.  The
  verifier's one-based Q-label return formulas are also named in Lean as
  `targetAQExpected23`, `targetAQExpected32`, and
  `targetAQFirstReturn23Formula`/`targetAQFirstReturn32Formula`, with
  validity lemmas showing that the expected formulas preserve valid Q labels.
  The subtype `QLabel m` and endomap predicates
  `targetAQFirstReturn23EndomapFormula`/`targetAQFirstReturn32EndomapFormula`
  package the same target directly on valid Q labels.  The B-chain and
  A-even/A-odd transition lemmas
  `targetAQExpected23_B_step`, `targetAQExpected23_A_even_step`,
  `targetAQExpected23_A_odd_step`, `targetAQExpected32_B_step`,
  `targetAQExpected32_A_odd_step`, and `targetAQExpected32_A_even_step`
  provide the rewrite layer needed for the eventual expected-Q-map cycle
  proof.  The double-step lemmas
  `targetAQExpected23_A_odd_two_step` and
  `targetAQExpected32_A_odd_two_step` expose the tau/phi lane transitions
  directly.  The B-chain iteration lemmas
  `targetAQExpected23_B_iter`/`targetAQExpected32_B_iter` and the
  `targetAQExpected23_A_five_excursion`/
  `targetAQExpected32_A_six_excursion` theorems isolate the long bridges from
  the exceptional `A 11` state back to `A 1`.  The section-return theorems
  `targetAQExpected23_oddA_return` and `targetAQExpected32_oddA_return` now
  state directly that the expected maps return from odd-A labels by the
  quotient map `phi h`, and `targetAQOddA_valid` prepares the same section for
  the `QLabel m` subtype.
  The subtype theorems `QLabel.expected23_oddA_return` and
  `QLabel.expected32_oddA_return`, together with the raw cover lemmas
  `targetAQExpected23_oddA_cover` and `targetAQExpected32_oddA_cover`,
  provide the return-cover inputs for both expected Q maps.  Consequently
  `QLabel.expected23_single_cycle_of_good` and
  `QLabel.expected32_single_cycle_of_good` prove the `23` and `32` expected Q
  endomaps are single cycles whenever `h % 5 != 3`, and the corresponding
  `targetAQFirstReturn23EndomapFormula.single_cycle_of_good`/
  `targetAQFirstReturn32EndomapFormula.single_cycle_of_good` theorems transfer
  this to any actual first-return endomap satisfying the named formula.  The
  raw verifier-style formulas now also lift automatically through
  `targetAQLift23`/`targetAQLift32`, with
  `targetAQFirstReturn23Formula.lift_single_cycle_of_good` and
  `targetAQFirstReturn32Formula.lift_single_cycle_of_good` as the direct
  adapters from raw valid-label tables.
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
  `routeEThetaPoint`, making the bundle coordinate convention explicit.  The
  `RouteEB20` namespace records the first extracted residue branch
  `m = 24*q+20`: its count vector, count-sum theorem, and weighted
  return-time polynomial identity.  It also records the expected B20 seam map
  as index addition on the nonzero seam, proves the two translation-block
  formulas, packages the corresponding block cover/disjoint/translation
  obligations, and proves that this expected seam map is a single cycle.
  `RouteEB20.ThetaTraceTarget` is the remaining trace-facing B20 proposition:
  once the concrete first-return equations, minimality, and return-time sum
  are supplied, `RouteEB20.thetaPiecewiseCertificateOfTraceTarget` packages
  them as a `RouteEThetaPiecewiseTranslationCertificate`.
  `RouteEB20.returnTimeFormula` and `RouteEB20.ThetaPointwiseTraceTarget`
  specialize that obligation to the six-value pointwise return-time formula
  checked by the B20 verifier, feeding the already-closed weighted-sum
  arithmetic theorem; the `RouteEB20.returnTimeFormula_*` lemmas expose the
  verifier's lower/boundary/upper/last cases as rewrite targets.
  `RouteEB20.returnTimeBlocks` and `RouteEB20.returnTimeBlocks_cover` package
  the same pointwise distribution as interval blocks over the nonzero seam,
  giving the symbolic trace proof a proof-facing case split.  The
  Route-E table `LambdaE` now lives here, with
  `LambdaE_latin` and `LambdaE_cyclic` recording its table invariants, and
  `LambdaE_routeEThetaVec`/`LambdaE_routeEThetaSeam` proving the bundle's
  `start_ok` port statement `p_s(Theta_s(a)) = s+2 mod 5`.  The open-port
  section normal form is also named as `routeEOpenPortSectionPairMap`; the
  chart `routeEOpenPortChart` conjugates it to `routeEOpenPortHMap`, and
  `RouteEOpenPortAffineChartCertificate` lowers a rank-step proof for that
  chart map to a single-cycle section result.  The finite odometer spine
  `routeEOpenPortFinSquareSucc_single_cycle` is available for explicit
  `m^2` chart-rank constructions, and
  `RouteEOpenPortFiniteOdometerCertificate` lets such a finite chart
  equivalence close the section map without first packaging a `ZMod (m^2)`
  rank.  For the uniform verifier triple `(A,B,C)=(0,m-2,1)`, the canonical
  chart is named as `routeEOpenPortCanonicalChartIdx`, with coordinates
  `(i,j)=(-a-s,-1-s)` on the `H(s,a)` chart.  Lean proves the finite carry
  law as `RouteEOpenPortCanonicalChartStepTarget.unconditional` and derives
  `routeEOpenPortCanonicalH_single_cycle` and
  `routeEOpenPortCanonicalSectionPairMap_single_cycle`.
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
- `Shared/D2Seed.lean`: direct D2 phase schedule.  It proves the two color
  returns are translations by `1` and `m - 1`, transfers the root-flat cycle to
  the standard Cayley torus, and exposes `Shared.D2.shared_cayley_uniform`.
- `Shared/D3Seed.lean`: adapter from the D3 odd formalization to the shared
  Cayley endpoint.  It exposes `Shared.D3.shared_cayley_uniform`, which is
  re-exported as the standard D3 odd-uniform seed.
- `RoundComposite/ConcreteEndpoints.lean`: concrete seed endpoints, including
  the D2/D3 seed endpoints and
  `standard_cayley_odd_uniform_all_dimensions_of_odd_core`, which reduces all
  dimensions `d >= 2` to the odd-dimensional core using D2 and product lift.
  The same reduction is exposed under
  `odd_modulus_tori_all_dimensions_uniform_of_odd_core` and
  `odd_modulus_tori_all_dimensions_of_odd_core`.
- `RoundComposite/SeedSemigroup.lean`: seed-semigroup arithmetic for the
  global odd-modulus goal.  It defines `SolvedBySeedSemigroup`, proves that
  every odd `d >= 13` has a seed-semigroup base `b` with
  `2 * b < d <= 3 * b`, and adapts such bases to odd-uniform standard Cayley
  solutions using the closed D2/D3 seeds.  It also provides
  `twoThreeBlockParts_spec`, the arithmetic decomposition of this range into
  `b` blocks of size `2` or `3` for the later base-tail lift, plus
  `unitCarryPacket_spec` for filling each such block by positive unit residues
  summing to `m`, `unitCarryPackets_spec` for the aggregate packet list, and
  `SmallBaseUnitPacketWitness` for packaging the solved base with that packet
  data.
- `RoundComposite/OddCore.lean`: Lean-facing odd-core dispatcher for the new
  global odd-modulus goal.  It closes `d = 3,5,7,9,11` from seeds/composites
  plus a D11 branch hypothesis, reduces all odd `d >= 13` to the high-modulus
  prefix-count branch or small-modulus base-tail branch, and includes the
  adapter from the seed-semigroup base availability lemma to the small branch.
  It also exposes `OddCoreSmallModulusOfUnitPacketsGoal`, a packet-level
  interface for the heavy base-tail theorem, and adapts it back to
  `OddCoreSmallModulusOfBaseGoal`.
  The refined endpoint
  `odd_modulus_tori_all_dimensions_of_refined_branches` leaves only the
  high-modulus prefix-count theorem, the D11-from-D5 small lift, and the
  general base-tail small lift as assumptions.  The companion endpoint
  `odd_modulus_tori_all_dimensions_of_main_lemmas` exposes those same inputs as
  the theorem-shaped goals `OddCoreHighModulusPrefixCountGoal`,
  `D11SmallModulusFromD5BaseGoal`, and `OddCoreSmallModulusOfBaseGoal`.
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
- `RoundComposite.lean`: composite-dimension product reduction from pointwise
  expansion and prime bases, including odd-modulus variants, concrete adapters
  for the shared standard torus/Cayley proposition, and graph-level standard
  Cayley/Torus product expansions.
- `docs/D7_PROGRESS_BLOCKING_FOUND_20260501.md`: current progress, blockers,
  and found facts for the D7 additive `4+2` bridge before the next research
  bundle comparison.
- `docs/PROOF_OBLIGATION_AUDIT_20260502.md`: current goal-to-artifact audit,
  recording which Lean/program artifacts prove which parts of the D7/D5-even
  research goal and which named propositions remain open.
- `docs/CURRENT_FLOW_AND_NEXT_BUNDLE_PLAN_20260502.md`: current-flow note for
  the D7 odd bridge, D5 even Route-E, D7 even root-flat track, proposed goal
  revision, and the concrete shape expected from the next bundle.
- `docs/REVISED_GOAL_20260502.md`: revised proof-program goal after the D7
  exceptional phase-splice and D5 Route-E branch-extraction bundles, splitting
  D7 Target A into good-class, exceptional-splice, and assembly targets and
  D5 even into a finite residue branch-menu program.
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
- `docs/A5_EXCEPTIONAL_PHASE_SPLICE_BUNDLE_V0_4_20260502.md`: absorption note
  for `A5_exceptional_phase_splice_bundle_v0_4.zip`, recording the
  exceptional `m = 10*t+7` five-lane splice system and the `00` correction
  block phase table for D7 Target A.
- `docs/D5_EVEN_ROUTE_E_NONOPEN_SMALL_SEAM_20260501.md`: absorption note for
  `d5_even_routeE_nonopen_small_seam_v0_4.zip`, recording the size `m-1`
  small-seam criterion for non-open one-`Lambda_E` schedules and the verified
  even range `m = 6,8,...,60`.
- `docs/D5_EVEN_ROUTE_E_BRANCH_EXTRACTION_V0_7_20260502.md`: absorption note
  for `d5_even_routeE_branch_extraction_v0_7.zip`, recording the branch/menu
  interpretation of the D5 even Route-E data and the B20 candidate
  `m == 20 mod 24` with counts `(r,0,0,h+r,r)`.
- `docs/TWO_GOAL_RESET_20260502.md`: current two-goal reset, separating the
  D7 odd structural `4+2` proof program from the D5 even Route-E branch-menu
  proof program and listing the blocking propositions for each.
- `docs/D11_AND_A5_A7_LEAN_HANDOFF_PLAN_20260502.md`: side-track Lean plan
  after reading `D11_odd_canonical_schedule_certificate.md` and
  `A5_to_A7_Lean_handoff_bundle_v1_0.zip`, separating the D11 odd canonical
  schedule formalization from the A5-to-A7 structural D7 handoff tasks.
- `docs/D3_A2_BRIDGE_REWRITE_BUNDLE_20260502.md`: absorption note for
  `d3_A2_bridge_rewrite_v0_1.zip`, recording the even D3 Route-E rewrite as
  an `A2`-fiber finite-defect bridge and its implication for a possible
  `D4 -> D5` lane-splice interpretation of D5 even Route-E.
- `docs/D_AGNOSTIC_BASE_TAIL_CERTIFICATE_PROGRAM_20260502.md`:
  legacy dimension-agnostic base-tail certificate/verifier design: reduce large
  `(ZMod m)^(d-1)` cycle checks to small base cycles plus tail carry units,
  with a D11 Lean status audit.  Superseded as the primary D11 route by the
  v2 prefix-count/base-tail Hall-slack manuscript note.
- `docs/D11_ODD_WORKING_CERTIFICATE_NOTE_20260502.md`: working D11 status
  note: treats odd `m >= 11` as a closed non-Lean certificate and records the
  older finite-search plan for `m = 3,5,7,9`; the small-case status is now
  superseded by the v2 base-tail Hall-slack lift from D5.
- `docs/D11_LEAN_HELPER_LEMMA_REQUESTS_20260502.md`: requested Lean helper
  lemma list for D11, covering generic skew-cycle facts, D11 coordinates,
  canonical layer/count arithmetic, triangular return, endpoint packaging, and
  the now-legacy small-case base-tail certificate checker.
- `docs/PREFIX_COUNT_ODD_TORI_OVERHAULED_V2_20260503.md`: absorption note for
  `prefix_count_odd_tori_overhauled_v2_submission_bundle (1).zip`, recording
  the new dimension-generic prefix-count branch, full-vertex base-tail
  Hall-slack lift, D11-from-D5 consequence, eventual odd-dimension corollary,
  and revised Lean formalization backlog.
- `docs/ODD_TORI_GLOBAL_FORMALIZATION_GOAL_20260503.md`: revised primary goal
  after the v2 absorption and D2 seed audit: defer Route E, use D2/D3/D5/D7
  seeds plus prefix-count and base-tail Hall-slack machinery, and target a Lean
  proof for every dimension `d >= 2` and odd modulus `m >= 3`, with even
  dimensions handled by the D2/product wrapper and the main construction
  concentrated in the odd-dimensional core.
- `docs/ODD_TORI_GLOBAL_COMPLETION_AUDIT_20260503.md`: prompt-to-artifact
  completion audit for the global odd-modulus theorem, recording which parts
  are Lean-closed, which are conditional skeletons, and the three remaining
  proof blocks needed to remove all assumptions.
- `docs/ODD_TORI_D_LT_29_BOUNDARY_WITNESSES_20260503.md`: exhaustive finite
  boundary audit table for the global odd-modulus goal, covering all `169`
  pairs with `2 <= d < 29`, odd `m`, and `3 <= m < d` by seed-semigroup
  dimensions or explicit base-tail witnesses.  This table is retained as
  audit/regression evidence, not as the intended main proof spine.
- `docs/GPT55_PRO_ODD_TORI_LEAN_REQUESTS_20260503.md`: high-cost GPT-5.5 Pro
  background requests for the two largest Lean-formalization planning blocks:
  active Hall-slack realization and signed transportation/count branch.
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
  theorem, finite Q-hitting, Q-first-return formulas, and length sums.  Its
  standard regression is pinned by
  `certs/d7_targetA_23_32_seam_quotient_manifest.json`.
- `scripts/verify_targetA_exceptional_phase_splice.py`: verifier for the D7
  Target-A exceptional `m = 10*t+7` phase-splice target, recomputing the
  `00` correction-block action from A5 state dynamics and checking it against
  the five-lane symbolic table for `H = 23` and `H = 32`.
- `scripts/search_targetA_primitive_words.cpp`: faster C++ primitive-word
  search for Target-A exceptional moduli where the Python exhaustive scan is
  too slow.
- `scripts/search_targetA_balanced_covers.py`: balanced Target-A row-family
  search over a primitive-word pool, accepting C++ `HIT ... word=...` output,
  enforcing aggregate slot counts `(m,m,m,m,m)`, then calling the column
  exact-cover placer.  It can also report balanced count-vector combinations
  separately from column placement.
- `scripts/search_4plus2_kappa_formulas.py`: fiber-compiler search aid for zero-set cyclic/reflected kappa formulas of the form `a*t + b*p(Z) + c*|Z| + d mod 3`, a larger dihedral `rotation mod 3 + reflection mod 2` family, and dependency diagnostics for bundled or generated kappa tables.
- `scripts/fast_4plus2_section_formula_search.cpp`: standalone C++ checker for
  generated full row covers and rotation-family Target-B' formulas.  It
  verifies the base/section criterion quickly and can also replay the direct
  product-return single-cycle check for larger finite witnesses such as
  `m = 17`.
- `scripts/verify_compact_4plus2_formula_certs.py`: verifier wrapper for the
  compact generated `m = 11,13,17` formula certificates in
  `certs/d7_4plus2_compact_formula_witnesses.json`.  It validates row/base
  shape, can rerun the Target-A section and column audits, and delegates
  formula/product/rank-step fingerprint checks to the C++ checker.
- `certs/d7_m9_zero_set_K_full_bridge_cert.json`: full `m = 9` Target-B'
  zero-set-only bridge certificate with the expanded `kappa_perm_indices`
  table.  It is the repo-local copy of the handoff `K(Z)` certificate and is
  verified by `scripts/verify_4plus2_allN_bridge_cert.py`.
- `certs/d7_m9_zero_set_K_scalar_cert.json`: compact `m = 9` Target-B'
  zero-set-only `K(Z)` scalar certificate, storing the mask table, row
  schedule, and scalar invariants used by `verify_zero_set_k_cert.py`.
- `certs/d7_m9_zero_set_K_triangular_obligations.json`: compact Target-B'
  manifest of the `A`, `E`, and `phi(s)` triangular data extracted from the
  `m = 9` scalar certificate.
- `scripts/verify_d7_4plus2_rank_fingerprints.py`: regression verifier for
  `certs/d7_4plus2_rank_fingerprints.json`; it recomputes compact D7 odd
  base/fiber rank-step fingerprints and compares them to the committed
  manifest, with optional Target-A and direct product checks.
- `scripts/verify_zero_set_k_cert.py`: Target-B' verifier for zero-set-only
  `K(Z)` certificates; it expands mask tables into full kappa tables, checks
  any provided full `kappa_perm_indices` table against that expansion, checks
  scalar unit invariants when present, extracts the triangular A3 `phi(s)`
  tables, verifies the Lean-facing `roundAtZero` equations, and can run the
  full bridge verifier.
- `scripts/d7_bridge_snapshot.py`: compact JSON snapshot tool for bridge bundles or extracted certificate JSON files, used to compare new research bundles against the current baseline.
- `scripts/d5_even_seam_sat_search.py`: SAT witness search for the D5 even seam certificate target.
- `scripts/verify_d5_even_routeE.py`: audit verifier for the absorbed D5 even
  Route-E bundle, checking the finite schedule table, normalized core
  first-return formula, open-port section formula/cycle examples, and the
  non-open small-seam criterion from the later small-seam bundle.
- `certs/d5_routeE_open_port_manifest.json`: compact D5 Route-E open-port
  regression manifest.  It records the uniform section affine chart through
  `m = 60` and the full-return scan through `m = 20`, including the expected
  open-port full failures at `m = 6,8,16`.
- `certs/d5_routeE_small_seam_family_scan_manifest.json`: compact D5 Route-E
  small-seam residue-family scan manifest.  It records that the current
  `m = 6,8,...,60` table does not yet support a robust simple affine
  normalized count family for the tested periods.
- `scripts/verify_d5_routeE_nonopen_bundle.py`: bundle-consistency checker for
  `d5_even_routeE_nonopen_small_seam_v0_4.zip`.  It compares the source TSV
  to the repo's `SMALL_SEAM_CASES`, parses the bundle verifier transcript,
  and recomputes the small-seam criterion with the repo Python verifier.
- `scripts/fast_d5_routeE_small_seam_verify.cpp`: standalone C++ verifier for
  one recorded D5 Route-E small-seam case, kept as an independent check of the
  `m-1` seam criterion.
- `scripts/summarize_d5_routeE_small_seam_blocks.py`: proof-facing summary of
  the D5 Route-E small-seam first-return maps, compressing the verifier's
  translation blocks into block-count, long-block, piecewise-translation, and
  fingerprint diagnostics.
- `scripts/verify_d5_routeE_b20_branch.py`: verifier for the extracted D5
  Route-E B20 branch `m == 20 mod 24`, checking the count formula, two-block
  `Theta_0` seam map, pointwise return-time partition, and return-time sum for
  selected moduli.
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
  --manifest certs/d7_targetA_23_32_seam_quotient_manifest.json \
  --json-out /tmp/d7_targetA_23_32_seam_quotient.json
```

The verifier also records the inverse-map explanation for the arithmetic:
`phi_h^{-1}` walks by `+5` inside residue classes and crosses the top boundary
with residue shift `3-h mod 5`.  The Lean target now proves the full seam
quotient cycle criterion as `phi_single_cycle_iff_goodPhiClass`.

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
The same script can now test column placements for a bounded number of
balanced count-vector combinations without running the full multiset search:

```bash
python3 scripts/search_targetA_balanced_covers.py \
  --m 11 --word-file /tmp/targetA_m11_primitive_words_len11.txt \
  --lengths 7,8,8,8,8,8,8 \
  --combo-limit 0 --count-vector-limit 3 \
  --count-vector-placement-start 0 \
  --count-vector-placement-limit 50 --count-vector-product-limit 5000 \
  --json-out /tmp/targetA_m11_count_vector_placement_diag.json
```

The `--count-vector-placement-start` option lets the same check run in
windows.  On the current temporary pool, the windows `0..50`, `50..100`,
`100..150`, and `150..200` reject all first 200 balanced vector combos at the
first-symbol mask gate, before any concrete word product or deeper DP is
entered.
For pools that are closed under cyclic rotations, the same diagnostic can
sample representatives by first symbol:

```bash
python3 scripts/search_targetA_balanced_covers.py \
  --m 11 --word-file /tmp/targetA_m11_primitive_words_len11.txt \
  --cyclic-rotations \
  --lengths 7,8,8,8,8,8,8 \
  --combo-limit 0 \
  --count-vector-placement-start 0 \
  --count-vector-placement-limit 5 \
  --count-vector-product-limit 100000 \
  --count-vector-representatives-per-symbol 1 \
  --json-out /tmp/targetA_m11_rot_symbol1_0_5.json
```

This finds column exact-cover diagnostics for the first `m = 11` vector combo;
one resulting base-word set is
`2434343,43033334,33342440,01241242,01110212,10212011,42020010`.  Each word
passes the Target-A section audit at `m = 11`, and the seven words have a
column exact cover.  This is finite evidence for the Target-A row-family
search, not an all-odd symbolic family.
The resulting cover JSON can be fed directly into the kappa formula search,
even though `m = 11` is not part of the original bundle:

```bash
python3 scripts/search_4plus2_kappa_formulas.py \
  --cover-json /tmp/targetA_m11_rot_symbol1_solution0_cover_diag.json \
  --allow-cover-dummy-kappa \
  --max-cover-solutions 1 \
  --formula-family rotation --section-only \
  --json-out /tmp/targetA_m11_cover_json_rotation_section_formula_search.json
```

For the cover above, this finds the zero-set-derived rotation formula
`r = p(Z) + |Z| + 1 mod 3`.  Emitting that hit as a full certificate and
checking it with `scripts/verify_4plus2_allN_bridge_cert.py` verifies
`11^6 = 1771561` product states with single color-return cycles.
The same pipeline now also has a finite `m = 13` witness.  One base-word set is
`14244442,312324442,312231334,423021000,2041033232,0041011111,4230300013`;
the fiber formula is the simpler `r = |Z| mod 3`, and the full verifier checks
`13^6 = 4826809` product states.
The next exceptional modulus also now has a finite witness.  For `m = 17`, one
Target-A base-word set is
`10431414033,322442322442,101121101121,432300432300,230400230400,0412223123234,0113344041341`;
the C++ section checker finds the first rotation-family hit
`r = 2|Z| + 1 mod 3` and verifies `17^6 = 24137569` product states.  This is
finite evidence for the bridge pipeline, not yet a symbolic all-odd row family.
The generated `m = 11,13,17` witnesses are also committed in compact form and
can be replayed with:

```bash
python3 scripts/verify_compact_4plus2_formula_certs.py --target-a --product \
  --rank-summary-dir /tmp/d7_compact_rank_summaries \
  --json-out /tmp/d7_compact_formula_full_verify.json
```

The committed rank-fingerprint manifest can be replayed directly:

```bash
python3 scripts/verify_d7_4plus2_rank_fingerprints.py \
  --target-a --product \
  --json-out /tmp/d7_4plus2_rank_fingerprint_full_verify.json
```

For fixed word sets, `scripts/analyze_4plus2_base_rows.py --diagnose-cover`
now reports exact-cover DP depth, reachable/dead states, and dead-frontier
examples.

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
  --cert-json certs/d7_m9_zero_set_K_full_bridge_cert.json
python3 scripts/search_4plus2_kappa_formulas.py \
  --cert-json certs/d7_m9_zero_set_K_full_bridge_cert.json \
  --diagnostics-only --diagnostic-profile all --section-trace-diagnostics \
  --json-out /tmp/d7_m9_zero_set_K_diag.json
python3 scripts/d7_bridge_snapshot.py \
  --cert-json certs/d7_m9_zero_set_K_full_bridge_cert.json \
  --include-full-verify --include-section-trace \
  --json-out /tmp/d7_m9_zero_set_K_snapshot.json
```

The snapshot records whether a certificate-provided `K(Z)` table matches the
shifted zero-set mask encoding used by the finite kappa table.

For zero-set `K(Z)` certificates, check the full-table expansion and the A3
unit invariants plus triangular Lean obligations directly:

```bash
python3 scripts/verify_zero_set_k_cert.py \
  certs/d7_m9_zero_set_K_full_bridge_cert.json \
  certs/d7_m9_zero_set_K_scalar_cert.json \
  --allow-missing-scalar \
  --json-out /tmp/d7_m9_zero_set_K_full_and_scalar_verify.json
python3 scripts/verify_zero_set_k_cert.py \
  certs/d7_m9_zero_set_K_scalar_cert.json \
  --triangular-manifest certs/d7_m9_zero_set_K_triangular_obligations.json \
  --json-out /tmp/d7_m9_zero_set_K_scalar_verify.json
```

For the current `m = 9` scalar certificate this reports
`scalar_ok=True`, `triangular_ok=True`, `table_ok=True`,
`provided_kappa=absent`, `triangular_manifest_ok=True`,
`expanded_valid=True`, and `full_ok=True`; the JSON includes the per-color
`A`, `E`, and `phi(s)` data matching
`A3TriangularScalarCertificate`.

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
The corresponding Lean interface records the section formula as
`routeEOpenPortChart_sectionPairMap`: under `A+B+C+1=0`, the open-port
section-pair map is conjugate by `(a,b) |-> (a+b,a)` to
`H(sigma,a)=(sigma-C, a+A+1-1_{sigma=0})`.  A future affine/rank formula for
this chart map can be supplied through `RouteEOpenPortAffineChartCertificate`.

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

The pinned open-port regression combines the section scan through `m = 60`
with the full-return scan through `m = 20`:

```bash
python3 scripts/verify_d5_even_routeE.py --mode section \
  --section-scan-moduli 6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,50,52,54,56,58,60 \
  --section-scan-limit 1 \
  --full-scan-moduli 6,8,10,12,14,16,18,20 \
  --full-scan-limit 1 \
  --manifest certs/d5_routeE_open_port_manifest.json \
  --json-out /tmp/d5_routeE_open_port_manifest_verify.json
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
python3 scripts/verify_d5_routeE_nonopen_bundle.py \
  /data/angel/repos/etc/d5_even_routeE_nonopen_small_seam_v0_4.zip \
  --json-out /tmp/d5_routeE_nonopen_bundle_check.json

python3 scripts/verify_d5_even_routeE.py --mode section \
  --small-seam-moduli all \
  --json-out /tmp/d5_even_routeE_small_seam_all.json
```

The first command verifies that the source bundle's TSV, its verifier
transcript, and the repo's embedded `SMALL_SEAM_CASES` all describe the same
`28` cases.  The second recomputes the recorded even cases `m = 6,8,...,60`:
each first-return map on the size `m-1` seam is a single cycle and has
return-time sum `m^4`.  The same output includes maximal translation blocks
for the induced seam map, which are the finite traces for the next
one-dimensional block-splice proof.
The Lean target also includes `RouteEThetaSmallSeamCertificate`, specialized
to the canonical bundle seam
`Theta_s = {rho_s(0,a,0,0,-a) : a != 0}` via
`routeEThetaSeamPoint`.  The named lemmas
`routeEThetaVec_port_zero`, `routeEThetaVec_pos_param`,
`routeEThetaVec_neg_param`, and `LambdaE_routeEThetaSeam` record the exact
coordinate and port facts used by the verifier's `start_ok` check.  It lowers
to the more general
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
  --manifest certs/d5_routeE_small_seam_family_scan_manifest.json \
  --json-out /tmp/d5_routeE_small_seam_family_scan.json
```

This is a research aid.  On the current table, simple affine normalized count
vectors fail for tested periods up to `26`; periods `28` and `30` are too
sparse to give robust family evidence.  The manifest check should print
`manifest_ok True mismatches []`.

The same analyzer can also summarize prefix hits from a full one-`Lambda_E`
count/slot scan:

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

For `m = 6,8,10,12`, the recorded witness appears in the prefix hits, but so
do alternative normalized count vectors.  The `m = 10,12` prefixes even
include open-port normal forms.  This means the finite table should be treated
as a validated small-seam evidence set, not as a canonical residue-family
formula to extrapolate.  With `--score-count-scan-small-seam`, the analyzer
also reruns the small-seam block verifier on each distinct normalized prefix
hit and reports the best candidates under three objectives: minimum block
count, open-port first, and low support.  These objectives can diverge, so the
next uniform-family search should choose one explicitly before trying to fit
residue formulas.

The same small-seam verifier output can be compressed into one-dimensional
translation-block diagnostics:

```bash
python3 scripts/summarize_d5_routeE_small_seam_blocks.py \
  --json-out /tmp/d5_routeE_small_seam_block_summary.json
```

On the recorded `m = 6,8,...,60` cases, this reports `all_ok=True` and
`return_sums_ok=True`.  Low block-count cases are
`m = 6,8,10,44,48,50`; long-block cases are `m = 6,8,36,44,48,50`.  These are
finite trace targets for the next block-splice proof, not an all-even formula.
Clustering the same data by normalized zero/support positions finds no robust
sample-count-at-least-three affine count family.

The finite ranked block certs can be regenerated and checked with:

```bash
python3 scripts/verify_d5_routeE_small_seam_rank_certs.py \
  --cert certs/d5_routeE_small_seam_rank_certs.json \
  --json-out /tmp/d5_routeE_small_seam_rank_cert_verify.json
```

This verifies the recorded rank arrays, inverse rank arrays, maximal
translation blocks, and return-time sums for all `28` small-seam cases.

Candidate families can now be searched directly against the small-seam
criterion, without replaying a full `m^4` state-cycle scan:

```bash
python3 scripts/search_d5_routeE_small_seam_candidates.py \
  --mode open-port \
  --moduli 6,8,10,12,14,16,18,20 \
  --hit-limit 2 \
  --json-out /tmp/d5_open_port_small_seam_search_6_20.json

python3 scripts/search_d5_routeE_small_seam_candidates.py \
  --mode support \
  --max-support 3 \
  --moduli 6,8,10,12,14,16 \
  --hit-limit 3 \
  --json-out /tmp/d5_support3_small_seam_search_6_16.json

python3 scripts/search_d5_routeE_small_seam_candidates.py \
  --mode support \
  --max-support 3 \
  --support-pattern 0,1,3 \
  --moduli 14,16,18,20,22,24 \
  --hit-limit 0 \
  --json-out /tmp/d5_support013_small_seam_search_14_24.json
```

The open-port search first checks the `m^2` section formula/cycle and then
checks the `Theta` small seam.  It confirms open-port small-seam hits at
`m = 10,12,14,18,20` and no hit in that search at `m = 6,8,16`.  The
support-limited search finds low-support alternatives, including the
early support-3 candidates `(1,3,0,9,0)` at `m = 14`,
`(5,7,0,5,0)` at `m = 18`, and `(3,1,0,17,0)` at `m = 22`.  Wide ranges
should be run with care because failed candidates can still require long
first-return searches.  For exploratory scans, `--max-return-steps` or
`--max-return-m3-factor` can cap each seam point's first-return search; capped
results are heuristic and should be rechecked without the cap before being
used as proof evidence.
The `--support-pattern 0,1,3` search targets vectors of the form
`(a,b,0,c,0)`.  It now gives a concrete low-support route through
`m = 14,16,...,30`, with full-shape min-block examples
`(1,3,0,9,0)`, `(1,13,0,1,0)`, `(5,7,0,5,0)`,
`(3,13,0,3,0)`, `(11,3,0,7,0)`, `(5,13,0,5,0)`,
`(13,5,0,7,0)`, `(3,5,0,19,0)`, and `(11,7,0,11,0)`.
This is still finite evidence, but it is a much sharper candidate family than
the arbitrary recorded small-seam table.

`D5Odd/EvenRouteE.lean` also exposes these trace summaries as a Lean-facing
piecewise translation interface: `RouteESeamTranslationBlock`,
`RouteEThetaPiecewiseTranslationCertificate`, and the all-large target
`D5EvenRouteEThetaPiecewiseAllLargeEvenTarget`.  This currently packages
block cover/disjointness and interval translation formulas on top of
`RouteEThetaSmallSeamCertificate`; it does not yet derive the one-cycle or
return-time sum hypotheses from the block decomposition alone.  The named
target is still useful because a future block-splice proof can lower
immediately to the existing D5 even Hamilton, torus, and Cayley endpoints.
There is now also a ranked variant,
`RouteEThetaRankedSmallSeamCertificate`, which replaces the assumed seam
one-cycle proof by a bijective rank
`RouteENonzeroSeam m -> ZMod (m-1)` with rank step `+1`.  The combined
`RouteEThetaRankedPiecewiseTranslationCertificate` is the preferred endpoint
for a symbolic block-splice proof: prove block translations, a seam rank
formula, and the return-time sum, then Lean derives the seam cycle and lowers
to the same endpoints.  Since the finite `m=4` Route-E branch is closed,
`D5Odd/EvenRouteEM4.lean` also provides unconditional adapters from the
ranked, piecewise, and ranked-piecewise all-large targets to the all-even
Hamilton, torus, and Cayley targets.
For the separate open-port branch, `RouteEOpenPortAffineChartCertificate`
packages the smaller `m^2` section map.  This is useful as a checked
intermediate normal form, but it does not replace the still-needed full
one-`Lambda_E` return proof on the D5 even state space.
The supporting finite odometer lemma `routeEOpenPortFinSquareSucc_single_cycle`
closes the base-`m` successor on `Fin m x Fin m`, which is the intended target
for an explicit open-port chart rank.
The alternate certificate shape `RouteEOpenPortFiniteOdometerCertificate`
therefore accepts a chart equivalence to this finite odometer plus a step law,
then derives both the `H`-map cycle and the original section-pair cycle.
For the uniform open-port triple `(A,B,C)=(0,m-2,1)`, Lean now fixes the
candidate odometer chart
`routeEOpenPortCanonicalChartIdx(s,a)=(-a-s,-1-s)`.  The carry law is closed as
`RouteEOpenPortCanonicalChartStepTarget.unconditional`, giving the theorem
`routeEOpenPortCanonicalH_single_cycle` and the corresponding section-pair
cycle `routeEOpenPortCanonicalSectionPairMap_single_cycle` for `B=-2`, i.e.
`m-2` in `ZMod m`.

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
