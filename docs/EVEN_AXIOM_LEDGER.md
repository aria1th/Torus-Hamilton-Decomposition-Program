# Even-modulus axiom ledger

Recorded with `#print axioms` on the pinned toolchain (docs/EVEN_LOCK.md).
"standard" = `propext`, `Classical.choice`, `Quot.sound`.  Every `native_decide`
entry is a `Lean.ofReduceBool`-style trusted finite leaf and is listed by name.

Rechecked on 2026-09-11 using the existing compiled artifacts at source commit
`83064463d40a889ad30f1ce896a5ede1a5256fd9`; this was not a clean rebuild.
The D3 count below is corrected from 16 to **14** (1 + 5 + 1 + 7), so the current
conditional even endpoint has **18** native axioms, including the four D5(4)
leaves. See the [raw output](/fsx/angel/operations/torus-lean-preparation-20260911/endpoint-audit.log)
and [preparation note](LEAN_PREPARATION_20260911.md).

## 2026-09-10 (E0/E1 closed; E2-E5 open)

| Lean name | Status | Axioms |
|---|---|---|
| `TorusEven.even_two_pow_dimensions` (D_{2^k}(m), even m ≥ 4, k ≥ 1) | unconditional | standard only |
| `TorusEven.d5_even_four` (D_5(4)) | unconditional | standard + 4 native leaves: `D5Odd.m4RouteESchedule_exact`, `D5Odd.m4RouteESchedule_latin`, `D5Odd.m4RankZ_step`, `D5Odd.m4RankZ_bijective` |
| `TorusEven.even_modulus_tori_all_dimensions_of_successor` | conditional on `D3EvenGoal`, `D5EvenLargeGoal`, `D7EvenGoal`, `EvenSuccessorGoal` | standard + the same 4 leaves |
| `TorusEven.even_modulus_tori_all_dimensions_of_collar` | conditional on `D3EvenGoal`, `D5EvenLargeGoal`, `EvenOddDegreeGoal` | standard + the same 4 leaves |
| `RoundComposite.Concrete.odd_modulus_tori_all_dimensions_v75` (odd baseline, unchanged) | unconditional | standard + 88 native leaves (D5Odd, D7Odd.Handoff, RoundComposite.PrefixCount) |

The odd baseline was rebuilt on the restructured tree (Route E files moved to
`TorusEvenAttic`) and its axiom set is unchanged from the `0.0.3-allodd` audit.

## 2026-09-10 (E2 closed: `D3EvenGoal`)

| Lean name | Status | Axioms |
|---|---|---|
| `TorusEven.d3_even_four` (D_3(4)) | unconditional | standard only (kernel `decide`) |
| `TorusEven.d3_even_of_six_le` (D_3(m), even m ≥ 6, Route E) | unconditional | standard + 14 native leaves, all in `TorusD3Even/Color2.lean`: `firstReturn_four_m6`, `hfirst_four_m6` (5), `firstReturn_six_m8`, `hfirst_six_m8` (7) — finite first-return checks at `m = 6, 8` |
| `TorusEven.d3_even : D3EvenGoal` | unconditional | union of the two rows above |
| `TorusEven.even_dimension_nine` (D_9(m), even m ≥ 4) | unconditional | same as `d3_even` |
| `TorusEven.even_modulus_tori_all_dimensions_of_collar` | conditional on `D5EvenLargeGoal`, `EvenOddDegreeGoal` | standard + 4 (D_5(4)) + 14 (D_3) native leaves |

Note: the Lean `D_3` witness is the Route E construction of arXiv:2603.24708, not the
manuscript's anchored cyclic-star (`prop:anchor`). Both prove the same statement; the
anchored version is still needed for E5 (agreement at the four anchor vertices).

Manuscript ↔ Lean correspondence for the open goals is in `TorusEven/Goals.lean`.

## 2026-09-10 (E3 closed: `D5EvenLargeGoal`)

| Lean name | Status | Axioms |
|---|---|---|
| `TorusEven.d5_even_large : D5EvenLargeGoal` (D_5(m), even m ≥ 6, chronological transversal route) | unconditional | standard only (no native leaf; the integer certificates are kernel `decide`/`simp` on `LatticeData.lean`) |
| `TorusEven.d5_even_uniform` / `even_dimension_five` (D_5(m), even m ≥ 4) | unconditional | standard + the 4 D_5(4) leaves |
| `TorusEven.even_dimension_ten` (D_10(m), even m ≥ 4) | unconditional | same as `even_dimension_five` |
| `TorusEven.even_dimension_fifteen` (D_15(m), even m ≥ 4) | unconditional | standard + 4 (D_5(4)) + 14 (D_3) native leaves |
| `TorusEven.even_modulus_tori_all_dimensions_of_successor` | conditional on `D7EvenGoal`, `EvenSuccessorGoal` | standard + 4 + 14 native leaves |
| `TorusEven.even_modulus_tori_all_dimensions_of_collar` | conditional on `EvenOddDegreeGoal` | standard + 4 + 14 native leaves |

Route (files under `TorusEven/D5/`): `Chart` (root-flat chart of `D_5(m)`), `Schedule`
(the ω-rule schedule, hash-checked against the Python checker at m = 6, 8), `Layers`,
`Certificates`/`LatticeData`/`Lattice` (integer complement certificates), `Stage`/`Preterminal`
(chronological stages: colours 0, 2 return as single cycles), `FirstReturn`/`Terminal`
(source surgery, abstract terminal splice), `Endpoint`/`Endpoint1`/`Endpoint2` (the three
terminal planes: supports `B_i`, partners `N_i`, the explicit `2m`-cycles of `N_i ∘ j_i`,
evenness of `m` used in the parity ranges of `pos_i`), `Terminal1`/`Terminal3`/`Terminal4`
(colours 1, 3, 4), `D5.lean` (assembly through `Chart.cayley_of_rootFlat`).

## 2026-09-11 (E4 partial: relative lifts, physical splits, incidence parity)

Built with `lake build TorusEven` on the CPU node and checked using
[CollarAudit.lean](/fsx/angel/operations/torus-lean-preparation-20260911/CollarAudit.lean).
All 19 new declarations in that audit use standard axioms only; there are no new native leaves.
The [raw output](/fsx/angel/operations/torus-lean-preparation-20260911/collar-axioms.log)
also rechecks the existing conditional endpoint, whose 18 native axioms are unchanged.

| Lean name (namespace prefixes as shown) | Result | Axioms |
|---|---|---|
| `TorusEven.Surgery.patch_circuitCount` | return-circuit count plus the unhit-circuit term | standard only |
| `TorusEven.Collar.oneGap` | additive first return, exact roofs, renewal | standard only |
| `TorusEven.Collar.relative_transport`, `relative_transport_hamilton` | circuit count and Hamiltonicity under source surgery | standard only |
| `TorusEven.Collar.FibreGap.lift_preserves` | renewal from pinning and unit carry | standard only |
| `TorusEven.Collar.MultitorusFactorization.split`, `split_excess`, `split_circuitCount` | physical splitting, exact excess decrease, circuit correspondence | standard only |
| `TorusEven.Collar.MultitorusFactorization.toCayleyOfUnitWidths` | terminal factorization adapter | standard only |
| `TorusEven.Collar.Incidence.evenComponents_of_coherent_odd_columns`, `evenComponents_copied` | selected-child counting lemma and unsplit partition preservation | standard only |

These are component lemmas, with their stated selection/unit/coherence hypotheses.
At this audit, pinned selection and complete collar state induction were still open.
Pinned selection is closed by the following entry; see the current
[implementation boundary](COLLAR_PROGRESS_20260911.md).

## 2026-09-11 (E4: pinned coherent selection proved)

`pinnedSelection_iff` proves both directions of manuscript `thm:pinned`, with all
columns included, exact half quotas, residues ±1, row-zero pinning, and coherence
of each nonterminal child. The existence proof constructs its selection from
component parity and the one-active-column condition.

| Lean name (under `TorusEven.Collar`) | Result | Axioms |
|---|---|---|
| `Incidence.exists_parity_join` | even block degrees and odd column degrees | standard only |
| `Multigraph.exists_odd_orientation` | signed divergence ±1, preserving edge identities | standard only |
| `Incidence.exists_directed_pairs` | disjoint local pairs with column divergence ±1 | standard only |
| `LocalPairs.exists_fillers`, `exists_event_bits`, `coherent_row`, `sum_rows` | quota, pinning, coherence, and modular sum construction | standard only |
| `Incidence.exists_pinnedSelection`, `pinnedSelection_iff` | complete pinned selection theorem | standard only |
| `Incidence.IsPinnedSelection.selected_evenComponents`, `complement_evenComponents` | parity for both nonterminal children at the row level | standard only |

CPU `lake build TorusEven` and isolation checks passed. All 18 new declarations in
[SelectorAudit.lean](/fsx/angel/operations/torus-lean-selector-20260911/SelectorAudit.lean)
use only `propext`, `Classical.choice`, and `Quot.sound`; the existing global
conditional endpoint retains its same 18 native axioms. See the
[raw audit](/fsx/angel/operations/torus-lean-selector-20260911/axioms.log).

At this selector audit, full relative collar state assembly and excess induction
were still open. They are closed by the following entry; E5 anchored entry remains open.

## 2026-09-11 (E4 closed: relative collar closure and every even dimension)

The source selector now supplies the physical split's quota, unit carry, pinning,
and full-column parity. `RelativeCollarState.exists_split` constructs a balanced
split preserving all state fields and every valid active recolouring's colourwise
circuit counts. Excess induction supplies an explicit `SplitResolution` with
exactly `d − |I|` splits and transports a Hamilton recolouring to the Cayley endpoint.

| Lean name (under `TorusEven.Collar`, except the final two rows) | Result | Axioms |
|---|---|---|
| `sourceSelection_orbit_sum`, `sourceSelection_unit` | row-column totals equal actual orbit voltage sums; each carry is a unit | standard only |
| `splitCircuitEquiv`, `BlockSelection.childSupport_mem`, `BlockSelection.parity` | physical circuit correspondence and all child incidence conditions | standard only |
| `RelativeCollarState.selection`, `split`, `transport` | selection exists, the full state renews, marked surgery preserves counts | standard only |
| `Recolouring.factorization`, `lift`, `lift_circuitCount` | valid head routing and quotas, colourwise count preservation | standard only |
| `RelativeCollarState.exists_split` | relative splitting theorem, uniform over valid recolourings | standard only |
| `RelativeCollarState.resolution`, `hamilton_decomposition` | exact split count and Hamilton endpoint by excess induction | standard only |
| `OneDirection.state` | empty-active one-coordinate seed with d circuit columns | standard only |
| `TorusEven.even_degree_collar : EvenDegreeCollarGoal` | every even d≥2, even m≥4, with no odd-degree hypothesis | standard only |
| `TorusEven.even_modulus_tori_all_dimensions_of_collar` | still conditional on `EvenOddDegreeGoal`; uses collar directly for even d | standard + the same 18 native leaves |

CPU `lake build TorusEven` passed, with no new Collar linter warnings. All 24
declarations in [ClosureAudit.lean](/fsx/angel/operations/torus-lean-closure-20260911/ClosureAudit.lean)
use standard axioms only. The existing global conditional endpoint retains its
18 native axioms from D3 and D5(4); the new even-degree theorem uses none of them.
See the [raw audit](/fsx/angel/operations/torus-lean-closure-20260911/axioms.log) and
[verification manifest](/fsx/angel/operations/torus-lean-closure-20260911/verification.json).

The remaining manuscript obligation is E5: anchored entry for odd d≥7.

## 2026-09-11 (E5 partial: near-core, four anchors, entry interface)

The complete near-core lemma is now proved: the displayed directions define a
factorization, colours 0 and 1 are Hamilton, and colour 2 has exactly two circuits
of length m³/2 distinguished by the manuscript's defect expression. Fixed (h,w)
blocks are circuit-consistent in both the y-fibre and x-row charts.

| Lean name | Result | Axioms |
|---|---|---|
| `TorusEven.Entry.NearCore.factorization`, `hamilton`, `circuitCount` | physical near-core and exact colourwise circuit inventory | standard only |
| `TorusEven.Entry.NearCore.orbit_defect_iff`, `orbit_card_two` | exact defect classes and lengths | standard only |
| `TorusEven.Entry.anchor_agreement`, `anchorEquiv` | four-anchor agreement and bijection with actual circuit columns | standard only |
| `TorusEven.Entry.anchorVoltage_single`, `anchorVoltage_unit`, `anchorVoltage_gapSupport` | one selected source on each active circuit, outside the replacement support | standard only |
| `TorusEven.Collar.Recolouring.ofReplacement`, `split_circuitCount` | replacement adapter and first-split transport | standard only |
| `TorusEven.Collar.BlockSelection.enters_collar`, `hamilton_decomposition_of_entry` | entry-to-closure implication with explicit selection and replacement inputs | standard only |

CPU `lake build TorusEven` passed (8432 jobs); isolation passed with 74 main-path
files. The 39 new declarations in
[EntryAudit.lean](/fsx/angel/operations/torus-lean-entry-20260911/EntryAudit.lean)
use standard axioms only. The existing even-degree theorem remains standard-only,
and the conditional global endpoint retains the same 18 native leaves. See the
[raw audit](/fsx/angel/operations/torus-lean-entry-20260911/axioms.log) and
[entry boundary](ENTRY_PROGRESS_20260911.md).

E5 remains open: cyclic-star Hamiltonicity, the auxiliary shell, incidence and
matched selection, and the p=2 / p=3 / p≥4 entry assembly are still required.
