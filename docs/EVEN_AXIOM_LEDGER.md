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
