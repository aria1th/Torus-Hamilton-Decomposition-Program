# Even-modulus axiom ledger

Recorded with `#print axioms` on the pinned toolchain (docs/EVEN_LOCK.md).
"standard" = `propext`, `Classical.choice`, `Quot.sound`.  Every `native_decide`
entry is a `Lean.ofReduceBool`-style trusted finite leaf and is listed by name.

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
| `TorusEven.d3_even_of_six_le` (D_3(m), even m ≥ 6, Route E) | unconditional | standard + 16 native leaves, all in `TorusD3Even/Color2.lean`: `firstReturn_four_m6`, `hfirst_four_m6` (5), `firstReturn_six_m8`, `hfirst_six_m8` (7) — finite first-return checks at `m = 6, 8` |
| `TorusEven.d3_even : D3EvenGoal` | unconditional | union of the two rows above |
| `TorusEven.even_dimension_nine` (D_9(m), even m ≥ 4) | unconditional | same as `d3_even` |
| `TorusEven.even_modulus_tori_all_dimensions_of_collar` | conditional on `D5EvenLargeGoal`, `EvenOddDegreeGoal` | standard + 4 (D_5(4)) + 16 (D_3) native leaves |

Note: the Lean `D_3` witness is the Route E construction of arXiv:2603.24708, not the
manuscript's anchored cyclic-star (`prop:anchor`). Both prove the same statement; the
anchored version is still needed for E5 (agreement at the four anchor vertices).

Manuscript ↔ Lean correspondence for the open goals is in `TorusEven/Goals.lean`.
