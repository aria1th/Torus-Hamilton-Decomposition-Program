# 0.3.0-alleven — Hamilton decompositions of directed tori at every modulus

Tag `0.3.0-alleven` (2026-09-11). Previous release: `0.0.3-allodd` (odd moduli).

## Theorem

For every `d ≥ 2` and every `m ≥ 3`, the directed Cayley digraph
`Cay((ZMod m)^d, {e_0, …, e_{d-1}})` decomposes into `d` directed Hamilton cycles.

```lean
TorusAll.all_moduli_tori_all_dimensions :
  ∀ {d m : ℕ}, 2 ≤ d → 3 ≤ m → Shared.CayleyHamiltonDecomposition d m
```

New in this release: every even modulus `m ≥ 4`.

```lean
TorusEven.even_modulus_tori_all_dimensions :
  ∀ {d m : ℕ}, 2 ≤ d → Even m → 4 ≤ m → Shared.CayleyHamiltonDecomposition d m
```

## Axioms (checked on the release commit, `evidence/lean_audit_20260911/final-control-check/`)

| Theorem | Axioms |
|---|---|
| `TorusEven.d5_even_large` (`D_5(m)`, even `m ≥ 6`) | `propext`, `Classical.choice`, `Quot.sound` |
| `TorusEven.even_degree_collar` (even `d`, even `m ≥ 4`) | standard only |
| `TorusEven.even_odd_degree` (odd `d ≥ 7`, even `m ≥ 4`) | standard only |
| `TorusEven.even_modulus_tori_all_dimensions` | standard + 18 `native_decide` leaves (`D_5(4)`: 4, `D_3`: 14) |
| `TorusAll.all_moduli_tori_all_dimensions` | standard + 106 leaves (18 even, 88 odd, unchanged from `0.0.3-allodd`) |

No `sorry`, no author axioms. The registered `native_decide` leaves are finite
checks listed by name in `docs/EVEN_AXIOM_LEDGER.md`; `scripts/check_even_isolation.py`
enforces that no other file on the even path uses `native_decide` and that the even
library imports neither the odd core nor the retired attempts (`TorusEvenAttic/`).

## Route (manuscript `even_directed_tori_integrated.tex`, SHA256 `846a1e5f…88e98`)

- `TorusEven/Dispatch.lean`: parity-neutral dimension product (`D_a(m) ⊗ D_b(m^a)`).
- `TorusEven/D3/`, `TorusD3Even/`, `TorusD3Odometer/`: `D_3(m)` (vendored Route-E odometer, `m = 4` by kernel `decide`).
- `TorusEven/D5/`: `D_5(m)` for even `m ≥ 6` by the chronological transversal splice, integer complement certificates, and the three terminal planes; `D_5(4)` by the existing kernel-checked leaf.
- `TorusEven/Collar/`: relative collar closure (`thm:pinned`, `lem:inherit`, `thm:onegap`, `prop:transport`, `thm:closure`) and the empty-palette specialization (`thm:even-dim`).
- `TorusEven/Entry/`: near core, anchored cyclic star (both residue cases of `m mod 3`), auxiliary shell, matched selection, and the entries for `p = 2`, `p = 3`, `p ≥ 4` (`thm:oddconstruction`).
- `TorusAll.lean`: parity split between the even endpoint and the all-odd theorem.

The manuscript-to-Lean correspondence table is the last section of
`docs/EVEN_AXIOM_LEDGER.md`. Deliberately not formalized (used by no endpoint):
the permutation-valued form of the one-gap theorem, the manuscript's exact
classification of seed and residual incidence components (a parity statement is
proved instead), and the manuscript's own `m = 4` tour certificate as a Lean leaf.

## Build

```
lake exe cache get
lake build TorusEven TorusAll
python3 scripts/check_even_isolation.py
lake env lean evidence/lean_audit_20260911/final-control-check/FinalAudit.lean
```

Toolchain `leanprover/lean4:v4.30.0-rc2`, mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`
(`docs/EVEN_LOCK.md`).

## Contributions

See `docs/CONTRIBUTIONS.md`: the manuscript proof was completed by GPT-6-Pro with
the human author supplying direction, generalizations and corrections; the Lean
formalization was designed and started by Claude Fable 5.1 (E0–E3), carried through
the collar closure and the entry by GPT 6 Astra (max) (E4–E5), and recorded and
reviewed by Claude Fable 5.1. All theorems are kernel-checked; provenance of proof
text plays no role in the trust argument.
