# Ancillary Source Bundle

This bundle is the machine-checkable companion artifact for the paper
"Hamilton decompositions of directed odd-dimensional tori for odd modulus",
including the directed 5-torus and 7-torus developments.

It is intentionally a source bundle, not a built Lean workspace.  The generated
`.lake/` build directory and the `.git/` directory are omitted.

## Contents

- `D5Odd/*.lean`, `D5Odd.lean`: Lean 4 formalization of the D5 odd case.
- `D5Odd/Matching.lean`: zero-set table and exact-cover certificate.
- `D5Odd/ReturnCycle.lean`: return-map proof and the finite `m = 3` rank tables.
- `D5Odd/Cayley.lean`: top-level Cayley-graph theorem.
- `D7Odd/*.lean`, `D7Odd.lean`: Lean 4 formalization of the D7 odd case.
- `D7Odd/Handoff/CanonicalFamily.lean`: canonical generic construction and root-flat D7 theorem.
- `D7Odd/Torus.lean`: bridge from root-flat D7 certificates to the full torus theorem.
- `D7Odd/Cayley.lean`: top-level D7 Cayley-graph theorem.
- `docs/D7_ODD_SPECIAL_THEOREM_REQUESTS.md`: D7 handoff notes and proof-status record.
- `scripts/d5_odd_paper_verify.py`: independent Python audit script for the finite tables,
  first-return formulas on supplied odd moduli, and the five `m = 3` color returns.
- `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`: reproducibility metadata.
- `README.md`, `CITATION.cff`: repository and citation metadata.

## Lean Check

The cited artifact uses Lean `v4.30.0-rc2` and mathlib `v4.30.0-rc2`.

```bash
lake build D5Odd D7Odd
```

The top-level D5 theorem is:

```lean
D5Odd.D5_odd_cayley_unconditional
```

The top-level D7 theorem is:

```lean
D7Odd.D7_odd_cayley_unconditional
```

## Python Audit

```bash
python3 scripts/d5_odd_paper_verify.py 3 5 7 9 11
```

This script is D5-specific and is not used as the symbolic proof of the
`m >= 5` first-return theorem.  It audits the
finite zero-set table, the matching map, selected first-return formulas, the normalized return cycle,
and the exceptional `m = 3` color-return cycles.
