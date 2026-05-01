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
- `D7Odd/`: Lean 4 formalization of the odd D7 construction.
- `D7Odd/Handoff/CanonicalFamily.lean`: canonical generic branch and root-flat D7 endpoint.
- `D7Odd/Torus.lean`: lift from root-flat D7 certificates to full torus color cycles.
- `D7Odd/Cayley.lean`: final D7 Cayley-edge wrapper and theorem.
- `docs/D7_ODD_SPECIAL_THEOREM_REQUESTS.md`: D7 handoff/proof-status notes.
- `scripts/d5_odd_paper_verify.py`: audit-only Python verifier used for independent sanity checks.
- `ANCILLARY.md`: description of the source bundle supplied with the manuscript.

## Build

Install Lean with `elan`, then run:

```bash
lake build D5Odd D7Odd
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

## Citation

If you use this formalization, cite the repository using `CITATION.cff`.

Paper drafts may link to:

```text
https://github.com/aria1th/Torus-Hamilton-Decomposition-Program
```

## Notes

The Python verifier is retained as an audit and illustration tool.  The formal proof artifact is the Lean 4 development.
