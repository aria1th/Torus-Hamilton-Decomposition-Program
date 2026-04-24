# Torus Hamilton Decomposition Program

Lean 4 formalization and audit artifacts for Hamilton decompositions of directed torus/Cayley digraphs.

The current formalized endpoint is the odd-modulus directed 5-torus construction.  In particular, the repository proves:

```lean
theorem D5Odd.D5_odd_cayley_unconditional {m : Nat} [NeZero m]
    (hodd : Odd m) (hm3 : 3 <= m) :
    D5Odd.CayleyHamiltonDecompositionD5 m
```

This states an explicit Cayley-edge decomposition for
`Cay((ZMod m)^5, {e_0, e_1, e_2, e_3, e_4})` when `m` is odd and `m >= 3`.

## Repository Layout

- `D5Odd/`: Lean 4 formalization.
- `D5Odd/Cayley.lean`: final Cayley-edge wrapper and theorem.
- `D5Odd/Torus.lean`: layer/root-flat lift from return maps to full torus color cycles.
- `D5Odd/Main.lean`: model-level odd D5 endpoint.
- `docs/`: audit, cleanup, and paper-critical-addition notes.
- `scripts/d5_odd_paper_verify.py`: audit-only Python verifier used for independent sanity checks.

## Build

Install Lean with `elan`, then run:

```bash
lake build D5Odd
```

The project currently uses:

```text
leanprover/lean4:v4.30.0-rc2
mathlib v4.30.0-rc2
```

Optional audit script:

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
