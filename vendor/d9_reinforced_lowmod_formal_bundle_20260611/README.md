# D9 reinforced all-even proof bundle — 2026-06-11

This bundle strengthens the D9 all-even certificate package after adversarial
audit.  It adds semantic verifiers for the terminal `A2` carrier, the marked
comparison cycle/endpoint reserve, and the D9-to-D11 chain fields.

Run:

```bash
bash scripts/run_all_reinforced_verifications.sh
```

Expected final line:

```text
ALL D9 REINFORCED CERTIFICATES VERIFIED
```

## Proven by this bundle

Modulo the signed D9 anchor-realization theorem recorded in
`proof/d9_reinforced_realization_bridges_20260611.md`, the certificates prove

```text
HED(9,m) for every even m >= 4.
```

Together with corrected midpoint-collision paired growth, this gives the odd
branch for all odd `d >= 9` and all even `m >= 4`, without using the old chained
`7 -> 9` step.

## Important limitation

This is a theorem/certificate proof.  It is not a brute-force pointwise
permutation certificate for `D9(4)`, `D9(6)`, or `D9(8)`.  See
`proof/d9_pointwise_verifier_limitations_20260611.md`.
