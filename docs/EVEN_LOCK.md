# Even-modulus work: pinned environment (E0)

Opened: 2026-09-10.

| Item | Value |
|---|---|
| Lean toolchain | leanprover/lean4:v4.30.0-rc2 (commit 3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc) |
| Lake | 5.0.0-src+3dc1a08 |
| mathlib | 5450b53e5ddc75d46418fabb605edbf36bd0beb6 (v4.30.0-rc2), cache via `lake exe cache get` |
| elan | 4.2.4 |
| Repository base commit | 0a00a8a40707ddd76355a5963e17aad9fea10649 (main, tag 0.0.3-allodd lineage) |
| Manuscript | even_directed_tori_integrated.tex, SHA256 846a1e5f0a4ab5ea3511b312a3a8230210dc10e27f1483d1700445a670188e98 |
| Original manuscript | SHA256 a073b6e3cff6f3c6de0545482e27f5786e4ad3c26f085d371c90f92450d8827f |
| D_5(4) tour certificate | evidence/even_d5/certificates/d5_m4_tours.json, SHA256 6dc36c0d080278ca3cf37246e09a3be987f3726444e7699fc96403e23aa9c434 |
| D5 complement matrices | evidence/even_d5/certificates/d5_complement_matrices.json, SHA256 4b9f9d2614ad0a4fefb550f144512789bf5400c66dbd670a818e1aae0d744c8b |
| Python evidence env | Python 3.12.3, numpy 2.5.3, sympy 1.14.0 (uv venv); zip was produced with 3.13.5 / 2.3.5 / 1.14.0 |

Build logs and `#print axioms` outputs for the even endpoints are appended below as
milestones close (see docs/EVEN_AXIOM_LEDGER.md once created).

## Baseline (2026-09-10)

- `lake build Shared`: success (8332 jobs including mathlib cache).
- `lake build RoundComposite D5Odd D7Odd TorusEven TorusEvenAttic`: see log section below.

### Log (2026-09-10, after the attic restructure)

- `lake build RoundComposite D5Odd D7Odd TorusEven TorusEvenAttic`: success
  (TorusEven.Dispatch needed two fixes for implicit-binder elaboration; final build 8336 jobs).
- `lake build RoundComposite.V75Endpoints RoundComposite.ConcreteEndpoints`: success (8396 jobs).
- `#print axioms`: see docs/EVEN_AXIOM_LEDGER.md.
- `python3 scripts/check_even_isolation.py`: passed (5 main-path files, 4 attic files, 2 registered native leaves).
