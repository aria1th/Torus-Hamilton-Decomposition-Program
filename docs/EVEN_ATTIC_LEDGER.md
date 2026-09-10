# Even-modulus attic ledger

Date opened: 2026-09-10.  Each entry: what was tried, which assumption failed or was
superseded, and what remains reusable.  An approach with more than three entries for
the same target is to be re-examined before a fourth attempt (rule from
`docs/EVEN_MODULUS_FORMALIZATION_PLAN_20260910.md` §4b).

| # | Target | Location | Status | Reusable |
|---|---|---|---|---|
| A1 | D_5(m), even m, via seam framework | `TorusEvenAttic/D5Seam.lean` (was `D5Odd/Even.lean`) | superseded: reduces D_5(m) to `D5EvenSeamOrbitCertificateTarget m`, never discharged for general m | `D5_even_cayley_from_orbit_certificate` (parity-free adapter) |
| A2 | D_5(m), even m, Route E small seam | `TorusEvenAttic/D5RouteE.lean` (was `D5Odd/EvenRouteE.lean`), `attic/route_e/` | superseded: branch table for m=6..60 gave no uniform formula; all `*AllLargeEvenTarget` remain unproved | `RouteEB20` arithmetic lemmas; `LambdaE` table now in `D5Odd/EvenLambdaE.lean` |
| A3 | "all even from large + m=4" adapters | `TorusEvenAttic/D5RouteEM4Adapters.lean` (was tail of `EvenRouteEM4.lean`) | superseded by `TorusEven/D5Four.lean` (`d5_even_uniform_of_large`) | none |
| A4 | D_7(m), even m, root-flat target | `TorusEvenAttic/D7RootFlatTarget.lean` (was `D7Odd/Even.lean`) | empty: the `Even m` hypothesis was never used; content is a rename of `Shared.rootFlatLayeredDecomposition_of_certificate` | none |

Remote branch `route-e-v3-6-20260506` is Route E history and is not to be merged.

## Kept on the main path from the same period

- `D5Odd/EvenRouteEM4.lean`: `D5_even_m4_shared_cayley : Shared.CayleyHamiltonDecomposition 5 4`
  (kernel + `native_decide`; registered in `scripts/check_even_isolation.py`).
- `D5Odd/EvenLambdaE.lean`: the `Lambda_E` row table that schedule uses.
