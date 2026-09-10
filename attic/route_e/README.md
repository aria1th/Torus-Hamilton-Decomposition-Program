# Attic: D5 even Route E (retired 2026-09-10)

Program-side scripts and certificates of the 2026-05 Route-E attempt at `D_5(m)` for
even `m` (small-seam schedules, `m = 24q+20` branch, non-open small seam).  They were
moved here from `scripts/` and `certs/` unchanged.  Historical notes in `docs/` still
refer to the old paths.

The Lean side of the same attempt lives in the `TorusEvenAttic` library.  The only
result of that line that is used by the current even path is the `m = 4` finite
schedule, kept in `D5Odd/EvenRouteEM4.lean`.

Why retired: the branch classification never produced closed count formulas for all
even `m` (see `docs/D5_EVEN_ROUTE_E_BRANCH_EXTRACTION_V0_7_20260502.md`), and the
integrated manuscript now proves `D_5(m)`, `m >= 6`, by a different route
(chronological transversal splice).  See `docs/EVEN_ATTIC_LEDGER.md`.
