# Archived EvenV11 modules (retired 2026-06-07)

These files were moved out of the live `EvenV11/` library by the dead-code audit
(`docs/ROUTE_E_AND_DEADCODE_AUDIT_20260607.md`). They are **not** imported by the
main theorem spine (`EvenV11.Main`) and are kept here only for history /
restoration. They are outside the progress gate's `EvenV11/` scan and outside the
Lake library source path, so they are not compiled.

## ① Orphan `native_decide` blobs (imported by nothing)
Superseded by the structural cycle-data route (`EvenV11.RootFlatCycleData`,
`EvenV11.LowD5M4Structural`).
- `LowD5M4Finite.lean`   (108 KB, 54 native_decide)
- `LowD7M4Finite.lean`   (768 KB, 74 native_decide)
- `LowD7M6Finite.lean`   (16.7 MB, 102 native_decide)

## ② Route E (superseded D3-even methodology, umbrella-only)
v28 closes the D3-even base via the terminal `A₂` block (`lem:terminal-cyclicity`,
finite-verified in `scripts/verify_rootflat_certificates.py [B]`). Route E was an
earlier rank-table/zero-layer attempt that only *reduced* H1 and never closed it.
- `D3EvenRouteEGeSix.lean`         (3048 lines)
- `D3EvenRouteEColor2Bridge.lean`
- `D3EvenRouteERootFlatBridge.lean`
- `CycleOnBridge.lean`             (old `TorusD3Even.CycleOn` adapter, Route-E only)
- `D3EvenM4RootFlat.lean`          (m=4 D3 root-flat via the Route-E bridge; depends
                                    on `D3EvenRouteERootFlatBridge`)

`D3EvenM4.lean` (standalone m=4 finite witness, no Route-E dependency) is **kept**
in the live library for the future terminal-A2 H1 connection.

## ③ closure-first legacy
- `Status.lean` (730 KB) — the closure-first bookkeeping replaced by the
  unconditional `EvenV11.Main` skeleton.

## ④ dead H2 scaffolding (tame `paperReturn` / `resetPortRowOfBase`)
Retired 2026-06-07 when the H2 path committed to the t-dependent ribbon handoff
(`LowD5M4Structural.ResetPortH2RowEquivRibbonRealizationData`). See
`docs/H2_REALIZATION_BLOCKER_20260605.md`: the tame `returnMap = paperReturn`
chart is displacement-unsatisfiable (§1–6), and the t-independent
`resetPortRowOfBase` is RF2-unsatisfiable (§8). Both are superseded.
- `LowD5M4Realization.lean` (8806 lines) — tame `paperReturn` chart + the
  `resetPortRowOfBase` (first+final substitutions applied at every layer).
- `LowD5M4H2PaperRow.lean` — the `resetPortRowOfBase`-based handoff built on it.

To restore a file: `git mv archive/EvenV11/<f>.lean EvenV11/<f>.lean` and re-add its
`import` to `EvenV11.lean`.
