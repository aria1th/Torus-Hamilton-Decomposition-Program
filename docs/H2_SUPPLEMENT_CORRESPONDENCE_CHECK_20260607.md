# H2 Supplement Correspondence Check - 2026-06-07

This checks the proposed H2 `D5(4)` mathematical supplement against the current
paper data and Lean repository.

## Verdict

The supplement is directionally correct and matches the active Lean strategy:

- separate the return-level core from physical-row realization,
- keep `LowD5M4.fullReturn` as the return-level target,
- require a wild return-section equivalence `e`,
- require the terminal-level return-section equivalence `eT` as well,
- avoid the tame `paperReturn`/`seedRootEquiv` route,
- make terminal/product/switching realization the missing theorem layer.

Current Lean also has a separate direct RF closure of the H2 low-base
certificate:

```lean
EvenV11.LowD5M4Finite.finalLowD5M4RootFlatCertificateFamily
```

`EvenV11.Main.assume_lowD5M4` now uses this active source and no longer depends
on `sorryAx`.  In `EvenV11/D54DirectRF.lean`, the finite schedule is packaged as
`H2.D54.lowD5M4FiniteConjugateDirectRFInput :
H2.D54.D54ConjugateDirectRFInput`, so it passes through the same generic
conjugate-schedule bridge as generated RF certificates.  This does not prove
the paper run-collapse/ribbon realization; it closes the low-base H2 obligation
by a finite root-flat certificate.

The finite tables in the supplement were independently checked by Python and
match the current paper definitions:

- `omega4` table,
- `F0,F1,F2` full orbits,
- `W = F1 ∘ F2 ∘ F0` orbit,
- terminal `C4` comparison order,
- lifted `CX` and `Chat` successor lengths,
- protected set `NT`,
- final sites and reserve-point separation.

## Existing Lean Correspondence

The following parts already exist in active Lean.

| Supplement item | Current Lean |
|---|---|
| `Q4`, `Y`, `Z`, `Seed` | `EvenV11/LowD5M4Seed.lean`: `LowD5M4.Q4`, `Y`, `Z`; structural `Seed` in `LowD5M4Structural` |
| terminal `omega`, `eta`, `F_i` | `EvenV11/TerminalA2LowMod.lean`: `terminalOmega`, `terminalEta`, `terminalReturn`, `terminalSymbolStep` |
| `F_i` m=4 orbit tables | `EvenV11/LowD5M4Seed.lean`: `f0Orbit`, `f1Orbit`, `f2Orbit` |
| reset sites `p0,p1,p2` | `LowD5M4.p0,p1,p2` and `D54ResetData.d54TerminalResetSites_eq_lowD5M4` |
| `T_i`, `P0`, `P1`, `baseReturn` | `LowD5M4.T`, `P0`, `P1`, `baseReturn` |
| final sites `b0..b4` | `LowD5M4.a0..a4`, `LowD5M4.liftSite`; also `D54ResetData.d54FinalCylinders_eq_lowD5M4_liftSites` |
| `Rhat_i` cycles | `LowD5M4.fullReturn_singleCycle` |
| reserve table | `EvenV11/D54ResetData.lean`: `d54ReservePoints`, nodup/count/avoid lemmas |
| H2 direct RF certificate | `EvenV11/LowD5M4Finite.lean`: `finalLowD5M4RootFlatCertificateFamily` |
| H2 paper handoff target | `LowD5M4RibbonInterface.PhysicalRowsSingletonSwitchMapConjInput` |

Additional active bridge theorems in `EvenV11/D54ReturnCore.lean`:

```lean
F_eq_terminalReturn
terminalReturn4_singleCycle
TerminalA2M4PhysicalRealization.return_eq_terminalReturn
TerminalA2M4PhysicalRealization.not_terminalRootEquivSection
terminalStandardReturnMap_ne_fixedChartReturn_color1
terminalF0F2_iterate_33
terminalF0F2_no_positive_iterate_lt33
TerminalA2M4PhysicalRealization.actualF0F2_iterate_33
TerminalA2M4PhysicalRealization.actualF0F2_no_positive_iterate_lt33
RbaseNeutral_not_singleCycle
D54ProductBaseRealization.returnMap_not_singleCycle
D54TwoStageSingletonSwitchRealization.toFiveSwitchRealization
D54PaperRealization.ofTwoStageSingletonSwitchRealization
D54PaperRealizationLadder.ofStagesTwoStageSingletonSwitch
D54FiveSwitchSeedSwitchRealization.toFiveSwitchRealization
D54PaperRealization.ofFiveSwitchSeedSwitchRealization
```

These keep the return-level core aligned with the paper notation and make the
structured singleton-switch target assemble directly into the existing H2
paper payload once its physical rows and seed fold are supplied.

The fixed standard terminal chart is now also checked as a negative control:
there is no four-layer factorization of any paper terminal return `F_i` by
standard D3 root-flat bijective layer maps in the plain `terminalRootEquiv`
coordinates.  Thus `TerminalA2M4PhysicalRealization` must expose an equivalence
`eT : Q4 ~= TerminalRootState`; asking for `terminalRootEquiv` directly would be
too strong.  The Lean interface also records `step_eq_standard`, so the
terminal physical schedule is tied to the standard D3 root step rather than an
arbitrary `RootFlatSchedule.step`.

## Convention Note

The supplement's composition convention is:

```text
(G ∘ F)(x) = G(F x)
```

So

```text
W = F1 F2 F0 = F1 ∘ F2 ∘ F0
```

In current Lean, this is `terminalResetTrace4`, not `terminalResetWord4`:

```lean
terminalResetTrace4 = [F0, F2, F1]
wordEval F terminalResetTrace4 x = F1 (F2 (F0 x))
```

This distinction matters when naming the `W_cycle` theorem.  The active proof
already uses:

```lean
terminalResetTrace4_singleCycle
```

inside `LowD5M4Seed.P1_singleCycle`.

## Checked Finite Data

The following script calculation agrees with the supplement:

```bash
python3 scripts/verify_d5m4_h2_realization.py
```

Additional direct checks confirm:

- `omega4` table:
  - row `y=0`: `012,021,012,102`
  - row `y=1`: `012,120,201,012`
  - row `y=2`: `201,012,120,210`
  - row `y=3`: `120,201,012,012`
- `C4 = {(0,3),(3,0),(3,3)}` has comparison order
  `(0,3) -> (3,0) -> (3,3) -> (0,3)` for `F2^-1 F1`.
- The terminal relation invariant `order(F0 o F2) = 33` is now checked by
  Python and by the Lean theorems `terminalF0F2_iterate_33` and
  `terminalF0F2_no_positive_iterate_lt33`.  Any proposed
  `TerminalA2M4PhysicalRealization` also carries this invariant through its
  section equivalence, via
  `TerminalA2M4PhysicalRealization.actualF0F2_iterate_33` and
  `TerminalA2M4PhysicalRealization.actualF0F2_no_positive_iterate_lt33`.
- The existing finite `D3EvenM4` schedule fails this same terminal relation
  test: its relation has `order(R0 o R2) = 63`, not `33`.  Thus its lack of a
  common conjugacy to the paper terminal `F_i` is not just a search miss.
- On `CX = C4 x {0}`, successor lengths are:
  - `T1`: `9, 1, 54`
  - `T2`: `57, 6, 1`
- On `Chat = C4 x {0} x {0}`, successor lengths are:
  - `Rhat1`: `9, 1, 246`
  - `Rhat2`: `249, 6, 1`
- `NT` is exactly:
  `{(0,3),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,3)}`.

## Corrections And Clarifications

1. The `RootFlatSchedule` skeleton in the supplement is mathematically fine,
   but current Lean uses the standard schedule interface:

   ```lean
   dir : ZMod m -> RootState -> Color -> Direction
   step : Direction -> RootState -> RootState
   ```

   For H2 rows, the closest current row-facing type is:

   ```lean
   PhysicalLayerRows
   row : ZMod 4 -> RootState -> TorusColor 5 ≃ TorusDirection 5
   ```

2. `D54_fullReturn_eq_Rhat` should be essentially definitional if `Rhat` uses
   the same nesting as `LowD5M4.fullReturn`, namely `((q,y),z)`.  Still, adding
   this theorem is useful as a stable rewrite boundary.

3. The strengthened `NT`/`Nhat` protected-neighborhood facts are now named in
   `D54ReturnCore`, including:

   ```lean
   NTList
   NhatList
   NTList_mem_iff_terminalNeighborhoodList_mem
   resetSites_avoid_NTList
   finalCylinders_avoid_NhatList
   reservePoints_disjoint_NhatList
   ```

   `D54SupportTables`, `D54PaperRealization`, and `D54PaperRealizationLadder`
   also expose the protected-neighborhood avoidance fields needed by a future
   switching-ribbon proof.

4. `TerminalA2M4Realization` is exactly the right missing theorem shape, but it
   must avoid the known bad interpretations:
   - not `terminalStdBaseRowAtState`,
   - not color-anchored `omega(q-a_c)` as a root-flat row,
   - not the fixed standard terminal chart `terminalRootEquiv`,
   - not the existing finite `D3EvenM4` schedule unless an additional bridge
     proves common conjugacy to paper `F_i`.

## Missing Lean Interfaces

These are still absent and are the real paper-faithful H2 work.

```lean
theorem terminal_A2_m4_physical_realization :
  H2.D54.TerminalA2M4PhysicalRealization
```

```lean
theorem D54_product_base_realization
  (T : H2.D54.TerminalA2M4PhysicalRealization) :
  H2.D54.D54ProductBaseRealization
```

This stage is necessary but cannot close H2 by itself.  The pre-reset product
return preserves the neutral `Z` coordinate, and Lean now records the no-go
facts:

```lean
RbaseNeutral_not_singleCycle
D54ProductBaseRealization.returnMap_not_singleCycle
```

Thus the five final local switches are not optional bookkeeping; they are the
step that inserts the missing `Z` unit carry.

```lean
theorem D54_five_switches_realize_fullReturn
  (B : H2.D54.D54ProductBaseRealization) :
  H2.D54.D54FiveSwitchRealization
```

The final assembly then maps cleanly to the existing handoff:

```lean
LowD5M4RibbonInterface.PhysicalRowsSingletonSwitchMapConjInput
```

or, one layer lower:

```lean
LowD5M4Structural.ResetPortH2RowEquivRibbonRealizationData
```

2026-06-07 update: the finite reset/support fields are no longer live
obligations in the active Lean interface.  `D54PaperRealization` can now be
built from a `D54FiveSwitchRealization` by filling `D54ResetData`'s closed table
certificate and avoidance facts, and `EvenV11.Main` exposes
`lowD5M4_of_paperRealization` / `lowD5M4_of_paperRealizationLadder` for the
final low-base certificate.  It also exposes the stage-wise theorems
`lowD5M4_of_paperStagesTwoStageSingleton`, the narrower
`lowD5M4_of_paperStagesTwoStageLayerConjSingleton`,
`lowD5M4_of_paperLayerConjStages`, and the seed-row endpoint
`lowD5M4_of_paperSeedRowStages`, plus the all-seed-row endpoint
`lowD5M4_of_paperAllSeedRowStages`, and finally
`lowD5M4_of_paperTransportedSeedRowStages`.  The last one fixes each seed
generator step as the pullback of the standard root step through the supplied
return-section equivalence, so it takes exactly: terminal transported seed-row
realization, product-base transported seed-row realization, and a two-stage
transported seed-row singleton-switch realization.  Thus the smallest current
paper-realization target is

```lean
H2.D54.D54FiveSwitchRealization
```

namely: final physical rows, singleton-switch RF2 data, a wild equivalence
`e : Seed ~= RootState`, and return conjugacy to `LowD5M4.fullReturn`.

The active Lean interface also exposes a layer-model version:

```lean
H2.D54.D54FiveSwitchLayerModelRealization
```

This reduces the return-conjugacy proof to two smaller facts: every physical
layer map is conjugate to a seed-side layer map, and the four seed-side layers
fold to `Rhat`.  The generic fold step is closed by
`physical_returnMap_conj_of_seedLayerReturn_eq`.

There is now also a fixed two-stage seed-model target:

```lean
H2.D54.D54TwoStageLayerModelRealization
H2.D54.D54TwoStageLayerConjRealization
```

The `LayerModel` form asks for physical layer maps conjugate to the closed
`seedTwoStageFullReturnLayer` model plus RF2.  The newer `LayerConj` form drops
that RF2 field: `physical_layerBijective_of_seedLayer_conj` derives it from
the layerwise conjugacy and `seedTwoStageFullReturnLayer_bijective`.  This target
is useful as an audit or as a bridge endpoint for the paper switch model,
because its return fold, layer bijectivity, and return single-cycle facts are
already closed in Lean.

The seed-row bridge now goes one level closer to a literal row transcription:

```lean
physicalRowsOfSeedRow_layerMap_conj
H2.D54.TerminalA2M4SeedRowRealization
H2.D54.D54ProductBaseSeedRowRealization
H2.D54.D54TwoStageSeedRowRealization
H2.D54.D54TwoStageSeedRowSingletonSwitchRealization
H2.D54.TerminalA2M4TransportedSeedRowRealization
H2.D54.D54ProductBaseTransportedSeedRowRealization
H2.D54.D54TwoStageTransportedSeedRowSingletonSwitchRealization
```

Here the caller supplies a seed-side row equivalence table, a seed-side
generator step transported to the standard root step, and the seed fold/equality
facts.  In the transported variants, the generator step and its conjugacy proof
are fixed by the equivalence itself.  Lean constructs the physical
`PhysicalLayerRows` and their layerwise conjugacy automatically.

If the same rows also carry singleton-switch RF2 data, Lean now exposes the
direct bridge:

```lean
H2.D54.D54TwoStageSingletonSwitchRealization
H2.D54.D54TwoStageLayerConjSingletonSwitchRealization
H2.D54.D54TwoStageSingletonSwitchRealization.toFiveSwitchRealization
H2.D54.D54PaperRealization.ofTwoStageSingletonSwitchRealization
EvenV11.lowD5M4_of_paperStagesTwoStageSingleton
EvenV11.lowD5M4_of_paperStagesTwoStageLayerConjSingleton
EvenV11.lowD5M4_of_paperLayerConjStages
EvenV11.lowD5M4_of_paperSeedRowStages
EvenV11.lowD5M4_of_paperAllSeedRowStages
EvenV11.lowD5M4_of_paperTransportedSeedRowStages
```

This means a proof of layerwise conjugacy to `seedTwoStageFullReturnLayer`,
together with the paper's singleton-switch RF2 certificate for those rows,
already supplies the final `D54FiveSwitchRealization`; the closed D54
reset/support tables then package it as a `D54PaperRealization`.

For the first of the three transported inputs, the active finite audit helper is

```text
scripts/search_h2_terminal_transported.py
```

It fixes a candidate `eT : Q4 ~= (Z/4)^2`, enumerates the 2160 terminal
RF1/RF2 layers, builds the 4,662,609 two-layer products, and uses a
meet-in-the-middle check to decide whether `eT o F_i o eT^-1` factors as four
terminal layers for all three colors.  It confirms the plain identity chart has
no such four-layer factorization, matching the Lean obstruction
`TerminalA2M4PhysicalRealization.not_terminalRootEquivSection`.  Random section
checks are only search evidence; a successful output should be promoted to a
Lean table certificate for `TerminalA2M4TransportedSeedRowRealization`.

The most structured active paper target is now:

```lean
H2.D54.D54FiveSwitchSeedSwitchRealization
```

It requires the final physical rows and singleton-switch RF2 data, plus a
seed-side singleton-switch mirror of every physical comparison pair and site.
`D54SeedSingletonSwitchLayerData.layerMapConj` then proves the per-layer
conjugacy automatically.  The remaining seed-side calculation is the fold
equation:

```lean
seedLayerReturn seedSwitch.seedLayer c s = Rhat c s
```

The return-level fold itself is now also represented by a closed fixed seed
model:

```lean
postBaseCarry_after_RbaseNeutral_eq_Rhat
seedLayerReturn_twoStageFullReturnLayer
seedTwoStageFullReturnLayer_return_eq_Rhat
seedTwoStageFullReturnLayer_bijective
seedTwoStageFullReturnLayer_return_singleCycle
```

So the outstanding switch-specific seed calculation can be narrowed further:
show that the singleton-switch seed mirror produced by the paper ribbons folds
to the same map as `seedTwoStageFullReturnLayer`, or prove its fold equation
directly and use the fixed two-stage model as the audit target.

There is also a deliberately separate direct-RF bridge:

```lean
resetPortH2RootFlatCycleData_of_conjugateSchedule
```

It transports an arbitrary root-flat schedule on another 256-state model into
the standard D5(4) root chart, provided its step maps are conjugate to
`LowD5M4Schedule.rootStep`.  This can support generated/direct finite RF
certificates, but it does not prove the paper `LowD5M4.fullReturn`
run-collapse/ribbon realization.

The packaged active form is:

```lean
H2.D54.D54ConjugateDirectRFInput
```

The active `EvenV11.LowD5M4Finite` certificate has exactly the expected shape: a
finite schedule, row Latinness, layer bijectivity, return cyclicity, and
`rootIndexEquiv` conjugating its step to `LowD5M4Schedule.rootStep`.  It is now
the direct/generated RF witness path used by `Main`, not the paper-realization
path.

## Conclusion

The supplement is a good mathematical blueprint for the paper-faithful route.
Its return-level core matches the current Lean definitions and the finite
computations.  The low-base H2 certificate is now closed directly by
`LowD5M4Finite`; the remaining substantial paper-realization content is:
terminal physical rows, product rows, five-switch RF2/ribbon composition, and
the resulting wild equivalence `e`.
