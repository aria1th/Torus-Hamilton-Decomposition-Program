# v28 hard-parts code notes — 2026-06-06

This patch adds an experimental hard-slot layer under `EvenV11/V28Hard/`.  The
umbrella `EvenV11/V28Hard.lean` is intentionally **not** imported by
`EvenV11.lean`; the default theorem spine remains unchanged.  The new files are
for local repair, proof extraction, and eventual replacement of the six
`Main.lean` assumptions.

## Files added

### `EvenV11/V28Hard/D3TerminalA2Parametric.lean`

Hard slot H1.  This file replaces the old Route-E finite-tail strategy with a
terminal `A₂` root-flat schedule.  It defines the root/paper coordinate
identification, the terminal direction table, the RF1/RF2/RF3 handoff, and the
candidate family

```lean
V28Hard.D3TerminalA2Parametric.rootFlatCertificateFamily
```

The hard local proof holes are deliberately explicit:

* `rowLatin`: reconcile the color-dependent terminal anchor with the fixed
  physical terminal row;
* `layerBijective`: construct inverses for each terminal layer/color map;
* `returnMap_eq_terminalReturn`: collapse the `m` standard-lift layers to the
  paper return map;
* `terminalA2ParametricCyclicity`: prove the active-endpoint recurrence for all
  even `m ≥ 4`.

### `EvenV11/V28Hard/D5M4RibbonRows.lean`

Hard slot H2.  This file does not invent a new D5 interface; it gathers the
strongest useful interfaces already present in `LowD5M4Realization` and connects
them to the current H2 handoff:

```lean
structure H2PaperTableInput : Prop
structure H2PaperCertificateInput : Prop
```

The key closed adapters are

```lean
ribbonData_of_paperTableInput
nonemptyRibbonData_of_paperTableInput
lowD5M4RootFlatFamily_of_paperTableInput
paperTableInput_of_rf2_prefix_read
```

The intended proof path is to supply a reset-port base row, RF2 skew-product data,
prefix-path goals, and row-word read goals; the rest is bookkeeping.

### `EvenV11/V28Hard/D7FiniteToCycleData.lean`

Hard slots H3/H4, transitional bridge.  This file transports the generated
`LowD7M4Finite` and `LowD7M6Finite` schedules through their `rootIndexEquiv` and
packages them as the structural interface

```lean
RootFlatCycle.RootFlatCycleData 6 4
RootFlatCycle.RootFlatCycleData 6 6
```

This does not make the D7 proof paper-faithful by itself, but it is an important
refactoring: the generated blobs now feed the same RF1/RF2/RF3 interface that the
handwritten two-rail proof must eventually fill.

### `EvenV11/V28Hard/D7TwoRailRelay.lean`

Hard slots H3/H4, paper proof blueprint.  This file encodes the D7 two-rail
relay tables as Lean data:

* `stageSkeletons`: five shifted relay stages;
* `stageRows`: fourteen expanded support/splice rows;
* `colorClosureData`: seven coforest/closing-edge rows;
* `terminalAlignment`: final terminal `A₂` alignment.

The final handwritten D7 object is

```lean
structure TwoRailRelayRealization (m : Nat) [NeZero m]
```

which directly converts to `RootFlatCycle.RootFlatCycleData 6 m`.

### `EvenV11/V28Hard/HighEvenEndpointPromotions.lean`

Hard slots H5/H6.  This file introduces stronger paper-facing engines:

```lean
structure OddHighModulusEngine : Prop
structure OddEndpointPayloadEngine : Prop
```

The adapters

```lean
oddHighModulusPromotion_of_engine
endpointTargetPromotion_of_engine
```

forget these stronger engines to the existing target-promotion records consumed
by the final induction.

### `EvenV11/V28Hard/ChecklistFromHardParts.lean`

Handoff file.  It assembles the candidate hard parts into
`V28PaperInterface.PaperFaithfulChecklist`.  Two variants are present:

* `paperChecklist_with_finiteBackedD7`: practical stepping stone using
  `D7FiniteToCycleData` for H3/H4 and a parameterized H2 paper-table input;
* `paperChecklist_structuralD7`: final no-generated-D7 shape.

## Recommended local repair order

1. Repair `D7FiniteToCycleData` first.  It is closest to executable Lean and
   checks the transport lemmas (`layerMap_conj`, return-map conjugacy,
   single-cycle transport).
2. Fill an `H2PaperTableInput` via `D5M4RibbonRows.paperTableInput_of_rf2_prefix_read`.
3. Repair `D3TerminalA2Parametric`, starting with `returnMap_eq_terminalReturn`.
4. Replace the finite-backed D7 fields by `TwoRailRelayRealization 4` and
   `TwoRailRelayRealization 6`.
5. Fill `OddEndpointPayloadEngine`, then `OddHighModulusEngine`.

## Build note

This code was written without access to `lean`/`lake` in the execution
environment.  Some namespace, coercion, or simp-direction repairs are expected.
The proof holes are intentionally concentrated at the mathematically hard sites,
not hidden in the main theorem spine.
