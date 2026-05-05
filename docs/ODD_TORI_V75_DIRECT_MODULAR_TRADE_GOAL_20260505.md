# Odd Tori v7.5 Direct Modular-Trade Goal

Date: 2026-05-05.

This note fixes the current implementation goal after reviewing
`prefix_count_odd_tori_overhauled_v7_5_submission_bundle.zip`.

## Final Goal

The small-modulus branch should follow the v7.5 paper route directly:

```text
cylinder trade reservoir
  -> active residue scheduling/local trades
  -> active prefix-count lift
  -> successor closure
  -> all-dimensional odd-modulus dispatcher
```

The live Lean import for this route is:

```lean
import RoundComposite.V75Endpoints
```

The paper-facing endpoint package is:

```lean
Concrete.OddModulusToriV75DirectModularTradeInputsGoal
Concrete.OddModulusToriV75DirectModularTradeBlocksGoal
Concrete.oddSuccessorClosureGoal_of_v75_directModularTrade_blocks
Concrete.oddModulusToriAllDimensionsGoal_of_v75_directModularTrade_inputs
```

The final theorem remains:

```lean
Concrete.OddModulusToriAllDimensionsGoal
```

which expands to:

```lean
∀ {d m : Nat}, 2 ≤ d → Odd m → 3 ≤ m →
  Shared.CayleyHamiltonDecomposition d m
```

## Success Criteria

The final v7.5 route must not depend on the unrestricted finite Hall/de Werra
targets:

```lean
ActiveHall.HallRealizationGoal
ActiveHall.FiniteHoffman.RawZeroOneMatrixGoal
ActiveHall.FiniteHoffman.CompatibleDeWerraGoal
ActiveHallLargeMarginControlledResidueRoundingGoal
```

Those theorem shapes remain useful as legacy adapters and counterexample
context, but they are not live proof targets for the current paper route.

The small-modulus proof boundary is now:

```lean
BaseTail.Trades.SuccessorActiveBlockCanonicalLocalSymbolTradeGoal
BaseTail.PrimitiveActivePrefixLowerTriangularLiftAssemblyGoal
```

The broader local-trade theorem is still a sufficient fallback:

```lean
BaseTail.Trades.SuccessorActiveBlockLocalSymbolTradeGoal
```

but the canonical theorem is preferred because v7.5 only needs the residue
schedule selected by:

```lean
BaseTail.Trades.activeBlockResidueSpec
```

The active-block residue scheduler itself is closed and should not be listed
as a remaining proof blocker:

```lean
BaseTail.Trades.activeBlockResidueScheduleGoal
BaseTail.Trades.successorActiveBlockResidueScheduleGoal
```

## Work Split

### Worker A: Direct Local Trade / Reservoir

Owned files:

```text
RoundComposite/BaseTailTrades.lean
RoundComposite/ActiveHall.lean only if a small reusable finite lemma is needed
```

Primary theorem:

```lean
BaseTail.Trades.SuccessorActiveBlockCanonicalLocalSymbolTradeGoal
```

Paper correspondence:

```text
lem:local-symbol-trade
lem:trade-reservoir
thm:active-residue-scheduling
thm:active-realization
```

The proof should construct symbolings directly from reserved local trade sites.
It should not detour through a global count-matrix Hall realization theorem.

### Worker B: Base-Tail Prefix Lift

Owned file:

```text
RoundComposite/BaseTailGeometry.lean
```

Primary theorem:

```lean
BaseTail.PrimitiveActivePrefixLowerTriangularLiftAssemblyGoal
```

The proof should use the closed compressed base-cycle data:

```lean
BaseTail.CylinderBaseCycleData
BaseTail.cylinderBaseCycleData_of_isCylinder
```

and construct the lower-triangular/unit return data needed by the active
prefix-count lift.

Worker B status note:

```lean
BaseTail.expandedColorDirCore_fiberStep_coord_eq_add_directCarry
BaseTail.expandedColorDirCore_sectionReturn_coord_eq_add_sum_directCarry
```

These Lean lemmas now make the diagnostic `expandedColorDir` route explicit:
its fiber section return is a direct sum of symbol-count carries along the
compressed base orbit.  Therefore `expandedColorDir` itself should not be used
as the final lower-triangular primitive lift.  The remaining proof of
`BaseTail.PrimitiveActivePrefixLowerTriangularLiftAssemblyGoal` must introduce
a fiber-dependent active prefix-count tail rule whose section return has the
unit lower-triangular cocycles required by
`Shared.zmodVectorLowerTriangularUnitCycleCoordinate`.

### Main Thread: Endpoint Wiring

Owned files:

```text
RoundComposite/OddCore.lean
RoundComposite/V75Endpoints.lean
docs/
```

The main thread should keep theorem names synchronized with the paper and
preserve the final adapters:

```lean
Concrete.oddModulusToriV75DirectModularTradeBlocksGoal_of_inputs
Concrete.oddModulusToriAllDimensionsGoal_of_v75_directModularTrade_inputs
```

## More Efficient Workflow In Retrospect

The main inefficiency was treating the older ActiveHall/de Werra route as a
live theorem target for too long.  The counterexamples show that the
unrestricted theorem shape is false, so every wrapper built around it had
limited value for the final proof.

A better workflow would have been:

1. Read the newest paper bundle before adding more endpoint adapters.
2. State the final theorem and negative dependencies first.
3. Test any proposed finite theorem for small counterexamples before making it
   a central Lean target.
4. Keep theorem surfaces successor-specific whenever the paper proof is
   successor-specific.
5. Separate three tasks immediately: local trade reservoir, prefix lift, and
   endpoint wiring.
6. Add top-level paper-facing imports only after the route is stable enough to
   name, not while the mathematical target is still moving.

The useful artifacts from the previous route are the adapters and negative
evidence.  They clarify exactly what the v7.5 proof must avoid: global
capacity-oblivious Hall realization.  The current implementation should now
spend proof effort only on the direct local-trade reservoir and the base-tail
prefix lift.

## Build Gate

After each implementation slice:

```bash
lake build RoundComposite.V75Endpoints
```

Before declaring the branch closed:

```bash
lake build RoundComposite.OddCore
git diff --check
grep -R -n -E '\b(sorry|admit|axiom|constant)\b' \
  RoundComposite Shared TorusD3Odd D5Odd D7Odd --include='*.lean'
```
