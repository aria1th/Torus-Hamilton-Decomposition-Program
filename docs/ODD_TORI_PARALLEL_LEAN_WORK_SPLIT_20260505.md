# Odd Tori Parallel Lean Work Split

Date: 2026-05-05

Objective:

```lean
∀ {d m : Nat}, 2 ≤ d → Odd m → 3 ≤ m →
  Shared.CayleyHamiltonDecomposition d m
```

This document records the current two-goal split.  It supersedes the earlier
temporary worker split where Worker 1 meant base-tail geometry and Worker 2
meant finite integrality/de Werra.  The current split follows the mathematical
separation between the high-modulus prefix-count branch and the small-modulus
successor base-tail branch.

## Goal 1 / Worker 1: High-Modulus Prefix-Count Branch

Owner: current Codex thread.

Main files:

```text
RoundComposite/FiniteHoffman/SignedTrellis.lean
RoundComposite/PrefixCountHalfSlack.lean
RoundComposite/PrefixCount.lean
RoundComposite/OddCore.lean
RoundComposite.lean
docs/PREVIOUS_PAPER_ROUTE_AUDIT_20260505.md
```

Target:

```lean
RoundComposite.Concrete.OddCoreHighModulusPrefixCountGoal
```

Equivalently, for the high-modulus count branch:

```lean
∀ {d m : Nat}, Odd d → 5 ≤ d → Odd m → d ≤ m →
  StandardCayleySolved d m
```

### Included Work

1. q >= 2 signed core.

   The current Lean proof closes the formerly dangerous Appendix A input
   by binary-layer decomposition:

   ```lean
   PrefixCount.ordinaryQge2SignedBinaryLayerClosureGoal
   PrefixCount.ordinaryQge2SignedFullSupportTrellisGoal
   PrefixCount.ordinaryQge2SignedSeedProperCutClosureGoal
   ```

   The key construction is in:

   ```lean
   PrefixCount.qge2LayeredSignedEntry
   PrefixCount.OrdinaryQge2BinaryLayerTrellisGoal
   PrefixCount.OrdinaryQge2BinaryLayerDegreeGoal
   ```

   It replaces the unsafe manuscript route through generic
   Hoffman-Edmonds-Giles / glued-trellis cut sufficiency.

2. q = 1 branch.

   The current endpoint used by the high-modulus branch is:

   ```lean
   PrefixCount.ordinaryQeq1AuxTargetHallDataGoal
   ```

   Downstream q = 1 adapters checked in this pass include:

   ```lean
   PrefixCount.ordinaryQeq1CanonicalMatrixGoal_of_correction
   PrefixCount.ordinaryQeq1CanonicalCorrectionGoal_of_dataGoal
   PrefixCount.ordinaryQeq1CanonicalCorrectionDataGoal_of_auxSpecialMatchingData
   PrefixCount.ordinaryQeq1SignedCoreGoal_of_canonicalMatrix
   ```

3. Root-flat / prefix-count return adapter.

   The current high-modulus wrapper consumes:

   ```lean
   Concrete.PrefixCountRootFlatCanonicalReturnGoal
   ```

   and can also be fed by the schedule criterion through:

   ```lean
   Concrete.prefixCountRootFlatCanonicalReturnGoal_iff_scheduleCriterion
   ```

4. High-modulus endpoint.

   The key checked wrapper is:

   ```lean
   Concrete.oddCoreHighModulusPrefixCountGoal_of_qge2SeedClosure_qeq1AuxTargetHallData_and_rootFlatCanonical
   ```

   It has type:

   ```lean
   PrefixCount.OrdinaryQge2SignedSeedClosureGoal →
   PrefixCount.OrdinaryQeq1AuxTargetHallDataGoal →
   Concrete.PrefixCountRootFlatCanonicalReturnGoal →
   Concrete.OddCoreHighModulusPrefixCountGoal
   ```

   There is also a v4 preferred-block wrapper:

   ```lean
   Concrete.oddCoreHighModulusPrefixCountGoal_of_v4_preferred_blocks
   ```

### Worker 1 Current Status

The following focused checks pass in the current workspace:

```bash
lake env lean RoundComposite/PrefixCountHalfSlack.lean
lake env lean RoundComposite/FiniteHoffman/SignedTrellis.lean
lake env lean RoundComposite/OddCore.lean
lake env lean RoundComposite.lean
lake build RoundComposite
```

The global build completes successfully.  It reports nonfatal linter warnings,
mostly flexible `simp` warnings in `SignedTrellis.lean` and older style
warnings in `OddCore.lean` / `BaseTailGeometry.lean`.

No `sorry`, `admit`, `axiom`, or `constant` was found in the checked Goal 1
Lean files:

```text
RoundComposite/FiniteHoffman/SignedTrellis.lean
RoundComposite/PrefixCountHalfSlack.lean
RoundComposite/PrefixCount.lean
RoundComposite/OddCore.lean
```

### Worker 1 Follow-Up Notes

Worker 1's Lean stabilization is closed.  The remaining notes below are
paper-editing or cleanup choices, not open Lean blockers for the high-modulus
branch.

1. Decide whether to keep the current Lean case split:

   ```text
   n >= 8: uniform B-column construction
   n = 6: c=2-low construction
   n = 4: finite table
   ```

   or rewrite the manuscript to use the hand-proof split:

   ```text
   0 <= s <= h-3
   s = h-2
   s = h-1
   n = 4 finite table
   ```

   The two are mathematically compatible, but the paper and Lean theorem names
   should not suggest two different unresolved arguments.

2. Keep Appendix A synchronized with the Lean route when editing the paper:

   ```text
   ordinary q>=2 arithmetic
   -> binary-layer zero-one degree construction
   -> signed matrix
   -> q>=2 prefix-count core
   ```

   The old generic signed trellis / HEG sufficiency paragraph should not be
   used as the closing proof.

3. Optionally clean nonfatal linter warnings in `SignedTrellis.lean` after the
   mathematical content is frozen.

## Goal 2 / Worker 2: Small-Modulus Successor Base-Tail Branch

Owner: parallel Lean implementer / external prover.

Main files:

```text
RoundComposite/BaseTailTrades.lean
RoundComposite/ActiveHall.lean
RoundComposite/FiniteHoffman/EdgeColoring.lean
RoundComposite/BaseTailGeometry.lean
RoundComposite/OddCore.lean
```

Main theorem:

For every odd `m >= 3` and every `b >= 5`, the successor step should prove:

```lean
StandardCayleySolved b m →
StandardCayleySolved (2 * b + 1) m
```

Goal 1 handles the high-modulus count branch `2 * b + 1 <= m`, so the
substantive Goal 2 theorem is the small-modulus branch:

```lean
m < 2 * b + 1 →
StandardCayleySolved b m →
StandardCayleySolved (2 * b + 1) m
```

The current v7.5 endpoint import is:

```lean
import RoundComposite.V75Endpoints
```

The live paper-facing target is:

```lean
Concrete.OddModulusToriV75DirectModularTradeInputsGoal
Concrete.OddModulusToriV75DirectModularTradeBlocksGoal
Concrete.oddModulusToriAllDimensionsGoal_of_v75_directModularTrade_inputs
```

The detailed success criteria and retrospective workflow notes are in:

```text
docs/ODD_TORI_V75_DIRECT_MODULAR_TRADE_GOAL_20260505.md
```

Current Lean interfaces touched by this branch:

```lean
BaseTail.Trades.activeBlockResidueSpec
BaseTail.Trades.activeBlockResidueScheduleGoal
BaseTail.Trades.SuccessorActiveBlockCanonicalLocalSymbolTradeGoal
BaseTail.Trades.SuccessorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal
BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal
BaseTail.PrimitiveActivePrefixLiftAssemblyGoal
BaseTail.PrimitiveActivePrefixLowerTriangularLiftAssemblyGoal
BaseTail.ExpandedColorDirLowerTriangularMonodromyDataOfCountsPrimitiveGoal
BaseTail.CylinderBaseCycleData
BaseTail.cylinderBaseCycleData_of_isCylinder
BaseTail.ExpandedColorDirFiberLowerTriangularMonodromyGoal
BaseTail.primitiveActivePrefixLiftAssemblyGoal_of_expandedMonodromy
Concrete.OddSuccessorSmallModulusBaseTailGeometryFromModularTradesGoal
Concrete.OddSuccessorBaseTailWorker1CanonicalLocalTradeResidualGoal
Concrete.OddSuccessorBaseTailWorker1CanonicalLocalTradeLowerTriangularResidualGoal
Concrete.OddSuccessorBaseTailWorker1CanonicalFeasibleLocalTradeLowerTriangularResidualGoal
Concrete.OddSuccessorBaseTailWorker1CanonicalLocalTradeExpandedMonodromyResidualGoal
Concrete.OddSuccessorBaseTailWorker1CanonicalLocalTradeFiberMonodromyResidualGoal
Concrete.OddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeLowerTriangularBlocksGoal
Concrete.OddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalFeasibleLocalTradeLowerTriangularBlocksGoal
Concrete.oddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeBlocksGoal_of_lowerTriangularBlocks
Concrete.oddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeLowerTriangularBlocksGoal_of_feasibleLocalTradeLowerTriangularBlocks
Concrete.OddSuccessorSmallModulusSlackPacketLiftAddGoal
```

The former ActiveHall/de Werra interfaces remain as legacy adapters and
counterexample context, not as the current proof target:

```lean
ActiveHall.FiniteHoffman.RawZeroOneMatrixGoal.{0,0}
ActiveHall.FiniteHoffman.CompatibleDeWerraGoal.{0,0}
ActiveHall.HallRealizationGoal.{0,0}
Concrete.OddSuccessorSmallModulusBaseTailGeometryFromHallGoal
```

and then, with product closure and seeds:

```lean
D2, D3, D5, D7
  -> all d >= 2 and odd m >= 3
```

### Included Work

1. Base-tail cylinder construction.

   From `StandardCayleySolved b m`, build the `d = 2 * b + 1` base-tail
   cylinder.  In the successor case the packet numerology is:

   ```text
   T = b + 1
   d = b + T = 2b + 1
   packets.length = b
   total packet length = d
   each packet sums to m
   each packet entry is a unit modulo m
   ```

   The construction should expose active incidence data in which each base
   vertex has exactly `T` active colours.

2. Direct active-block modular residue schedule and local trade.

   The v7.3 residue schedule is now closed directly on the active-block
   cylinder:

```lean
BaseTail.Trades.activeBlockResidueSpec
BaseTail.Trades.activeBlockResidueScheduleGoal
BaseTail.Trades.successorActiveBlockResidueScheduleGoal
```

   It chooses a row/column-compatible primitive residue target:

   ```text
   R.RowCompatible Cyl.incidence
   R.ColCompatible Cyl.incidence
   PrimitiveResidueSpec hT R
   ```

   The remaining canonical local trade theorem must then produce:

   ```lean
   ActiveHall.SymbolingWithResidues Cyl.incidence R
   ```

   The current successor-scoped theorem surface is the canonical schedule case:

   ```lean
   BaseTail.Trades.SuccessorActiveBlockCanonicalLocalSymbolTradeGoal
   BaseTail.Trades.SuccessorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal
   ```

   The broader `BaseTail.Trades.SuccessorActiveBlockLocalSymbolTradeGoal`
   remains a sufficient optional fallback, but it is no longer the preferred
   residual.  The fallback is wired through:

   ```lean
   BaseTail.Trades.successorActiveBlockCanonicalLocalSymbolTradeGoal_of_successorLocalTrade
   Concrete.oddSuccessorBaseTailWorker1CanonicalLocalTradeLowerTriangularResidualGoal_of_successorLocalTrade_lowerTriangular
   Concrete.oddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeLowerTriangularBlocksGoal_of_successorLocalTrade_lowerTriangular
   ```

   A weaker decomposition point is also available when the proof is first
   formulated as canonical feasibility plus a local-symbol trade theorem:

   ```lean
   BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleResidueGoal
   BaseTail.Trades.successorActiveBlockCanonicalLocalSymbolTradeGoal_of_feasible_and_localTrade
   BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal
   BaseTail.Trades.successorActiveBlockCanonicalLocalSymbolTradeGoal_of_feasible_and_feasibleLocalTrade
   ```

   `SuccessorActiveBlockCanonicalFeasibleResidueGoal` only supplies the
   canonical feasible matrix.  The restricted
   `SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal` is the current
   Lean name for the successor-scoped feasible-to-symboling bridge that avoids
   the known-false unrestricted Hall-realization theorem.

   This combined endpoint feeds the existing active-block and prefix-lift
   adapters:

   ```lean
   Concrete.OddSuccessorBaseTailWorker1CanonicalLocalTradeResidualGoal
   Concrete.OddSuccessorBaseTailWorker1CanonicalLocalTradeLowerTriangularResidualGoal
   Concrete.OddSuccessorBaseTailWorker1CanonicalFeasibleLocalTradeLowerTriangularResidualGoal
   Concrete.OddSuccessorBaseTailWorker1CanonicalLocalTradeExpandedMonodromyResidualGoal
   Concrete.OddSuccessorBaseTailWorker1CanonicalLocalTradeFiberMonodromyResidualGoal
   Concrete.OddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeBlocksGoal
   Concrete.OddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeLowerTriangularBlocksGoal
   Concrete.OddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalFeasibleLocalTradeLowerTriangularBlocksGoal
   Concrete.oddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeBlocksGoal_of_lowerTriangularBlocks
   Concrete.oddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeLowerTriangularBlocksGoal_of_feasibleLocalTradeLowerTriangularBlocks
   Concrete.OddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeExpandedMonodromyBlocksGoal
   Concrete.OddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeFiberMonodromyBlocksGoal
   Concrete.oddModulusToriAllDimensionsGoal_of_v73_returnTailClosedFullSupportTrellisCanonicalLocalTrade_blocks
   Concrete.oddModulusToriAllDimensionsGoal_of_v73_returnTailClosedFullSupportTrellisCanonicalFeasibleLocalTradeLowerTriangular_blocks
   Concrete.oddModulusToriAllDimensionsGoal_of_v73_returnTailClosedFullSupportTrellisCanonicalLocalTradeExpandedMonodromy_blocks
   ```

   Paper labels for this part of v7.3 map to the current Lean surfaces as:

   ```text
   lem:trade-reservoir
     -> BaseTail.Trades.SuccessorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal,
        still missing as a proof in Lean
   thm:active-residue-scheduling
     -> BaseTail.Trades.SuccessorActiveBlockLocalSymbolTradeGoal
   thm:active-realization
     -> BaseTail.Trades.SuccessorActiveBlockCanonicalLocalSymbolTradeGoal
   thm:base-tail-lift
     -> BaseTail.PrimitiveActivePrefixLiftAssemblyGoal
        via BaseTail.PrimitiveActivePrefixLowerTriangularLiftAssemblyGoal
   ```

   The current primary Lean residual below the prefix lift is the generic
   lower-triangular projected-lift endpoint:

   ```lean
   BaseTail.PrimitiveActivePrefixLowerTriangularLiftAssemblyGoal
   Concrete.OddSuccessorBaseTailWorker1CanonicalLocalTradeLowerTriangularResidualGoal
   Concrete.OddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeLowerTriangularBlocksGoal
   Concrete.oddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeBlocksGoal_of_lowerTriangularBlocks
   ```

   The adapters from this endpoint to
   `BaseTail.PrimitiveActivePrefixLiftAssemblyGoal` are already present, so the
   missing proof is the theorem that constructs the lower-triangular/unit
   projected lift from `BaseTail.ActiveSymbolingCountsPrimitive`.

   The compressed base cycle part is no longer a residual:

   ```lean
   BaseTail.CylinderBaseCycleData
   BaseTail.cylinderBaseCycleData_of_isCylinder
   ```

   `CylinderBaseCycleData` fixes `period c = m ^ (b + 1)`, so the lower
   triangular lift theorem can work over exactly one compressed base cycle.

   The expanded-color-direction monodromy endpoints below remain useful
   diagnostic adapters, but they are no longer the preferred proof boundary.
   Because `expandedColorDir` depends only on the collapsed base direction, this
   route appears too weak for the final primitive fiber lift without an
   additional nontrivial fiber-return theorem.

   ```lean
   BaseTail.ExpandedColorDirLowerTriangularMonodromyDataOfCountsPrimitiveGoal
   BaseTail.ExpandedColorDirFiberLowerTriangularMonodromyGoal
   BaseTail.PrimitiveActivePrefixExpandedLowerTriangularMonodromyGoal
   BaseTail.primitiveActivePrefixLiftAssemblyGoal_of_expandedMonodromy
   ```

   Legacy warning: the earlier general finite theorem is not merely open.  In
   the current unrestricted form, it is false.  The affected Lean-facing
   endpoints are:

   ```lean
   RawZeroOneMatrixGoal
   CompatibleDeWerraGoal
   HallRealizationGoal
   ```

   Two finite counterexamples are now known:

   - The two-sided compatible de Werra statement with allowed pairs
     `A_k, B_k` and rectangle cuts is false on a `3 x 3` simple graph.  The
     edge `(1,3)` is forced to colour `β`, after which colour `β` needs the
     missing edge `(3,1)`.
   - The one-sided raw zero-one/Hall realization statement is also false.  In
     the `|R| = 3`, `|C| = 6`, `|X| = 5` matrix example, all row sums, column
     sums, and rectangle Hall cuts hold, but the support pattern forces
     `x1`, `x2`, and `x4` to use three copies of the cell `(c2,r3)` while only
     two copies exist.

   Therefore Worker 2 must not try to prove these endpoints as currently
   stated.  Ordinary Hall matching is still not enough by itself; any fallback
   count-matrix theorem must preserve the whole successor-specific residue
   schedule and cell capacities under the base-tail structure.

3. Residue-compatible rounding.

   The rounding proof must explicitly carry:

   ```text
   color-degree divisibility modulo m
   row/column residue compatibility
   nonnegativity after residue correction
   rectangle Hall cut slack
   universal unit residues
   ```

4. Base-tail geometry and primitive lift.

   The cylinder/lift proof must expose enough data for tail primitivity:

   ```text
   active block data
   mixed expansion data
   active symboling
   lower-triangular / unit monodromy primitive lift
   ```

### Worker 2 Current Residuals

The current Goal 2 residual package is:

```lean
BaseTail.Trades.SuccessorActiveBlockCanonicalLocalSymbolTradeGoal
BaseTail.Trades.SuccessorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal
BaseTail.PrimitiveActivePrefixLiftAssemblyGoal
BaseTail.PrimitiveActivePrefixLowerTriangularLiftAssemblyGoal
Concrete.OddSuccessorBaseTailWorker1CanonicalLocalTradeResidualGoal
Concrete.OddSuccessorBaseTailWorker1CanonicalLocalTradeLowerTriangularResidualGoal
Concrete.OddSuccessorBaseTailWorker1CanonicalFeasibleLocalTradeLowerTriangularResidualGoal
Concrete.OddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeLowerTriangularBlocksGoal
Concrete.OddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalFeasibleLocalTradeLowerTriangularBlocksGoal
Concrete.oddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeBlocksGoal_of_lowerTriangularBlocks
Concrete.oddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeLowerTriangularBlocksGoal_of_feasibleLocalTradeLowerTriangularBlocks
```

The expanded/fiber monodromy endpoints remain diagnostic or optional adapters,
not the current primary proof boundary:

```lean
BaseTail.ExpandedColorDirLowerTriangularMonodromyDataOfCountsPrimitiveGoal
BaseTail.ExpandedColorDirFiberLowerTriangularMonodromyGoal
BaseTail.PrimitiveActivePrefixExpandedLowerTriangularMonodromyGoal
Concrete.OddSuccessorBaseTailWorker1CanonicalLocalTradeExpandedMonodromyResidualGoal
Concrete.OddSuccessorBaseTailWorker1CanonicalLocalTradeFiberMonodromyResidualGoal
```

The active-block scheduler is no longer a residual theorem:

```lean
BaseTail.Trades.activeBlockResidueSpec
BaseTail.Trades.activeBlockResidueScheduleGoal
```

The previously isolated rounding residual remains useful as supporting
structure, but it is not the final theorem surface for v7.3:

```lean
Concrete.ActiveHallLargeMarginControlledResidueRoundingGoal
```

The old finite theorem residual is no longer a valid proof target as stated:

```lean
ActiveHall.FiniteHoffman.RawZeroOneMatrixGoal.{0,0}
```

and the same warning applies to the currently stated:

```lean
ActiveHall.HallRealizationGoal.{0,0}
```

A corrected Goal 2 proof must instead supply a successor-specific active
symboling theorem compatible with the actual base-tail incidence matrices,
together with the residue-compatible rounding and primitive lift above.

## Final Auditor

Owner: one person after both worker branches are merged.

Responsibilities:

1. Confirm the final theorem path proves exactly:

   ```lean
   ∀ {d m : Nat}, 2 ≤ d → Odd m → 3 ≤ m →
     Shared.CayleyHamiltonDecomposition d m
   ```

2. Run strict gates:

   ```bash
   lake build RoundComposite
   git diff --check
   grep -R -n -E '\b(sorry|admit|axiom|constant)\b' \
     RoundComposite Shared TorusD3Odd D5Odd D7Odd --include='*.lean'
   ```

3. Verify that no theorem used in the final branch is only a `Prop` endpoint
   unless it is explicitly part of the remaining external theorem boundary.

4. Check that the manuscript and Lean theorem names describe the same proof
   path, especially in Appendix A.

## Known Dirty State During This Update

At the time of this update, unrelated or Goal 2-oriented files are already
dirty in the shared worktree:

```text
RoundComposite/ActiveHall.lean
RoundComposite/FiniteHoffman/EdgeColoring.lean
lake-manifest.json
scripts/d5_odd_paper_verify.py
Torus-Hamilton-Decomposition/
```

Worker 1 should not revert or include those changes unless explicitly asked.
