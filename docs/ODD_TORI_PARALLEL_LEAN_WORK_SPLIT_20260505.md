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
RoundComposite/ActiveHall.lean
RoundComposite/FiniteHoffman/EdgeColoring.lean
RoundComposite/BaseTailGeometry.lean
RoundComposite/OddCore.lean
```

Targets:

```lean
ActiveHall.FiniteHoffman.RawZeroOneMatrixGoal.{0,0}
ActiveHall.FiniteHoffman.CompatibleDeWerraGoal.{0,0}
ActiveHall.HallRealizationGoal.{0,0}
Concrete.OddSuccessorSmallModulusBaseTailGeometryFromHallGoal
Concrete.OddSuccessorSmallModulusSlackPacketLiftAddGoal
```

Main endpoint:

```lean
StandardCayleySolved b m →
StandardCayleySolved (2 * b + 1) m
```

and then, with product closure and seeds:

```lean
D2, D3, D5, D7
  -> all d >= 2 and odd m >= 3
```

### Included Work

1. ActiveHall / finite de Werra.

   The adapters are already extensive, but the central finite theorem is still
   not closed:

   ```lean
   RawZeroOneMatrixGoal
   CompatibleDeWerraGoal
   HallRealizationGoal
   ```

   Mathlib ordinary Hall matching is not enough by itself, because the theorem
   must preserve all residual rectangle cuts / quota constraints.

2. Residue-compatible rounding.

   The rounding proof must explicitly carry:

   ```text
   color-degree divisibility modulo m
   row/column residue compatibility
   nonnegativity after residue correction
   rectangle Hall cut slack
   universal unit residues
   ```

3. Base-tail geometry and primitive lift.

   The cylinder/lift proof must expose enough data for tail primitivity:

   ```text
   active block data
   mixed expansion data
   active symboling
   lower-triangular / unit monodromy primitive lift
   ```

### Worker 2 Current Residuals

The previously isolated base-tail residuals remain in the Goal 2 scope:

```lean
Concrete.ActiveHallLargeMarginControlledResidueRoundingGoal
BaseTail.PrimitiveActivePrefixLiftAssemblyGoal
```

The finite theorem residual remains:

```lean
ActiveHall.FiniteHoffman.RawZeroOneMatrixGoal.{0,0}
```

or any equivalent proved endpoint that implies:

```lean
ActiveHall.HallRealizationGoal.{0,0}
```

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
