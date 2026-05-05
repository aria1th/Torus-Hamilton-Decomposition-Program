# Odd Tori Parallel Lean Work Split

Date: 2026-05-05

Objective:

```lean
∀ {d m : Nat}, 2 ≤ d → Odd m → 3 ≤ m →
  Shared.CayleyHamiltonDecomposition d m
```

The remaining proof work should be split between two Lean implementers, with a
third person doing the final audit.

## Worker 1: Base-Tail Geometry Integration

Owner: current Codex thread.

Main files:

```text
RoundComposite/BaseTailGeometry.lean
RoundComposite/OddCore.lean
RoundComposite/ActiveHall.lean
docs/ODD_TORI_COMPLETION_GOAL_20260505.md
```

Targets:

```lean
Concrete.OddSuccessorBaseTailActiveBlockMixedCylinderConstructionGoal
Concrete.OddSuccessorBaseTailActiveBlockMixedCompatibleResidueRoundingGoal
Concrete.OddSuccessorBaseTailActiveBlockPrimitiveLiftGoal
```

Current key interfaces:

```lean
Concrete.oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_activeBlockMixedCompatiblePieces
BaseTail.ActiveBlockData
BaseTail.MixedExpansionData
BaseTail.MixedExpansionData.slack_error_lt_T_mul_mixedCount_proper_min
ActiveHall.Incidence.mixedCount
ActiveHall.CountMatrix.hallCuts_of_nontrivial_scaled_bary_error_le_mixed
```

Work plan:

1. Prove the cylinder construction returns both `ActiveBlockData` and
   `MixedExpansionData`.
2. Prove the controlled residue-rounding theorem using the mixed-expansion
   slack bridge.
3. Prove the primitive active lift from `IsPrimitiveActiveSymboling` and packet
   proper-prefix-unit facts.
4. Connect the three pieces through
   `oddSuccessorSmallModulusBaseTailGeometryCoreFromHallGoal_of_activeBlockMixedCompatiblePieces`.

Do not weaken the target back to an opaque `OddCoreSmallModulusSlackPacketLift`
unless the proof internally exposes the cylinder, mixed expansion, rounding,
and lift components.

Current Worker 1 state:

```lean
Concrete.OddSuccessorBaseTailActiveBlockMixedCylinderConstructionGoal
```

is closed in Lean.  The base-tail geometry path now has a closed-cylinder
adapter:

```lean
Concrete.oddSuccessorSmallModulusBaseTailGeometryFromHallGoal_of_worker1LargeMarginResiduals
```

so the remaining Worker 1 residuals are exactly:

```lean
Concrete.ActiveHallLargeMarginControlledResidueRoundingGoal
BaseTail.PrimitiveActivePrefixLiftAssemblyGoal
```

The first is the pure finite residue-aware count-matrix rounding theorem with
large row margins.  The second is the prefix-tail lift theorem; the legacy
`BaseTail.ExpandedColorDirColorHamiltonianGoal` route is diagnostic only,
because the direct expanded direction has only translation monodromy on a
`(T - 1)`-dimensional fiber and cannot be the general `T > 2` proof.

## Worker 2: Finite Integrality And de Werra

Owner: parallel Lean implementer / external prover.

Main files:

```text
RoundComposite/PrefixCount.lean
RoundComposite/PrefixCountHalfSlack.lean
RoundComposite/ActiveHall.lean
RoundComposite/FiniteHoffman/EdgeColoring.lean
```

Targets:

```lean
PrefixCount.OrdinaryQge2SignedFullSupportTrellisGoal
ActiveHall.EraseLastHallCutsProperTokenQuotaSelectionGoal.{0,0}
```

Equivalent or downstream targets:

```lean
PrefixCount.OrdinaryQge2SignedSeedProperCutClosureGoal
ActiveHall.FiniteHoffman.RawZeroOneMatrixGoal.{0,0}
ActiveHall.HallRealizationGoal.{0,0}
```

Existing adapters:

```lean
PrefixCount.ordinaryQge2SignedSeedProperCutClosureGoal_of_fullSupportTrellisGoal
PrefixCount.ordinaryQge2SignedFullSupportTrellisGoal_iff_seedProperCutClosureGoal
ActiveHall.hallRealizationGoal_iff_eraseLastHallCutsProperTokenQuotaSelectionGoal
ActiveHall.FiniteHoffman.rawZeroOneMatrixGoal_iff_eraseLastHallCutsProperTokenQuotaSelectionGoal
```

Work plan:

1. Prove `OrdinaryQge2SignedFullSupportTrellisGoal` as the ordinary-row signed
   trellis integrality theorem. Do not generalize to arbitrary-row signed
   packing; the repository proves that stronger statement is false.
2. Prove `EraseLastHallCutsProperTokenQuotaSelectionGoal.{0,0}` or an
   equivalent finite Hoffman/de Werra theorem. Mathlib Hall alone closes
   ordinary one-column matching but does not preserve all residual rectangle
   cuts.
3. Keep the q>=2 trellis proof independent from the ActiveHall/de Werra proof
   where possible.

## Final Auditor

Owner: one person after both worker branches are merged.

Responsibilities:

1. Confirm that the final endpoint no longer requires the three core
   assumptions.
2. Run strict gates:

```bash
lake build RoundComposite
git diff --check
grep -R -n -E '\b(sorry|admit|axiom|constant)\b' \
  RoundComposite Shared TorusD3Odd D5Odd D7Odd --include='*.lean'
```

3. Inspect the final theorem path to ensure it proves exactly:

```lean
∀ {d m : Nat}, 2 ≤ d → Odd m → 3 ≤ m →
  Shared.CayleyHamiltonDecomposition d m
```

4. Check that any new theorem used as a bridge is proved in Lean, not declared
   by `axiom`, `constant`, `sorry`, or `admit`.

## Current Commit Baseline

Recent relevant commits:

```text
f963730 Isolate large-margin active rounding residual
47ef1c1 Close successor base-tail cylinder assembly
201469d Refine odd tori formalization targets
d2a28e7 Clarify active Hall mixed-count slack
fab6c04 Isolate base-tail mixed expansion target
36dc1ad Split base-tail controlled rounding target
8ad201a Characterize mixed active cuts
```

Known unrelated dirty state at the time of writing:

```text
lake-manifest.json
scripts/d5_odd_paper_verify.py
Torus-Hamilton-Decomposition/
```
