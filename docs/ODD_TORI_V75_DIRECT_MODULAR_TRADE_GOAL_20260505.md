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

The current Lean surface has been reduced to a one-site pre-correction
reservoir form, and the pre-correction/local-trade distinction is now closed:

```lean
BaseTail.Trades.SuccessorActiveBlockCanonicalPreCorrectionGoal
BaseTail.Trades.permuteResidueSpec_target_eq_activeBlockResidueSpec_of_preTarget
BaseTail.Trades.successorActiveBlockCanonicalLocalSymbolTradeGoal_of_preCorrection
BaseTail.Trades.successorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal_of_preCorrection
BaseTail.Trades.successorActiveBlockCanonicalPreCorrectionGoal_of_canonicalLocalTrade
BaseTail.Trades.successorActiveBlockCanonicalPreCorrectionGoal_iff_canonicalLocalTrade
BaseTail.Trades.successorActiveBlockCanonicalPreCorrectionGoal_of_finiteCoactiveSiteReservoir
BaseTail.Trades.successorActiveBlockCanonicalPermutationCorrectionGoal_of_canonicalLocalTrade
BaseTail.Trades.successorActiveBlockCanonicalPermutationCorrectionGoal_iff_canonicalLocalTrade
BaseTail.Trades.successorActiveBlockCanonicalPreCorrectionGoal_iff_finiteCoactiveSiteReservoir
```

The identity site permutation turns any canonical local-trade realization into a
valid pre-correction witness, while the earlier permutation-correction adapter
returns from pre-correction to canonical local trade.  The finite-reservoir,
pre-correction, and permutation-correction names are now theorem-equivalent to
the canonical local-trade endpoint.  Worker A's remaining mathematical content
is therefore the actual finite canonical local/reservoir realization, not an
extra correction endpoint.

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
BaseTail.CylinderBaseCycleData.sum_orbit_eq_univ
```

and construct the lower-triangular/unit return data needed by the active
prefix-count lift.

Worker B status note:

```lean
BaseTail.expandedColorDirCore_fiberStep_coord_eq_add_directCarry
BaseTail.expandedColorDirCore_sectionReturn_coord_eq_add_sum_directCarry
BaseTail.expandedColorDirCore_sectionReturn_increment_eq_sum_directCarry
BaseTail.expandedColorDirCore_sectionReturn_increment_independent_of_fiber
```

These Lean lemmas now make the diagnostic `expandedColorDir` route explicit:
its fiber section return is a direct sum of symbol-count carries along the
compressed base orbit, and the resulting coordinate increment is independent of
the incoming fiber point.  Therefore `expandedColorDir` itself should not be
used as the final lower-triangular primitive lift.  For ranks `k > 0`, a
fiber-independent increment cannot supply the unit lower-triangular cocycle
needed after summing over the previous `k` fiber coordinates.  The remaining
proof of `BaseTail.PrimitiveActivePrefixLowerTriangularLiftAssemblyGoal` must
introduce a fiber-dependent active prefix-count tail rule whose section return
has the unit lower-triangular cocycles required by
`Shared.zmodVectorLowerTriangularUnitCycleCoordinate`.

Completion audit for the current Worker B goal:

| Requirement | Current evidence | Status |
|---|---|---|
| Close `BaseTail.PrimitiveActivePrefixLowerTriangularLiftAssemblyGoal` | The name is still a `Prop` input in `RoundComposite/BaseTailGeometry.lean`; `RoundComposite/V75Endpoints.lean` packages it as an input. | Open |
| Wire the v7.5 endpoint without old ActiveHall/de Werra route | `RoundComposite/V75Endpoints.lean` uses the high branch, canonical local trade, and lower-triangular lift inputs. It does not require `RawZeroOneMatrixGoal`, `CompatibleDeWerraGoal`, or `HallRealizationGoal`. | Wired |
| Stabilize the build surface | `lake build RoundComposite.BaseTailGeometry` and `lake build RoundComposite.V75Endpoints` pass with warnings only. | Built |
| Identify the exact remaining theorem | The missing theorem is a concrete fiber-dependent active prefix-count lift, not the diagnostic `expandedColorDir` monodromy. | Open |

The next Lean target should be a new core below
`PrefixProjectedLowerTriangularLiftColorDir`, replacing `expandedColorDirCore`
with an active tail permutation depending on the collapse fiber.  Its local
rule should be the active analogue of the prefix-count `lambda_rho` rule:
symbol `0` supplies the rank-zero unit count, and symbols `sigma >= 2` supply
unit cocycles through the primitive differences `count sigma - count 1`.

The common Latin/projection part of this replacement is now separated in Lean:

```lean
BaseTail.activePermutedColorDir
BaseTail.collapseVertex_cayleyColorStep_activePermutedColorDir
BaseTail.activePermutedColorDirEdgePartition
BaseTail.activePermutedColorDirCore
BaseTail.ActiveSymboling.count_cast_eq_sum_indicator
BaseTail.activePermutedColorDirCore_fiberStep_coord_eq_add_directCarry
BaseTail.activePermutedColorDirCore_sectionReturn_coord_eq_add_sum_directCarry
```

Here `tailPerm y z : Fin T ≃ Fin T` is an arbitrary permutation depending on
the collapsed base point `y` and collapse fiber `z`.  The theorem
`activePermutedColorDirEdgePartition` proves that any such fiber-dependent
active-tail permutation preserves the Cayley edge partition, and
`collapseVertex_cayleyColorStep_activePermutedColorDir` proves that it still
projects to the compressed cylinder step.  Thus the remaining proof is now
purely the monodromy/cocycle theorem for the specific prefix-count
`lambda_rho` choice of `tailPerm`.  The direct-carry theorem records the
pointwise rule: at an active edge the fiber step adds `1` exactly in the
permuted non-last tail coordinate, and the section-return theorem rewrites the
fiber increment as the sum of those fiber-dependent carries along the base
orbit.

The canonical prefix-count specialization is also separated from the generic
permuted-tail skeleton:

```lean
BaseTail.activeTailLambdaRho
BaseTail.activeTailCanonicalRho
BaseTail.activePrefixTailPerm
BaseTail.activePrefixPermutedColorDirCore
BaseTail.activePrefixPermutedColorDirCore_fiberStep_coord_eq_add_directCarry
BaseTail.activePrefixPermutedColorDirCore_sectionReturn_coord_eq_add_sum_directCarry
```

This keeps `BaseTailGeometry.lean` independent of `OddCore.lean` while making
the intended prefix-count `lambda_rho` rule explicit at the active-tail level.
The latest decomposition also isolates the remaining monodromy theorem behind:

```lean
BaseTail.ActivePermutedColorDirLowerTriangularMonodromyGoal
BaseTail.ActivePermutedColorDirFiberLowerTriangularMonodromyGoal
BaseTail.primitiveActivePrefixLowerTriangularLiftAssemblyGoal_of_activePermutedMonodromy
BaseTail.primitiveActivePrefixLowerTriangularLiftAssemblyGoal_of_activePermutedFiberMonodromy
```

Thus `PrimitiveActivePrefixLowerTriangularLiftAssemblyGoal` is reduced to
constructing lower-triangular section-return data for the canonical active
prefix permutation, preferably over the already closed `CylinderBaseCycleData`
base-cycle witness.

The first canonical-rho layer is now closed in Lean:

```lean
BaseTail.activeTailCanonicalRhoFirstNat_minimal
BaseTail.activeTailCanonicalRho_val_lt_iff_exists_hit_before
BaseTail.activeTailCanonicalRho_val_lt_congr_of_agree_before
BaseTail.activeTailCanonicalRho_val_lt_add_single_iff
BaseTail.activeTailCanonicalRho_val_lt_sub_single_iff
BaseTail.activeTailCanonicalRho_last_iff
BaseTail.activeTailCanonicalRho_pred_hitNat
BaseTail.activeTailCanonicalRho_no_hit_before
BaseTail.activeTailCanonicalRho_update_at_rho
BaseTail.activeTailCanonicalRho_add_at_rho
BaseTail.activeTailCanonicalRho_sub_at_rho
BaseTail.activeTailCanonicalRho_dynamic_add_bijective
```

The reusable fiber-bijection algebra for piecewise single-coordinate
translations is also available:

```lean
BaseTail.zmodVector_piecewise_add_single_id_bijective
BaseTail.zmodVector_piecewise_id_add_single_bijective
BaseTail.zmodVector_piecewise_add_single_add_single_bijective
```

The local bijectivity target for the canonical active prefix rule is now also
closed:

```lean
BaseTail.activePrefixPermutedColorDirCore_fiberStep_bijective
BaseTail.CylinderBaseCycleData.sum_range_orbit_eq_univ
BaseTail.ActiveSymboling.count_cast_eq_sum_indicator
BaseTail.activePrefixColorDirCoreDirectCarry_zero
BaseTail.activePrefixPermutedColorDirCore_sectionReturn_zero_eq_add_count
BaseTail.ActivePrefixPermutedColorDirFiberLowerTriangularReturnData
BaseTail.ActivePrefixPermutedColorDirFiberLowerTriangularReturnGoal
BaseTail.activePrefixPermutedColorDirFiberLowerTriangularMonodromyGoal_of_return
BaseTail.primitiveActivePrefixLowerTriangularLiftAssemblyGoal_of_activePrefixPermutedFiberReturn
```

This proves that every one-step fiber map for the canonical `lambda_rho` active
tail rule is a permutation and exposes a smaller return-only residual.  The
rank-zero local carry is also identified: coordinate `0` receives a carry
exactly when the active symbol `0` is assigned to the current color, independent
of the incoming fiber.  This has now been lifted through a full base cycle:
the orbit sum over `CylinderBaseCycleData` is converted to a global vertex sum,
then folded into `ActiveHall.Symboling.count`, proving that the rank-zero
section-return carry is exactly `Φ.count c 0`.  The remaining Worker B content
is therefore the positive-rank section-return theorem showing that the iterated
canonical active prefix rule supplies all lower-triangular unit cocycles.  The
return-data target keeps only `gamma`, `return_lower_triangular`, and
`return_unit`; the `fiber_bijective` field is now filled automatically from
`BaseTail.activePrefixPermutedColorDirCore_fiberStep_bijective`.

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
Concrete.OddModulusToriV75PreCorrectionInputsGoal
Concrete.oddModulusToriV75DirectModularTradeBlocksGoal_of_preCorrectionInputs
Concrete.oddModulusToriAllDimensionsGoal_of_v75_preCorrection_inputs
Concrete.OddModulusToriV75PreCorrectionReturnInputsGoal
Concrete.oddModulusToriV75DirectModularTradeBlocksGoal_of_preCorrectionReturnInputs
Concrete.oddModulusToriAllDimensionsGoal_of_v75_preCorrection_return_inputs
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
