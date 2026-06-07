# H2 Paper-Only Theorem Targets - 2026-06-07

This note answers the question:

> If we only had the paper, which theorems should we prove to close H2
> faithfully?

The answer is not "prove the current rows compute by `rfl`."  The paper uses
run-collapse and switching-ribbon correspondences.  So the right target is a
small ladder of realization theorems, ending in a wild return-section
reindexing.

## Final Target

For paper-faithful H2, the final theorem should have this shape.

```lean
theorem D54_physical_rows_realize_fullReturn :
  ∃ rows : PhysicalLayerRows,
  ∃ e : Seed ≃ RootState,
    PhysicalRowsLayerBijectiveGoal rows ∧
    PhysicalRowsReturnMapConjGoal rows e
```

Equivalently, map-level:

```lean
(schedule rows).returnMap c w =
  e (LowD5M4.fullReturn c (e.symm w))
```

This is exactly the paper's last D5(4) realization sentence:

1. terminal `A2` layer word,
2. `Y` row word,
3. neutral `Z` row,
4. five local substitutions,
5. switching-ribbon/run-collapse reindexing.

The equivalence `e` must be allowed to be wild.  It is not the plain coordinate
chart `(Q4 x Y) x Z = (Z/4)^4`.

## Theorem Ladder

### T1. Root-Flat Return Criterion

Generic paper theorem.

```lean
theorem root_flat_return_criterion :
  RF1 S -> RF2 S -> (∀ c, IsSingleCycleMap (returnMap S c)) ->
  HamiltonDecomposition
```

This is already represented in Lean by the root-flat bridge.  If starting from
paper only, prove this first.

### T2. Partial Exchange Preserves RF2

Generic switching theorem.

```lean
theorem partial_exchange_preserves_layer_bijection :
  Function.Bijective T ->
  Function.Bijective R ->
  T.symm '' (R '' U) = U ->
  Function.Bijective (fun x => if x ∈ U then R x else T x)
```

Singleton form is enough for the expected D54 sites:

```lean
theorem singleton_switch_preserves_layer_bijection :
  T p = R p ->
  Function.Bijective (partialExchange T R {p})
```

This is the RF2 half of the paper's "two-entry exchange inside an existing
Latin row."

### T3. Switching Ribbon Return Effect

Generic ribbon theorem.

```lean
theorem switching_ribbon_realizes_cut_splice :
  supportSeparated switchData ->
  returnMap (switchedSchedule switchData) =
    cutSpliceReturn (returnMap baseSchedule) switchData
```

This theorem is the paper's bridge from local layer switches to first-return
maps.  It should not mention D5(4) constants.  It says that a local two-color
ribbon exchange changes the section return by the corresponding cut-splice
operation.

### T4. Terminal A2 Physical Realization

This is the first D54-specific prerequisite.  It must be a realization theorem,
not a pointwise guess for `dir`.

For H2, the `m = 4` version is enough:

```lean
theorem terminal_A2_m4_physical_realization :
  ∃ rows : TerminalPhysicalRows 4,
  ∃ eT : TerminalSeed 4 ≃ TerminalRootState 4,
    terminalRF1 rows ∧
    terminalRF2 rows ∧
    terminalStep rows = standardD3RootStep ∧
    ∀ c w,
      terminalReturnMap rows c w =
        eT (terminalReturn (m := 4) c (eT.symm w))
```

For the full paper, prove the parametric version for every even `m >= 4`.

The important point: the paper row word `omega_m(q)` is a physical elementary
triangle matching.  It should be converted into an actual root-flat schedule by
a theorem, not by reading `omega(qCoord w)` as a row at every root source.
For the current Lean interface this standard-root requirement is the
`TerminalA2M4PhysicalRealization.step_eq_standard` field.  The plain chart
`eT = terminalRootEquiv.symm` is now ruled out by
`TerminalA2M4PhysicalRealization.not_terminalRootEquivSection`.

### T5. Terminal A2 Cyclicity

Paper theorem:

```lean
theorem terminal_A2_cyclicity :
  Even m -> 4 <= m ->
  ∀ c, IsSingleCycleMap (terminalReturn (m := m) c)
```

For H2 alone, only `m = 4` is needed.  Lean already has the finite-orbit
content needed by `LowD5M4Seed`, but the realization theorem T4 is separate.

### T6. Product/Y/Neutral-Z Base Realization

Lift the terminal realization into the D5(4) product before final reset.

Target shape:

```lean
theorem D54_product_base_realization :
  ∃ rows0 : PhysicalLayerRows,
  ∃ e0 : Seed ≃ RootState,
    PhysicalRowsLayerBijectiveGoal rows0 ∧
    ∀ c w,
      (schedule rows0).returnMap c w =
        e0 (baseProductReturn c (e0.symm w))
```

Here `baseProductReturn` is the paper product of:

- terminal `F0,F1,F2`,
- the `Y` row word giving the `P0/P1` selector behavior,
- neutral `Z`.

This is only the pre-reset base.  The neutral `Z` coordinate is preserved, so
this stage cannot prove RF3 on `Q4 x Y x Z`; Lean records this as
`RbaseNeutral_not_singleCycle` and
`D54ProductBaseRealization.returnMap_not_singleCycle`.  The final five-switch
theorem is the stage that inserts the missing `Z` unit carry.

This theorem should be stated at the same abstraction level as the paper.  Do
not expand it into a guessed row such as `terminalStdBaseRowAtState`.

### T7. D54 Reset Site Separation

Finite D54 table theorem.

```lean
theorem D54_reset_sites_separated :
  resetSitesAreDisjoint ∧
  resetSitesAvoidProtectedSelector ∧
  resetSitesAreValidSingletonSwitches
```

This packages the table facts:

- first-stage reset sites `p0,p1,p2`,
- final `Z` lift sites `a0..a4`,
- protected selector neighborhood,
- reserve points.

The output should feed T2/T3.

### T8. D54 Five-Switch Realization

Apply the five local substitutions to T6 using T2, T3, and T7.

```lean
theorem D54_five_switches_realize_fullReturn :
  ∃ rows : PhysicalLayerRows,
  ∃ e : Seed ≃ RootState,
    PhysicalRowsLayerBijectiveGoal rows ∧
    ∀ c w,
      (schedule rows).returnMap c w =
        e (LowD5M4.fullReturn c (e.symm w))
```

This is the actual paper-realization hard theorem.  `Main` currently closes the
H2 low-base obligation through the direct finite RF certificate packaged in
`H2.D54.lowD5M4FiniteConjugateDirectRFInput`; T8 remains the theorem needed to
replace that direct/generated route by the paper's terminal/product/five-switch
ribbon realization.

Do not revive the archived broad row-read table route as T8.  The archive
theorems

```lean
not_preFinalP0P1RowWordReadGoals
H2TableRouteSkeleton_false
```

show that the old `H2TableRouteSkeleton` predicates overlap on the pre-final
`P0/P1` read.  The viable targets are path-local split data such as
`H2SkewProductPathRouteSkeleton`, or the active `H2RibbonCollapseInput` /
`D54FiveSwitchRealization` handoff.

Active Lean refinement: the return-level fold target has a closed seed model.

```lean
seedTwoStageFullReturnLayer_return_eq_Rhat :
  forall c s,
    seedLayerReturn seedTwoStageFullReturnLayer c s = Rhat c s
```

The model is:

- layer `0`: `RbaseNeutral c`;
- layer `1`: the post-base `Z` carry at `Rbase c (bSite c)`;
- layers `2,3`: identity.

Thus T8 no longer needs a raw finite proof that a four-layer seed fold equals
`LowD5M4.fullReturn`; it can instead prove that the paper five-switch/ribbon
construction is conjugate to this closed seed-level return model, or prove the
same rows satisfy:

```lean
D54TwoStageSingletonSwitchRealization
```

Lean now upgrades this directly to `D54FiveSwitchRealization` and then to
`D54PaperRealization` with the closed D54 table facts.  Alternatively, T8 can
prove the equivalent singleton-switch seed fold and then identify it with this
model.

The public stage-wise assembly endpoint is:

```lean
EvenV11.lowD5M4_of_paperStagesTwoStageSingleton
```

It takes exactly the three remaining construction stages: terminal realization,
product-base realization, and two-stage singleton-switch realization.

### T9. H2 Certificate Assembly

For the direct RF route, this is already active:

```lean
EvenV11.H2.D54.finalLowD5M4RootFlatCertificateFamily_of_lowD5M4Finite
```

For the paper-faithful route, once T8 is available:

```lean
EvenV11.lowD5M4_of_paperRealization
EvenV11.lowD5M4_of_paperRealizationLadder
```

This theorem is already structurally proved in Lean from either the direct RF
certificate or the H2 handoff.  If starting from paper only, it follows from T1
plus the single-cycle facts transported through `e`.

## What Not To Prove

These statements are tempting but not the paper-faithful H2 theorem.

1. `returnMap = paperReturn` under the plain coordinate chart.

   This is the tame-coordinate route.  It is not what the paper claims.

2. `terminalStdBaseRowAtState` realizes the terminal block.

   Python checks show this row is RF1/RF2 before substitutions but has the wrong
   return maps.

3. "Y and Z substitutions on chosen layers fix the naive row."

   Python checks show all 16 layer splits fail RF2.

4. The generated finite D5(4) blob implies the paper handoff.

   It is a valid direct RF certificate and now closes the active H2 low-base
   obligation, but it has no common conjugacy to `LowD5M4.fullReturn` and
   therefore does not close the paper handoff.

5. The existing finite D3 m=4 schedule is the terminal A2 carrier.

   It is RF-valid, but it has no common conjugacy to the paper terminal
   `F_i` returns.  The computed relation invariant is already different:
   `order(R0 o R2) = 63` for `D3EvenM4`, versus `order(F0 o F2) = 33` for the
   paper terminal maps.  It cannot replace T4.

## Minimal H2 Proof Order

The fastest paper-faithful order is:

1. T4 for `m = 4`.
2. T6 using T4.
3. T7 from the D54 table.
4. T2/T3 in the singleton-switch form, if the generic versions are not already
   strong enough.
5. T8.
6. Feed T8 into the existing `LowD5M4RibbonInterface` handoff if replacing the
   direct finite RF route by a paper-faithful realization.
