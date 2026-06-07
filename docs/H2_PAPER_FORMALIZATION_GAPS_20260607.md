# H2 Paper Formalization Gaps - 2026-06-07

This note records what is missing or underspecified in the paper text if the
goal is a Lean-formal, paper-faithful proof of H2 D5(4).

The point is not that the paper argument is wrong.  The issue is that several
steps are written at the usual mathematical-compression level, while Lean needs
explicit maps, domains, support conditions, and conjugacies.

## Summary

The paper gives the correct high-level construction:

1. terminal `A2` layer word,
2. product with the `Y` row word and neutral `Z` row,
3. five local D54 substitutions,
4. switching-ribbon realization,
5. root-flat return criterion.

What is missing for formalization is the explicit theorem interface connecting
these levels.

Current Lean status: the H2 `D5(4)` low-base certificate is closed by the
separate direct RF certificate

```lean
EvenV11.LowD5M4Finite.finalLowD5M4RootFlatCertificateFamily
```

The gaps below are therefore no longer blockers for `Main.assume_lowD5M4`; they
are the remaining obligations for a paper-faithful realization of the §11
terminal/product/five-switch construction.

2026-06-07 Lean update: `EvenV11/D54ReturnCore.lean` now records the
return-level terminal bridge explicitly:

```lean
F_eq_terminalReturn
F_fun_eq_terminalReturn
terminalReturn4_singleCycle
TerminalA2M4ReturnCore.terminalReturn_eq_paper
TerminalA2M4PhysicalRealization.return_eq_terminalReturn
TerminalA2M4PhysicalRealization.step_eq_standard
TerminalA2M4PhysicalRealization.not_terminalRootEquivSection
TerminalA2M4PhysicalRealization.actualF0F2_iterate_33
TerminalA2M4PhysicalRealization.actualF0F2_no_positive_iterate_lt33
RbaseNeutral_not_singleCycle
D54ProductBaseRealization.returnMap_not_singleCycle
```

Thus the return-level `F_i` used by `LowD5M4.fullReturn` is no longer merely an
internal `LowD5M4Seed` convention; it is theorem-linked to the paper-style
`TerminalA2LowMod.terminalReturn (m := 4)`.

The bridge now also records a conjugacy-invariant terminal relation: the
two-letter relation `F0 o F2` has exact order `33`, and every
`TerminalA2M4PhysicalRealization` must make the corresponding physical
relation

```lean
fun w => rows.returnMap 0 (rows.returnMap 2 w)
```

have the same exact order through its section equivalence `eT`.

## Gap 1. Terminal A2 Row Word Is Not Expanded Into Root-Flat Rows

The paper defines `omega_m(q)` as a row word on the elementary triangle
`q + {a0,a1,a2}` and states that it gives a Latin root-flat layer schedule.

For Lean, this is not enough.  We need the actual schedule:

```lean
terminalRows :
  ZMod m -> TerminalRootState m -> TorusColor 3 ≃ TorusDirection 3
```

plus the exact conversion from a physical triangle edge

```text
q + a_i  ->  q + a_{omega(q)_i}
```

to a standard root-flat direction at layer `t`.

This is the main source of ambiguity.  Reading `omega(qCoord w)` directly as a
row in root-flat coordinates is not the same statement as the paper's physical
triangle matching.

The stronger fixed-chart target is now ruled out computationally: in the plain
`terminalRootEquiv` chart, no paper terminal return `F_i` factors as four
standard D3 root-flat bijective layer maps.  Therefore the Lean terminal
realization must construct a section equivalence

```lean
eT : Q4 ~= TerminalRootState
```

and prove the return equality through `eT`, rather than using the standard
coordinate chart directly.  This negative control is now also recorded in Lean:

```lean
terminalStandardReturnMap_ne_fixedChartReturn_color1
TerminalA2M4PhysicalRealization.not_terminalRootEquivSection
```

The terminal realization record also now explicitly requires the standard D3
root step via `step_eq_standard`, so a future proof cannot satisfy the interface
with an arbitrary non-root-flat `step`.

## Gap 2. Terminal First-Return Equals `F_i` Is Only Sketched

The paper says the default word contributes the default fiber advance `Delta_i`,
and inserting the non-default local jumps gives `F_i`.

For Lean, this must be a precise run-collapse theorem:

```lean
terminalReturnMap terminalRows c =
  eT ∘ terminalReturn c ∘ eT.symm
```

or at least a pointwise version.  The proof must specify:

- the section being returned to,
- the intermediate default-run states,
- the active/non-default sites,
- the exact reindexing `eT`,
- why one period of physical layers collapses to `eta_i(z + Delta_i)`.

The paper has the idea, but not the explicit map-level statement.

## Gap 3. Product With `Y` and Neutral `Z` Is Not Written as Four Physical Rows

In D54, the paper says to start with the product of:

- terminal `A2` layer word,
- `Y` row word,
- neutral `Z` row.

For Lean, this product must become four actual D5(4) physical rows:

```lean
rows0 : PhysicalLayerRows
```

with RF1/RF2 and a return conjugacy to the pre-reset product returns:

```lean
baseProductReturn =
  (F0,F1,F2,P0,P1) × neutralZ
```

The paper does not spell out the row table or the product reindexing.  That is
acceptable in prose, but it is a missing formal interface.

This stage is necessary but not sufficient.  The neutral `Z` row means the
product-base return preserves the `Z` coordinate, so it cannot be RF3 on the
full `Seed = Q4 x Y x Z`.  Lean now records this no-go fact:

```lean
RbaseNeutral_not_singleCycle
D54ProductBaseRealization.returnMap_not_singleCycle
```

Therefore the final five-switch stage is mathematically necessary, not merely a
marked/reserve enhancement.

## Gap 4. "Rows Remain Latin and Layer Maps Remain Bijective" Needs Local Data

The paper says each substitution is a two-entry exchange inside an existing
Latin row, so Latinness and layer bijectivity are preserved.

For Lean, Latinness is local and easy, but RF2 needs a precise invariant:

```lean
T^{-1} R (U) = U
```

or, for singleton switches:

```lean
T p = R p
```

The paper lists the sites, but it does not explicitly give, for every
layer/color switch:

- the two maps `T` and `R`,
- the support `U`,
- the common image or comparison-set invariant,
- the layer-map equality connecting the physical row swap to the partial
  exchange theorem.

Those are required to prove RF2 without a finite blob.

Archive Lean also records a separate row-read blocker for the old table route:
the broad pre-final `P0/P1` read predicates overlap.  The theorem

```lean
not_preFinalP0P1RowWordReadGoals
H2TableRouteSkeleton_false
```

in `archive/EvenV11/V28Hard/D5M4H2PaperRows.lean` shows that the legacy
`H2TableRouteSkeleton` cannot be the next target as stated.  The active route
must use a path-local split such as `H2SkewProductPathRouteSkeleton`, or the
broader row/ribbon handoff `H2RibbonCollapseInput` / `D54FiveSwitchRealization`.

## Gap 5. Switching-Ribbon Realization Is Not Given in a D54-Ready Form

The paper's switching-ribbon lemma explains that local two-color ribbons realize
cut-splice operations on first returns.

For H2, Lean needs the instantiated theorem:

```lean
returnMap after five switches =
  cutSplice_4 (cutSplice_3 (... baseReturn ...))
```

and then:

```lean
that cut-splice product = LowD5M4.fullReturn
```

The paper does not provide this D54-specialized composition equation.  It states
the mechanism and the intended effect, but not the full map-level equality.

Active Lean status: the full map-level equality can now be supplied through the
smaller `D54FiveSwitchLayerModelRealization` interface.  That interface asks for
per-layer conjugacy to seed-side maps plus the seed-side fold equation

```lean
seedLayerReturn seedLayer c s = Rhat c s
```

and the generic theorem `physical_returnMap_conj_of_seedLayerReturn_eq` turns
these into the required physical return conjugacy.

The still more structured `D54FiveSwitchSeedSwitchRealization` interface fixes
the seed-side layer maps to singleton partial exchanges mirroring the physical
RF2 data.  Thus the physical layer-conjugacy proof is no longer an arbitrary
field: it follows from conjugating each comparison pair `T/R` and its singleton
site.  What remains is the paper-specific seed-side fold computation showing
that those five switches produce exactly `Rhat`.

2026-06-07 update: Lean now has a closed fixed seed model for the return-level
calculation:

```lean
seedTwoStageFullReturnLayer_return_eq_Rhat
seedTwoStageFullReturnLayer_bijective
seedTwoStageFullReturnLayer_return_singleCycle
```

This model performs `RbaseNeutral` in layer `0`, the corresponding post-base
`Z` carry in layer `1`, and neutral maps in layers `2,3`.  It closes the finite
fold calculation of `Rhat` itself.  The remaining paper-specific work is to
prove that the physical five-switch/ribbon construction is conjugate to the
appropriate seed-side switch model, or equivalently to bridge that switch model
to this closed two-stage return model.

The corresponding active Lean handoff is:

```lean
D54TwoStageLayerModelRealization
```

Supplying this fixed-layer conjugacy already produces the existing H2 ribbon
data.  If the same rows also come with singleton-switch RF2 data, the new
intermediate target

```lean
D54TwoStageSingletonSwitchRealization
```

upgrades directly to `D54FiveSwitchRealization`, and the closed D54 table facts
then package it as `D54PaperRealization` via
`D54PaperRealization.ofTwoStageSingletonSwitchRealization`.  Supplying
`D54FiveSwitchSeedSwitchRealization` remains the more paper-faithful route
because it exposes the seed-side singleton switch/ribbon mirror explicitly.

## Gap 6. The Wild Reindexing `e` Is Not Constructed Explicitly

The paper's argument uses run-collapse/ribbon correspondence.  In Lean, the H2
handoff needs:

```lean
e : Seed ≃ RootState
```

such that:

```lean
(schedule rows).returnMap c w =
  e (LowD5M4.fullReturn c (e.symm w))
```

The paper does not write this `e` as a concrete equivalence.  It is implicitly
obtained from the return-section correspondence.  That is enough in prose, but
Lean needs either:

- an explicit definition of `e`, or
- a theorem saying the switching-ribbon construction produces such an `e`.

The plain coordinate equivalence is not sufficient.

## Gap 7. Support Separation and Protected Selector Facts Are Table-Level, Not Theorem-Level

The paper says the supports are disjoint from the lifted selector/protected
neighborhood and references the reserve table.

For Lean, these must be theorem-level facts:

```lean
resetSupportsPairwiseDisjoint
resetSupportsAvoidSelector
resetSupportsAvoidProtectedNeighborhood
reservePointsAdmissible
```

The current Lean data has much of the table content, but the paper does not
spell out every membership/nonmembership statement needed by the switching
proof.

Active Lean status: the finite D54 reset/support/protected-neighborhood table
facts are now packaged strongly enough for final assembly.  They are no longer
a separate H2-closing obligation: `D54PaperRealization.ofFiveSwitchRealization`
fills them from `D54ResetData.d54ResetTableCertificate`, the closed avoidance
lemmas, and the named `NTList`/`NhatList` protected-neighborhood lemmas in
`D54ReturnCore`.  `EvenV11.Main` now also exposes
`lowD5M4_of_paperRealization` and `lowD5M4_of_paperRealizationLadder`, so a
paper payload directly yields `FinalLowD5M4RootFlatCertificateFamily`.

The support payload now includes:

```lean
NTList_mem_iff_terminalNeighborhoodList_mem
resetSites_avoid_NTList
finalCylinders_avoid_NhatList
reservePoints_disjoint_NhatList
D54PaperRealization.finalCylindersAvoidProtected
D54PaperRealization.reserveDisjointProtected
```

What remains is not table separation, but the physical switching theorem that
uses these facts.

## Gap 8. The Paper Does Not Separate "Direct RF Certificate" From "Paper Realization"

A finite root-flat table can prove RF1/RF2/RF3 directly.  This is now the active
low-base closure through `LowD5M4Finite`.  But the paper-faithful path requires
a stronger statement: the returns must be linked to the paper's `fullReturn`
maps by the run-collapse/ribbon reindexing.

The paper naturally treats these as the same construction.  For Lean they should
be separated:

```lean
directRFData : RF1 ∧ RF2 ∧ RF3
paperRealizationData :
  rows ∧ e ∧ RF2 ∧ returnMap = e ∘ fullReturn ∘ e.symm
```

The first closes the current main-theorem H2 low-base obligation.  The second is
what closes the paper-faithful H2 handoff.

## What the Paper Does Provide

The paper does provide enough mathematical direction to choose the right Lean
targets:

- the abstract `T_i`, `P0`, `P1`, and `R_hat_i` maps,
- the reset and final switching sites,
- the terminal `A2` word and terminal returns `F_i`,
- the RF criterion,
- the partial-exchange/switching-ribbon mechanism,
- the reserve/protected-neighborhood intent.

So the missing content is mostly not new mathematics.  It is explicit
formalization glue:

1. exact root-flat rows,
2. exact return-section equivalences,
3. exact support invariants,
4. exact map-level switching equations.

## Practical Conclusion

To close H2 faithfully, do not try to repair `paperReturn` or a guessed
`terminalStdBaseRowAtState` row.  The proof should first introduce the missing
formal theorem interfaces above, especially:

```lean
terminal_A2_m4_physical_realization
D54_product_base_realization
D54_five_switches_realize_fullReturn
```

Once these are available, the existing H2 structural handoff is the right final
assembly point for replacing the direct RF witness by the paper-realization
witness.
