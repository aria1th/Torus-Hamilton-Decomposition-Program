import EvenV11.V28Hard.D5M4H2Skeleton

/-!
# Paper-row checkpoints for the D5(4) H2 reset

This file records the first row-read facts that close directly from the standard
terminal row, and isolates a mismatch in the current full P0/P1 read interface.
The mismatch is useful for the next H2 repair pass: the paper row word is
path-local, while the current read predicates are broad enough to overlap.
-/

namespace EvenV11
namespace V28Hard
namespace D5M4H2PaperRows

open Shared
open LowD5M4Realization
open LowD5M4H2PaperRow
open D5M4H2Skeleton

/-- The naive product-row candidate before the five reset-port substitutions:
every layer uses the terminal `A2` row word plus the standard `Y` and `Z`
directions in the D5 chart.  The actual physical rows are obtained by applying
`resetPortRowOfBase` to this base row.

This candidate is useful as a row-read sanity checkpoint, but the RF2 check
below shows it is not the final paper row table. -/
def d54PaperProductRows : PaperLayeredBaseRows where
  layer0 := terminalStdBaseRowAtState
  layer1 := terminalStdBaseRowAtState
  layer2 := terminalStdBaseRowAtState
  layer3 := terminalStdBaseRowAtState

/-- The base-row API for the naive product-row candidate. -/
abbrev d54PaperProductBaseRow : ResetPortBaseRow :=
  d54PaperProductRows.baseRow

/-- The reset-port rows obtained from the naive product-row candidate by the
five local substitutions of Table D54-reset-ports. -/
abbrev d54PaperResetPortRow :
    ZMod 4 → LowD5M4Realization.RootState →
      TorusColor 5 ≃ TorusDirection 5 :=
  resetPortRowOfBase d54PaperProductBaseRow

@[simp] theorem d54PaperProductRows_baseRow
    (t : ZMod 4) (w : LowD5M4Realization.RootState) :
    d54PaperProductRows.baseRow t w =
      terminalStdBaseRowAtState w := by
  fin_cases t <;> simp [PaperLayeredBaseRows.baseRow, d54PaperProductRows]

theorem d54PaperProductRows_reads_terminalTailIndex
    (t : ZMod 4) (i : Fin 3) (q : LowD5M4.Q4) (y : LowD5M4.Y)
    (z : LowD5M4.Z) :
    BaseRowReadsTerminalTailIndex
      d54PaperProductRows.baseRow t i q y z := by
  rw [BaseRowReadsTerminalTailIndex]
  rw [d54PaperProductRows_baseRow]
  rfl

theorem d54PaperProductRows_reads_yShift_color3
    (t : ZMod 4) (q : LowD5M4.Q4) (y : LowD5M4.Y)
    (z : LowD5M4.Z) :
    BaseRowReadsYShift
      d54PaperProductRows.baseRow t 3 q y z := by
  rw [BaseRowReadsYShift]
  rw [d54PaperProductRows_baseRow]
  rfl

/-- First source in the RF2 collision for the naive product-row candidate. -/
abbrev d54PaperProductRowsCollisionA : LowD5M4Realization.RootState :=
  rootOfCoords ((0 : ZMod 4), (0 : ZMod 4))
    (0 : LowD5M4.Y) (0 : LowD5M4.Z)

/-- Second source in the RF2 collision for the naive product-row candidate. -/
abbrev d54PaperProductRowsCollisionB : LowD5M4Realization.RootState :=
  rootOfCoords ((0 : ZMod 4), (0 : ZMod 4))
    (3 : LowD5M4.Y) (1 : LowD5M4.Z)

theorem d54PaperProductRows_collision_sources_ne :
    d54PaperProductRowsCollisionA ≠ d54PaperProductRowsCollisionB := by
  decide

theorem d54PaperProductRows_layerMap_collision :
    (LowD5M4Schedule.schedule
      (dirOfRowEquiv (resetPortRowOfBase d54PaperProductRows.baseRow))).layerMap
        (0 : ZMod 4) (0 : TorusColor 5) d54PaperProductRowsCollisionA =
      (LowD5M4Schedule.schedule
      (dirOfRowEquiv (resetPortRowOfBase d54PaperProductRows.baseRow))).layerMap
        (0 : ZMod 4) (0 : TorusColor 5) d54PaperProductRowsCollisionB := by
  decide

/-- The all-terminal product-row candidate is not RF2: color `0` on layer `0`
identifies two distinct root states.  Hence this row table cannot be the final
paper H2 table, even though several row-read leaves close on it. -/
theorem not_d54PaperProductRows_layerBijective :
    ¬ ResetPortLayerBijectiveGoal d54PaperProductRows.baseRow := by
  intro hLayer
  exact d54PaperProductRows_collision_sources_ne
    ((hLayer (0 : ZMod 4) (0 : TorusColor 5)).1
      d54PaperProductRows_layerMap_collision)

theorem not_nonempty_d54PaperProductRows_layerEquivRF2Goal :
    ¬ Nonempty (PaperBaseRowLayerEquivRF2Goal d54PaperProductRows) := by
  rintro ⟨rf2⟩
  exact not_d54PaperProductRows_layerBijective
    (resetPortLayerBijective_of_layerEquivData
      d54PaperProductRows.baseRow rf2)

theorem not_nonempty_d54PaperProductRows_skewProductRF2Goal :
    ¬ Nonempty (PaperBaseRowSkewProductRF2Goal d54PaperProductRows) := by
  rintro ⟨rf2⟩
  exact not_d54PaperProductRows_layerBijective
    (resetPortLayerBijective_of_layerSkewProductData
      d54PaperProductRows.baseRow rf2)

theorem not_nonempty_d54PaperProductRows_singletonSwitchRF2Goal :
    ¬ Nonempty (ResetPortSingletonSwitchLayerData d54PaperProductRows.baseRow) := by
  rintro ⟨rf2⟩
  exact not_d54PaperProductRows_layerBijective
    (resetPortLayerBijective_of_singletonSwitchLayerData
      d54PaperProductRows.baseRow rf2)

/-- Compatibility wrapper retained for the now-refuted product-row candidate:
an inhabitant would still be enough to replace the current H2 `sorry`, but the
RF2 collision above proves this structure is empty. -/
structure D54PaperProductLayerEquivRibbonCollapseInput where
  rf2 : PaperBaseRowLayerEquivRF2Goal d54PaperProductRows
  e : LowD5M4Structural.Seed ≃ LowD5M4Structural.RootState
  returnRealization :
    PaperBaseRowReturnRealizationGoal d54PaperProductRows e

def D54PaperProductLayerEquivRibbonCollapseInput.toPaperRowsInput
    (input : D54PaperProductLayerEquivRibbonCollapseInput) :
    PaperRowsLayerEquivRibbonCollapseInput where
  rows := d54PaperProductRows
  rf2 := input.rf2
  e := input.e
  returnRealization := input.returnRealization

def D54PaperProductLayerEquivRibbonCollapseInput.toResetPortBaseRowData
    (input : D54PaperProductLayerEquivRibbonCollapseInput) :
    ResetPortBaseRowRibbonRealizationData :=
  input.toPaperRowsInput.toResetPortBaseRowData

theorem D54PaperProductLayerEquivRibbonCollapseInput.nonemptyMainH2Input
    (input : D54PaperProductLayerEquivRibbonCollapseInput) :
    Nonempty ResetPortBaseRowRibbonRealizationData :=
  input.toPaperRowsInput.nonemptyMainH2Input

/-- Skew-product RF2 wrapper for the now-refuted product-row candidate. -/
structure D54PaperProductSkewProductRibbonCollapseInput where
  rf2 : PaperBaseRowSkewProductRF2Goal d54PaperProductRows
  e : LowD5M4Structural.Seed ≃ LowD5M4Structural.RootState
  returnRealization :
    PaperBaseRowReturnRealizationGoal d54PaperProductRows e

noncomputable def D54PaperProductSkewProductRibbonCollapseInput.toPaperRowsInput
    (input : D54PaperProductSkewProductRibbonCollapseInput) :
    PaperRowsSkewProductRibbonCollapseInput where
  rows := d54PaperProductRows
  rf2 := input.rf2
  e := input.e
  returnRealization := input.returnRealization

noncomputable def D54PaperProductSkewProductRibbonCollapseInput.toLayerEquivInput
    (input : D54PaperProductSkewProductRibbonCollapseInput) :
    D54PaperProductLayerEquivRibbonCollapseInput where
  rf2 := layerEquivInput_of_skewProductInput input.rf2
  e := input.e
  returnRealization := input.returnRealization

theorem D54PaperProductSkewProductRibbonCollapseInput.nonemptyMainH2Input
    (input : D54PaperProductSkewProductRibbonCollapseInput) :
    Nonempty ResetPortBaseRowRibbonRealizationData :=
  input.toLayerEquivInput.nonemptyMainH2Input

/-- Singleton-switch RF2 wrapper for the now-refuted product-row candidate. -/
structure D54PaperProductSingletonSwitchRibbonCollapseInput where
  rf2 : ResetPortSingletonSwitchLayerData d54PaperProductRows.baseRow
  e : LowD5M4Structural.Seed ≃ LowD5M4Structural.RootState
  returnRealization :
    PaperBaseRowReturnRealizationGoal d54PaperProductRows e

noncomputable def D54PaperProductSingletonSwitchRibbonCollapseInput.toLayerEquivInput
    (input : D54PaperProductSingletonSwitchRibbonCollapseInput) :
    D54PaperProductLayerEquivRibbonCollapseInput where
  rf2 := resetPortLayerEquivData_of_singletonSwitchLayerData
    d54PaperProductRows.baseRow input.rf2
  e := input.e
  returnRealization := input.returnRealization

noncomputable def D54PaperProductSingletonSwitchRibbonCollapseInput.toResetPortBaseRowData
    (input : D54PaperProductSingletonSwitchRibbonCollapseInput) :
    ResetPortBaseRowRibbonRealizationData :=
  input.toLayerEquivInput.toResetPortBaseRowData

theorem D54PaperProductSingletonSwitchRibbonCollapseInput.nonemptyMainH2Input
    (input : D54PaperProductSingletonSwitchRibbonCollapseInput) :
    Nonempty ResetPortBaseRowRibbonRealizationData :=
  input.toLayerEquivInput.nonemptyMainH2Input

theorem not_nonempty_D54PaperProductLayerEquivRibbonCollapseInput :
    ¬ Nonempty D54PaperProductLayerEquivRibbonCollapseInput := by
  rintro ⟨input⟩
  exact not_nonempty_d54PaperProductRows_layerEquivRF2Goal ⟨input.rf2⟩

theorem not_nonempty_D54PaperProductSkewProductRibbonCollapseInput :
    ¬ Nonempty D54PaperProductSkewProductRibbonCollapseInput := by
  rintro ⟨input⟩
  exact not_nonempty_d54PaperProductRows_skewProductRF2Goal ⟨input.rf2⟩

theorem not_nonempty_D54PaperProductSingletonSwitchRibbonCollapseInput :
    ¬ Nonempty D54PaperProductSingletonSwitchRibbonCollapseInput := by
  rintro ⟨input⟩
  exact not_nonempty_d54PaperProductRows_singletonSwitchRF2Goal ⟨input.rf2⟩

/-- Baseline layer table: every layer reads the standard terminal row at the
current `Q4` coordinate.  This is not the final H2 row table, but it is the
smallest checkpoint for terminal-row read leaves. -/
def canonicalTerminalRows : PaperLayeredBaseRows where
  layer0 := terminalStdBaseRowAtState
  layer1 := terminalStdBaseRowAtState
  layer2 := terminalStdBaseRowAtState
  layer3 := terminalStdBaseRowAtState

@[simp] theorem canonicalTerminalRows_baseRow_three
    (w : LowD5M4Realization.RootState) :
    canonicalTerminalRows.baseRow (3 : ZMod 4) w =
      terminalStdBaseRowAtState w := by
  simp [PaperLayeredBaseRows.baseRow, canonicalTerminalRows]

theorem canonicalTerminalRows_reads_terminalTailIndex
    (i : Fin 3) (q : LowD5M4.Q4) (y : LowD5M4.Y)
    (z : LowD5M4.Z) :
    BaseRowReadsTerminalTailIndex
      canonicalTerminalRows.baseRow (3 : ZMod 4) i q y z := by
  rw [BaseRowReadsTerminalTailIndex]
  rw [canonicalTerminalRows_baseRow_three]
  rfl

/-- The terminal-core last-layer read closes by definitional reduction for the
standard terminal row. -/
theorem canonicalTerminalRows_terminalCoreTailReadGoal :
    TerminalCoreTailReadGoal canonicalTerminalRows.baseRow := by
  intro i w _hNo
  exact canonicalTerminalRows_reads_terminalTailIndex
    i (qCoord w) (yCoord w) (zCoord w)

/-- The pre-final terminal-color read after the first `Y` lift also closes by the
same terminal-row reduction. -/
theorem canonicalTerminalRows_preFinalTerminalFirstYTailReadGoal
    (i : Fin 3) :
    ResetPortPreFinalTerminalFirstYTailReadOnGoal
      canonicalTerminalRows.baseRow i
      (preFinalTerminalFirstYTailSource i) := by
  intro w _hSource
  exact canonicalTerminalRows_reads_terminalTailIndex
    i (qCoord w) (yCoord w + 1) (zCoord w)

/-- Closed terminal-color read package for the canonical terminal rows. -/
def canonicalTerminalRows_preFinalTerminalReadGoals :
    ResetPortPreFinalTerminalReadGoals canonicalTerminalRows.baseRow where
  terminalCoreTail := canonicalTerminalRows_terminalCoreTailReadGoal
  terminalFirstNoFinalYFirstTail :=
    canonicalTerminalRows_preFinalTerminalFirstYTailReadGoal

theorem canonicalTerminalRows_reads_yShift_color3
    (q : LowD5M4.Q4) (y : LowD5M4.Y) (z : LowD5M4.Z) :
    BaseRowReadsYShift
      canonicalTerminalRows.baseRow (3 : ZMod 4) 3 q y z := by
  rw [BaseRowReadsYShift]
  rw [canonicalTerminalRows_baseRow_three]
  rfl

/-- The canonical terminal row already supplies the pure `Y` read for color `3`.
This is the P0 pure-Y leaf; terminal-factor leaves need a different layer-3 row
or a narrower path-local read predicate. -/
theorem canonicalTerminalRows_p0YShiftLastReadGoal :
    ResetPortYShiftLastStepReadOnGoal
      canonicalTerminalRows.baseRow 3 preFinalP0YShiftSource zCoord := by
  intro w _hSource
  exact canonicalTerminalRows_reads_yShift_color3
    (qCoord w) (yCoord w) (zCoord w)

/-- Same color-`3` pure `Y` leaf after the final `Z`-first carry split. -/
theorem canonicalTerminalRows_finalZFirstP0YShiftLastReadGoal :
    ResetPortFinalZFirstYShiftLastStepReadOnGoal
      canonicalTerminalRows.baseRow 3 finalZFirstP0YShiftSource := by
  intro w _hSource
  exact canonicalTerminalRows_reads_yShift_color3
    (qCoord w) (yCoord w) (zCoord w + 1)

theorem terminalStdBaseRowEquiv5_zero_ne_liftY (q : LowD5M4.Q4) :
    terminalStdBaseRowEquiv5 q (0 : TorusColor 5) ≠ liftYDirection5 := by
  cases hrow : terminalOmega q <;>
    simp [terminalStdBaseRowEquiv5, hrow, terminalStdRowEquiv5,
      terminalStdRowTargetIndex5, terminalStdDirection5, liftYDirection5,
      terminalRowEquiv, terminalRowTargetIndex]

/-- The present broad pre-final P0/P1 row-read package is inconsistent: the P0
`y = 0` terminal-factor read reaches the same layer-3 source that the P0 pure-`Y`
read also admits at `y = 1`, forcing color `3` to read both a terminal direction
and `liftYDirection5`. -/
theorem not_preFinalP0P1RowWordReadGoals
    (baseRow : ResetPortBaseRow) :
    ¬ ResetPortPreFinalP0P1RowWordReadGoals baseRow := by
  intro hRead
  let q0 : LowD5M4.Q4 := LowD5M4.p0
  let z0 : LowD5M4.Z := 0
  let sourceF0 : LowD5M4Realization.RootState := rootOfCoords q0 0 z0
  let commonTail : LowD5M4Realization.RootState :=
    rootOfCoords
      (terminalReturnTailBaseOfSymbol TerminalSymbol.F0 q0) 1 z0
  have hF0Source : preFinalP0F0Source sourceF0 := by
    constructor
    · intro hFinal
      change
        (qCoord sourceF0, yCoord sourceF0) =
          LowD5M4.liftSite (3 : TorusColor 5) at hFinal
      have hy := congrArg Prod.snd hFinal
      exact (by decide : (0 : LowD5M4.Y) ≠ 3)
        (by simpa [sourceF0, LowD5M4.liftSite, LowD5M4.a3] using hy)
    · rfl
  have hYSource : preFinalP0YShiftSource commonTail := by
    constructor
    · intro hFinal
      change
        (qCoord commonTail, yCoord commonTail) =
          LowD5M4.liftSite (3 : TorusColor 5) at hFinal
      have hy := congrArg Prod.snd hFinal
      exact (by decide : (1 : LowD5M4.Y) ≠ 3)
        (by simpa [commonTail, LowD5M4.liftSite, LowD5M4.a3] using hy)
    · exact (by decide : (1 : LowD5M4.Y) ≠ 0)
  have hF0 :
      baseRow (3 : ZMod 4) commonTail 3 =
        terminalStdBaseRowEquiv5
          (terminalReturnTailBaseOfSymbol TerminalSymbol.F0 q0) 0 := by
    simpa [BaseRowReadsTerminalTailSymbol, sourceF0, commonTail, q0, z0,
      terminalReturnTailBaseOfSymbol, terminalIndexOfSymbol, fin3ToFin5]
      using hRead.p0F0Tail sourceF0 hF0Source
  have hY :
      baseRow (3 : ZMod 4) commonTail 3 = liftYDirection5 := by
    simpa [BaseRowReadsYShift, commonTail]
      using hRead.p0YShiftLast commonTail hYSource
  have hContr :
      terminalStdBaseRowEquiv5
          (terminalReturnTailBaseOfSymbol TerminalSymbol.F0 q0) 0 =
        liftYDirection5 := by
    exact hF0.symm.trans hY
  exact terminalStdBaseRowEquiv5_zero_ne_liftY
    (terminalReturnTailBaseOfSymbol TerminalSymbol.F0 q0) hContr

theorem not_fullPaperRowWordReadGoals
    (baseRow : ResetPortBaseRow) :
    ¬ ResetPortFullPaperRowWordReadGoals baseRow := by
  intro hRead
  exact not_preFinalP0P1RowWordReadGoals baseRow hRead.preFinalP0P1

theorem not_paperRowReadPieces
    (baseRow : ResetPortBaseRow) :
    ¬ PaperRowReadPieces baseRow := by
  intro pieces
  exact not_preFinalP0P1RowWordReadGoals baseRow pieces.preFinalP0P1

/-- The legacy H2 table route cannot be the next target with the current broad
read predicates.  Use `H2SkewProductPathRouteSkeleton` or
`H2RibbonCollapseInput` instead. -/
theorem H2TableRouteSkeleton_false :
    H2TableRouteSkeleton → False := by
  intro input
  exact not_fullPaperRowWordReadGoals input.baseRow input.read

end D5M4H2PaperRows
end V28Hard
end EvenV11
