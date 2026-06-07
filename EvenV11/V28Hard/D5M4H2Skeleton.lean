import EvenV11.V28Hard.D5M4RibbonRows

/-!
# H2 skeleton for the paper-faithful D5(4) reset

This file adds an opt-in skeleton for the next H2 attack.  It deliberately keeps
three tracks separate:

* row-word/read transcription from the paper table;
* RF2 layer-bijectivity, preferably via skew-product data;
* the final RF3/ribbon-collapse route, which should not be forced through the
  old prefix-table equality if that interface proves too strong.

All declarations here are packaging/adapters; no new finite blob is introduced.
-/

namespace EvenV11
namespace V28Hard
namespace D5M4H2Skeleton

open Shared
open LowD5M4Structural
open LowD5M4Realization
open LowD5M4H2PaperRow
open D5M4RibbonRows

/-- Local name for the §11 candidate base row before reset-port swaps. -/
abbrev BaseRow := ResetPortBaseRow

/-- The direction table after applying Table D54-reset-ports to a base row. -/
abbrev ResetDir (baseRow : BaseRow) := resetPortDirOfBase baseRow

/-- The root-flat schedule induced by the reset-port row family. -/
abbrev ResetSchedule (baseRow : BaseRow) :=
  LowD5M4Schedule.schedule (ResetDir baseRow)

/-- A layer-dependent row blueprint.  This is intentionally less committed than
a single formula such as `fun _ w => terminalStdBaseRowAtState w`: the last read
layer and the three transport layers can be repaired independently. -/
structure PaperLayeredBaseRows where
  layer0 : LowD5M4Structural.RootState → TorusColor 5 ≃ TorusDirection 5
  layer1 : LowD5M4Structural.RootState → TorusColor 5 ≃ TorusDirection 5
  layer2 : LowD5M4Structural.RootState → TorusColor 5 ≃ TorusDirection 5
  layer3 : LowD5M4Structural.RootState → TorusColor 5 ≃ TorusDirection 5

/-- Convert four displayed layer rows into the `ResetPortBaseRow` API. -/
def PaperLayeredBaseRows.baseRow
    (rows : PaperLayeredBaseRows) : BaseRow :=
  fun t w =>
    if t = (0 : ZMod 4) then rows.layer0 w
    else if t = (1 : ZMod 4) then rows.layer1 w
    else if t = (2 : ZMod 4) then rows.layer2 w
    else rows.layer3 w

/-- The last-layer read obligations, grouped in the order that should be attacked
first.  These are expected to be mostly `simp`, `rfl`, `fin_cases`, and small
case splits after the row table is transcribed. -/
structure PaperRowReadPieces (baseRow : BaseRow) where
  preFinalTerminal : ResetPortPreFinalTerminalReadGoals baseRow
  preFinalP0P1 : ResetPortPreFinalP0P1RowWordReadGoals baseRow
  finalCarryP0P1 : ResetPortFinalZFirstP0P1RowWordReadGoals baseRow

/-- Assemble the row-read pieces into the existing full paper read package. -/
def PaperRowReadPieces.fullReadGoals
    {baseRow : BaseRow}
    (pieces : PaperRowReadPieces baseRow) :
    ResetPortFullPaperRowWordReadGoals baseRow :=
  resetPortFullPaperRowWordReadGoals_of_components
    pieces.preFinalTerminal
    pieces.preFinalP0P1
    pieces.finalCarryP0P1

/-- Concrete row-read milestone: a base row plus the full read table, with no
prefix path or RF3 assertion yet. -/
structure PaperRowReadMilestone where
  baseRow : BaseRow
  readPieces : PaperRowReadPieces baseRow

/-- Extract the full row-read goals from the row-read milestone. -/
def PaperRowReadMilestone.readGoals
    (milestone : PaperRowReadMilestone) :
    ResetPortFullPaperRowWordReadGoals milestone.baseRow :=
  milestone.readPieces.fullReadGoals

/-- RF2 in the paper's stronger skew-product form. -/
abbrev PaperRF2SkewProductInput (baseRow : BaseRow) :=
  ResetPortLayerSkewProductData baseRow

/-- RF2 in the direct layer-equivalence form.  This is a useful fallback if the
skew-product normal form is too rigid during early repair. -/
abbrev PaperRF2LayerEquivInput (baseRow : BaseRow) :=
  ResetPortLayerEquivData baseRow

/-- Convert the skew-product RF2 package into the direct layer-equivalence RF2
package. -/
noncomputable def layerEquivInput_of_skewProductInput
    {baseRow : BaseRow}
    (rf2 : PaperRF2SkewProductInput baseRow) :
    PaperRF2LayerEquivInput baseRow :=
  resetPortLayerEquivData_of_layerSkewProductData baseRow rf2

/-- RF2 layer-bijectivity from direct layer-equivalence data. -/
def layerBijective_of_layerEquivInput
    {baseRow : BaseRow}
    (rf2 : PaperRF2LayerEquivInput baseRow) :
    ResetPortLayerBijectiveGoal baseRow :=
  resetPortLayerBijective_of_layerEquivData baseRow rf2

/-- RF2 layer-bijectivity from skew-product data. -/
def layerBijective_of_skewProductInput
    {baseRow : BaseRow}
    (rf2 : PaperRF2SkewProductInput baseRow) :
    ResetPortLayerBijectiveGoal baseRow :=
  resetPortLayerBijective_of_layerSkewProductData baseRow rf2

/-- Paper-faithful path route: RF2 is closed for the chosen reset-port rows, and
the four-layer return calculation is supplied directly as path goals.  This is
the route to use when last-layer row reads cannot be separated into global
source predicates. -/
structure H2PathRouteSkeleton where
  baseRow : BaseRow
  layerBijective : ResetPortLayerBijectiveGoal baseRow
  paths : ResetPortFullRowWordSplitPathGoals baseRow

/-- Convert the path route into the low-level H2 realization package already
provided by `LowD5M4Realization`. -/
def H2PathRouteSkeleton.toRealizationData
    (input : H2PathRouteSkeleton) :
    ResetPortH2RealizationData where
  baseRow := input.baseRow
  layerBijective := input.layerBijective
  paths := input.paths

/-- The four-layer return calculation carried by the path route. -/
def H2PathRouteSkeleton.fourLayerRealizationGoal
    (input : H2PathRouteSkeleton) :
    ResetPortFourLayerRealizationGoal input.baseRow :=
  resetPortFourLayerRealizationGoal_of_preFinalFinalCarryGoals
    input.baseRow
    (resetPortPreFinalRealizationGoal_of_rowWordSplitPathGoals
      input.baseRow input.paths.preFinal)
    (resetPortFinalCarryRealizationGoal_of_rowWordSplitPathGoals
      input.baseRow input.paths.finalCarry)

/-- Convert the path route into the current `Main.lean` H2 slot.  This route uses
the paper-return equality supplied by the four-layer path goals, so the
coordinate `seedRootEquiv` adapter in `LowD5M4H2PaperRow` is sufficient. -/
def H2PathRouteSkeleton.toRowEquivRibbonData
    (input : H2PathRouteSkeleton) :
    ResetPortH2RowEquivRibbonRealizationData :=
  rowEquivRibbonRealizationData_of_resetPortBaseFourLayer
    input.baseRow input.layerBijective input.fourLayerRealizationGoal

/-- Nonempty current-spine H2 slot from the path route. -/
theorem H2PathRouteSkeleton.nonemptyRibbonData
    (input : H2PathRouteSkeleton) :
    Nonempty ResetPortH2RowEquivRibbonRealizationData :=
  ⟨input.toRowEquivRibbonData⟩

/-- Low-base family from the path-only H2 route. -/
theorem H2PathRouteSkeleton.lowBaseFamily
    (input : H2PathRouteSkeleton) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_rowEquivRibbonRealizationData
    input.toRowEquivRibbonData

/-- Same path route with RF2 supplied in the paper's skew-product form. -/
structure H2SkewProductPathRouteSkeleton where
  baseRow : BaseRow
  rf2 : PaperRF2SkewProductInput baseRow
  paths : ResetPortFullRowWordSplitPathGoals baseRow

/-- Convert skew-product RF2 path data to the direct path route. -/
def H2SkewProductPathRouteSkeleton.toPathRoute
    (input : H2SkewProductPathRouteSkeleton) :
    H2PathRouteSkeleton where
  baseRow := input.baseRow
  layerBijective := layerBijective_of_skewProductInput input.rf2
  paths := input.paths

/-- Low-base family from the paper skew-product RF2 path route. -/
theorem H2SkewProductPathRouteSkeleton.lowBaseFamily
    (input : H2SkewProductPathRouteSkeleton) :
    FinalLowD5M4RootFlatCertificateFamily :=
  input.toPathRoute.lowBaseFamily

/-- Nonempty current-spine H2 slot from the skew-product RF2 path route. -/
theorem H2SkewProductPathRouteSkeleton.nonemptyRibbonData
    (input : H2SkewProductPathRouteSkeleton) :
    Nonempty ResetPortH2RowEquivRibbonRealizationData :=
  input.toPathRoute.nonemptyRibbonData

/-- Paper-specialized core/tail route: RF2 is closed for the chosen reset-port
rows, and the return calculation is supplied in the decomposed form that already
splits terminal-core, first-`Y`, and first-`Z` phases.  This is the preferred
target when the global last-layer read package is too strong. -/
structure H2CoreYFirstZFirstRouteSkeleton where
  baseRow : BaseRow
  layerBijective : ResetPortLayerBijectiveGoal baseRow
  goals : ResetPortFullCoreYFirstZFirstTailRowWordGoals baseRow

/-- The four-layer return calculation carried by the core/tail route. -/
def H2CoreYFirstZFirstRouteSkeleton.fourLayerRealizationGoal
    (input : H2CoreYFirstZFirstRouteSkeleton) :
    ResetPortFourLayerRealizationGoal input.baseRow :=
  resetPortFourLayerRealizationGoal_of_preFinalFinalCarryGoals
    input.baseRow
    (resetPortPreFinalRealizationGoal_of_coreYFirstTailRowWordGoals
      input.goals.preFinal)
    (resetPortFinalCarryRealizationGoal_of_rowWordSplitPathGoals
      input.baseRow
      (resetPortFinalCarryRowWordSplitPathGoals_of_zFirstTail
        input.goals.finalCarry))

/-- Convert the decomposed paper core/tail route into the current `Main.lean`
H2 slot. -/
def H2CoreYFirstZFirstRouteSkeleton.toRowEquivRibbonData
    (input : H2CoreYFirstZFirstRouteSkeleton) :
    ResetPortH2RowEquivRibbonRealizationData :=
  rowEquivRibbonRealizationData_of_resetPortBaseFourLayer
    input.baseRow input.layerBijective input.fourLayerRealizationGoal

/-- Nonempty current-spine H2 slot from the decomposed core/tail route. -/
theorem H2CoreYFirstZFirstRouteSkeleton.nonemptyRibbonData
    (input : H2CoreYFirstZFirstRouteSkeleton) :
    Nonempty ResetPortH2RowEquivRibbonRealizationData :=
  ⟨input.toRowEquivRibbonData⟩

/-- Low-base family from the decomposed core/tail H2 route. -/
theorem H2CoreYFirstZFirstRouteSkeleton.lowBaseFamily
    (input : H2CoreYFirstZFirstRouteSkeleton) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_rowEquivRibbonRealizationData
    input.toRowEquivRibbonData

/-- Same core/tail route with RF2 supplied in the paper's skew-product form. -/
structure H2SkewProductCoreYFirstZFirstRouteSkeleton where
  baseRow : BaseRow
  rf2 : PaperRF2SkewProductInput baseRow
  goals : ResetPortFullCoreYFirstZFirstTailRowWordGoals baseRow

/-- Convert skew-product RF2 core/tail data to the direct core/tail route. -/
def H2SkewProductCoreYFirstZFirstRouteSkeleton.toCoreRoute
    (input : H2SkewProductCoreYFirstZFirstRouteSkeleton) :
    H2CoreYFirstZFirstRouteSkeleton where
  baseRow := input.baseRow
  layerBijective := layerBijective_of_skewProductInput input.rf2
  goals := input.goals

/-- Repackage the low-level paper §11 skew-product/core-tail handoff in the
local H2 skeleton namespace. -/
def H2SkewProductCoreYFirstZFirstRouteSkeleton.ofPaperData
    (data : ResetPortH2PaperSkewProductCoreYFirstZFirstTailData) :
    H2SkewProductCoreYFirstZFirstRouteSkeleton where
  baseRow := data.baseRow
  rf2 := data.layerData
  goals := data.goals

/-- Nonempty current-spine H2 slot from the skew-product core/tail route. -/
theorem H2SkewProductCoreYFirstZFirstRouteSkeleton.nonemptyRibbonData
    (input : H2SkewProductCoreYFirstZFirstRouteSkeleton) :
    Nonempty ResetPortH2RowEquivRibbonRealizationData :=
  input.toCoreRoute.nonemptyRibbonData

/-- Low-base family from the skew-product core/tail route. -/
theorem H2SkewProductCoreYFirstZFirstRouteSkeleton.lowBaseFamily
    (input : H2SkewProductCoreYFirstZFirstRouteSkeleton) :
    FinalLowD5M4RootFlatCertificateFamily :=
  input.toCoreRoute.lowBaseFamily

/-- The low-level paper §11 skew-product/core-tail package is strong enough to
replace the current `Main.lean` H2 data assumption once the package is
constructed. -/
theorem H2SkewProductCoreYFirstZFirstRouteSkeleton.nonemptyRibbonData_ofPaperData
    (data : ResetPortH2PaperSkewProductCoreYFirstZFirstTailData) :
    Nonempty ResetPortH2RowEquivRibbonRealizationData :=
  (H2SkewProductCoreYFirstZFirstRouteSkeleton.ofPaperData data).nonemptyRibbonData

/-- A concrete source away from every D54 reset-port site.  It is used as a
negative check for the current collapsed core-tail prefix interface. -/
def terminalCoreTailPrefixContradictionSource : LowD5M4Realization.RootState :=
  rootOfCoords (D54ResetData.d54q4 0 2) (0 : LowD5M4.Y) (0 : LowD5M4.Z)

theorem terminalCoreTailPrefixContradictionSource_noResetPortSites :
    NoResetPortSites terminalCoreTailPrefixContradictionSource := by
  apply noResetPortSites_of_not_mem_d54TableLists
  · decide
  · decide

/-- At the contradiction source, no three literal D5 root steps can reach the
color-0 collapsed terminal-return tail. -/
theorem no_three_rootSteps_terminalReturnTailBase_zero_from_q02 :
    ∀ d0 d1 d2 : TorusDirection 5,
      LowD5M4Schedule.rootStep d2
        (LowD5M4Schedule.rootStep d1
          (LowD5M4Schedule.rootStep d0
            terminalCoreTailPrefixContradictionSource)) ≠
      rootOfCoords
        (terminalReturnTailBase (0 : Fin 3) (D54ResetData.d54q4 0 2))
        (0 : LowD5M4.Y) (0 : LowD5M4.Z) := by
  decide

/-- The current `TerminalCoreTailPrefixPathGoal` asks three literal D5 root
steps to move to the paper's collapsed terminal-return tail.  The displacement is
impossible, so this interface is too strong for the paper route. -/
theorem not_terminalCoreTailPrefixPathGoal
    (baseRow : BaseRow) :
    ¬ TerminalCoreTailPrefixPathGoal baseRow := by
  intro hPrefix
  rcases hPrefix (0 : Fin 3) with ⟨x1, x2, hsteps⟩
  rcases hsteps terminalCoreTailPrefixContradictionSource
      terminalCoreTailPrefixContradictionSource_noResetPortSites with
    ⟨h0, h1, h2, _hNo1, _hNo2, _hNo3⟩
  let d0 := baseRow (0 : ZMod 4) terminalCoreTailPrefixContradictionSource
    (fin3ToFin5 (0 : Fin 3))
  let d1 := baseRow (1 : ZMod 4)
    (x1 terminalCoreTailPrefixContradictionSource)
    (fin3ToFin5 (0 : Fin 3))
  let d2 := baseRow (2 : ZMod 4)
    (x2 terminalCoreTailPrefixContradictionSource)
    (fin3ToFin5 (0 : Fin 3))
  have hChain :
      LowD5M4Schedule.rootStep d2
        (LowD5M4Schedule.rootStep d1
          (LowD5M4Schedule.rootStep d0
            terminalCoreTailPrefixContradictionSource)) =
      rootOfCoords
        (terminalReturnTailBase (0 : Fin 3) (D54ResetData.d54q4 0 2))
        (0 : LowD5M4.Y) (0 : LowD5M4.Z) := by
    dsimp [d0, d1, d2]
    rw [h0, h1, h2]
    simp [terminalCoreTailPrefixContradictionSource, qCoord, yCoord, zCoord,
      rootOfCoords, seedRootEquiv]
  exact no_three_rootSteps_terminalReturnTailBase_zero_from_q02 d0 d1 d2 hChain

theorem not_terminalCoreTailPathGoal
    (baseRow : BaseRow) :
    ¬ TerminalCoreTailPathGoal baseRow := by
  intro hPath
  apply not_terminalCoreTailPrefixPathGoal baseRow
  intro i
  rcases hPath i with ⟨x1, x2, hsteps⟩
  refine ⟨x1, x2, ?_⟩
  intro w hNo
  rcases hsteps w hNo with
    ⟨h0, h1, h2, _hRead, hNo1, hNo2, hNo3⟩
  exact ⟨h0, h1, h2, hNo1, hNo2, hNo3⟩

theorem not_resetPortFullCoreYFirstZFirstTailRowWordGoals
    (baseRow : BaseRow) :
    ¬ ResetPortFullCoreYFirstZFirstTailRowWordGoals baseRow := by
  intro hGoals
  exact not_terminalCoreTailPathGoal baseRow hGoals.preFinal.terminalCoreTail

theorem not_nonempty_resetPortH2PaperSkewProductCoreYFirstZFirstTailData :
    ¬ Nonempty ResetPortH2PaperSkewProductCoreYFirstZFirstTailData := by
  rintro ⟨data⟩
  exact not_resetPortFullCoreYFirstZFirstTailRowWordGoals data.baseRow data.goals

/-- Full legacy table route.  This is useful as a test target, but should not be
the only paper-faithful H2 route because `ResetPortFullPaperPrefixGoals` may be
stronger than the manuscript's ribbon-collapse assertion. -/
structure H2TableRouteSkeleton where
  baseRow : BaseRow
  rf2 : PaperRF2SkewProductInput baseRow
  prefixGoals : ResetPortFullPaperPrefixGoals baseRow
  read : ResetPortFullPaperRowWordReadGoals baseRow

/-- Assemble the old `ResetPortH2PaperTableData` route from the separated fields. -/
def H2TableRouteSkeleton.toPaperTableInput
    (input : H2TableRouteSkeleton) : H2PaperTableInput :=
  paperTableInput_of_rf2_prefix_read
    input.baseRow input.rf2 input.prefixGoals input.read

/-- The old row-equivalence/ribbon handoff produced by the legacy table route. -/
theorem H2TableRouteSkeleton.nonemptyRibbonData
    (input : H2TableRouteSkeleton) : Nonempty RibbonData :=
  nonemptyRibbonData_of_paperTableInput input.toPaperTableInput

/-- More relaxed paper-faithful route: RF1 and RF2 are on actual reset-port
root-flat rows; RF3 is supplied as single-cycle data for the resulting return
maps.  This avoids forcing RF3 through the old prefix equality interface. -/
structure H2RootFlatRouteSkeleton where
  baseRow : BaseRow
  layerBijective : ResetPortLayerBijectiveGoal baseRow
  returnsSingleCycle : (ResetSchedule baseRow).returnsSingleCycle

/-- Convert the relaxed H2 route into the low-level root-flat cycle data. -/
def H2RootFlatRouteSkeleton.toCycleData
    (input : H2RootFlatRouteSkeleton) :
    ResetPortH2RootFlatCycleData where
  dir := ResetDir input.baseRow
  rowLatin := by
    simpa [ResetDir, resetPortDirOfBase] using
      rowLatin_of_resetPortRowOfBase input.baseRow
  layerBijective := input.layerBijective
  returnsSingleCycle := input.returnsSingleCycle

/-- D5(4) low-base family from the relaxed root-flat H2 route. -/
theorem H2RootFlatRouteSkeleton.lowBaseFamily
    (input : H2RootFlatRouteSkeleton) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_rootFlatCycleData
    input.toCycleData

/-- Nonempty form of the relaxed H2 route, convenient for checklist assembly. -/
theorem H2RootFlatRouteSkeleton.nonemptyCycleData
    (input : H2RootFlatRouteSkeleton) :
    Nonempty ResetPortH2RootFlatCycleData :=
  ⟨input.toCycleData⟩

/-- Paper ribbon-collapse route.  This is the current `Main.lean` H2 shape: RF1
is a row equivalence, RF2 is layer bijectivity, and RF3 is inherited from the
already-proved `LowD5M4.fullReturn_singleCycle` through a return-section
reindexing `e`. -/
structure H2RibbonCollapseInput where
  baseRow : BaseRow
  e : LowD5M4Structural.Seed ≃ LowD5M4Structural.RootState
  layerBijective : ResetPortLayerBijectiveGoal baseRow
  returnRealization : ∀ c : TorusColor 5, ∀ x : LowD5M4Structural.Seed,
    e.symm ((ResetSchedule baseRow).returnMap c (e x)) =
      LowD5M4.fullReturn c x

/-- Convert the ribbon-collapse route into the current row-equivalence H2 slot. -/
def H2RibbonCollapseInput.toRowEquivRibbonData
    (input : H2RibbonCollapseInput) :
    ResetPortH2RowEquivRibbonRealizationData where
  row := resetPortRowOfBase input.baseRow
  e := input.e
  layerBijective := by
    simpa [ResetSchedule, ResetDir, resetPortDirOfBase] using
      input.layerBijective
  returnRealization := by
    intro c x
    simpa [ResetSchedule, ResetDir, resetPortDirOfBase] using
      input.returnRealization c x

/-- Nonempty current-spine H2 slot from the ribbon-collapse skeleton. -/
theorem H2RibbonCollapseInput.nonemptyRibbonData
    (input : H2RibbonCollapseInput) :
    Nonempty ResetPortH2RowEquivRibbonRealizationData :=
  ⟨input.toRowEquivRibbonData⟩

/-- Low-base family from the ribbon-collapse skeleton. -/
theorem H2RibbonCollapseInput.lowBaseFamily
    (input : H2RibbonCollapseInput) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_rowEquivRibbonRealizationData
    input.toRowEquivRibbonData

/-- Convert the local ribbon-collapse skeleton to the exact lower H2 input used
by `EvenV11.Main`. -/
def H2RibbonCollapseInput.toResetPortBaseRowData
    (input : H2RibbonCollapseInput) :
    ResetPortBaseRowRibbonRealizationData where
  baseRow := input.baseRow
  e := input.e
  layerBijective := by
    simpa [ResetSchedule, ResetDir, resetPortDirOfBase] using
      input.layerBijective
  returnRealization := by
    intro c x
    simpa [ResetSchedule, ResetDir, resetPortDirOfBase] using
      input.returnRealization c x

/-- Nonempty form of the exact `Main.lean` H2 input produced by the local
ribbon-collapse skeleton. -/
theorem H2RibbonCollapseInput.nonemptyResetPortBaseRowData
    (input : H2RibbonCollapseInput) :
    Nonempty ResetPortBaseRowRibbonRealizationData :=
  ⟨input.toResetPortBaseRowData⟩

/-- A practical H2 work packet: first close row-read goals, then RF2, and only
then choose between the legacy prefix route and the relaxed RF3/ribbon route. -/
structure H2WorkPacket where
  rows : PaperLayeredBaseRows
  read : PaperRowReadPieces rows.baseRow
  rf2SkewProduct : Option (PaperRF2SkewProductInput rows.baseRow)
  rf2LayerEquiv : Option (PaperRF2LayerEquivInput rows.baseRow)

/-- The base row carried by an H2 work packet. -/
def H2WorkPacket.baseRow (packet : H2WorkPacket) : BaseRow :=
  packet.rows.baseRow

/-- The row-read package carried by an H2 work packet. -/
def H2WorkPacket.readGoals
    (packet : H2WorkPacket) :
    ResetPortFullPaperRowWordReadGoals packet.baseRow :=
  packet.read.fullReadGoals

/-!
## Named targets for the next H2 proof pass

These abbreviations are intentionally theorem-shaped but proof-free.  They give
repair work stable names without asserting any new mathematics.
-/

/-- First target: verify that the transcribed paper row table reads the terminal
row words at the last layer. -/
abbrev PaperBaseRowReadGoal (rows : PaperLayeredBaseRows) : Prop :=
  ResetPortFullPaperRowWordReadGoals rows.baseRow

/-- RF2 target in the strong skew-product form. -/
abbrev PaperBaseRowSkewProductRF2Goal (rows : PaperLayeredBaseRows) : Type :=
  PaperRF2SkewProductInput rows.baseRow

/-- RF2 target in the direct layer-equivalence fallback form. -/
abbrev PaperBaseRowLayerEquivRF2Goal (rows : PaperLayeredBaseRows) : Type :=
  PaperRF2LayerEquivInput rows.baseRow

/-- Legacy prefix-table target.  This is useful for regression, but failure here
should not be interpreted as failure of the paper H2 strategy. -/
abbrev PaperBaseRowLegacyPrefixGoal (rows : PaperLayeredBaseRows) : Prop :=
  ResetPortFullPaperPrefixGoals rows.baseRow

/-- Preferred RF3 target for the relaxed root-flat H2 route. -/
abbrev PaperBaseRowReturnCycleGoal (rows : PaperLayeredBaseRows) : Prop :=
  (ResetSchedule rows.baseRow).returnsSingleCycle

/-- Stronger current-spine RF3 target: return-section reindexing to the existing
`LowD5M4.fullReturn` single-cycle engine. -/
abbrev PaperBaseRowReturnRealizationGoal
    (rows : PaperLayeredBaseRows)
    (e : LowD5M4Structural.Seed ≃ LowD5M4Structural.RootState) : Prop :=
  ∀ c : TorusColor 5, ∀ x : LowD5M4Structural.Seed,
    e.symm ((ResetSchedule rows.baseRow).returnMap c (e x)) =
      LowD5M4.fullReturn c x

/-- Direct physical-row schedule for a displayed four-layer row table.  Unlike
`ResetSchedule`, this does not apply the layer-blind reset-port transformer; the
rows are already the physical rows. -/
abbrev DirectPaperRowsSchedule (rows : PaperLayeredBaseRows) :=
  LowD5M4Schedule.schedule
    (LowD5M4Structural.dirOfRowEquiv rows.baseRow)

/-- RF2 target for a physical four-layer row table whose local reset
substitutions have already been transcribed into the rows. -/
abbrev PaperPhysicalRowsLayerBijectiveGoal
    (rows : PaperLayeredBaseRows) : Prop :=
  (DirectPaperRowsSchedule rows).layerBijective

/-- RF3/ribbon-collapse target for a physical four-layer row table. -/
abbrev PaperPhysicalRowsReturnRealizationGoal
    (rows : PaperLayeredBaseRows)
    (e : LowD5M4Structural.Seed ≃ LowD5M4Structural.RootState) : Prop :=
  ∀ c : TorusColor 5, ∀ x : LowD5M4Structural.Seed,
    e.symm ((DirectPaperRowsSchedule rows).returnMap c (e x)) =
      LowD5M4.fullReturn c x

/-- Current preferred H2 target after the layer-blind `resetPortRowOfBase`
route was found too strong: transcribe the actual four physical layer rows,
prove RF2 for that row schedule, and prove the return-section conjugacy. -/
structure PaperRowsDirectRibbonCollapseInput where
  rows : PaperLayeredBaseRows
  e : LowD5M4Structural.Seed ≃ LowD5M4Structural.RootState
  layerBijective : PaperPhysicalRowsLayerBijectiveGoal rows
  returnRealization : PaperPhysicalRowsReturnRealizationGoal rows e

def PaperRowsDirectRibbonCollapseInput.toRowEquivRibbonData
    (input : PaperRowsDirectRibbonCollapseInput) :
    ResetPortH2RowEquivRibbonRealizationData where
  row := input.rows.baseRow
  e := input.e
  layerBijective := input.layerBijective
  returnRealization := input.returnRealization

theorem PaperRowsDirectRibbonCollapseInput.nonemptyRibbonData
    (input : PaperRowsDirectRibbonCollapseInput) :
    Nonempty ResetPortH2RowEquivRibbonRealizationData :=
  ⟨input.toRowEquivRibbonData⟩

theorem PaperRowsDirectRibbonCollapseInput.lowBaseFamily
    (input : PaperRowsDirectRibbonCollapseInput) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_rowEquivRibbonRealizationData
    input.toRowEquivRibbonData

/-- RF2 data for a physical four-layer paper row table, expressed as a
layer/color-wise partial exchange.  This is the direct-row analogue of
`ResetPortPartialExchangeLayerData`: the schedule is `DirectPaperRowsSchedule`,
so no layer-blind reset-port transformer is inserted. -/
structure PaperPhysicalPartialExchangeLayerData
    (rows : PaperLayeredBaseRows) where
  T :
    ZMod 4 → TorusColor 5 →
      LowD5M4Structural.RootState ≃ LowD5M4Structural.RootState
  R :
    ZMod 4 → TorusColor 5 →
      LowD5M4Structural.RootState ≃ LowD5M4Structural.RootState
  U : ZMod 4 → TorusColor 5 → Set LowD5M4Structural.RootState
  chooseLeft : ZMod 4 → TorusColor 5 → Bool
  [decidableMem : ∀ t c w, Decidable (w ∈ U t c)]
  invariant : ∀ t c, ComparisonSetInvariant (T t c) (R t c) (U t c)
  layerMap_eq :
    ∀ t c w,
      (DirectPaperRowsSchedule rows).layerMap t c w =
        (if chooseLeft t c then
          partialExchangeLeft (T t c) (R t c) (U t c)
        else
          partialExchangeRight (T t c) (R t c) (U t c)) w

theorem paperPhysicalRowsLayerBijective_of_partialExchangeLayerData
    {rows : PaperLayeredBaseRows}
    (data : PaperPhysicalPartialExchangeLayerData rows) :
    PaperPhysicalRowsLayerBijectiveGoal rows := by
  letI := data.decidableMem
  exact rootFlatLayerBijective_of_partialExchangeChoice_eq
    (DirectPaperRowsSchedule rows)
    data.T data.R data.U data.chooseLeft data.invariant data.layerMap_eq

/-- Singleton-switch specialization of the direct physical-row RF2 interface.
This is the expected shape for the five local substitutions in §11: each
layer/color map is compared with a Latin row at one common-image switching
site. -/
structure PaperPhysicalSingletonSwitchLayerData
    (rows : PaperLayeredBaseRows) where
  T :
    ZMod 4 → TorusColor 5 →
      LowD5M4Structural.RootState ≃ LowD5M4Structural.RootState
  R :
    ZMod 4 → TorusColor 5 →
      LowD5M4Structural.RootState ≃ LowD5M4Structural.RootState
  site : ZMod 4 → TorusColor 5 → LowD5M4Structural.RootState
  chooseLeft : ZMod 4 → TorusColor 5 → Bool
  commonImage : ∀ t c, T t c (site t c) = R t c (site t c)
  layerMap_eq :
    ∀ t c w,
      (DirectPaperRowsSchedule rows).layerMap t c w =
        (if chooseLeft t c then
          partialExchangeLeft (T t c) (R t c)
            ({site t c} : Set LowD5M4Structural.RootState)
        else
          partialExchangeRight (T t c) (R t c)
            ({site t c} : Set LowD5M4Structural.RootState)) w

def paperPhysicalPartialExchangeLayerData_of_singletonSwitchLayerData
    {rows : PaperLayeredBaseRows}
    (data : PaperPhysicalSingletonSwitchLayerData rows) :
    PaperPhysicalPartialExchangeLayerData rows where
  T := data.T
  R := data.R
  U := fun t c => ({data.site t c} : Set LowD5M4Structural.RootState)
  chooseLeft := data.chooseLeft
  decidableMem := fun _ _ _ => inferInstance
  invariant := fun t c =>
    comparisonSetInvariant_singleton_of_common_image
      (data.commonImage t c)
  layerMap_eq := data.layerMap_eq

theorem paperPhysicalRowsLayerBijective_of_singletonSwitchLayerData
    {rows : PaperLayeredBaseRows}
    (data : PaperPhysicalSingletonSwitchLayerData rows) :
    PaperPhysicalRowsLayerBijectiveGoal rows :=
  paperPhysicalRowsLayerBijective_of_partialExchangeLayerData
    (paperPhysicalPartialExchangeLayerData_of_singletonSwitchLayerData data)

/-- RF3 path target for a direct physical row table.  This is the direct-row
analogue of the reset-port path goals: prove that the four physical layers
realize the transported paper return `paperReturn` for each color. -/
abbrev PaperPhysicalRowsPathRealizationGoal
    (rows : PaperLayeredBaseRows) : Prop :=
  ∀ c : TorusColor 5,
    FourLayerPathGoal
      (LowD5M4Structural.dirOfRowEquiv rows.baseRow)
      c (paperReturn c)

theorem paperPhysicalRowsReturnRealization_of_pathGoals
    {rows : PaperLayeredBaseRows}
    (paths : PaperPhysicalRowsPathRealizationGoal rows) :
    PaperPhysicalRowsReturnRealizationGoal rows seedRootEquiv := by
  intro c x
  have hFour :
      FourLayerRealizationGoal
        (LowD5M4Structural.dirOfRowEquiv rows.baseRow) :=
    fourLayerRealizationGoal_of_pathGoals
      (LowD5M4Structural.dirOfRowEquiv rows.baseRow) paths
  have hReturn :
      ReturnMapRealizationGoal
        (LowD5M4Structural.dirOfRowEquiv rows.baseRow) :=
    returnMapRealizationGoal_of_fourLayer
      (LowD5M4Structural.dirOfRowEquiv rows.baseRow) hFour
  change seedRootEquiv.symm
      ((LowD5M4Schedule.schedule
        (LowD5M4Structural.dirOfRowEquiv rows.baseRow)).returnMap c
          (seedRootEquiv x)) =
    LowD5M4.fullReturn c x
  rw [hReturn c (seedRootEquiv x)]
  simp [paperReturn]

/-- Direct physical-row H2 input with RF3 supplied as four-layer path goals
instead of the final conjugacy equation. -/
structure PaperRowsDirectPathRibbonCollapseInput where
  rows : PaperLayeredBaseRows
  layerBijective : PaperPhysicalRowsLayerBijectiveGoal rows
  pathRealization : PaperPhysicalRowsPathRealizationGoal rows

def PaperRowsDirectPathRibbonCollapseInput.toDirectInput
    (input : PaperRowsDirectPathRibbonCollapseInput) :
    PaperRowsDirectRibbonCollapseInput where
  rows := input.rows
  e := seedRootEquiv
  layerBijective := input.layerBijective
  returnRealization :=
    paperPhysicalRowsReturnRealization_of_pathGoals input.pathRealization

theorem PaperRowsDirectPathRibbonCollapseInput.nonemptyRibbonData
    (input : PaperRowsDirectPathRibbonCollapseInput) :
    Nonempty ResetPortH2RowEquivRibbonRealizationData :=
  input.toDirectInput.nonemptyRibbonData

theorem PaperRowsDirectPathRibbonCollapseInput.lowBaseFamily
    (input : PaperRowsDirectPathRibbonCollapseInput) :
    FinalLowD5M4RootFlatCertificateFamily :=
  input.toDirectInput.lowBaseFamily

/-- Direct physical-row H2 input with RF2 supplied in the singleton-switch form.
After the four paper rows are transcribed, this is the smallest RF2 target
before the remaining RF3 return-realization calculation. -/
structure PaperRowsSingletonDirectRibbonCollapseInput where
  rows : PaperLayeredBaseRows
  rf2 : PaperPhysicalSingletonSwitchLayerData rows
  e : LowD5M4Structural.Seed ≃ LowD5M4Structural.RootState
  returnRealization : PaperPhysicalRowsReturnRealizationGoal rows e

def PaperRowsSingletonDirectRibbonCollapseInput.toDirectInput
    (input : PaperRowsSingletonDirectRibbonCollapseInput) :
    PaperRowsDirectRibbonCollapseInput where
  rows := input.rows
  e := input.e
  layerBijective :=
    paperPhysicalRowsLayerBijective_of_singletonSwitchLayerData input.rf2
  returnRealization := input.returnRealization

theorem PaperRowsSingletonDirectRibbonCollapseInput.nonemptyRibbonData
    (input : PaperRowsSingletonDirectRibbonCollapseInput) :
    Nonempty ResetPortH2RowEquivRibbonRealizationData :=
  input.toDirectInput.nonemptyRibbonData

theorem PaperRowsSingletonDirectRibbonCollapseInput.lowBaseFamily
    (input : PaperRowsSingletonDirectRibbonCollapseInput) :
    FinalLowD5M4RootFlatCertificateFamily :=
  input.toDirectInput.lowBaseFamily

/-- Direct physical-row H2 input with RF2 in singleton-switch form and RF3 in
four-layer path form.  This is the intended next concrete target after the
actual §11 row table is transcribed. -/
structure PaperRowsSingletonDirectPathRibbonCollapseInput where
  rows : PaperLayeredBaseRows
  rf2 : PaperPhysicalSingletonSwitchLayerData rows
  pathRealization : PaperPhysicalRowsPathRealizationGoal rows

def PaperRowsSingletonDirectPathRibbonCollapseInput.toDirectPathInput
    (input : PaperRowsSingletonDirectPathRibbonCollapseInput) :
    PaperRowsDirectPathRibbonCollapseInput where
  rows := input.rows
  layerBijective :=
    paperPhysicalRowsLayerBijective_of_singletonSwitchLayerData input.rf2
  pathRealization := input.pathRealization

def PaperRowsSingletonDirectPathRibbonCollapseInput.toDirectInput
    (input : PaperRowsSingletonDirectPathRibbonCollapseInput) :
    PaperRowsDirectRibbonCollapseInput :=
  input.toDirectPathInput.toDirectInput

theorem PaperRowsSingletonDirectPathRibbonCollapseInput.nonemptyRibbonData
    (input : PaperRowsSingletonDirectPathRibbonCollapseInput) :
    Nonempty ResetPortH2RowEquivRibbonRealizationData :=
  input.toDirectInput.nonemptyRibbonData

theorem PaperRowsSingletonDirectPathRibbonCollapseInput.lowBaseFamily
    (input : PaperRowsSingletonDirectPathRibbonCollapseInput) :
    FinalLowD5M4RootFlatCertificateFamily :=
  input.toDirectInput.lowBaseFamily

/-- Paper-row-table version of the preferred H2 route, with RF2 supplied as
direct layer equivalences.  This is the most direct target for replacing
`Main.lean`'s H2 `sorry`: transcribe rows, prove RF2, then prove the
ribbon-collapse return realization for a wild return-section reindexing `e`. -/
structure PaperRowsLayerEquivRibbonCollapseInput where
  rows : PaperLayeredBaseRows
  rf2 : PaperBaseRowLayerEquivRF2Goal rows
  e : LowD5M4Structural.Seed ≃ LowD5M4Structural.RootState
  returnRealization : PaperBaseRowReturnRealizationGoal rows e

def PaperRowsLayerEquivRibbonCollapseInput.toH2RibbonCollapseInput
    (input : PaperRowsLayerEquivRibbonCollapseInput) :
    H2RibbonCollapseInput where
  baseRow := input.rows.baseRow
  e := input.e
  layerBijective := layerBijective_of_layerEquivInput input.rf2
  returnRealization := input.returnRealization

def PaperRowsLayerEquivRibbonCollapseInput.toResetPortBaseRowData
    (input : PaperRowsLayerEquivRibbonCollapseInput) :
    ResetPortBaseRowRibbonRealizationData :=
  input.toH2RibbonCollapseInput.toResetPortBaseRowData

theorem PaperRowsLayerEquivRibbonCollapseInput.nonemptyMainH2Input
    (input : PaperRowsLayerEquivRibbonCollapseInput) :
    Nonempty ResetPortBaseRowRibbonRealizationData :=
  ⟨input.toResetPortBaseRowData⟩

theorem PaperRowsLayerEquivRibbonCollapseInput.nonemptyRibbonData
    (input : PaperRowsLayerEquivRibbonCollapseInput) :
    Nonempty ResetPortH2RowEquivRibbonRealizationData :=
  input.toH2RibbonCollapseInput.nonemptyRibbonData

/-- Paper-row-table version of the preferred H2 route, with RF2 supplied in the
paper's stronger skew-product form. -/
structure PaperRowsSkewProductRibbonCollapseInput where
  rows : PaperLayeredBaseRows
  rf2 : PaperBaseRowSkewProductRF2Goal rows
  e : LowD5M4Structural.Seed ≃ LowD5M4Structural.RootState
  returnRealization : PaperBaseRowReturnRealizationGoal rows e

noncomputable def PaperRowsSkewProductRibbonCollapseInput.toLayerEquivInput
    (input : PaperRowsSkewProductRibbonCollapseInput) :
    PaperRowsLayerEquivRibbonCollapseInput where
  rows := input.rows
  rf2 := layerEquivInput_of_skewProductInput input.rf2
  e := input.e
  returnRealization := input.returnRealization

noncomputable def PaperRowsSkewProductRibbonCollapseInput.toH2RibbonCollapseInput
    (input : PaperRowsSkewProductRibbonCollapseInput) :
    H2RibbonCollapseInput :=
  input.toLayerEquivInput.toH2RibbonCollapseInput

noncomputable def PaperRowsSkewProductRibbonCollapseInput.toResetPortBaseRowData
    (input : PaperRowsSkewProductRibbonCollapseInput) :
    ResetPortBaseRowRibbonRealizationData :=
  input.toH2RibbonCollapseInput.toResetPortBaseRowData

theorem PaperRowsSkewProductRibbonCollapseInput.nonemptyMainH2Input
    (input : PaperRowsSkewProductRibbonCollapseInput) :
    Nonempty ResetPortBaseRowRibbonRealizationData :=
  ⟨input.toResetPortBaseRowData⟩

theorem PaperRowsSkewProductRibbonCollapseInput.nonemptyRibbonData
    (input : PaperRowsSkewProductRibbonCollapseInput) :
    Nonempty ResetPortH2RowEquivRibbonRealizationData :=
  input.toH2RibbonCollapseInput.nonemptyRibbonData

end D5M4H2Skeleton
end V28Hard
end EvenV11
