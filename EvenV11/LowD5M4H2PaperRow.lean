import EvenV11.LowD5M4Realization

/-!
# D5(4) H2 reset-port row pilot

This module connects the row-level assets in `LowD5M4Realization` to the current
`LowD5M4Structural` H2 handoff.  It does not choose the final terminal base row:
the worksheet records that the naive `qCoord` row is a negative control.  Instead
it packages an arbitrary paper base row after the D54 reset-port switches.

It is intentionally not imported by `EvenV11.Main` yet.  The remaining hard
H2 work is still RF2 plus the switching-ribbon/run-collapse conjugacy.
-/

namespace EvenV11
namespace LowD5M4H2PaperRow

open Shared
open LowD5M4Structural

/-- H2 data after the D54 reset-port local switches have been applied to a
candidate paper base row.  RF1 is automatic from the row equivalence; the
remaining obligations are RF2 and the wild return-section conjugacy. -/
structure ResetPortBaseRowRibbonRealizationData where
  baseRow : LowD5M4Realization.ResetPortBaseRow
  e : Seed ≃ RootState
  layerBijective :
    (LowD5M4Schedule.schedule
      (dirOfRowEquiv
        (LowD5M4Realization.resetPortRowOfBase baseRow))).layerBijective
  returnRealization : ∀ c : TorusColor 5, ∀ x : Seed,
    e.symm
        ((LowD5M4Schedule.schedule
          (dirOfRowEquiv
            (LowD5M4Realization.resetPortRowOfBase baseRow))).returnMap c
            (e x)) =
      LowD5M4.fullReturn c x

def rowEquivRibbonRealizationData_of_resetPortBaseRowData
    (data : ResetPortBaseRowRibbonRealizationData) :
    ResetPortH2RowEquivRibbonRealizationData where
  row := LowD5M4Realization.resetPortRowOfBase data.baseRow
  e := data.e
  layerBijective := data.layerBijective
  returnRealization := data.returnRealization

/-- Package a reset-port base row, RF2, and the transported paper return-map
equality as the current `Main` H2 row-equivalence handoff. -/
def rowEquivRibbonRealizationData_of_resetPortBaseReturnMap
    (baseRow : LowD5M4Realization.ResetPortBaseRow)
    (hLayer : LowD5M4Realization.ResetPortLayerBijectiveGoal baseRow)
    (hReturn :
      LowD5M4Realization.ReturnMapRealizationGoal
        (dirOfRowEquiv
          (LowD5M4Realization.resetPortRowOfBase baseRow))) :
    ResetPortH2RowEquivRibbonRealizationData where
  row := LowD5M4Realization.resetPortRowOfBase baseRow
  e := LowD5M4Realization.seedRootEquiv
  layerBijective := hLayer
  returnRealization := by
    intro c x
    rw [hReturn c (LowD5M4Realization.seedRootEquiv x)]
    simp [LowD5M4Realization.paperReturn]

def rowEquivRibbonRealizationData_of_resetPortBaseFourLayer
    (baseRow : LowD5M4Realization.ResetPortBaseRow)
    (hLayer : LowD5M4Realization.ResetPortLayerBijectiveGoal baseRow)
    (hFour : LowD5M4Realization.ResetPortFourLayerRealizationGoal baseRow) :
    ResetPortH2RowEquivRibbonRealizationData :=
  rowEquivRibbonRealizationData_of_resetPortBaseReturnMap
    baseRow hLayer
    (LowD5M4Realization.returnMapRealizationGoal_of_fourLayer
      (dirOfRowEquiv
        (LowD5M4Realization.resetPortRowOfBase baseRow))
      hFour)

def resetPortFourLayerRealizationGoal_of_fullSplitGoals
    {baseRow : LowD5M4Realization.ResetPortBaseRow}
    (hGoals :
      LowD5M4Realization.ResetPortFullCoreYFirstZFirstTailSplitRowWordGoals
        baseRow) :
    LowD5M4Realization.ResetPortFourLayerRealizationGoal baseRow :=
  LowD5M4Realization.resetPortFourLayerRealizationGoal_of_preFinalFinalCarryGoals
    baseRow
    (LowD5M4Realization.resetPortPreFinalRealizationGoal_of_coreYFirstTailSplitRowWordGoals
      hGoals.preFinal)
    (LowD5M4Realization.resetPortFinalCarryRealizationGoal_of_zFirstTailSplitRowWordGoals
      hGoals.finalCarry)

def rowEquivRibbonRealizationData_of_resetPortBaseFullSplitGoals
    (baseRow : LowD5M4Realization.ResetPortBaseRow)
    (hLayer : LowD5M4Realization.ResetPortLayerBijectiveGoal baseRow)
    (hGoals :
      LowD5M4Realization.ResetPortFullCoreYFirstZFirstTailSplitRowWordGoals
        baseRow) :
    ResetPortH2RowEquivRibbonRealizationData :=
  rowEquivRibbonRealizationData_of_resetPortBaseFourLayer
    baseRow hLayer
    (resetPortFourLayerRealizationGoal_of_fullSplitGoals hGoals)

def rowEquivRibbonRealizationData_of_resetPortBasePrefixReadGoals
    (baseRow : LowD5M4Realization.ResetPortBaseRow)
    (hLayer : LowD5M4Realization.ResetPortLayerBijectiveGoal baseRow)
    (hPrefix : LowD5M4Realization.ResetPortFullSplitPrefixGoals baseRow)
    (hRead : LowD5M4Realization.ResetPortFullSplitReadGoals baseRow) :
    ResetPortH2RowEquivRibbonRealizationData :=
  rowEquivRibbonRealizationData_of_resetPortBaseFullSplitGoals
    baseRow hLayer
    (LowD5M4Realization.resetPortFullSplitGoals_of_prefixRead
      hPrefix hRead)

def rowEquivRibbonRealizationData_of_resetPortBasePaperTableGoals
    (baseRow : LowD5M4Realization.ResetPortBaseRow)
    (hLayer : LowD5M4Realization.ResetPortLayerBijectiveGoal baseRow)
    (hTable : LowD5M4Realization.ResetPortFullPaperTableGoals baseRow) :
    ResetPortH2RowEquivRibbonRealizationData :=
  rowEquivRibbonRealizationData_of_resetPortBasePrefixReadGoals
    baseRow hLayer hTable.splitPrefixGoals hTable.splitReadGoals

def rowEquivRibbonRealizationData_of_paperTableData
    (data : LowD5M4Realization.ResetPortH2PaperTableData) :
    ResetPortH2RowEquivRibbonRealizationData :=
  rowEquivRibbonRealizationData_of_resetPortBasePaperTableGoals
    data.baseRow
    data.layerBijective
    data.tableGoals

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortBaseRowData
    (data : ResetPortBaseRowRibbonRealizationData) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_rowEquivRibbonRealizationData
    (rowEquivRibbonRealizationData_of_resetPortBaseRowData data)

theorem finalLowD5M4RootFlatCertificateFamily_of_nonemptyResetPortBaseRowData
    (hData : Nonempty ResetPortBaseRowRibbonRealizationData) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortBaseRowData
    (Classical.choice hData)

theorem finalLowD5M4RootFlatCertificateFamily_of_paperTableData
    (data : LowD5M4Realization.ResetPortH2PaperTableData) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_rowEquivRibbonRealizationData
    (rowEquivRibbonRealizationData_of_paperTableData data)

theorem finalLowD5M4RootFlatCertificateFamily_of_nonemptyPaperTableData
    (hData : Nonempty LowD5M4Realization.ResetPortH2PaperTableData) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_paperTableData
    (Classical.choice hData)

end LowD5M4H2PaperRow
end EvenV11
