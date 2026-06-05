import EvenV11.FiniteAudit

namespace EvenV11
namespace FiniteAuditBridge

def highEvenAnchorAuditBool
    (forestClosing supportRows reservePlane : Bool) : Bool :=
  forestClosing && supportRows && reservePlane

def d5HighEvenAnchorAuditBool : Bool :=
  highEvenAnchorAuditBool
    FiniteAudit.d5ForestClosingAuditBool
    FiniteAudit.d5SupportAuditBool
    FiniteAudit.d5ReservePlaneAuditBool

def d7HighEvenAnchorAuditBool : Bool :=
  highEvenAnchorAuditBool
    FiniteAudit.d7ForestClosingAuditBool
    FiniteAudit.d7SupportAuditBool
    FiniteAudit.d7ReservePlaneAuditBool

def highEvenAnchorDimensions : List Nat :=
  [5, 7]

def highEvenAnchorDimensionAuditBool (D : Nat) : Bool :=
  if D = 5 then d5HighEvenAnchorAuditBool
  else if D = 7 then d7HighEvenAnchorAuditBool
  else false

def highEvenAnchorDimensionsAuditBool : Bool :=
  highEvenAnchorDimensions.all highEvenAnchorDimensionAuditBool

theorem d5HighEvenAnchorAudit :
    d5HighEvenAnchorAuditBool = true := by
  unfold d5HighEvenAnchorAuditBool highEvenAnchorAuditBool
  rw [d5ForestClosingAudit, d5SupportAudit, d5ReservePlaneAudit]
  rfl

theorem d7HighEvenAnchorAudit :
    d7HighEvenAnchorAuditBool = true := by
  unfold d7HighEvenAnchorAuditBool highEvenAnchorAuditBool
  rw [d7ForestClosingAudit, d7SupportAudit, d7ReservePlaneAudit]
  rfl

theorem highEvenAnchorDimensions_nodup :
    highEvenAnchorDimensions.Nodup := by
  decide

theorem highEvenAnchorDimensionsAudit :
    highEvenAnchorDimensionsAuditBool = true := by
  unfold highEvenAnchorDimensionsAuditBool highEvenAnchorDimensions
  unfold highEvenAnchorDimensionAuditBool
  rw [d5HighEvenAnchorAudit, d7HighEvenAnchorAudit]
  rfl

theorem v28FiniteInputBridgeAudit :
    highEvenAnchorDimensionsAuditBool = true ∧
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4)
        (FoldedSiteTrace.chronologicalTrace 4 foldedSites4)) ∧
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 6)
        (FoldedSiteTrace.chronologicalTrace 6 foldedSites6)) :=
  ⟨highEvenAnchorDimensionsAudit,
    foldedTerminalWordAudit.1, foldedTerminalWordAudit.2⟩

end FiniteAuditBridge

export FiniteAuditBridge
  (d5HighEvenAnchorAudit d7HighEvenAnchorAudit
   highEvenAnchorDimensions_nodup highEvenAnchorDimensionsAudit
   v28FiniteInputBridgeAudit)

end EvenV11
