import EvenV11.FiniteAudit
import EvenV11.FiniteAuditBridge
import EvenV11.TerminalFiniteCyclicity
import EvenV11.V28Hard.D3TerminalA2Parametric
import EvenV11.V28Hard.D7TwoRailRelay

/-!
# Closed JSON / finite-proof handoff for the v28 hard sections

This file collects the finite values that are now actual Lean terms rather than
external JSON assumptions: terminal carrier orbits, D7 support/closure JSON
identity, determinant/support/reserve audit proofs, and folded terminal-word
cycles.
-/

namespace EvenV11
namespace V28Hard
namespace JsonProof

open Shared

/-- All three terminal carriers at `m = 4` are full cycles. -/
theorem terminal_m4_all_carriers :
    ∀ i : TorusColor 3,
      IsSingleCycleMap (terminalReturn (m := 4) i) :=
  D3TerminalA2Parametric.terminalA2M4FiniteCyclicity.terminalReturn_singleCycle

/-- All three terminal carriers at `m = 6` are full cycles. -/
theorem terminal_m6_all_carriers :
    ∀ i : TorusColor 3,
      IsSingleCycleMap (terminalReturn (m := 6) i) :=
  D3TerminalA2Parametric.terminalA2M6FiniteCyclicity.terminalReturn_singleCycle

/-- The D7 relay support table is exactly the finite-audit JSON table. -/
theorem d7_support_json_exact :
    D7TwoRailRelay.stageRows.map D7TwoRailRelay.relayRowToSupportDatum =
      FiniteAudit.d7SupportRows :=
  D7TwoRailRelay.stageRows_match_finiteAudit_d7SupportRows

/-- The D7 relay closure table is exactly the finite-audit JSON table. -/
theorem d7_closure_json_exact :
    D7TwoRailRelay.colorClosureData.map
        D7TwoRailRelay.closureDatumToForestClosingDatum =
      FiniteAudit.d7ForestClosingData :=
  D7TwoRailRelay.colorClosureData_match_finiteAudit_d7ForestClosingData

/-- The closed D7 finite audit evidence consumed by H3/H4. -/
def d7FiniteAuditEvidence : D7TwoRailRelay.RelayFiniteAuditEvidence :=
  D7TwoRailRelay.relayFiniteAuditEvidence

/-- Combined v28 finite-audit theorem: D5/D7 closing determinants, support
containment, reserve separation, and folded terminal cycles. -/
theorem v28FiniteAuditSummary :
    FiniteAudit.d5ForestClosingAuditBool = true ∧
    FiniteAudit.d7ForestClosingAuditBool = true ∧
    FiniteAudit.d5SupportAuditBool = true ∧
    FiniteAudit.d7SupportAuditBool = true ∧
    FiniteAudit.d5ReservePlaneAuditBool = true ∧
    FiniteAudit.d7ReservePlaneAuditBool = true ∧
    IsSingleCycleMap
      (wordEval (terminalSymbolStep 4)
        (FoldedSiteTrace.chronologicalTrace 4 foldedSites4)) ∧
    IsSingleCycleMap
      (wordEval (terminalSymbolStep 6)
        (FoldedSiteTrace.chronologicalTrace 6 foldedSites6)) :=
  FiniteAudit.v28FiniteAuditSummary

/-- The bridge-level high-even anchor input audit is closed for both D5 and D7. -/
theorem highEvenAnchorInputsClosed :
    FiniteAuditBridge.highEvenAnchorDimensionsAuditBool = true :=
  FiniteAuditBridge.highEvenAnchorDimensionsAudit

end JsonProof
end V28Hard
end EvenV11
