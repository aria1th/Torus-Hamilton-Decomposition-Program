import EvenV11.D54ResetData
import EvenV11.FinalTargetSixObligationBridge

namespace EvenV11
namespace FinalTargetLowBaseCertificateBridge

structure FinalLowD5M4ClosedInputs : Prop where
  resetTable : D54ResetTableCertificate
  endpointInput : FinalEndpointInput

theorem finalLowD5M4ClosedInputs_of_lowBase
    (input : FinalLowMarkedBaseClosedInputs) :
    FinalLowD5M4ClosedInputs where
  resetTable := d54ResetTableCertificate
  endpointInput := input.endpointInput

theorem finalLowD5M4ClosedInputs_holds :
    FinalLowD5M4ClosedInputs :=
  finalLowD5M4ClosedInputs_of_lowBase
    finalLowMarkedBaseClosedInputs_holds

theorem finalLowD5M4ResetTable
    (input : FinalLowD5M4ClosedInputs) :
    D54ResetTableCertificate :=
  input.resetTable

theorem finalLowD5M4TerminalResetCycle
    (input : FinalLowD5M4ClosedInputs) :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4) terminalResetTrace4) :=
  input.resetTable.terminalSingleCycle

theorem finalLowD5M4EndpointInput
    (input : FinalLowD5M4ClosedInputs) :
    FinalEndpointInput :=
  input.endpointInput

theorem finalLowD5M4EndpointTransferInput
    (input : FinalLowD5M4ClosedInputs) :
    EndpointMarkedTransferBridge.foldedEndpointMarkedTransferInput4 :=
  input.endpointInput.endpointMarkedTransferInput.1

structure FinalLowD7M4ClosedInputs : Prop where
  terminalTrace4Cycle :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4) terminalTrace4)
  endpointInput : FinalEndpointInput

theorem finalLowD7M4ClosedInputs_of_lowBase
    (input : FinalLowMarkedBaseClosedInputs) :
    FinalLowD7M4ClosedInputs where
  terminalTrace4Cycle := input.terminalInput.terminalTrace4Cycle
  endpointInput := input.endpointInput

theorem finalLowD7M4ClosedInputs_holds :
    FinalLowD7M4ClosedInputs :=
  finalLowD7M4ClosedInputs_of_lowBase
    finalLowMarkedBaseClosedInputs_holds

theorem finalLowD7M4TerminalTraceCycle
    (input : FinalLowD7M4ClosedInputs) :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4) terminalTrace4) :=
  input.terminalTrace4Cycle

theorem finalLowD7M4EndpointInput
    (input : FinalLowD7M4ClosedInputs) :
    FinalEndpointInput :=
  input.endpointInput

theorem finalLowD7M4EndpointTransferInput
    (input : FinalLowD7M4ClosedInputs) :
    EndpointMarkedTransferBridge.foldedEndpointMarkedTransferInput4 :=
  input.endpointInput.endpointMarkedTransferInput.1

structure FinalLowD7M6ClosedInputs : Prop where
  terminalTrace6Cycle :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 6) terminalTrace6)
  endpointInput : FinalEndpointInput

theorem finalLowD7M6ClosedInputs_of_lowBase
    (input : FinalLowMarkedBaseClosedInputs) :
    FinalLowD7M6ClosedInputs where
  terminalTrace6Cycle := input.terminalInput.terminalTrace6Cycle
  endpointInput := input.endpointInput

theorem finalLowD7M6ClosedInputs_holds :
    FinalLowD7M6ClosedInputs :=
  finalLowD7M6ClosedInputs_of_lowBase
    finalLowMarkedBaseClosedInputs_holds

theorem finalLowD7M6TerminalTraceCycle
    (input : FinalLowD7M6ClosedInputs) :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 6) terminalTrace6) :=
  input.terminalTrace6Cycle

theorem finalLowD7M6EndpointInput
    (input : FinalLowD7M6ClosedInputs) :
    FinalEndpointInput :=
  input.endpointInput

theorem finalLowD7M6EndpointTransferInput
    (input : FinalLowD7M6ClosedInputs) :
    EndpointMarkedTransferBridge.foldedEndpointMarkedTransferInput6 :=
  input.endpointInput.endpointMarkedTransferInput.2

structure FinalLowD5M4TargetPromotion : Prop where
  markedD5M4 :
    FinalLowD5M4ClosedInputs → FinalMarkedTarget 5 4

structure FinalLowD7M4TargetPromotion : Prop where
  markedD7M4 :
    FinalLowD7M4ClosedInputs → FinalMarkedTarget 7 4

structure FinalLowD7M6TargetPromotion : Prop where
  markedD7M6 :
    FinalLowD7M6ClosedInputs → FinalMarkedTarget 7 6

theorem finalLowMarkedD5M4Promotion_of_targetPromotion
    (promotion : FinalLowD5M4TargetPromotion) :
    FinalLowMarkedD5M4Promotion where
  markedD5M4 := fun input =>
    promotion.markedD5M4
      (finalLowD5M4ClosedInputs_of_lowBase input)

theorem finalLowMarkedD7M4Promotion_of_targetPromotion
    (promotion : FinalLowD7M4TargetPromotion) :
    FinalLowMarkedD7M4Promotion where
  markedD7M4 := fun input =>
    promotion.markedD7M4
      (finalLowD7M4ClosedInputs_of_lowBase input)

theorem finalLowMarkedD7M6Promotion_of_targetPromotion
    (promotion : FinalLowD7M6TargetPromotion) :
    FinalLowMarkedD7M6Promotion where
  markedD7M6 := fun input =>
    promotion.markedD7M6
      (finalLowD7M6ClosedInputs_of_lowBase input)

structure FinalRefinedLowBasePromotions : Prop where
  d5m4 : FinalLowD5M4TargetPromotion
  d7m4 : FinalLowD7M4TargetPromotion
  d7m6 : FinalLowD7M6TargetPromotion

theorem finalLowMarkedBasePromotions_of_refinedLow
    (promotions : FinalRefinedLowBasePromotions) :
    FinalLowMarkedBasePromotions :=
  finalLowMarkedBasePromotions_of_individual
    (finalLowMarkedD5M4Promotion_of_targetPromotion promotions.d5m4)
    (finalLowMarkedD7M4Promotion_of_targetPromotion promotions.d7m4)
    (finalLowMarkedD7M6Promotion_of_targetPromotion promotions.d7m6)

structure FinalSixRefinedLowPromotionObligations : Prop where
  d3EvenPromotion : FinalD3EvenBasePromotion
  lowPromotions : FinalRefinedLowBasePromotions
  oddHighModulusPromotion : FinalOddHighModulusPromotion
  oddEndpointPromotion : FinalOddEndpointPromotion

theorem finalSixRemainingPromotionObligations_of_refinedLow
    (remaining : FinalSixRefinedLowPromotionObligations) :
    FinalSixRemainingPromotionObligations where
  d3EvenPromotion := remaining.d3EvenPromotion
  lowD5M4Promotion :=
    finalLowMarkedD5M4Promotion_of_targetPromotion
      remaining.lowPromotions.d5m4
  lowD7M4Promotion :=
    finalLowMarkedD7M4Promotion_of_targetPromotion
      remaining.lowPromotions.d7m4
  lowD7M6Promotion :=
    finalLowMarkedD7M6Promotion_of_targetPromotion
      remaining.lowPromotions.d7m6
  oddHighModulusPromotion := remaining.oddHighModulusPromotion
  oddEndpointPromotion := remaining.oddEndpointPromotion

theorem finalTargetTorus_from_refinedLow
    (remaining : FinalSixRefinedLowPromotionObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorus_from_sixRemaining
    (finalSixRemainingPromotionObligations_of_refinedLow remaining)
    hRange

theorem finalTargetMarkedTorus_from_refinedLow
    (remaining : FinalSixRefinedLowPromotionObligations)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorus_from_sixRemaining
    (finalSixRemainingPromotionObligations_of_refinedLow remaining)
    hRange

theorem finalTargetCayley_from_refinedLow
    (remaining : FinalSixRefinedLowPromotionObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayley_from_sixRemaining
    (finalSixRemainingPromotionObligations_of_refinedLow remaining)
    hRange

end FinalTargetLowBaseCertificateBridge

export FinalTargetLowBaseCertificateBridge
  (FinalLowD5M4ClosedInputs FinalLowD7M4ClosedInputs
   FinalLowD7M6ClosedInputs FinalLowD5M4TargetPromotion
   FinalLowD7M4TargetPromotion FinalLowD7M6TargetPromotion
   FinalRefinedLowBasePromotions FinalSixRefinedLowPromotionObligations
   finalLowD5M4ClosedInputs_of_lowBase
   finalLowD5M4ClosedInputs_holds
   finalLowD5M4ResetTable
   finalLowD5M4TerminalResetCycle
   finalLowD5M4EndpointInput
   finalLowD5M4EndpointTransferInput
   finalLowD7M4ClosedInputs_of_lowBase
   finalLowD7M4ClosedInputs_holds
   finalLowD7M4TerminalTraceCycle
   finalLowD7M4EndpointInput
   finalLowD7M4EndpointTransferInput
   finalLowD7M6ClosedInputs_of_lowBase
   finalLowD7M6ClosedInputs_holds
   finalLowD7M6TerminalTraceCycle
   finalLowD7M6EndpointInput
   finalLowD7M6EndpointTransferInput
   finalLowMarkedD5M4Promotion_of_targetPromotion
   finalLowMarkedD7M4Promotion_of_targetPromotion
   finalLowMarkedD7M6Promotion_of_targetPromotion
   finalLowMarkedBasePromotions_of_refinedLow
   finalSixRemainingPromotionObligations_of_refinedLow
   finalTargetTorus_from_refinedLow
   finalTargetMarkedTorus_from_refinedLow
   finalTargetCayley_from_refinedLow)

end EvenV11
