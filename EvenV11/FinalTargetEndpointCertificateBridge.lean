import EvenV11.FinalTargetLowBaseCertificateBridge

namespace EvenV11
namespace FinalTargetEndpointCertificateBridge

structure FinalOddEndpointCertificateInputs : Prop where
  terminalInput : FinalTerminalInput
  markedTransferInput :
    EndpointMarkedTransferBridge.foldedEndpointMarkedTransferInputAudit
  phaseProductSupportInput :
    ∀ {Parent : Type} (parent : Parent)
      (h a m : Nat) [NeZero h] [NeZero m]
      (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m),
      PhaseDoublingProductSupportInput parent h a m hh ha hm
  phaseProductRealizationInput :
    ∀ {ι κ Parent : Type} (parent : Parent)
      (h a m : Nat) [NeZero h] [NeZero m]
      (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
      (T : Set Parent)
      (reserveStep : ι → Parent × PhaseSection h (m ^ a) →
        Parent × PhaseSection h (m ^ a))
      (protectedStep : κ → Parent × PhaseSection h (m ^ a) →
        Parent × PhaseSection h (m ^ a)),
      (∀ i : ι, SupportedOn
        (phaseProductReserveSupportCertificate
          parent h a m hh ha hm).supportSet (reserveStep i)) →
      (∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
        (protectedStep j)) →
      (reserveWord : List ι) →
      (protectedWord : List κ) →
      (n k : Nat) →
      PhaseDoublingProductRealizationInput parent h a m hh ha hm T
        reserveStep protectedStep reserveWord protectedWord n k
  completionCarryInput :
    ∀ {Base Coord : Type} [Finite Base]
      {N m : Nat} [NeZero N] [NeZero m]
      (baseStep : Base → Base) (rank : Base ≃ ZMod N)
      (_base : Base) (C : CompletionCarryCertificate Base Coord m),
      (∀ x : Base, rank (baseStep x) = rank x + 1) →
      IsUnit C.epsilon →
      Shared.IsSingleCycleMap
        (additiveSkewMap baseStep
          (completionCarry C.coordRead C.row C.tail))
  b4FirstCompletionInput :
    ∀ {m : Nat} [NeZero m],
      Shared.IsSingleCycleMap
        (additiveSkewMap finCompletionBaseStep
          (completionCarry
            (endpointB4FirstCompletionOnePointCertificate m).coordRead
            (cyclicCompletionRow
              (endpointB4FirstCompletionOnePointCertificate m).shift)
            (endpointB4FirstCompletionOnePointCertificate m).tail))
  rangeInput : FinalRangeInput

theorem finalOddEndpointCertificateInputs_of_endpointInputs
    (input : FinalOddEndpointClosedInputs) :
    FinalOddEndpointCertificateInputs where
  terminalInput := input.terminalInput
  markedTransferInput := input.endpointInput.endpointMarkedTransferInput
  phaseProductSupportInput :=
    input.endpointInput.phaseProductSupportInput
  phaseProductRealizationInput :=
    input.endpointInput.phaseProductRealizationInput
  completionCarryInput := input.endpointInput.completionCarryInput
  b4FirstCompletionInput := input.endpointInput.b4FirstCompletionInput
  rangeInput := input.rangeInput

theorem finalOddEndpointCertificateInputs_holds :
    FinalOddEndpointCertificateInputs :=
  finalOddEndpointCertificateInputs_of_endpointInputs
    finalOddEndpointClosedInputs_holds

theorem finalOddEndpointCertificateTerminalTrace4Cycle
    (input : FinalOddEndpointCertificateInputs) :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4) terminalTrace4) :=
  input.terminalInput.terminalTrace4Cycle

theorem finalOddEndpointCertificateTerminalTrace6Cycle
    (input : FinalOddEndpointCertificateInputs) :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 6) terminalTrace6) :=
  input.terminalInput.terminalTrace6Cycle

theorem finalOddEndpointCertificateTerminalReset4Cycle
    (input : FinalOddEndpointCertificateInputs) :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4) terminalResetTrace4) :=
  input.terminalInput.terminalResetTrace4Cycle

theorem finalOddEndpointCertificateMarkedTransferAudit
    (input : FinalOddEndpointCertificateInputs) :
    EndpointMarkedTransferBridge.foldedEndpointMarkedTransferInputAudit :=
  input.markedTransferInput

theorem finalOddEndpointCertificateMarkedTransfer4
    (input : FinalOddEndpointCertificateInputs) :
    EndpointMarkedTransferBridge.foldedEndpointMarkedTransferInput4 :=
  input.markedTransferInput.1

theorem finalOddEndpointCertificateMarkedTransfer6
    (input : FinalOddEndpointCertificateInputs) :
    EndpointMarkedTransferBridge.foldedEndpointMarkedTransferInput6 :=
  input.markedTransferInput.2

theorem finalOddEndpointCertificatePhaseProductSupport
    (input : FinalOddEndpointCertificateInputs)
    {Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    PhaseDoublingProductSupportInput parent h a m hh ha hm :=
  input.phaseProductSupportInput parent h a m hh ha hm

theorem finalOddEndpointCertificatePhaseProductRealization
    (input : FinalOddEndpointCertificateInputs)
    {ι κ Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (reserveStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (protectedStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hreserve :
      ∀ i : ι, SupportedOn
        (phaseProductReserveSupportCertificate
          parent h a m hh ha hm).supportSet (reserveStep i))
    (hprotected :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
        (protectedStep j))
    (reserveWord : List ι) (protectedWord : List κ)
    (n k : Nat) :
    PhaseDoublingProductRealizationInput parent h a m hh ha hm T
      reserveStep protectedStep reserveWord protectedWord n k :=
  input.phaseProductRealizationInput parent h a m hh ha hm T
    reserveStep protectedStep hreserve hprotected reserveWord
    protectedWord n k

theorem finalOddEndpointCertificateCompletionCarry
    (input : FinalOddEndpointCertificateInputs)
    {Base Coord : Type} [Finite Base]
    {N m : Nat} [NeZero N] [NeZero m]
    (baseStep : Base → Base) (rank : Base ≃ ZMod N)
    (base : Base) (C : CompletionCarryCertificate Base Coord m)
    (hstep : ∀ x : Base, rank (baseStep x) = rank x + 1)
    (hepsilon : IsUnit C.epsilon) :
    Shared.IsSingleCycleMap
      (additiveSkewMap baseStep
        (completionCarry C.coordRead C.row C.tail)) :=
  input.completionCarryInput baseStep rank base C hstep hepsilon

theorem finalOddEndpointCertificateB4FirstCompletion
    (input : FinalOddEndpointCertificateInputs)
    {m : Nat} [NeZero m] :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry
          (endpointB4FirstCompletionOnePointCertificate m).coordRead
          (cyclicCompletionRow
            (endpointB4FirstCompletionOnePointCertificate m).shift)
          (endpointB4FirstCompletionOnePointCertificate m).tail)) :=
  input.b4FirstCompletionInput

theorem finalOddEndpointCertificateParentRange
    (input : FinalOddEndpointCertificateInputs)
    {b m : Nat} (hb : 4 ≤ b)
    (hm : EvenModulusRange m) (hmle : m ≤ 2 * b + 1) :
    MarkedDimensionRange b m :=
  input.rangeInput.endpointParent rfl hb hm hmle

structure FinalOddEndpointTargetPromotion : Prop where
  oddEndpoint :
    ∀ {b m : Nat}, 4 ≤ b → MarkedDimensionRange b m →
      FinalMarkedTarget b m → FinalOddEndpointCertificateInputs →
      FinalMarkedTarget (2 * b + 1) m

theorem finalOddEndpointPromotion_of_targetPromotion
    (promotion : FinalOddEndpointTargetPromotion) :
    FinalOddEndpointPromotion where
  oddEndpoint := fun hb hRange parent input =>
    promotion.oddEndpoint hb hRange parent
      (finalOddEndpointCertificateInputs_of_endpointInputs input)

structure FinalRefinedEndpointGrowthPromotions : Prop where
  oddHighModulusPromotion : FinalOddHighModulusPromotion
  oddEndpointPromotion : FinalOddEndpointTargetPromotion

theorem finalPostPhaseGrowthPromotions_of_refinedEndpoint
    (promotions : FinalRefinedEndpointGrowthPromotions) :
    FinalPostPhaseGrowthPromotions where
  oddHighModulusPromotion := promotions.oddHighModulusPromotion
  oddEndpointPromotion :=
    finalOddEndpointPromotion_of_targetPromotion
      promotions.oddEndpointPromotion

structure FinalSixRefinedEndpointPromotionObligations : Prop where
  d3EvenPromotion : FinalD3EvenBasePromotion
  lowPromotions : FinalRefinedLowBasePromotions
  growthPromotions : FinalRefinedEndpointGrowthPromotions

theorem finalSixRefinedLowPromotionObligations_of_refinedEndpoint
    (remaining : FinalSixRefinedEndpointPromotionObligations) :
    FinalSixRefinedLowPromotionObligations where
  d3EvenPromotion := remaining.d3EvenPromotion
  lowPromotions := remaining.lowPromotions
  oddHighModulusPromotion :=
    remaining.growthPromotions.oddHighModulusPromotion
  oddEndpointPromotion :=
    finalOddEndpointPromotion_of_targetPromotion
      remaining.growthPromotions.oddEndpointPromotion

theorem finalTargetTorus_from_refinedEndpoint
    (remaining : FinalSixRefinedEndpointPromotionObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorus_from_refinedLow
    (finalSixRefinedLowPromotionObligations_of_refinedEndpoint remaining)
    hRange

theorem finalTargetMarkedTorus_from_refinedEndpoint
    (remaining : FinalSixRefinedEndpointPromotionObligations)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorus_from_refinedLow
    (finalSixRefinedLowPromotionObligations_of_refinedEndpoint remaining)
    hRange

theorem finalTargetCayley_from_refinedEndpoint
    (remaining : FinalSixRefinedEndpointPromotionObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayley_from_refinedLow
    (finalSixRefinedLowPromotionObligations_of_refinedEndpoint remaining)
    hRange

end FinalTargetEndpointCertificateBridge

export FinalTargetEndpointCertificateBridge
  (FinalOddEndpointCertificateInputs FinalOddEndpointTargetPromotion
   FinalRefinedEndpointGrowthPromotions
   FinalSixRefinedEndpointPromotionObligations
   finalOddEndpointCertificateInputs_of_endpointInputs
   finalOddEndpointCertificateInputs_holds
   finalOddEndpointCertificateTerminalTrace4Cycle
   finalOddEndpointCertificateTerminalTrace6Cycle
   finalOddEndpointCertificateTerminalReset4Cycle
   finalOddEndpointCertificateMarkedTransferAudit
   finalOddEndpointCertificateMarkedTransfer4
   finalOddEndpointCertificateMarkedTransfer6
   finalOddEndpointCertificatePhaseProductSupport
   finalOddEndpointCertificatePhaseProductRealization
   finalOddEndpointCertificateCompletionCarry
   finalOddEndpointCertificateB4FirstCompletion
   finalOddEndpointCertificateParentRange
   finalOddEndpointPromotion_of_targetPromotion
   finalPostPhaseGrowthPromotions_of_refinedEndpoint
   finalSixRefinedLowPromotionObligations_of_refinedEndpoint
   finalTargetTorus_from_refinedEndpoint
   finalTargetMarkedTorus_from_refinedEndpoint
   finalTargetCayley_from_refinedEndpoint)

end EvenV11
