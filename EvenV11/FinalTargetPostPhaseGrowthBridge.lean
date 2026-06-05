import EvenV11.FinalTargetRemainingBridge

namespace EvenV11
namespace FinalTargetPostPhaseGrowthBridge

structure FinalOddHighModulusClosedInputs : Prop where
  returnCoreInput : FinalReturnCoreInput
  wordCoreInput : FinalWordCoreInput
  highEvenInput : FinalHighEvenInput
  rangeInput : FinalRangeInput

theorem finalOddHighModulusClosedInputs_holds :
    FinalOddHighModulusClosedInputs where
  returnCoreInput := finalReturnCoreInput_holds
  wordCoreInput := finalWordCoreInput_holds
  highEvenInput := finalHighEvenInput_holds
  rangeInput := finalRangeInput_holds

theorem finalOddHighModulusSuccessorInput
    (input : FinalOddHighModulusClosedInputs) :
    HighEvenSuccessorBridgeInput :=
  input.highEvenInput.highEvenSuccessorInput

theorem finalOddHighModulusFiniteAnchorInput
    (input : FinalOddHighModulusClosedInputs) :
    HighEvenFiniteAnchorInput :=
  (finalOddHighModulusSuccessorInput input).finiteAnchorInput

theorem finalOddHighModulusProjectionKernelInput
    (input : FinalOddHighModulusClosedInputs) :
    HighEvenProjectionKernelInput :=
  (finalOddHighModulusSuccessorInput input).projectionKernelInput

theorem finalOddHighModulusGuideLocalityInput
    (input : FinalOddHighModulusClosedInputs) :
    HighEvenGuideLocalityInput :=
  (finalOddHighModulusSuccessorInput input).guideLocalityInput

structure FinalOddEndpointClosedInputs : Prop where
  returnCoreInput : FinalReturnCoreInput
  wordCoreInput : FinalWordCoreInput
  terminalInput : FinalTerminalInput
  endpointInput : FinalEndpointInput
  rangeInput : FinalRangeInput

theorem finalOddEndpointClosedInputs_holds :
    FinalOddEndpointClosedInputs where
  returnCoreInput := finalReturnCoreInput_holds
  wordCoreInput := finalWordCoreInput_holds
  terminalInput := finalTerminalInput_holds
  endpointInput := finalEndpointInput_holds
  rangeInput := finalRangeInput_holds

theorem finalOddEndpointInput
    (input : FinalOddEndpointClosedInputs) :
    FinalEndpointInput :=
  input.endpointInput

theorem finalOddEndpointMarkedTransferAudit
    (input : FinalOddEndpointClosedInputs) :
    EndpointMarkedTransferBridge.foldedEndpointMarkedTransferInputAudit :=
  input.endpointInput.endpointMarkedTransferInput

structure FinalOddHighModulusPromotion : Prop where
  oddHighModulus :
    ∀ {d m : Nat}, 5 ≤ d → (∃ b : Nat, d = 2 * b + 1) →
      EvenModulusRange m → d < m →
      FinalOddHighModulusClosedInputs → FinalMarkedTarget d m

structure FinalOddEndpointPromotion : Prop where
  oddEndpoint :
    ∀ {b m : Nat}, 4 ≤ b → MarkedDimensionRange b m →
      FinalMarkedTarget b m → FinalOddEndpointClosedInputs →
      FinalMarkedTarget (2 * b + 1) m

structure FinalPostPhaseGrowthPromotions : Prop where
  oddHighModulusPromotion : FinalOddHighModulusPromotion
  oddEndpointPromotion : FinalOddEndpointPromotion

theorem finalPostPhaseGrowthArrows_of_promotions
    (promotions : FinalPostPhaseGrowthPromotions) :
    FinalRemainingTargetPostPhaseGrowthArrows where
  oddHighModulus := fun hd hodd hm hdm =>
    promotions.oddHighModulusPromotion.oddHighModulus
      hd hodd hm hdm finalOddHighModulusClosedInputs_holds
  oddEndpoint := fun hb hRange parent =>
    promotions.oddEndpointPromotion.oddEndpoint
      hb hRange parent finalOddEndpointClosedInputs_holds

theorem finalPostPhaseGrowthAssemblyInput_of_promotions
    (promotions : FinalPostPhaseGrowthPromotions) :
    FinalTargetPostPhaseGrowthAssemblyInput :=
  finalTargetPostPhaseGrowthAssemblyInput_of_remaining
    (finalPostPhaseGrowthArrows_of_promotions promotions)

structure FinalExactRemainingPromotionObligations : Prop where
  d3EvenPromotion : FinalD3EvenBasePromotion
  lowMarkedPromotions : FinalLowMarkedBasePromotions
  postPhaseGrowthPromotions : FinalPostPhaseGrowthPromotions

theorem finalExactRemainingTargetObligations_of_promotions
    (remaining : FinalExactRemainingPromotionObligations) :
    FinalExactRemainingTargetObligations where
  d3EvenPromotion := remaining.d3EvenPromotion
  lowMarkedPromotions := remaining.lowMarkedPromotions
  postPhaseGrowth :=
    finalPostPhaseGrowthArrows_of_promotions
      remaining.postPhaseGrowthPromotions

theorem finalTargetTorus_from_promotionObligations
    (remaining : FinalExactRemainingPromotionObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorus_from_exactRemaining
    (finalExactRemainingTargetObligations_of_promotions remaining)
    hRange

theorem finalTargetMarkedTorus_from_promotionObligations
    (remaining : FinalExactRemainingPromotionObligations)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorus_from_exactRemaining
    (finalExactRemainingTargetObligations_of_promotions remaining)
    hRange

theorem finalTargetCayley_from_promotionObligations
    (remaining : FinalExactRemainingPromotionObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayley_from_exactRemaining
    (finalExactRemainingTargetObligations_of_promotions remaining)
    hRange

end FinalTargetPostPhaseGrowthBridge

export FinalTargetPostPhaseGrowthBridge
  (FinalOddHighModulusClosedInputs FinalOddEndpointClosedInputs
   FinalOddHighModulusPromotion FinalOddEndpointPromotion
   FinalPostPhaseGrowthPromotions FinalExactRemainingPromotionObligations
   finalOddHighModulusClosedInputs_holds
   finalOddHighModulusSuccessorInput
   finalOddHighModulusFiniteAnchorInput
   finalOddHighModulusProjectionKernelInput
   finalOddHighModulusGuideLocalityInput
   finalOddEndpointClosedInputs_holds
   finalOddEndpointInput
   finalOddEndpointMarkedTransferAudit
   finalPostPhaseGrowthArrows_of_promotions
   finalPostPhaseGrowthAssemblyInput_of_promotions
   finalExactRemainingTargetObligations_of_promotions
   finalTargetTorus_from_promotionObligations
   finalTargetMarkedTorus_from_promotionObligations
   finalTargetCayley_from_promotionObligations)

end EvenV11
