import EvenV11.FinalTargetGrowthAssemblyBridge

namespace EvenV11
namespace FinalTargetLowBaseBridge

structure FinalLowMarkedBaseClosedInputs : Prop where
  terminalInput : FinalTerminalInput
  endpointInput : FinalEndpointInput

theorem finalLowMarkedBaseClosedInputs_holds :
    FinalLowMarkedBaseClosedInputs where
  terminalInput := finalTerminalInput_holds
  endpointInput := finalEndpointInput_holds

theorem finalLowMarkedBaseTerminalTrace4Cycle
    (input : FinalLowMarkedBaseClosedInputs) :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4) terminalTrace4) :=
  input.terminalInput.terminalTrace4Cycle

theorem finalLowMarkedBaseTerminalTrace6Cycle
    (input : FinalLowMarkedBaseClosedInputs) :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 6) terminalTrace6) :=
  input.terminalInput.terminalTrace6Cycle

theorem finalLowMarkedBaseTerminalReset4Cycle
    (input : FinalLowMarkedBaseClosedInputs) :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4) terminalResetTrace4) :=
  input.terminalInput.terminalResetTrace4Cycle

theorem finalLowMarkedBaseEndpointInput
    (input : FinalLowMarkedBaseClosedInputs) :
    FinalEndpointInput :=
  input.endpointInput

structure FinalLowMarkedBasePromotions : Prop where
  markedD5M4 :
    FinalLowMarkedBaseClosedInputs → FinalMarkedTarget 5 4
  markedD7M4 :
    FinalLowMarkedBaseClosedInputs → FinalMarkedTarget 7 4
  markedD7M6 :
    FinalLowMarkedBaseClosedInputs → FinalMarkedTarget 7 6

structure FinalLowMarkedBaseObligations : Prop where
  markedD5M4 : FinalMarkedTarget 5 4
  markedD7M4 : FinalMarkedTarget 7 4
  markedD7M6 : FinalMarkedTarget 7 6

theorem finalLowMarkedBaseObligations_of_promotions
    (promotions : FinalLowMarkedBasePromotions) :
    FinalLowMarkedBaseObligations where
  markedD5M4 :=
    promotions.markedD5M4 finalLowMarkedBaseClosedInputs_holds
  markedD7M4 :=
    promotions.markedD7M4 finalLowMarkedBaseClosedInputs_holds
  markedD7M6 :=
    promotions.markedD7M6 finalLowMarkedBaseClosedInputs_holds

structure FinalOrdinaryThreeBaseObligation : Prop where
  ordinaryThree :
    ∀ {m : Nat}, EvenModulusRange m → FinalOrdinaryTarget 3 m

theorem finalRemainingBase_of_ordinaryThreeAndLowMarkedBase
    (ordinary : FinalOrdinaryThreeBaseObligation)
    (low : FinalLowMarkedBaseObligations) :
    FinalRemainingTargetBaseObligations where
  ordinaryThree := ordinary.ordinaryThree
  markedD5M4 := low.markedD5M4
  markedD7M4 := low.markedD7M4
  markedD7M6 := low.markedD7M6

theorem finalRemainingBase_of_ordinaryThreeAndLowPromotions
    (ordinary : FinalOrdinaryThreeBaseObligation)
    (promotions : FinalLowMarkedBasePromotions) :
    FinalRemainingTargetBaseObligations :=
  finalRemainingBase_of_ordinaryThreeAndLowMarkedBase
    ordinary
    (finalLowMarkedBaseObligations_of_promotions promotions)

structure FinalTargetBasePromotionAssemblyInput : Prop where
  ordinaryThree : FinalOrdinaryThreeBaseObligation
  lowMarkedPromotions : FinalLowMarkedBasePromotions

theorem finalRemainingBase_of_basePromotionAssemblyInput
    (input : FinalTargetBasePromotionAssemblyInput) :
    FinalRemainingTargetBaseObligations :=
  finalRemainingBase_of_ordinaryThreeAndLowPromotions
    input.ordinaryThree input.lowMarkedPromotions

theorem finalTargetTorus_from_basePromotionGrowthArrows
    (base : FinalTargetBasePromotionAssemblyInput)
    (growth : FinalRemainingTargetGrowthArrows)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorusConclusionFromRemainingBaseAndGrowthArrows
    (finalRemainingBase_of_basePromotionAssemblyInput base)
    growth hRange

theorem finalTargetMarkedTorus_from_basePromotionGrowthArrows
    (base : FinalTargetBasePromotionAssemblyInput)
    (growth : FinalRemainingTargetGrowthArrows)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorusConclusionFromRemainingBaseAndGrowthArrows
    (finalRemainingBase_of_basePromotionAssemblyInput base)
    growth hRange

theorem finalTargetCayley_from_basePromotionGrowthArrows
    (base : FinalTargetBasePromotionAssemblyInput)
    (growth : FinalRemainingTargetGrowthArrows)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayleyConclusionFromRemainingBaseAndGrowthArrows
    (finalRemainingBase_of_basePromotionAssemblyInput base)
    growth hRange

theorem finalTargetTorus_from_basePromotionGrowthAssembly
    (base : FinalTargetBasePromotionAssemblyInput)
    (growth : FinalTargetGrowthAssemblyInput)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorusConclusionFromRemainingBaseAndGrowthAssembly
    (finalRemainingBase_of_basePromotionAssemblyInput base)
    growth hRange

theorem finalTargetMarkedTorus_from_basePromotionGrowthAssembly
    (base : FinalTargetBasePromotionAssemblyInput)
    (growth : FinalTargetGrowthAssemblyInput)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorusConclusionFromRemainingBaseAndGrowthAssembly
    (finalRemainingBase_of_basePromotionAssemblyInput base)
    growth hRange

theorem finalTargetCayley_from_basePromotionGrowthAssembly
    (base : FinalTargetBasePromotionAssemblyInput)
    (growth : FinalTargetGrowthAssemblyInput)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayleyConclusionFromRemainingBaseAndGrowthAssembly
    (finalRemainingBase_of_basePromotionAssemblyInput base)
    growth hRange

end FinalTargetLowBaseBridge

export FinalTargetLowBaseBridge
  (FinalLowMarkedBaseClosedInputs FinalLowMarkedBasePromotions
   FinalLowMarkedBaseObligations FinalOrdinaryThreeBaseObligation
   FinalTargetBasePromotionAssemblyInput
   finalLowMarkedBaseClosedInputs_holds
   finalLowMarkedBaseTerminalTrace4Cycle
   finalLowMarkedBaseTerminalTrace6Cycle
   finalLowMarkedBaseTerminalReset4Cycle
   finalLowMarkedBaseEndpointInput
   finalLowMarkedBaseObligations_of_promotions
   finalRemainingBase_of_ordinaryThreeAndLowMarkedBase
   finalRemainingBase_of_ordinaryThreeAndLowPromotions
   finalRemainingBase_of_basePromotionAssemblyInput
   finalTargetTorus_from_basePromotionGrowthArrows
   finalTargetMarkedTorus_from_basePromotionGrowthArrows
   finalTargetCayley_from_basePromotionGrowthArrows
   finalTargetTorus_from_basePromotionGrowthAssembly
   finalTargetMarkedTorus_from_basePromotionGrowthAssembly
   finalTargetCayley_from_basePromotionGrowthAssembly)

end EvenV11
