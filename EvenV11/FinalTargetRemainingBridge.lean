import EvenV11.FinalTargetPhaseDoublingBridge

namespace EvenV11
namespace FinalTargetRemainingBridge

structure FinalExactRemainingTargetObligations : Prop where
  d3EvenPromotion : FinalD3EvenBasePromotion
  lowMarkedPromotions : FinalLowMarkedBasePromotions
  postPhaseGrowth : FinalRemainingTargetPostPhaseGrowthArrows

theorem finalBasePromotionAssemblyInput_of_exactRemaining
    (remaining : FinalExactRemainingTargetObligations) :
    FinalBasePromotionAssemblyInput where
  d3EvenPromotion := remaining.d3EvenPromotion
  lowMarkedPromotions := remaining.lowMarkedPromotions

theorem finalPostPhaseGrowthAssemblyInput_of_exactRemaining
    (remaining : FinalExactRemainingTargetObligations) :
    FinalTargetPostPhaseGrowthAssemblyInput :=
  finalTargetPostPhaseGrowthAssemblyInput_of_remaining
    remaining.postPhaseGrowth

theorem finalTargetGrowthAssemblyInput_of_exactRemaining
    (remaining : FinalExactRemainingTargetObligations) :
    FinalTargetGrowthAssemblyInput :=
  finalTargetGrowthAssemblyInput_of_postPhase
    (finalPostPhaseGrowthAssemblyInput_of_exactRemaining remaining)

theorem finalRemainingBase_of_exactRemaining
    (remaining : FinalExactRemainingTargetObligations) :
    FinalRemainingTargetBaseObligations :=
  finalRemainingBase_of_basePromotions
    (finalBasePromotionAssemblyInput_of_exactRemaining remaining)

theorem finalRemainingTargetGrowthArrows_of_exactRemaining
    (remaining : FinalExactRemainingTargetObligations) :
    FinalRemainingTargetGrowthArrows :=
  finalRemainingTargetGrowthArrows_of_postPhase
    remaining.postPhaseGrowth

theorem finalTargetBaseObligations_of_exactRemaining
    (remaining : FinalExactRemainingTargetObligations) :
    FinalTargetBaseObligations :=
  finalTargetBaseObligations_of_remainingBase
    (finalRemainingBase_of_exactRemaining remaining)

theorem finalTargetGrowthObligations_of_exactRemaining
    (remaining : FinalExactRemainingTargetObligations) :
    FinalTargetGrowthObligations :=
  finalTargetGrowthObligations_of_remainingGrowthArrows
    (finalRemainingTargetGrowthArrows_of_exactRemaining remaining)

theorem finalTargetTorus_from_exactRemaining
    (remaining : FinalExactRemainingTargetObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorus_from_basePromotionsPostPhaseGrowth
    (finalBasePromotionAssemblyInput_of_exactRemaining remaining)
    remaining.postPhaseGrowth hRange

theorem finalTargetMarkedTorus_from_exactRemaining
    (remaining : FinalExactRemainingTargetObligations)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorus_from_basePromotionsPostPhaseGrowth
    (finalBasePromotionAssemblyInput_of_exactRemaining remaining)
    remaining.postPhaseGrowth hRange

theorem finalTargetCayley_from_exactRemaining
    (remaining : FinalExactRemainingTargetObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayley_from_basePromotionsPostPhaseGrowth
    (finalBasePromotionAssemblyInput_of_exactRemaining remaining)
    remaining.postPhaseGrowth hRange

end FinalTargetRemainingBridge

export FinalTargetRemainingBridge
  (FinalExactRemainingTargetObligations
   finalBasePromotionAssemblyInput_of_exactRemaining
   finalPostPhaseGrowthAssemblyInput_of_exactRemaining
   finalTargetGrowthAssemblyInput_of_exactRemaining
   finalRemainingBase_of_exactRemaining
   finalRemainingTargetGrowthArrows_of_exactRemaining
   finalTargetBaseObligations_of_exactRemaining
   finalTargetGrowthObligations_of_exactRemaining
   finalTargetTorus_from_exactRemaining
   finalTargetMarkedTorus_from_exactRemaining
   finalTargetCayley_from_exactRemaining)

end EvenV11
