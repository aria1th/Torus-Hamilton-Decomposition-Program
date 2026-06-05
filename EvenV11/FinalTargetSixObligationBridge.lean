import EvenV11.FinalTargetPostPhaseGrowthBridge

namespace EvenV11
namespace FinalTargetSixObligationBridge

structure FinalLowMarkedD5M4Promotion : Prop where
  markedD5M4 :
    FinalLowMarkedBaseClosedInputs → FinalMarkedTarget 5 4

structure FinalLowMarkedD7M4Promotion : Prop where
  markedD7M4 :
    FinalLowMarkedBaseClosedInputs → FinalMarkedTarget 7 4

structure FinalLowMarkedD7M6Promotion : Prop where
  markedD7M6 :
    FinalLowMarkedBaseClosedInputs → FinalMarkedTarget 7 6

theorem finalLowMarkedBasePromotions_of_individual
    (d5m4 : FinalLowMarkedD5M4Promotion)
    (d7m4 : FinalLowMarkedD7M4Promotion)
    (d7m6 : FinalLowMarkedD7M6Promotion) :
    FinalLowMarkedBasePromotions where
  markedD5M4 := d5m4.markedD5M4
  markedD7M4 := d7m4.markedD7M4
  markedD7M6 := d7m6.markedD7M6

structure FinalSixRemainingPromotionObligations : Prop where
  d3EvenPromotion : FinalD3EvenBasePromotion
  lowD5M4Promotion : FinalLowMarkedD5M4Promotion
  lowD7M4Promotion : FinalLowMarkedD7M4Promotion
  lowD7M6Promotion : FinalLowMarkedD7M6Promotion
  oddHighModulusPromotion : FinalOddHighModulusPromotion
  oddEndpointPromotion : FinalOddEndpointPromotion

theorem finalLowMarkedBasePromotions_of_sixRemaining
    (remaining : FinalSixRemainingPromotionObligations) :
    FinalLowMarkedBasePromotions :=
  finalLowMarkedBasePromotions_of_individual
    remaining.lowD5M4Promotion
    remaining.lowD7M4Promotion
    remaining.lowD7M6Promotion

theorem finalPostPhaseGrowthPromotions_of_sixRemaining
    (remaining : FinalSixRemainingPromotionObligations) :
    FinalPostPhaseGrowthPromotions where
  oddHighModulusPromotion := remaining.oddHighModulusPromotion
  oddEndpointPromotion := remaining.oddEndpointPromotion

theorem finalExactRemainingPromotionObligations_of_sixRemaining
    (remaining : FinalSixRemainingPromotionObligations) :
    FinalExactRemainingPromotionObligations where
  d3EvenPromotion := remaining.d3EvenPromotion
  lowMarkedPromotions :=
    finalLowMarkedBasePromotions_of_sixRemaining remaining
  postPhaseGrowthPromotions :=
    finalPostPhaseGrowthPromotions_of_sixRemaining remaining

theorem finalExactRemainingTargetObligations_of_sixRemaining
    (remaining : FinalSixRemainingPromotionObligations) :
    FinalExactRemainingTargetObligations :=
  finalExactRemainingTargetObligations_of_promotions
    (finalExactRemainingPromotionObligations_of_sixRemaining remaining)

theorem finalTargetTorus_from_sixRemaining
    (remaining : FinalSixRemainingPromotionObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorus_from_promotionObligations
    (finalExactRemainingPromotionObligations_of_sixRemaining remaining)
    hRange

theorem finalTargetMarkedTorus_from_sixRemaining
    (remaining : FinalSixRemainingPromotionObligations)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorus_from_promotionObligations
    (finalExactRemainingPromotionObligations_of_sixRemaining remaining)
    hRange

theorem finalTargetCayley_from_sixRemaining
    (remaining : FinalSixRemainingPromotionObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayley_from_promotionObligations
    (finalExactRemainingPromotionObligations_of_sixRemaining remaining)
    hRange

end FinalTargetSixObligationBridge

export FinalTargetSixObligationBridge
  (FinalLowMarkedD5M4Promotion FinalLowMarkedD7M4Promotion
   FinalLowMarkedD7M6Promotion FinalSixRemainingPromotionObligations
   finalLowMarkedBasePromotions_of_individual
   finalLowMarkedBasePromotions_of_sixRemaining
   finalPostPhaseGrowthPromotions_of_sixRemaining
   finalExactRemainingPromotionObligations_of_sixRemaining
   finalExactRemainingTargetObligations_of_sixRemaining
   finalTargetTorus_from_sixRemaining
   finalTargetMarkedTorus_from_sixRemaining
   finalTargetCayley_from_sixRemaining)

end EvenV11
