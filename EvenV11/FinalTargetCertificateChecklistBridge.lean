import EvenV11.FinalTargetPhaseProductCertificateBridge

namespace EvenV11
namespace FinalTargetCertificateChecklistBridge

structure FinalTargetCertificateChecklist : Prop where
  d3EvenPromotion : FinalD3EvenBasePromotion
  d5m4Promotion : FinalLowD5M4TargetPromotion
  d7m4Promotion : FinalLowD7M4TargetPromotion
  d7m6Promotion : FinalLowD7M6TargetPromotion
  oddHighModulusPromotion : FinalOddHighModulusTargetPromotion
  oddEndpointPromotion : FinalOddEndpointPhaseProductTargetPromotion

theorem finalTargetCertificateChecklistD3EvenPromotion
    (checklist : FinalTargetCertificateChecklist) :
    FinalD3EvenBasePromotion :=
  checklist.d3EvenPromotion

theorem finalTargetCertificateChecklistD5M4Promotion
    (checklist : FinalTargetCertificateChecklist) :
    FinalLowD5M4TargetPromotion :=
  checklist.d5m4Promotion

theorem finalTargetCertificateChecklistD7M4Promotion
    (checklist : FinalTargetCertificateChecklist) :
    FinalLowD7M4TargetPromotion :=
  checklist.d7m4Promotion

theorem finalTargetCertificateChecklistD7M6Promotion
    (checklist : FinalTargetCertificateChecklist) :
    FinalLowD7M6TargetPromotion :=
  checklist.d7m6Promotion

theorem finalTargetCertificateChecklistOddHighModulusPromotion
    (checklist : FinalTargetCertificateChecklist) :
    FinalOddHighModulusTargetPromotion :=
  checklist.oddHighModulusPromotion

theorem finalTargetCertificateChecklistOddEndpointPromotion
    (checklist : FinalTargetCertificateChecklist) :
    FinalOddEndpointPhaseProductTargetPromotion :=
  checklist.oddEndpointPromotion

theorem finalRefinedLowBasePromotions_of_certificateChecklist
    (checklist : FinalTargetCertificateChecklist) :
    FinalRefinedLowBasePromotions where
  d5m4 := checklist.d5m4Promotion
  d7m4 := checklist.d7m4Promotion
  d7m6 := checklist.d7m6Promotion

theorem finalRefinedPhaseProductGrowthPromotions_of_certificateChecklist
    (checklist : FinalTargetCertificateChecklist) :
    FinalRefinedPhaseProductGrowthPromotions where
  oddHighModulusPromotion := checklist.oddHighModulusPromotion
  oddEndpointPromotion := checklist.oddEndpointPromotion

theorem finalSixRefinedPhaseProductPromotionObligations_of_certificateChecklist
    (checklist : FinalTargetCertificateChecklist) :
    FinalSixRefinedPhaseProductPromotionObligations where
  d3EvenPromotion := checklist.d3EvenPromotion
  lowPromotions :=
    finalRefinedLowBasePromotions_of_certificateChecklist checklist
  growthPromotions :=
    finalRefinedPhaseProductGrowthPromotions_of_certificateChecklist
      checklist

theorem finalTargetTorus_from_certificateChecklist
    (checklist : FinalTargetCertificateChecklist)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorus_from_refinedPhaseProduct
    (finalSixRefinedPhaseProductPromotionObligations_of_certificateChecklist
      checklist)
    hRange

theorem finalTargetMarkedTorus_from_certificateChecklist
    (checklist : FinalTargetCertificateChecklist)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorus_from_refinedPhaseProduct
    (finalSixRefinedPhaseProductPromotionObligations_of_certificateChecklist
      checklist)
    hRange

theorem finalTargetCayley_from_certificateChecklist
    (checklist : FinalTargetCertificateChecklist)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayley_from_refinedPhaseProduct
    (finalSixRefinedPhaseProductPromotionObligations_of_certificateChecklist
      checklist)
    hRange

end FinalTargetCertificateChecklistBridge

export FinalTargetCertificateChecklistBridge
  (FinalTargetCertificateChecklist
   finalTargetCertificateChecklistD3EvenPromotion
   finalTargetCertificateChecklistD5M4Promotion
   finalTargetCertificateChecklistD7M4Promotion
   finalTargetCertificateChecklistD7M6Promotion
   finalTargetCertificateChecklistOddHighModulusPromotion
   finalTargetCertificateChecklistOddEndpointPromotion
   finalRefinedLowBasePromotions_of_certificateChecklist
   finalRefinedPhaseProductGrowthPromotions_of_certificateChecklist
   finalSixRefinedPhaseProductPromotionObligations_of_certificateChecklist
   finalTargetTorus_from_certificateChecklist
   finalTargetMarkedTorus_from_certificateChecklist
   finalTargetCayley_from_certificateChecklist)

end EvenV11
