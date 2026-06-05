import EvenV11.FinalTargetEndpointCertificateBridge

namespace EvenV11
namespace FinalTargetHighEvenCertificateBridge

structure FinalOddHighModulusCertificateInputs : Prop where
  returnCoreInput : FinalReturnCoreInput
  wordCoreInput : FinalWordCoreInput
  finiteAnchorInput : HighEvenFiniteAnchorInput
  projectionKernelInput : HighEvenProjectionKernelInput
  guideLocalityInput : HighEvenGuideLocalityInput
  rangeInput : FinalRangeInput

theorem finalOddHighModulusCertificateInputs_of_highEvenInputs
    (input : FinalOddHighModulusClosedInputs) :
    FinalOddHighModulusCertificateInputs where
  returnCoreInput := input.returnCoreInput
  wordCoreInput := input.wordCoreInput
  finiteAnchorInput :=
    (finalOddHighModulusSuccessorInput input).finiteAnchorInput
  projectionKernelInput :=
    (finalOddHighModulusSuccessorInput input).projectionKernelInput
  guideLocalityInput :=
    (finalOddHighModulusSuccessorInput input).guideLocalityInput
  rangeInput := input.rangeInput

theorem finalOddHighModulusCertificateInputs_holds :
    FinalOddHighModulusCertificateInputs :=
  finalOddHighModulusCertificateInputs_of_highEvenInputs
    finalOddHighModulusClosedInputs_holds

theorem finalOddHighModulusCertificateSuccessorInput
    (input : FinalOddHighModulusCertificateInputs) :
    HighEvenSuccessorBridgeInput where
  finiteAnchorInput := input.finiteAnchorInput
  projectionKernelInput := input.projectionKernelInput
  guideLocalityInput := input.guideLocalityInput

theorem finalOddHighModulusCertificateD5AnchorCheck
    (input : FinalOddHighModulusCertificateInputs) :
    FiniteAuditBridge.d5HighEvenAnchorAuditBool = true :=
  input.finiteAnchorInput.d5AnchorAudit

theorem finalOddHighModulusCertificateD7AnchorCheck
    (input : FinalOddHighModulusCertificateInputs) :
    FiniteAuditBridge.d7HighEvenAnchorAuditBool = true :=
  input.finiteAnchorInput.d7AnchorAudit

theorem finalOddHighModulusCertificateAnchorDimensionsNodup
    (input : FinalOddHighModulusCertificateInputs) :
    FiniteAuditBridge.highEvenAnchorDimensions.Nodup :=
  input.finiteAnchorInput.anchorDimensionsNodup

theorem finalOddHighModulusCertificateAnchorDimensionsCheck
    (input : FinalOddHighModulusCertificateInputs) :
    FiniteAuditBridge.highEvenAnchorDimensionsAuditBool = true :=
  input.finiteAnchorInput.anchorDimensionsAudit

theorem finalOddHighModulusCertificateV28FiniteInput
    (input : FinalOddHighModulusCertificateInputs) :
    TypeA.v28FiniteInputCoforestAudit :=
  input.finiteAnchorInput.v28FiniteInput

theorem finalOddHighModulusCertificateV28FoldedTerminal
    (input : FinalOddHighModulusCertificateInputs) :
    TypeA.v28FoldedTerminalInputAudit :=
  input.finiteAnchorInput.v28FiniteInput.2.1

theorem finalOddHighModulusCertificateD5CoforestRooted
    (input : FinalOddHighModulusCertificateInputs) :
    TypeA.d5CoforestRowsRootedAudit :=
  input.finiteAnchorInput.v28FiniteInput.2.2.1

theorem finalOddHighModulusCertificateD5CoforestIncidence
    (input : FinalOddHighModulusCertificateInputs) :
    TypeA.d5CoforestRowsIncidenceAudit :=
  input.finiteAnchorInput.v28FiniteInput.2.2.2.1

theorem finalOddHighModulusCertificateD7CoforestRooted
    (input : FinalOddHighModulusCertificateInputs) :
    TypeA.d7Stage12CoforestRowsRootedAudit :=
  input.finiteAnchorInput.v28FiniteInput.2.2.2.2.1

theorem finalOddHighModulusCertificateD7CoforestIncidence
    (input : FinalOddHighModulusCertificateInputs) :
    TypeA.d7Stage12CoforestRowsIncidenceAudit :=
  input.finiteAnchorInput.v28FiniteInput.2.2.2.2.2

theorem finalOddHighModulusCertificateProjectionKernelCoordinate
    (input : FinalOddHighModulusCertificateInputs)
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (H : Vec m r → Prop)
    (e g x : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hThetaTranslatedLine :
      ∀ h : Vec m r, ∀ c : ZMod m, H h →
        theta (fun i => h i + c * e i) = 0)
    (hxPlane : planeSpan e g x)
    (hxTranslatedLine : translatedLineSet H e x) :
    lineSpan e x :=
  input.projectionKernelInput.projectionKernelCoordinate
    theta H e g x hThetaPlane hThetaTranslatedLine hxPlane
    hxTranslatedLine

theorem finalOddHighModulusCertificateProjectionKernelQuotientZero
    (input : FinalOddHighModulusCertificateInputs)
    {m r : Nat} [NeZero m]
    (theta : Vec m r → ZMod m) (H : Vec m r → Prop)
    (e g x : Vec m r)
    (hThetaPlane :
      ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
    (hThetaTranslatedLine :
      ∀ h : Vec m r, ∀ c : ZMod m, H h →
        theta (fun i => h i + c * e i) = 0)
    (hxPlane : planeSpan e g x)
    (hxTranslatedLine : translatedLineSet H e x) :
    planeLineQuotientMk e g x hxPlane = planeLineQuotientZero e g :=
  input.projectionKernelInput.projectionKernelQuotientZero
    theta H e g x hThetaPlane hThetaTranslatedLine hxPlane
    hxTranslatedLine

theorem finalOddHighModulusCertificateTriangularKernelCoordinate
    (input : FinalOddHighModulusCertificateInputs)
    {m r : Nat} (H : Vec m r → Prop)
    (e0 e1 g1 x : Vec m r)
    (hkill :
      ∀ b : ZMod m,
        translatedTwoLineSet H e0 e1 (fun i => b * g1 i) →
          b = 0)
    (hxPlane :
      planeSpan e1 (triangularPlaneGenerator e0 g1) x)
    (hxTranslated :
      translatedTwoLineSet H e0 e1 x) :
    lineSpan e1 x :=
  input.projectionKernelInput.triangularKernelCoordinate
    H e0 e1 g1 x hkill hxPlane hxTranslated

theorem finalOddHighModulusCertificateTriangularKernelQuotientZero
    (input : FinalOddHighModulusCertificateInputs)
    {m r : Nat} (H : Vec m r → Prop)
    (e0 e1 g1 x : Vec m r)
    (hkill :
      ∀ b : ZMod m,
        translatedTwoLineSet H e0 e1 (fun i => b * g1 i) →
          b = 0)
    (hxPlane :
      planeSpan e1 (triangularPlaneGenerator e0 g1) x)
    (hxTranslated :
      translatedTwoLineSet H e0 e1 x) :
    planeLineQuotientMk e1 (triangularPlaneGenerator e0 g1)
      x hxPlane =
    planeLineQuotientZero e1 (triangularPlaneGenerator e0 g1) :=
  input.projectionKernelInput.triangularKernelQuotientZero
    H e0 e1 g1 x hkill hxPlane hxTranslated

theorem finalOddHighModulusCertificateOrdinaryNonzeroLocality
    (input : FinalOddHighModulusCertificateInputs)
    {D : Nat} {Row Value : Type} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod D)
    {actualCenters : Set (ZMod D)}
    (rho : ZMod D) (growthRow : OrdinaryHighEvenRow)
    (hsubset :
      actualCenters ⊆ ordinaryHighEvenBoundaryGuideSet rho growthRow)
    (hzero : VanishesOutsideGuide theta center actualCenters)
    {row : Row} (hne : theta row ≠ 0) :
    (center row = rho - ordinaryHighEvenRowDelta growthRow ∨
      center row = rho ∨
      center row = rho + ordinaryHighEvenRowDelta growthRow) ∧
      center row ∈ ordinaryHighEvenRowBoundary growthRow :=
  input.guideLocalityInput.ordinaryNonzeroLocality
    theta center rho growthRow hsubset hzero hne

theorem finalOddHighModulusCertificateOrdinaryBoundaryChoiceVanishes
    (input : FinalOddHighModulusCertificateInputs)
    {D : Nat} {Row Value : Type} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod D)
    (hD : 11 ≤ D) (growthRow : OrdinaryHighEvenRow)
    (C : OrdinaryHighEvenBoundaryVisibleListCertificate
      (@ordinaryHighEvenBoundaryAvoidingPhaseChoice D growthRow)
      growthRow)
    (hzero : VanishesOutsideGuideList theta center C.centers)
    (row : Row) :
    theta row = 0 :=
  input.guideLocalityInput.ordinaryBoundaryChoiceVanishes
    theta center hD growthRow C hzero row

theorem finalOddHighModulusCertificateOrdinaryOldGeneratorVanishes
    (input : FinalOddHighModulusCertificateInputs)
    {D : Nat} {Row Value : Type} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod D)
    (hD : 11 ≤ D) (growthRow : OrdinaryHighEvenRow)
    (hzero :
      VanishesOutsideGuideList theta center
        (ordinaryHighEvenOldGeneratorCenters growthRow))
    (row : Row) :
    theta row = 0 :=
  input.guideLocalityInput.ordinaryOldGeneratorVanishes
    theta center hD growthRow hzero row

theorem finalOddHighModulusCertificateChainedNonzeroLocality
    (input : FinalOddHighModulusCertificateInputs)
    {Row Value : Type} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod 9)
    {actualCenters : Set (ZMod 9)}
    (rho : ZMod 9) (growthRow : ChainedHighEvenRow)
    (hsubset :
      actualCenters ⊆ chainedHighEvenBoundaryGuideSet rho growthRow)
    (hzero : VanishesOutsideGuide theta center actualCenters)
    {row : Row} (hne : theta row ≠ 0) :
    (center row = rho - chainedHighEvenRowDelta growthRow ∨
      center row = rho ∨
      center row = rho + chainedHighEvenRowDelta growthRow) ∧
      center row ∈ chainedHighEvenRowBoundary growthRow :=
  input.guideLocalityInput.chainedNonzeroLocality
    theta center rho growthRow hsubset hzero hne

theorem finalOddHighModulusCertificateChainedBoundaryChoiceVanishes
    (input : FinalOddHighModulusCertificateInputs)
    {Row Value : Type} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod 9)
    (growthRow : ChainedHighEvenRow)
    (C : ChainedHighEvenBoundaryVisibleListCertificate
      (chainedHighEvenBoundaryAvoidingPhaseChoice growthRow)
      growthRow)
    (hzero : VanishesOutsideGuideList theta center C.centers)
    (row : Row) :
    theta row = 0 :=
  input.guideLocalityInput.chainedBoundaryChoiceVanishes
    theta center growthRow C hzero row

theorem finalOddHighModulusCertificateChainedOldGeneratorVanishes
    (input : FinalOddHighModulusCertificateInputs)
    {Row Value : Type} [Zero Value]
    (theta : Row → Value) (center : Row → ZMod 9)
    (growthRow : ChainedHighEvenRow)
    (hzero :
      VanishesOutsideGuideList theta center
        (chainedHighEvenOldGeneratorCenters growthRow))
    (row : Row) :
    theta row = 0 :=
  input.guideLocalityInput.chainedOldGeneratorVanishes
    theta center growthRow hzero row

theorem finalOddHighModulusCertificateBranchCase
    (input : FinalOddHighModulusCertificateInputs)
    {d m : Nat} (hodd : ∃ b : Nat, d = 2 * b + 1)
    (hmin : 5 ≤ d) (hm : EvenModulusRange m) :
    OddBranchRangeCase d m :=
  input.rangeInput.oddBranchCase hodd hmin hm

structure FinalOddHighModulusTargetPromotion : Prop where
  oddHighModulus :
    ∀ {d m : Nat}, 5 ≤ d → (∃ b : Nat, d = 2 * b + 1) →
      EvenModulusRange m → d < m →
      FinalOddHighModulusCertificateInputs → FinalMarkedTarget d m

theorem finalOddHighModulusPromotion_of_targetPromotion
    (promotion : FinalOddHighModulusTargetPromotion) :
    FinalOddHighModulusPromotion where
  oddHighModulus := fun hd hodd hm hdm input =>
    promotion.oddHighModulus hd hodd hm hdm
      (finalOddHighModulusCertificateInputs_of_highEvenInputs input)

theorem finalOddHighModulusClosedInputs_of_certificateInputs
    (input : FinalOddHighModulusCertificateInputs) :
    FinalOddHighModulusClosedInputs where
  returnCoreInput := input.returnCoreInput
  wordCoreInput := input.wordCoreInput
  highEvenInput :=
    { highEvenSuccessorInput :=
        finalOddHighModulusCertificateSuccessorInput input }
  rangeInput := input.rangeInput

theorem finalOddHighModulusTargetPromotion_of_closedPromotion
    (promotion : FinalOddHighModulusPromotion) :
    FinalOddHighModulusTargetPromotion where
  oddHighModulus := fun hd hodd hm hdm input =>
    promotion.oddHighModulus hd hodd hm hdm
      (finalOddHighModulusClosedInputs_of_certificateInputs input)

structure FinalRefinedHighEvenGrowthPromotions : Prop where
  oddHighModulusPromotion : FinalOddHighModulusTargetPromotion
  oddEndpointPromotion : FinalOddEndpointTargetPromotion

theorem finalRefinedEndpointGrowthPromotions_of_refinedHighEven
    (promotions : FinalRefinedHighEvenGrowthPromotions) :
    FinalRefinedEndpointGrowthPromotions where
  oddHighModulusPromotion :=
    finalOddHighModulusPromotion_of_targetPromotion
      promotions.oddHighModulusPromotion
  oddEndpointPromotion := promotions.oddEndpointPromotion

theorem finalPostPhaseGrowthPromotions_of_refinedHighEven
    (promotions : FinalRefinedHighEvenGrowthPromotions) :
    FinalPostPhaseGrowthPromotions :=
  finalPostPhaseGrowthPromotions_of_refinedEndpoint
    (finalRefinedEndpointGrowthPromotions_of_refinedHighEven promotions)

structure FinalSixRefinedHighEvenPromotionObligations : Prop where
  d3EvenPromotion : FinalD3EvenBasePromotion
  lowPromotions : FinalRefinedLowBasePromotions
  growthPromotions : FinalRefinedHighEvenGrowthPromotions

theorem finalSixRefinedEndpointPromotionObligations_of_refinedHighEven
    (remaining : FinalSixRefinedHighEvenPromotionObligations) :
    FinalSixRefinedEndpointPromotionObligations where
  d3EvenPromotion := remaining.d3EvenPromotion
  lowPromotions := remaining.lowPromotions
  growthPromotions :=
    finalRefinedEndpointGrowthPromotions_of_refinedHighEven
      remaining.growthPromotions

theorem finalTargetTorus_from_refinedHighEven
    (remaining : FinalSixRefinedHighEvenPromotionObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorus_from_refinedEndpoint
    (finalSixRefinedEndpointPromotionObligations_of_refinedHighEven
      remaining)
    hRange

theorem finalTargetMarkedTorus_from_refinedHighEven
    (remaining : FinalSixRefinedHighEvenPromotionObligations)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorus_from_refinedEndpoint
    (finalSixRefinedEndpointPromotionObligations_of_refinedHighEven
      remaining)
    hRange

theorem finalTargetCayley_from_refinedHighEven
    (remaining : FinalSixRefinedHighEvenPromotionObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayley_from_refinedEndpoint
    (finalSixRefinedEndpointPromotionObligations_of_refinedHighEven
      remaining)
    hRange

end FinalTargetHighEvenCertificateBridge

export FinalTargetHighEvenCertificateBridge
  (FinalOddHighModulusCertificateInputs
   FinalOddHighModulusTargetPromotion
   FinalRefinedHighEvenGrowthPromotions
   FinalSixRefinedHighEvenPromotionObligations
   finalOddHighModulusCertificateInputs_of_highEvenInputs
   finalOddHighModulusCertificateInputs_holds
   finalOddHighModulusCertificateSuccessorInput
   finalOddHighModulusCertificateD5AnchorCheck
   finalOddHighModulusCertificateD7AnchorCheck
   finalOddHighModulusCertificateAnchorDimensionsNodup
   finalOddHighModulusCertificateAnchorDimensionsCheck
   finalOddHighModulusCertificateV28FiniteInput
   finalOddHighModulusCertificateV28FoldedTerminal
   finalOddHighModulusCertificateD5CoforestRooted
   finalOddHighModulusCertificateD5CoforestIncidence
   finalOddHighModulusCertificateD7CoforestRooted
   finalOddHighModulusCertificateD7CoforestIncidence
   finalOddHighModulusCertificateProjectionKernelCoordinate
   finalOddHighModulusCertificateProjectionKernelQuotientZero
   finalOddHighModulusCertificateTriangularKernelCoordinate
   finalOddHighModulusCertificateTriangularKernelQuotientZero
   finalOddHighModulusCertificateOrdinaryNonzeroLocality
   finalOddHighModulusCertificateOrdinaryBoundaryChoiceVanishes
   finalOddHighModulusCertificateOrdinaryOldGeneratorVanishes
   finalOddHighModulusCertificateChainedNonzeroLocality
   finalOddHighModulusCertificateChainedBoundaryChoiceVanishes
   finalOddHighModulusCertificateChainedOldGeneratorVanishes
   finalOddHighModulusCertificateBranchCase
   finalOddHighModulusPromotion_of_targetPromotion
   finalOddHighModulusClosedInputs_of_certificateInputs
   finalOddHighModulusTargetPromotion_of_closedPromotion
   finalRefinedEndpointGrowthPromotions_of_refinedHighEven
   finalPostPhaseGrowthPromotions_of_refinedHighEven
   finalSixRefinedEndpointPromotionObligations_of_refinedHighEven
   finalTargetTorus_from_refinedHighEven
   finalTargetMarkedTorus_from_refinedHighEven
   finalTargetCayley_from_refinedHighEven)

end EvenV11
