import EvenV11.ProjectionKernel
import EvenV11.GuideLocality
import EvenV11.TypeA.AnchorBridge

namespace EvenV11
namespace HighEvenSuccessorBridge

structure HighEvenProjectionKernelInput : Prop where
  projectionKernelCoordinate :
    ∀ {m r : Nat} [NeZero m]
      (theta : Vec m r → ZMod m) (H : Vec m r → Prop)
      (e g x : Vec m r)
      (_hThetaPlane :
        ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
      (_hThetaTranslatedLine :
        ∀ h : Vec m r, ∀ c : ZMod m, H h →
          theta (fun i => h i + c * e i) = 0)
      (_hxPlane : planeSpan e g x)
      (_hxTranslatedLine : translatedLineSet H e x),
      lineSpan e x
  projectionKernelQuotientZero :
    ∀ {m r : Nat} [NeZero m]
      (theta : Vec m r → ZMod m) (H : Vec m r → Prop)
      (e g x : Vec m r)
      (_hThetaPlane :
        ∀ a b : ZMod m, theta (fun i => a * e i + b * g i) = b)
      (_hThetaTranslatedLine :
        ∀ h : Vec m r, ∀ c : ZMod m, H h →
          theta (fun i => h i + c * e i) = 0)
      (hxPlane : planeSpan e g x)
      (_hxTranslatedLine : translatedLineSet H e x),
      planeLineQuotientMk e g x hxPlane = planeLineQuotientZero e g
  triangularKernelCoordinate :
    ∀ {m r : Nat} (H : Vec m r → Prop)
      (e0 e1 g1 x : Vec m r)
      (_hkill :
        ∀ b : ZMod m,
          translatedTwoLineSet H e0 e1 (fun i => b * g1 i) →
            b = 0)
      (_hxPlane :
        planeSpan e1 (triangularPlaneGenerator e0 g1) x)
      (_hxTranslated :
        translatedTwoLineSet H e0 e1 x),
      lineSpan e1 x
  triangularKernelQuotientZero :
    ∀ {m r : Nat} (H : Vec m r → Prop)
      (e0 e1 g1 x : Vec m r)
      (_hkill :
        ∀ b : ZMod m,
          translatedTwoLineSet H e0 e1 (fun i => b * g1 i) →
            b = 0)
      (hxPlane :
        planeSpan e1 (triangularPlaneGenerator e0 g1) x)
      (_hxTranslated :
        translatedTwoLineSet H e0 e1 x),
      planeLineQuotientMk e1 (triangularPlaneGenerator e0 g1)
        x hxPlane =
      planeLineQuotientZero e1 (triangularPlaneGenerator e0 g1)

theorem highEvenProjectionKernelInput_holds :
    HighEvenProjectionKernelInput where
  projectionKernelCoordinate :=
    projectionKernelCriterion_coordinate
  projectionKernelQuotientZero :=
    projectionKernelCriterion_planeLineQuotientZero
  triangularKernelCoordinate :=
    triangularTwoLeafProjectionKernel_coordinate
  triangularKernelQuotientZero :=
    triangularTwoLeafProjectionKernel_planeLineQuotientZero

structure HighEvenGuideLocalityInput : Prop where
  ordinaryNonzeroLocality :
    ∀ {D : Nat} {Row Value : Type} [Zero Value]
      (theta : Row → Value) (center : Row → ZMod D)
      {actualCenters : Set (ZMod D)}
      (rho : ZMod D) (growthRow : OrdinaryHighEvenRow)
      (_hsubset :
        actualCenters ⊆ ordinaryHighEvenBoundaryGuideSet rho growthRow)
      (_hzero : VanishesOutsideGuide theta center actualCenters)
      {row : Row} (_hne : theta row ≠ 0),
      (center row = rho - ordinaryHighEvenRowDelta growthRow ∨
        center row = rho ∨
        center row = rho + ordinaryHighEvenRowDelta growthRow) ∧
        center row ∈ ordinaryHighEvenRowBoundary growthRow
  ordinaryBoundaryChoiceVanishes :
    ∀ {D : Nat} {Row Value : Type} [Zero Value]
      (theta : Row → Value) (center : Row → ZMod D)
      (_hD : 11 ≤ D) (growthRow : OrdinaryHighEvenRow)
      (C : OrdinaryHighEvenBoundaryVisibleListCertificate
        (@ordinaryHighEvenBoundaryAvoidingPhaseChoice D growthRow)
        growthRow)
      (_hzero : VanishesOutsideGuideList theta center C.centers)
      (row : Row),
      theta row = 0
  ordinaryOldGeneratorVanishes :
    ∀ {D : Nat} {Row Value : Type} [Zero Value]
      (theta : Row → Value) (center : Row → ZMod D)
      (_hD : 11 ≤ D) (growthRow : OrdinaryHighEvenRow)
      (_hzero :
        VanishesOutsideGuideList theta center
          (ordinaryHighEvenOldGeneratorCenters growthRow))
      (row : Row),
      theta row = 0
  chainedNonzeroLocality :
    ∀ {Row Value : Type} [Zero Value]
      (theta : Row → Value) (center : Row → ZMod 9)
      {actualCenters : Set (ZMod 9)}
      (rho : ZMod 9) (growthRow : ChainedHighEvenRow)
      (_hsubset :
        actualCenters ⊆ chainedHighEvenBoundaryGuideSet rho growthRow)
      (_hzero : VanishesOutsideGuide theta center actualCenters)
      {row : Row} (_hne : theta row ≠ 0),
      (center row = rho - chainedHighEvenRowDelta growthRow ∨
        center row = rho ∨
        center row = rho + chainedHighEvenRowDelta growthRow) ∧
        center row ∈ chainedHighEvenRowBoundary growthRow
  chainedBoundaryChoiceVanishes :
    ∀ {Row Value : Type} [Zero Value]
      (theta : Row → Value) (center : Row → ZMod 9)
      (growthRow : ChainedHighEvenRow)
      (C : ChainedHighEvenBoundaryVisibleListCertificate
        (chainedHighEvenBoundaryAvoidingPhaseChoice growthRow)
        growthRow)
      (_hzero : VanishesOutsideGuideList theta center C.centers)
      (row : Row),
      theta row = 0
  chainedOldGeneratorVanishes :
    ∀ {Row Value : Type} [Zero Value]
      (theta : Row → Value) (center : Row → ZMod 9)
      (growthRow : ChainedHighEvenRow)
      (_hzero :
        VanishesOutsideGuideList theta center
          (chainedHighEvenOldGeneratorCenters growthRow))
      (row : Row),
      theta row = 0

theorem highEvenGuideLocalityInput_holds :
    HighEvenGuideLocalityInput where
  ordinaryNonzeroLocality :=
    guideLocalityOfNonzero_ordinaryHighEvenBoundaryGuide_subset
  ordinaryBoundaryChoiceVanishes :=
    theta_eq_zero_of_ordinaryHighEvenBoundaryChoice_boundaryVisibleCertificate
  ordinaryOldGeneratorVanishes :=
    theta_eq_zero_of_ordinaryHighEvenOldGenerator_boundaryChoice
  chainedNonzeroLocality :=
    guideLocalityOfNonzero_chainedHighEvenBoundaryGuide_subset
  chainedBoundaryChoiceVanishes :=
    theta_eq_zero_of_chainedHighEvenBoundaryChoice_boundaryVisibleCertificate
  chainedOldGeneratorVanishes :=
    theta_eq_zero_of_chainedHighEvenOldGenerator_boundaryChoice

structure HighEvenFiniteAnchorInput : Prop where
  d5AnchorAudit :
    FiniteAuditBridge.d5HighEvenAnchorAuditBool = true
  d7AnchorAudit :
    FiniteAuditBridge.d7HighEvenAnchorAuditBool = true
  anchorDimensionsNodup :
    FiniteAuditBridge.highEvenAnchorDimensions.Nodup
  anchorDimensionsAudit :
    FiniteAuditBridge.highEvenAnchorDimensionsAuditBool = true
  v28FiniteInput :
    TypeA.v28FiniteInputCoforestAudit

theorem highEvenFiniteAnchorInput_holds :
    HighEvenFiniteAnchorInput where
  d5AnchorAudit := d5HighEvenAnchorAudit
  d7AnchorAudit := d7HighEvenAnchorAudit
  anchorDimensionsNodup := highEvenAnchorDimensions_nodup
  anchorDimensionsAudit := highEvenAnchorDimensionsAudit
  v28FiniteInput := TypeA.v28FiniteInputCoforestAudit_holds

structure HighEvenSuccessorBridgeInput : Prop where
  finiteAnchorInput : HighEvenFiniteAnchorInput
  projectionKernelInput : HighEvenProjectionKernelInput
  guideLocalityInput : HighEvenGuideLocalityInput

theorem highEvenSuccessorBridgeInput_holds :
    HighEvenSuccessorBridgeInput where
  finiteAnchorInput := highEvenFiniteAnchorInput_holds
  projectionKernelInput := highEvenProjectionKernelInput_holds
  guideLocalityInput := highEvenGuideLocalityInput_holds

end HighEvenSuccessorBridge

export HighEvenSuccessorBridge
  (HighEvenProjectionKernelInput HighEvenGuideLocalityInput
   HighEvenFiniteAnchorInput HighEvenSuccessorBridgeInput
   highEvenProjectionKernelInput_holds
   highEvenGuideLocalityInput_holds
   highEvenFiniteAnchorInput_holds
   highEvenSuccessorBridgeInput_holds)

end EvenV11
