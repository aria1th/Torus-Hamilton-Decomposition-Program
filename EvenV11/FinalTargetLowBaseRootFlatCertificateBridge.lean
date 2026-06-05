import EvenV11.FinalTargetD3RootFlatCertificateBridge

namespace EvenV11
namespace FinalTargetLowBaseRootFlatCertificateBridge

structure FinalLowD5M4RootFlatCertificateFamily : Prop where
  rootFlatCertificate :
    FinalLowD5M4ClosedInputs → FinalRootFlatTorusCertificate 5 4

structure FinalLowD7M4RootFlatCertificateFamily : Prop where
  rootFlatCertificate :
    FinalLowD7M4ClosedInputs → FinalRootFlatTorusCertificate 7 4

structure FinalLowD7M6RootFlatCertificateFamily : Prop where
  rootFlatCertificate :
    FinalLowD7M6ClosedInputs → FinalRootFlatTorusCertificate 7 6

theorem finalLowD5M4RootFlatCertificateFamily_of_certificate
    (certificate : FinalRootFlatTorusCertificate 5 4) :
    FinalLowD5M4RootFlatCertificateFamily where
  rootFlatCertificate := fun _ => certificate

theorem finalLowD7M4RootFlatCertificateFamily_of_certificate
    (certificate : FinalRootFlatTorusCertificate 7 4) :
    FinalLowD7M4RootFlatCertificateFamily where
  rootFlatCertificate := fun _ => certificate

theorem finalLowD7M6RootFlatCertificateFamily_of_certificate
    (certificate : FinalRootFlatTorusCertificate 7 6) :
    FinalLowD7M6RootFlatCertificateFamily where
  rootFlatCertificate := fun _ => certificate

theorem finalLowD5M4Target_of_rootFlatCertificateFamily
    (family : FinalLowD5M4RootFlatCertificateFamily)
    (input : FinalLowD5M4ClosedInputs) :
    FinalMarkedTarget 5 4 :=
  finalRootFlatMarkedTarget_of_certificate
    (family.rootFlatCertificate input)

theorem finalLowD7M4Target_of_rootFlatCertificateFamily
    (family : FinalLowD7M4RootFlatCertificateFamily)
    (input : FinalLowD7M4ClosedInputs) :
    FinalMarkedTarget 7 4 :=
  finalRootFlatMarkedTarget_of_certificate
    (family.rootFlatCertificate input)

theorem finalLowD7M6Target_of_rootFlatCertificateFamily
    (family : FinalLowD7M6RootFlatCertificateFamily)
    (input : FinalLowD7M6ClosedInputs) :
    FinalMarkedTarget 7 6 :=
  finalRootFlatMarkedTarget_of_certificate
    (family.rootFlatCertificate input)

theorem finalLowD5M4TargetPromotion_of_rootFlatCertificateFamily
    (family : FinalLowD5M4RootFlatCertificateFamily) :
    FinalLowD5M4TargetPromotion where
  markedD5M4 := finalLowD5M4Target_of_rootFlatCertificateFamily family

theorem finalLowD7M4TargetPromotion_of_rootFlatCertificateFamily
    (family : FinalLowD7M4RootFlatCertificateFamily) :
    FinalLowD7M4TargetPromotion where
  markedD7M4 := finalLowD7M4Target_of_rootFlatCertificateFamily family

theorem finalLowD7M6TargetPromotion_of_rootFlatCertificateFamily
    (family : FinalLowD7M6RootFlatCertificateFamily) :
    FinalLowD7M6TargetPromotion where
  markedD7M6 := finalLowD7M6Target_of_rootFlatCertificateFamily family

structure FinalLowBaseRootFlatCertificateFamilies : Prop where
  d5m4 : FinalLowD5M4RootFlatCertificateFamily
  d7m4 : FinalLowD7M4RootFlatCertificateFamily
  d7m6 : FinalLowD7M6RootFlatCertificateFamily

theorem finalLowBaseRootFlatCertificateFamilies_of_certificates
    (d5m4 : FinalRootFlatTorusCertificate 5 4)
    (d7m4 : FinalRootFlatTorusCertificate 7 4)
    (d7m6 : FinalRootFlatTorusCertificate 7 6) :
    FinalLowBaseRootFlatCertificateFamilies where
  d5m4 := finalLowD5M4RootFlatCertificateFamily_of_certificate d5m4
  d7m4 := finalLowD7M4RootFlatCertificateFamily_of_certificate d7m4
  d7m6 := finalLowD7M6RootFlatCertificateFamily_of_certificate d7m6

theorem finalRefinedLowBasePromotions_of_rootFlatCertificateFamilies
    (families : FinalLowBaseRootFlatCertificateFamilies) :
    FinalRefinedLowBasePromotions where
  d5m4 :=
    finalLowD5M4TargetPromotion_of_rootFlatCertificateFamily
      families.d5m4
  d7m4 :=
    finalLowD7M4TargetPromotion_of_rootFlatCertificateFamily
      families.d7m4
  d7m6 :=
    finalLowD7M6TargetPromotion_of_rootFlatCertificateFamily
      families.d7m6

theorem finalLowBaseRootFlatD5M4Target
    (families : FinalLowBaseRootFlatCertificateFamilies)
    (input : FinalLowD5M4ClosedInputs) :
    FinalMarkedTarget 5 4 :=
  finalLowD5M4Target_of_rootFlatCertificateFamily
    families.d5m4 input

theorem finalLowBaseRootFlatD7M4Target
    (families : FinalLowBaseRootFlatCertificateFamilies)
    (input : FinalLowD7M4ClosedInputs) :
    FinalMarkedTarget 7 4 :=
  finalLowD7M4Target_of_rootFlatCertificateFamily
    families.d7m4 input

theorem finalLowBaseRootFlatD7M6Target
    (families : FinalLowBaseRootFlatCertificateFamilies)
    (input : FinalLowD7M6ClosedInputs) :
    FinalMarkedTarget 7 6 :=
  finalLowD7M6Target_of_rootFlatCertificateFamily
    families.d7m6 input

structure FinalTargetCertificateChecklistWithD3AndLowRootFlat : Prop where
  d3RootFlatFamily : FinalD3EvenRootFlatCertificateFamily
  lowRootFlatFamilies : FinalLowBaseRootFlatCertificateFamilies
  oddHighModulusPromotion : FinalOddHighModulusTargetPromotion
  oddEndpointPromotion : FinalOddEndpointPhaseProductTargetPromotion

structure FinalTargetCertificateChecklistWithD3PromotionAndLowRootFlat :
    Prop where
  d3EvenPromotion : FinalD3EvenBasePromotion
  lowRootFlatFamilies : FinalLowBaseRootFlatCertificateFamilies
  oddHighModulusPromotion : FinalOddHighModulusTargetPromotion
  oddEndpointPromotion : FinalOddEndpointPhaseProductTargetPromotion

theorem finalTargetCertificateChecklist_of_d3PromotionAndLowRootFlat
    (checklist : FinalTargetCertificateChecklistWithD3PromotionAndLowRootFlat) :
    FinalTargetCertificateChecklist where
  d3EvenPromotion := checklist.d3EvenPromotion
  d5m4Promotion :=
    (finalRefinedLowBasePromotions_of_rootFlatCertificateFamilies
      checklist.lowRootFlatFamilies).d5m4
  d7m4Promotion :=
    (finalRefinedLowBasePromotions_of_rootFlatCertificateFamilies
      checklist.lowRootFlatFamilies).d7m4
  d7m6Promotion :=
    (finalRefinedLowBasePromotions_of_rootFlatCertificateFamilies
      checklist.lowRootFlatFamilies).d7m6
  oddHighModulusPromotion := checklist.oddHighModulusPromotion
  oddEndpointPromotion := checklist.oddEndpointPromotion

theorem finalTargetReadyPackage_of_d3PromotionAndLowRootFlatChecklist
    (checklist : FinalTargetCertificateChecklistWithD3PromotionAndLowRootFlat) :
    FinalTargetCertificateReadyPackage :=
  finalTargetCertificateReadyPackage_of_checklist
    (finalTargetCertificateChecklist_of_d3PromotionAndLowRootFlat checklist)

theorem finalTargetTorus_from_d3PromotionAndLowRootFlatChecklist
    (checklist : FinalTargetCertificateChecklistWithD3PromotionAndLowRootFlat)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorus_from_certificateChecklist
    (finalTargetCertificateChecklist_of_d3PromotionAndLowRootFlat checklist)
    hRange

theorem finalTargetMarkedTorus_from_d3PromotionAndLowRootFlatChecklist
    (checklist : FinalTargetCertificateChecklistWithD3PromotionAndLowRootFlat)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorus_from_certificateChecklist
    (finalTargetCertificateChecklist_of_d3PromotionAndLowRootFlat checklist)
    hRange

theorem finalTargetCayley_from_d3PromotionAndLowRootFlatChecklist
    (checklist : FinalTargetCertificateChecklistWithD3PromotionAndLowRootFlat)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayley_from_certificateChecklist
    (finalTargetCertificateChecklist_of_d3PromotionAndLowRootFlat checklist)
    hRange

theorem finalTargetCertificateChecklistWithD3RootFlat_of_lowRootFlat
    (checklist : FinalTargetCertificateChecklistWithD3AndLowRootFlat) :
    FinalTargetCertificateChecklistWithD3RootFlat where
  d3RootFlatFamily := checklist.d3RootFlatFamily
  d5m4Promotion :=
    (finalRefinedLowBasePromotions_of_rootFlatCertificateFamilies
      checklist.lowRootFlatFamilies).d5m4
  d7m4Promotion :=
    (finalRefinedLowBasePromotions_of_rootFlatCertificateFamilies
      checklist.lowRootFlatFamilies).d7m4
  d7m6Promotion :=
    (finalRefinedLowBasePromotions_of_rootFlatCertificateFamilies
      checklist.lowRootFlatFamilies).d7m6
  oddHighModulusPromotion := checklist.oddHighModulusPromotion
  oddEndpointPromotion := checklist.oddEndpointPromotion

theorem finalTargetCertificateChecklist_of_d3AndLowRootFlat
    (checklist : FinalTargetCertificateChecklistWithD3AndLowRootFlat) :
    FinalTargetCertificateChecklist :=
  finalTargetCertificateChecklist_of_d3RootFlatChecklist
    (finalTargetCertificateChecklistWithD3RootFlat_of_lowRootFlat
      checklist)

theorem finalTargetReadyPackage_of_d3AndLowRootFlatChecklist
    (checklist : FinalTargetCertificateChecklistWithD3AndLowRootFlat) :
    FinalTargetCertificateReadyPackage :=
  finalTargetCertificateReadyPackage_of_checklist
    (finalTargetCertificateChecklist_of_d3AndLowRootFlat checklist)

theorem finalTargetTorus_from_d3AndLowRootFlatChecklist
    (checklist : FinalTargetCertificateChecklistWithD3AndLowRootFlat)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorus_from_certificateChecklist
    (finalTargetCertificateChecklist_of_d3AndLowRootFlat checklist)
    hRange

theorem finalTargetMarkedTorus_from_d3AndLowRootFlatChecklist
    (checklist : FinalTargetCertificateChecklistWithD3AndLowRootFlat)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorus_from_certificateChecklist
    (finalTargetCertificateChecklist_of_d3AndLowRootFlat checklist)
    hRange

theorem finalTargetCayley_from_d3AndLowRootFlatChecklist
    (checklist : FinalTargetCertificateChecklistWithD3AndLowRootFlat)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayley_from_certificateChecklist
    (finalTargetCertificateChecklist_of_d3AndLowRootFlat checklist)
    hRange

end FinalTargetLowBaseRootFlatCertificateBridge

export FinalTargetLowBaseRootFlatCertificateBridge
  (FinalLowD5M4RootFlatCertificateFamily
   FinalLowD7M4RootFlatCertificateFamily
   FinalLowD7M6RootFlatCertificateFamily
   finalLowD5M4RootFlatCertificateFamily_of_certificate
   finalLowD7M4RootFlatCertificateFamily_of_certificate
   finalLowD7M6RootFlatCertificateFamily_of_certificate
   finalLowD5M4Target_of_rootFlatCertificateFamily
   finalLowD7M4Target_of_rootFlatCertificateFamily
   finalLowD7M6Target_of_rootFlatCertificateFamily
   finalLowD5M4TargetPromotion_of_rootFlatCertificateFamily
   finalLowD7M4TargetPromotion_of_rootFlatCertificateFamily
   finalLowD7M6TargetPromotion_of_rootFlatCertificateFamily
   FinalLowBaseRootFlatCertificateFamilies
   finalLowBaseRootFlatCertificateFamilies_of_certificates
   finalRefinedLowBasePromotions_of_rootFlatCertificateFamilies
   finalLowBaseRootFlatD5M4Target
   finalLowBaseRootFlatD7M4Target
   finalLowBaseRootFlatD7M6Target
   FinalTargetCertificateChecklistWithD3AndLowRootFlat
   FinalTargetCertificateChecklistWithD3PromotionAndLowRootFlat
   finalTargetCertificateChecklist_of_d3PromotionAndLowRootFlat
   finalTargetReadyPackage_of_d3PromotionAndLowRootFlatChecklist
   finalTargetTorus_from_d3PromotionAndLowRootFlatChecklist
   finalTargetMarkedTorus_from_d3PromotionAndLowRootFlatChecklist
   finalTargetCayley_from_d3PromotionAndLowRootFlatChecklist
   finalTargetCertificateChecklistWithD3RootFlat_of_lowRootFlat
   finalTargetCertificateChecklist_of_d3AndLowRootFlat
   finalTargetReadyPackage_of_d3AndLowRootFlatChecklist
   finalTargetTorus_from_d3AndLowRootFlatChecklist
   finalTargetMarkedTorus_from_d3AndLowRootFlatChecklist
   finalTargetCayley_from_d3AndLowRootFlatChecklist)

end EvenV11
