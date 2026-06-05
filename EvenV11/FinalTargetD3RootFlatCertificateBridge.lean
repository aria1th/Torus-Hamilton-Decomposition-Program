import EvenV11.FinalTargetRootFlatCertificateBridge
import EvenV11.FinalTargetCertificateInputInventoryBridge

namespace EvenV11
namespace FinalTargetD3RootFlatCertificateBridge

abbrev finalD3RootFlatModelColorDir {m : Nat} {RootState : Type}
    (schedule :
      Shared.RootFlatSchedule (Shared.TorusColor 3)
        (Shared.TorusDirection 3) RootState m)
    (torusEquiv : ZMod m × RootState ≃ Shared.TorusVertex 3 m) :
    Shared.TorusColor 3 → Shared.TorusVertex 3 m →
      Shared.TorusDirection 3 :=
  finalRootFlatModelColorDir schedule torusEquiv

abbrev FinalD3EvenRootFlatModel
    (m : Nat) [NeZero m] (RootState : Type)
    (schedule :
      Shared.RootFlatSchedule (Shared.TorusColor 3)
        (Shared.TorusDirection 3) RootState m)
    (torusEquiv : ZMod m × RootState ≃ Shared.TorusVertex 3 m) :
    Prop :=
  FinalRootFlatTorusModel 3 m RootState schedule torusEquiv

abbrev FinalD3EvenRootFlatCertificate (m : Nat) : Prop :=
  FinalRootFlatTorusCertificate 3 m

theorem finalD3EvenRootFlatModelEdgePartition
    {m : Nat} [NeZero m] {RootState : Type}
    {schedule :
      Shared.RootFlatSchedule (Shared.TorusColor 3)
        (Shared.TorusDirection 3) RootState m}
    {torusEquiv : ZMod m × RootState ≃ Shared.TorusVertex 3 m}
    (model :
      FinalD3EvenRootFlatModel m RootState schedule torusEquiv) :
    Shared.IsCayleyEdgePartition
      (finalD3RootFlatModelColorDir schedule torusEquiv) :=
  finalRootFlatTorusModelEdgePartition model

theorem finalD3EvenRootFlatModelColorHamiltonian
    {m : Nat} [NeZero m] {RootState : Type}
    {schedule :
      Shared.RootFlatSchedule (Shared.TorusColor 3)
        (Shared.TorusDirection 3) RootState m}
    {torusEquiv : ZMod m × RootState ≃ Shared.TorusVertex 3 m}
    (model :
      FinalD3EvenRootFlatModel m RootState schedule torusEquiv) :
    Shared.IsCayleyColorHamiltonian
      (finalD3RootFlatModelColorDir schedule torusEquiv) :=
  finalRootFlatTorusModelColorHamiltonian model

theorem finalD3EvenRootFlatModelCayley
    {m : Nat} [NeZero m] {RootState : Type}
    {schedule :
      Shared.RootFlatSchedule (Shared.TorusColor 3)
        (Shared.TorusDirection 3) RootState m}
    {torusEquiv : ZMod m × RootState ≃ Shared.TorusVertex 3 m}
    (model :
      FinalD3EvenRootFlatModel m RootState schedule torusEquiv) :
    Shared.CayleyHamiltonDecomposition 3 m :=
  finalRootFlatTorusModelCayley model

theorem finalD3EvenTarget_of_rootFlatModel
    {m : Nat} [NeZero m] {RootState : Type}
    {schedule :
      Shared.RootFlatSchedule (Shared.TorusColor 3)
        (Shared.TorusDirection 3) RootState m}
    {torusEquiv : ZMod m × RootState ≃ Shared.TorusVertex 3 m}
    (model :
      FinalD3EvenRootFlatModel m RootState schedule torusEquiv) :
    FinalOrdinaryTarget 3 m :=
  finalRootFlatOrdinaryTarget_of_model model

theorem finalD3EvenTarget_of_rootFlatCertificate
    {m : Nat} (certificate : FinalD3EvenRootFlatCertificate m) :
    FinalOrdinaryTarget 3 m :=
  finalRootFlatOrdinaryTarget_of_certificate certificate

structure FinalD3EvenRootFlatCertificateFamily : Prop where
  rootFlatCertificate :
    ∀ {m : Nat}, EvenModulusRange m → FinalD3EvenRootFlatCertificate m

theorem finalD3EvenTarget_of_rootFlatCertificateFamily
    (family : FinalD3EvenRootFlatCertificateFamily)
    {m : Nat} (hm : EvenModulusRange m) :
    FinalOrdinaryTarget 3 m :=
  finalD3EvenTarget_of_rootFlatCertificate
    (family.rootFlatCertificate hm)

theorem finalD3EvenBasePromotion_of_rootFlatCertificateFamily
    (family : FinalD3EvenRootFlatCertificateFamily) :
    FinalD3EvenBasePromotion where
  ordinaryThree := fun hm _input =>
    finalD3EvenTarget_of_rootFlatCertificateFamily family hm

structure FinalTargetCertificateChecklistWithD3RootFlat : Prop where
  d3RootFlatFamily : FinalD3EvenRootFlatCertificateFamily
  d5m4Promotion : FinalLowD5M4TargetPromotion
  d7m4Promotion : FinalLowD7M4TargetPromotion
  d7m6Promotion : FinalLowD7M6TargetPromotion
  oddHighModulusPromotion : FinalOddHighModulusTargetPromotion
  oddEndpointPromotion : FinalOddEndpointPhaseProductTargetPromotion

theorem finalTargetCertificateChecklist_of_d3RootFlatChecklist
    (checklist : FinalTargetCertificateChecklistWithD3RootFlat) :
    FinalTargetCertificateChecklist where
  d3EvenPromotion :=
    finalD3EvenBasePromotion_of_rootFlatCertificateFamily
      checklist.d3RootFlatFamily
  d5m4Promotion := checklist.d5m4Promotion
  d7m4Promotion := checklist.d7m4Promotion
  d7m6Promotion := checklist.d7m6Promotion
  oddHighModulusPromotion := checklist.oddHighModulusPromotion
  oddEndpointPromotion := checklist.oddEndpointPromotion

theorem finalTargetReadyPackage_of_d3RootFlatChecklist
    (checklist : FinalTargetCertificateChecklistWithD3RootFlat) :
    FinalTargetCertificateReadyPackage :=
  finalTargetCertificateReadyPackage_of_checklist
    (finalTargetCertificateChecklist_of_d3RootFlatChecklist checklist)

theorem finalTargetTorus_from_d3RootFlatChecklist
    (checklist : FinalTargetCertificateChecklistWithD3RootFlat)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorus_from_certificateChecklist
    (finalTargetCertificateChecklist_of_d3RootFlatChecklist checklist)
    hRange

theorem finalTargetMarkedTorus_from_d3RootFlatChecklist
    (checklist : FinalTargetCertificateChecklistWithD3RootFlat)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorus_from_certificateChecklist
    (finalTargetCertificateChecklist_of_d3RootFlatChecklist checklist)
    hRange

theorem finalTargetCayley_from_d3RootFlatChecklist
    (checklist : FinalTargetCertificateChecklistWithD3RootFlat)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayley_from_certificateChecklist
    (finalTargetCertificateChecklist_of_d3RootFlatChecklist checklist)
    hRange

end FinalTargetD3RootFlatCertificateBridge

export FinalTargetD3RootFlatCertificateBridge
  (finalD3RootFlatModelColorDir
   FinalD3EvenRootFlatModel
   FinalD3EvenRootFlatCertificate
   finalD3EvenRootFlatModelEdgePartition
   finalD3EvenRootFlatModelColorHamiltonian
   finalD3EvenRootFlatModelCayley
   finalD3EvenTarget_of_rootFlatModel
   finalD3EvenTarget_of_rootFlatCertificate
   FinalD3EvenRootFlatCertificateFamily
   finalD3EvenTarget_of_rootFlatCertificateFamily
   finalD3EvenBasePromotion_of_rootFlatCertificateFamily
   FinalTargetCertificateChecklistWithD3RootFlat
   finalTargetCertificateChecklist_of_d3RootFlatChecklist
   finalTargetReadyPackage_of_d3RootFlatChecklist
   finalTargetTorus_from_d3RootFlatChecklist
   finalTargetMarkedTorus_from_d3RootFlatChecklist
   finalTargetCayley_from_d3RootFlatChecklist)

end EvenV11
