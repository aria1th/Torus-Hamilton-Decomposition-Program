import EvenV11.FinalTargetCertificateChecklistBridge

namespace EvenV11
namespace FinalTargetCertificateInputInventoryBridge

structure FinalTargetCertificateInputInventory : Prop where
  d3EvenInput : FinalD3EvenBaseClosedInputs
  d5m4Input : FinalLowD5M4ClosedInputs
  d7m4Input : FinalLowD7M4ClosedInputs
  d7m6Input : FinalLowD7M6ClosedInputs
  oddHighModulusInput : FinalOddHighModulusCertificateInputs
  phaseProductInput : FinalPhaseProductCertificateInputs
  oddEndpointInput : FinalOddEndpointPhaseProductCertificateInputs

theorem finalTargetCertificateInputInventory_holds :
    FinalTargetCertificateInputInventory where
  d3EvenInput := finalD3EvenBaseClosedInputs_holds
  d5m4Input := finalLowD5M4ClosedInputs_holds
  d7m4Input := finalLowD7M4ClosedInputs_holds
  d7m6Input := finalLowD7M6ClosedInputs_holds
  oddHighModulusInput := finalOddHighModulusCertificateInputs_holds
  phaseProductInput := finalPhaseProductCertificateInputs_holds
  oddEndpointInput := finalOddEndpointPhaseProductCertificateInputs_holds

theorem finalTargetCertificateInventoryD3EvenInput
    (inventory : FinalTargetCertificateInputInventory) :
    FinalD3EvenBaseClosedInputs :=
  inventory.d3EvenInput

theorem finalTargetCertificateInventoryD5M4Input
    (inventory : FinalTargetCertificateInputInventory) :
    FinalLowD5M4ClosedInputs :=
  inventory.d5m4Input

theorem finalTargetCertificateInventoryD7M4Input
    (inventory : FinalTargetCertificateInputInventory) :
    FinalLowD7M4ClosedInputs :=
  inventory.d7m4Input

theorem finalTargetCertificateInventoryD7M6Input
    (inventory : FinalTargetCertificateInputInventory) :
    FinalLowD7M6ClosedInputs :=
  inventory.d7m6Input

theorem finalTargetCertificateInventoryOddHighModulusInput
    (inventory : FinalTargetCertificateInputInventory) :
    FinalOddHighModulusCertificateInputs :=
  inventory.oddHighModulusInput

theorem finalTargetCertificateInventoryPhaseProductInput
    (inventory : FinalTargetCertificateInputInventory) :
    FinalPhaseProductCertificateInputs :=
  inventory.phaseProductInput

theorem finalTargetCertificateInventoryOddEndpointInput
    (inventory : FinalTargetCertificateInputInventory) :
    FinalOddEndpointPhaseProductCertificateInputs :=
  inventory.oddEndpointInput

theorem finalTargetCertificateInventoryEndpointPhaseProductInput
    (inventory : FinalTargetCertificateInputInventory) :
    FinalPhaseProductCertificateInputs :=
  finalOddEndpointPhaseProductCertificatePhaseProductInput
    inventory.oddEndpointInput

structure FinalTargetCertificateReadyPackage : Prop where
  inventory : FinalTargetCertificateInputInventory
  checklist : FinalTargetCertificateChecklist

theorem finalTargetCertificateReadyPackage_of_checklist
    (checklist : FinalTargetCertificateChecklist) :
    FinalTargetCertificateReadyPackage where
  inventory := finalTargetCertificateInputInventory_holds
  checklist := checklist

theorem finalTargetCertificateReadyPackageInventory
    (ready : FinalTargetCertificateReadyPackage) :
    FinalTargetCertificateInputInventory :=
  ready.inventory

theorem finalTargetCertificateReadyPackageChecklist
    (ready : FinalTargetCertificateReadyPackage) :
    FinalTargetCertificateChecklist :=
  ready.checklist

theorem finalTargetReadyPackageD3EvenTarget
    (ready : FinalTargetCertificateReadyPackage)
    {m : Nat} (hm : EvenModulusRange m) :
    FinalOrdinaryTarget 3 m :=
  (finalTargetCertificateChecklistD3EvenPromotion ready.checklist).ordinaryThree
    hm ready.inventory.d3EvenInput

theorem finalTargetReadyPackageD5M4Target
    (ready : FinalTargetCertificateReadyPackage) :
    FinalMarkedTarget 5 4 :=
  (finalTargetCertificateChecklistD5M4Promotion ready.checklist).markedD5M4
    ready.inventory.d5m4Input

theorem finalTargetReadyPackageD7M4Target
    (ready : FinalTargetCertificateReadyPackage) :
    FinalMarkedTarget 7 4 :=
  (finalTargetCertificateChecklistD7M4Promotion ready.checklist).markedD7M4
    ready.inventory.d7m4Input

theorem finalTargetReadyPackageD7M6Target
    (ready : FinalTargetCertificateReadyPackage) :
    FinalMarkedTarget 7 6 :=
  (finalTargetCertificateChecklistD7M6Promotion ready.checklist).markedD7M6
    ready.inventory.d7m6Input

theorem finalTargetReadyPackageOddHighModulusTarget
    (ready : FinalTargetCertificateReadyPackage)
    {d m : Nat} (hd : 5 ≤ d) (hodd : ∃ b : Nat, d = 2 * b + 1)
    (hm : EvenModulusRange m) (hdm : d < m) :
    FinalMarkedTarget d m :=
  (finalTargetCertificateChecklistOddHighModulusPromotion
    ready.checklist).oddHighModulus
    hd hodd hm hdm ready.inventory.oddHighModulusInput

theorem finalTargetReadyPackageOddEndpointTarget
    (ready : FinalTargetCertificateReadyPackage)
    {b m : Nat} (hb : 4 ≤ b) (hRange : MarkedDimensionRange b m)
    (parent : FinalMarkedTarget b m) :
    FinalMarkedTarget (2 * b + 1) m :=
  (finalTargetCertificateChecklistOddEndpointPromotion
    ready.checklist).oddEndpoint
    hb hRange parent ready.inventory.oddEndpointInput

theorem finalSixRefinedPhaseProductPromotionObligations_of_readyPackage
    (ready : FinalTargetCertificateReadyPackage) :
    FinalSixRefinedPhaseProductPromotionObligations :=
  finalSixRefinedPhaseProductPromotionObligations_of_certificateChecklist
    ready.checklist

theorem finalTargetTorus_from_readyPackage
    (ready : FinalTargetCertificateReadyPackage)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorus_from_certificateChecklist ready.checklist hRange

theorem finalTargetMarkedTorus_from_readyPackage
    (ready : FinalTargetCertificateReadyPackage)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorus_from_certificateChecklist ready.checklist hRange

theorem finalTargetCayley_from_readyPackage
    (ready : FinalTargetCertificateReadyPackage)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayley_from_certificateChecklist ready.checklist hRange

end FinalTargetCertificateInputInventoryBridge

export FinalTargetCertificateInputInventoryBridge
  (FinalTargetCertificateInputInventory
   finalTargetCertificateInputInventory_holds
   finalTargetCertificateInventoryD3EvenInput
   finalTargetCertificateInventoryD5M4Input
   finalTargetCertificateInventoryD7M4Input
   finalTargetCertificateInventoryD7M6Input
   finalTargetCertificateInventoryOddHighModulusInput
   finalTargetCertificateInventoryPhaseProductInput
   finalTargetCertificateInventoryOddEndpointInput
   finalTargetCertificateInventoryEndpointPhaseProductInput
   FinalTargetCertificateReadyPackage
   finalTargetCertificateReadyPackage_of_checklist
   finalTargetCertificateReadyPackageInventory
   finalTargetCertificateReadyPackageChecklist
   finalTargetReadyPackageD3EvenTarget
   finalTargetReadyPackageD5M4Target
   finalTargetReadyPackageD7M4Target
   finalTargetReadyPackageD7M6Target
   finalTargetReadyPackageOddHighModulusTarget
   finalTargetReadyPackageOddEndpointTarget
   finalSixRefinedPhaseProductPromotionObligations_of_readyPackage
   finalTargetTorus_from_readyPackage
   finalTargetMarkedTorus_from_readyPackage
   finalTargetCayley_from_readyPackage)

end EvenV11
