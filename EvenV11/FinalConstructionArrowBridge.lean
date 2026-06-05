import EvenV11.FinalSchemeProjectionBridge

namespace EvenV11
namespace FinalConstructionArrowBridge

structure FinalConstructionArrowBridgeInput
    (Ordinary Marked : Nat → Nat → Prop) : Prop where
  interfaceInput : FinalInductionInterfaceInput
  schemeProjectionInput : FinalSchemeProjectionInput
  arrows : FinalInductionArrowInput Ordinary Marked

theorem finalConstructionArrowBridgeInput_of_arrows
    {Ordinary Marked : Nat → Nat → Prop}
    (arrows : FinalInductionArrowInput Ordinary Marked) :
    FinalConstructionArrowBridgeInput Ordinary Marked where
  interfaceInput := finalInductionInterfaceInput_holds
  schemeProjectionInput := finalSchemeProjectionInput_holds
  arrows := arrows

theorem ordinaryConclusionFromConstructionArrows
    {Ordinary Marked : Nat → Nat → Prop}
    (input : FinalConstructionArrowBridgeInput Ordinary Marked)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Ordinary d m :=
  input.schemeProjectionInput.ordinaryConclusion input.arrows
    (d := d) (m := m) hRange

theorem markedConclusionFromConstructionArrows
    {Ordinary Marked : Nat → Nat → Prop}
    (input : FinalConstructionArrowBridgeInput Ordinary Marked)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Marked d m :=
  input.schemeProjectionInput.markedConclusion input.arrows
    (d := d) (m := m) hRange

end FinalConstructionArrowBridge

export FinalConstructionArrowBridge
  (FinalConstructionArrowBridgeInput
   finalConstructionArrowBridgeInput_of_arrows
   ordinaryConclusionFromConstructionArrows
   markedConclusionFromConstructionArrows)

end EvenV11
