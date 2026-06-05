import EvenV11.FinalConstructionArrowBridge

namespace EvenV11
namespace FinalArrowObligationBridge

structure FinalBaseArrowObligations
    (Ordinary Marked : Nat → Nat → Prop) : Prop where
  ordinaryTwo :
    ∀ {m : Nat}, EvenModulusRange m → Ordinary 2 m
  ordinaryThree :
    ∀ {m : Nat}, EvenModulusRange m → Ordinary 3 m
  markedD5M4 : Marked 5 4
  markedD7M4 : Marked 7 4
  markedD7M6 : Marked 7 6

structure FinalSuccessorArrowObligations
    (Ordinary Marked : Nat → Nat → Prop) : Prop where
  markedToOrdinary :
    ∀ {d m : Nat}, Marked d m → Ordinary d m
  evenPhaseDoubling :
    ∀ {a m : Nat}, 2 ≤ a → EvenModulusRange m →
      Ordinary a m → Marked (2 * a) m
  oddHighModulus :
    ∀ {d m : Nat}, 5 ≤ d → (∃ b : Nat, d = 2 * b + 1) →
      EvenModulusRange m → d < m → Marked d m
  oddEndpoint :
    ∀ {b m : Nat}, 4 ≤ b → MarkedDimensionRange b m →
      Marked b m → Marked (2 * b + 1) m

structure FinalArrowObligationInput
    (Ordinary Marked : Nat → Nat → Prop) : Prop where
  base : FinalBaseArrowObligations Ordinary Marked
  successor : FinalSuccessorArrowObligations Ordinary Marked

theorem finalArrowObligationInput_of_finalInductionArrows
    {Ordinary Marked : Nat → Nat → Prop}
    (arrows : FinalInductionArrowInput Ordinary Marked) :
    FinalArrowObligationInput Ordinary Marked where
  base :=
    { ordinaryTwo := arrows.ordinaryBaseTwo
      ordinaryThree := arrows.ordinaryBaseThree
      markedD5M4 := arrows.markedBaseD5M4
      markedD7M4 := arrows.markedBaseD7M4
      markedD7M6 := arrows.markedBaseD7M6 }
  successor :=
    { markedToOrdinary := arrows.markedForgetsToOrdinary
      evenPhaseDoubling := arrows.phaseDoubling
      oddHighModulus := arrows.highModulusStep
      oddEndpoint := arrows.endpointStep }

theorem finalInductionArrowInput_of_arrowObligationInput
    {Ordinary Marked : Nat → Nat → Prop}
    (input : FinalArrowObligationInput Ordinary Marked) :
    FinalInductionArrowInput Ordinary Marked where
  ordinaryBaseTwo := input.base.ordinaryTwo
  ordinaryBaseThree := input.base.ordinaryThree
  markedBaseD5M4 := input.base.markedD5M4
  markedBaseD7M4 := input.base.markedD7M4
  markedBaseD7M6 := input.base.markedD7M6
  markedForgetsToOrdinary := input.successor.markedToOrdinary
  phaseDoubling := input.successor.evenPhaseDoubling
  highModulusStep := input.successor.oddHighModulus
  endpointStep := input.successor.oddEndpoint

theorem finalConstructionArrowBridgeInput_of_arrowObligationInput
    {Ordinary Marked : Nat → Nat → Prop}
    (input : FinalArrowObligationInput Ordinary Marked) :
    FinalConstructionArrowBridgeInput Ordinary Marked :=
  finalConstructionArrowBridgeInput_of_arrows
    (finalInductionArrowInput_of_arrowObligationInput input)

theorem ordinaryConclusionFromArrowObligations
    {Ordinary Marked : Nat → Nat → Prop}
    (input : FinalArrowObligationInput Ordinary Marked)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Ordinary d m :=
  ordinaryConclusionFromConstructionArrows
    (finalConstructionArrowBridgeInput_of_arrowObligationInput input)
    (d := d) (m := m) hRange

theorem markedConclusionFromArrowObligations
    {Ordinary Marked : Nat → Nat → Prop}
    (input : FinalArrowObligationInput Ordinary Marked)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Marked d m :=
  markedConclusionFromConstructionArrows
    (finalConstructionArrowBridgeInput_of_arrowObligationInput input)
    (d := d) (m := m) hRange

end FinalArrowObligationBridge

export FinalArrowObligationBridge
  (FinalBaseArrowObligations FinalSuccessorArrowObligations
   FinalArrowObligationInput
   finalArrowObligationInput_of_finalInductionArrows
   finalInductionArrowInput_of_arrowObligationInput
   finalConstructionArrowBridgeInput_of_arrowObligationInput
   ordinaryConclusionFromArrowObligations
   markedConclusionFromArrowObligations)

end EvenV11
