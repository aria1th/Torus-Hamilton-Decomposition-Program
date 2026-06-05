import EvenV11.FinalInductionSchemeBridge

namespace EvenV11
namespace FinalSchemeProjectionBridge

theorem ordinaryConclusionFromFinalInductionScheme
    {Ordinary Marked : Nat → Nat → Prop}
    (range : FinalRangeInput)
    (arrows : FinalInductionArrowInput Ordinary Marked)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Ordinary d m :=
  (finalInductionScheme range arrows).1 d m hRange

theorem markedConclusionFromFinalInductionScheme
    {Ordinary Marked : Nat → Nat → Prop}
    (range : FinalRangeInput)
    (arrows : FinalInductionArrowInput Ordinary Marked)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Marked d m :=
  (finalInductionScheme range arrows).2 d m hRange

structure FinalSchemeProjectionInput : Prop where
  schemeBridge : FinalInductionSchemeBridgeInput
  ordinaryConclusion :
    ∀ {Ordinary Marked : Nat → Nat → Prop},
      FinalInductionArrowInput Ordinary Marked →
        ∀ {d m : Nat}, OrdinaryDimensionRange d m → Ordinary d m
  markedConclusion :
    ∀ {Ordinary Marked : Nat → Nat → Prop},
      FinalInductionArrowInput Ordinary Marked →
        ∀ {d m : Nat}, MarkedDimensionRange d m → Marked d m

theorem finalSchemeProjectionInput_holds :
    FinalSchemeProjectionInput where
  schemeBridge := finalInductionSchemeBridgeInput_holds
  ordinaryConclusion := fun arrows => fun {d m} hRange =>
    ordinaryConclusionFromFinalInductionScheme
      finalRangeInput_holds arrows (d := d) (m := m) hRange
  markedConclusion := fun arrows => fun {d m} hRange =>
    markedConclusionFromFinalInductionScheme
      finalRangeInput_holds arrows (d := d) (m := m) hRange

end FinalSchemeProjectionBridge

export FinalSchemeProjectionBridge
  (ordinaryConclusionFromFinalInductionScheme
   markedConclusionFromFinalInductionScheme
   FinalSchemeProjectionInput finalSchemeProjectionInput_holds)

end EvenV11
