import EvenV11.FinalRangeBookkeepingBridge

namespace EvenV11
namespace FinalInductionSchemeBridge

structure FinalInductionArrowInput
    (Ordinary Marked : Nat → Nat → Prop) : Prop where
  ordinaryBaseTwo :
    ∀ {m : Nat}, EvenModulusRange m → Ordinary 2 m
  ordinaryBaseThree :
    ∀ {m : Nat}, EvenModulusRange m → Ordinary 3 m
  markedBaseD5M4 : Marked 5 4
  markedBaseD7M4 : Marked 7 4
  markedBaseD7M6 : Marked 7 6
  markedForgetsToOrdinary :
    ∀ {d m : Nat}, Marked d m → Ordinary d m
  phaseDoubling :
    ∀ {a m : Nat}, 2 ≤ a → EvenModulusRange m →
      Ordinary a m → Marked (2 * a) m
  highModulusStep :
    ∀ {d m : Nat}, 5 ≤ d → (∃ b : Nat, d = 2 * b + 1) →
      EvenModulusRange m → d < m → Marked d m
  endpointStep :
    ∀ {b m : Nat}, 4 ≤ b → MarkedDimensionRange b m →
      Marked b m → Marked (2 * b + 1) m

theorem finalInductionScheme
    {Ordinary Marked : Nat → Nat → Prop}
    (range : FinalRangeInput)
    (arrows : FinalInductionArrowInput Ordinary Marked) :
    (∀ d m : Nat, OrdinaryDimensionRange d m → Ordinary d m) ∧
      (∀ d m : Nat, MarkedDimensionRange d m → Marked d m) := by
  let P : Nat → Prop :=
    fun d =>
      (∀ m : Nat, OrdinaryDimensionRange d m → Ordinary d m) ∧
        (∀ m : Nat, MarkedDimensionRange d m → Marked d m)
  have hmain : ∀ d : Nat, P d := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        constructor
        · intro m hOrd
          by_cases hd2 : d = 2
          · subst d
            exact arrows.ordinaryBaseTwo hOrd.2
          · by_cases hd3 : d = 3
            · subst d
              exact arrows.ordinaryBaseThree hOrd.2
            · have hmin4 : 4 ≤ d := by omega
              rcases Nat.even_or_odd' d with ⟨a, hEven | hOdd⟩
              · have hParentRange :
                    OrdinaryDimensionRange a m :=
                  range.evenStepParent hOrd hEven hmin4
                have hParent : Ordinary a m :=
                  (ih a (by omega)).1 m hParentRange
                have hMarked : Marked d m := by
                  rw [hEven]
                  exact arrows.phaseDoubling hParentRange.1
                    hParentRange.2 hParent
                exact arrows.markedForgetsToOrdinary hMarked
              · have hdOdd : ∃ b : Nat, d = 2 * b + 1 :=
                  ⟨a, hOdd⟩
                have hmin5 : 5 ≤ d := by omega
                cases range.oddBranchCase hdOdd hmin5 hOrd.2 with
                | highModulusStep h5 hOdd' hm hhigh =>
                    exact arrows.markedForgetsToOrdinary
                      (arrows.highModulusStep h5 hOdd' hm hhigh)
                | lowModulusStep hlow =>
                    cases hlow with
                    | dimensionFiveModulusFour hd hm =>
                        rw [hd, hm]
                        exact arrows.markedForgetsToOrdinary
                          arrows.markedBaseD5M4
                    | dimensionSevenModulusFour hd hm =>
                        rw [hd, hm]
                        exact arrows.markedForgetsToOrdinary
                          arrows.markedBaseD7M4
                    | dimensionSevenModulusSix hd hm =>
                        rw [hd, hm]
                        exact arrows.markedForgetsToOrdinary
                          arrows.markedBaseD7M6
                    | endpointStep b hd hb hParentRange =>
                        have hParent : Marked b m :=
                          (ih b (by omega)).2 m hParentRange
                        have hMarked :
                            Marked (2 * b + 1) m :=
                          arrows.endpointStep hb hParentRange hParent
                        rw [hd]
                        exact arrows.markedForgetsToOrdinary hMarked
        · intro m hMarkedRange
          have hOrdRange : OrdinaryDimensionRange d m :=
            range.markedForgetsToOrdinary hMarkedRange
          by_cases hd2 : d = 2
          · subst d
            omega
          · by_cases hd3 : d = 3
            · subst d
              omega
            · have hmin4 : 4 ≤ d := hMarkedRange.1
              rcases Nat.even_or_odd' d with ⟨a, hEven | hOdd⟩
              · have hParentRange :
                    OrdinaryDimensionRange a m :=
                  range.markedEvenStepParent hMarkedRange hEven hmin4
                have hParent : Ordinary a m :=
                  (ih a (by omega)).1 m hParentRange
                rw [hEven]
                exact arrows.phaseDoubling hParentRange.1
                  hParentRange.2 hParent
              · have hdOdd : ∃ b : Nat, d = 2 * b + 1 :=
                  ⟨a, hOdd⟩
                have hmin5 : 5 ≤ d := by omega
                cases range.oddBranchCase hdOdd hmin5 hOrdRange.2 with
                | highModulusStep h5 hOdd' hm hhigh =>
                    exact arrows.highModulusStep h5 hOdd' hm hhigh
                | lowModulusStep hlow =>
                    cases hlow with
                    | dimensionFiveModulusFour hd hm =>
                        rw [hd, hm]
                        exact arrows.markedBaseD5M4
                    | dimensionSevenModulusFour hd hm =>
                        rw [hd, hm]
                        exact arrows.markedBaseD7M4
                    | dimensionSevenModulusSix hd hm =>
                        rw [hd, hm]
                        exact arrows.markedBaseD7M6
                    | endpointStep b hd hb hParentRange =>
                        have hParent : Marked b m :=
                          (ih b (by omega)).2 m hParentRange
                        have hMarked :
                            Marked (2 * b + 1) m :=
                          arrows.endpointStep hb hParentRange hParent
                        rw [hd]
                        exact hMarked
  constructor
  · intro d m hOrd
    exact (hmain d).1 m hOrd
  · intro d m hMarked
    exact (hmain d).2 m hMarked

structure FinalInductionSchemeBridgeInput : Prop where
  rangeBridge : FinalInductionRangeBridgeInput
  scheme :
    ∀ {Ordinary Marked : Nat → Nat → Prop},
      FinalInductionArrowInput Ordinary Marked →
        (∀ d m : Nat, OrdinaryDimensionRange d m → Ordinary d m) ∧
          (∀ d m : Nat, MarkedDimensionRange d m → Marked d m)

theorem finalInductionSchemeBridgeInput_holds :
    FinalInductionSchemeBridgeInput where
  rangeBridge := finalInductionRangeBridgeInput_holds
  scheme := fun arrows =>
    finalInductionScheme finalRangeInput_holds arrows

end FinalInductionSchemeBridge

export FinalInductionSchemeBridge
  (FinalInductionArrowInput FinalInductionSchemeBridgeInput
   finalInductionScheme finalInductionSchemeBridgeInput_holds)

end EvenV11
