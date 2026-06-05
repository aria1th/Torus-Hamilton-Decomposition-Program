import EvenV11.FinalInductionBridge

namespace EvenV11
namespace FinalRangeBookkeepingBridge

abbrev EvenModulusRange (m : Nat) : Prop :=
  4 ≤ m ∧ ∃ k : Nat, m = 2 * k

abbrev OrdinaryDimensionRange (d m : Nat) : Prop :=
  2 ≤ d ∧ EvenModulusRange m

abbrev MarkedDimensionRange (d m : Nat) : Prop :=
  4 ≤ d ∧ EvenModulusRange m ∧ m ≤ 2 * d + 1

inductive OddLowRangeCase (d m : Nat) : Prop where
  | dimensionFiveModulusFour :
      d = 5 → m = 4 → OddLowRangeCase d m
  | dimensionSevenModulusFour :
      d = 7 → m = 4 → OddLowRangeCase d m
  | dimensionSevenModulusSix :
      d = 7 → m = 6 → OddLowRangeCase d m
  | endpointStep :
      ∀ b : Nat,
        d = 2 * b + 1 →
        4 ≤ b →
        MarkedDimensionRange b m →
        OddLowRangeCase d m

inductive OddBranchRangeCase (d m : Nat) : Prop where
  | highModulusStep :
      5 ≤ d →
      (∃ b : Nat, d = 2 * b + 1) →
      EvenModulusRange m →
      d < m →
      OddBranchRangeCase d m
  | lowModulusStep :
      OddLowRangeCase d m → OddBranchRangeCase d m

theorem ordinaryBaseTwoRange
    {m : Nat} (hm : EvenModulusRange m) :
    OrdinaryDimensionRange 2 m := by
  exact ⟨by omega, hm⟩

theorem ordinaryBaseThreeRange
    {m : Nat} (hm : EvenModulusRange m) :
    OrdinaryDimensionRange 3 m := by
  exact ⟨by omega, hm⟩

theorem d5ResetMarkedRange :
    MarkedDimensionRange 5 4 := by
  exact ⟨by omega, ⟨by omega, ⟨2, by omega⟩⟩, by omega⟩

theorem rankThreeMarkedRange4 :
    MarkedDimensionRange 7 4 := by
  exact ⟨by omega, ⟨by omega, ⟨2, by omega⟩⟩, by omega⟩

theorem rankThreeMarkedRange6 :
    MarkedDimensionRange 7 6 := by
  exact ⟨by omega, ⟨by omega, ⟨3, by omega⟩⟩, by omega⟩

theorem markedRange_forget
    {d m : Nat} (h : MarkedDimensionRange d m) :
    OrdinaryDimensionRange d m := by
  exact ⟨by omega, h.2.1⟩

theorem evenStepParentOrdinaryRange
    {d a m : Nat} (h : OrdinaryDimensionRange d m)
    (hd : d = 2 * a) (hmin : 4 ≤ d) :
    OrdinaryDimensionRange a m := by
  exact ⟨by omega, h.2⟩

theorem markedEvenStepParentOrdinaryRange
    {d a m : Nat} (h : MarkedDimensionRange d m)
    (hd : d = 2 * a) (hmin : 4 ≤ d) :
    OrdinaryDimensionRange a m :=
  evenStepParentOrdinaryRange (markedRange_forget h) hd hmin

theorem endpointParentMarkedRange
    {d b m : Nat} (hd : d = 2 * b + 1)
    (hb : 4 ≤ b) (hm : EvenModulusRange m) (hmle : m ≤ d) :
    MarkedDimensionRange b m := by
  exact ⟨hb, hm, by omega⟩

theorem oddLowRangeCase_of_range
    {d m : Nat}
    (hdOdd : ∃ b : Nat, d = 2 * b + 1)
    (hmin : 5 ≤ d) (hm : EvenModulusRange m) (hmle : m ≤ d) :
    OddLowRangeCase d m := by
  rcases hdOdd with ⟨b, rfl⟩
  have hb2 : 2 ≤ b := by omega
  by_cases hb_two : b = 2
  · subst b
    have hm4 : m = 4 := by
      rcases hm.2 with ⟨k, hk⟩
      omega
    exact OddLowRangeCase.dimensionFiveModulusFour rfl hm4
  · by_cases hb_three : b = 3
    · subst b
      rcases hm.2 with ⟨k, hk⟩
      by_cases hk_two : k = 2
      · subst k
        have hm4 : m = 4 := by omega
        exact OddLowRangeCase.dimensionSevenModulusFour rfl hm4
      · have hk_three : k = 3 := by omega
        subst k
        have hm6 : m = 6 := by omega
        exact OddLowRangeCase.dimensionSevenModulusSix rfl hm6
    · have hb4 : 4 ≤ b := by omega
      exact OddLowRangeCase.endpointStep b rfl hb4
        (endpointParentMarkedRange rfl hb4 hm (by omega))

theorem oddBranchRangeCase_of_range
    {d m : Nat}
    (hdOdd : ∃ b : Nat, d = 2 * b + 1)
    (hmin : 5 ≤ d) (hm : EvenModulusRange m) :
    OddBranchRangeCase d m := by
  by_cases hhigh : d < m
  · exact OddBranchRangeCase.highModulusStep hmin hdOdd hm hhigh
  · have hmle : m ≤ d := by omega
    exact OddBranchRangeCase.lowModulusStep
      (oddLowRangeCase_of_range hdOdd hmin hm hmle)

structure FinalRangeInput : Prop where
  ordinaryBaseTwo :
    ∀ {m : Nat}, EvenModulusRange m → OrdinaryDimensionRange 2 m
  ordinaryBaseThree :
    ∀ {m : Nat}, EvenModulusRange m → OrdinaryDimensionRange 3 m
  markedBaseD5M4 : MarkedDimensionRange 5 4
  markedBaseD7M4 : MarkedDimensionRange 7 4
  markedBaseD7M6 : MarkedDimensionRange 7 6
  markedForgetsToOrdinary :
    ∀ {d m : Nat}, MarkedDimensionRange d m →
      OrdinaryDimensionRange d m
  evenStepParent :
    ∀ {d a m : Nat}, OrdinaryDimensionRange d m →
      d = 2 * a → 4 ≤ d → OrdinaryDimensionRange a m
  markedEvenStepParent :
    ∀ {d a m : Nat}, MarkedDimensionRange d m →
      d = 2 * a → 4 ≤ d → OrdinaryDimensionRange a m
  endpointParent :
    ∀ {d b m : Nat}, d = 2 * b + 1 → 4 ≤ b →
      EvenModulusRange m → m ≤ d → MarkedDimensionRange b m
  oddLowCase :
    ∀ {d m : Nat}, (∃ b : Nat, d = 2 * b + 1) →
      5 ≤ d → EvenModulusRange m → m ≤ d → OddLowRangeCase d m
  oddBranchCase :
    ∀ {d m : Nat}, (∃ b : Nat, d = 2 * b + 1) →
      5 ≤ d → EvenModulusRange m → OddBranchRangeCase d m

theorem finalRangeInput_holds :
    FinalRangeInput where
  ordinaryBaseTwo := ordinaryBaseTwoRange
  ordinaryBaseThree := ordinaryBaseThreeRange
  markedBaseD5M4 := d5ResetMarkedRange
  markedBaseD7M4 := rankThreeMarkedRange4
  markedBaseD7M6 := rankThreeMarkedRange6
  markedForgetsToOrdinary := markedRange_forget
  evenStepParent := evenStepParentOrdinaryRange
  markedEvenStepParent := markedEvenStepParentOrdinaryRange
  endpointParent := endpointParentMarkedRange
  oddLowCase := oddLowRangeCase_of_range
  oddBranchCase := oddBranchRangeCase_of_range

structure FinalInductionRangeBridgeInput : Prop where
  inductionInput : FinalInductionInterfaceInput
  rangeInput : FinalRangeInput

theorem finalInductionRangeBridgeInput_holds :
    FinalInductionRangeBridgeInput where
  inductionInput := finalInductionInterfaceInput_holds
  rangeInput := finalRangeInput_holds

end FinalRangeBookkeepingBridge

export FinalRangeBookkeepingBridge
  (EvenModulusRange OrdinaryDimensionRange MarkedDimensionRange
   OddLowRangeCase OddBranchRangeCase FinalRangeInput
   FinalInductionRangeBridgeInput ordinaryBaseTwoRange
   ordinaryBaseThreeRange d5ResetMarkedRange rankThreeMarkedRange4
   rankThreeMarkedRange6 markedRange_forget
   evenStepParentOrdinaryRange markedEvenStepParentOrdinaryRange
   endpointParentMarkedRange oddLowRangeCase_of_range
   oddBranchRangeCase_of_range finalRangeInput_holds
   finalInductionRangeBridgeInput_holds)

end EvenV11
