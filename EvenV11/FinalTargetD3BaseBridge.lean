import EvenV11.FinalTargetLowBaseBridge

namespace EvenV11
namespace FinalTargetD3BaseBridge

structure FinalD3EvenBaseClosedInputs : Prop where
  returnCoreInput : FinalReturnCoreInput
  rangeInput : FinalRangeInput

theorem finalD3EvenBaseClosedInputs_holds :
    FinalD3EvenBaseClosedInputs where
  returnCoreInput := finalReturnCoreInput_holds
  rangeInput := finalRangeInput_holds

theorem finalD3EvenBaseOrdinaryRange
    (input : FinalD3EvenBaseClosedInputs)
    {m : Nat} (hm : EvenModulusRange m) :
    OrdinaryDimensionRange 3 m :=
  input.rangeInput.ordinaryBaseThree hm

theorem finalD3EvenBaseReturnCriterionInput
    (input : FinalD3EvenBaseClosedInputs) :
    ∀ {Color Direction RootState : Type} {m : Nat} [NeZero m]
      {S : Shared.RootFlatSchedule Color Direction RootState m},
      S.rowLatin →
      S.layerBijective →
      S.returnsSingleCycle →
      Shared.RootFlatReturnCriterion Color Direction RootState m :=
  input.returnCoreInput.rootFlatReturnCriterionInput

theorem finalD3EvenBaseLayeredHamiltonianInput
    (input : FinalD3EvenBaseClosedInputs) :
    ∀ {Color Direction RootState : Type} {m : Nat} [NeZero m]
      {S : Shared.RootFlatSchedule Color Direction RootState m},
      S.rowLatin →
      S.layerBijective →
      S.returnsSingleCycle →
      Shared.RootFlatLayeredHamiltonDecomposition
        Color Direction RootState m :=
  input.returnCoreInput.rootFlatLayeredHamiltonianInput

structure FinalD3EvenBasePromotion : Prop where
  ordinaryThree :
    ∀ {m : Nat}, EvenModulusRange m →
      FinalD3EvenBaseClosedInputs → FinalOrdinaryTarget 3 m

theorem finalD3EvenBasePromotion_of_ordinaryTargetFamily
    (target : ∀ {m : Nat}, EvenModulusRange m → FinalOrdinaryTarget 3 m) :
    FinalD3EvenBasePromotion where
  ordinaryThree := fun hm _input => target hm

theorem finalD3EvenBasePromotion_of_cayleyFamily
    (target :
      ∀ {m : Nat}, EvenModulusRange m →
        Shared.CayleyHamiltonDecomposition 3 m) :
    FinalD3EvenBasePromotion :=
  finalD3EvenBasePromotion_of_ordinaryTargetFamily
    (fun hm => (Shared.torusHamiltonDecomposition_iff_cayley).mpr (target hm))

theorem finalOrdinaryThreeBaseObligation_of_d3Promotion
    (promotion : FinalD3EvenBasePromotion) :
    FinalOrdinaryThreeBaseObligation where
  ordinaryThree := fun hm =>
    promotion.ordinaryThree hm finalD3EvenBaseClosedInputs_holds

structure FinalBasePromotionAssemblyInput : Prop where
  d3EvenPromotion : FinalD3EvenBasePromotion
  lowMarkedPromotions : FinalLowMarkedBasePromotions

theorem finalTargetBasePromotionAssemblyInput_of_basePromotions
    (input : FinalBasePromotionAssemblyInput) :
    FinalTargetBasePromotionAssemblyInput where
  ordinaryThree :=
    finalOrdinaryThreeBaseObligation_of_d3Promotion
      input.d3EvenPromotion
  lowMarkedPromotions := input.lowMarkedPromotions

theorem finalRemainingBase_of_basePromotions
    (input : FinalBasePromotionAssemblyInput) :
    FinalRemainingTargetBaseObligations :=
  finalRemainingBase_of_basePromotionAssemblyInput
    (finalTargetBasePromotionAssemblyInput_of_basePromotions input)

theorem finalTargetTorus_from_basePromotionsGrowthArrows
    (base : FinalBasePromotionAssemblyInput)
    (growth : FinalRemainingTargetGrowthArrows)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorus_from_basePromotionGrowthArrows
    (finalTargetBasePromotionAssemblyInput_of_basePromotions base)
    growth hRange

theorem finalTargetMarkedTorus_from_basePromotionsGrowthArrows
    (base : FinalBasePromotionAssemblyInput)
    (growth : FinalRemainingTargetGrowthArrows)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorus_from_basePromotionGrowthArrows
    (finalTargetBasePromotionAssemblyInput_of_basePromotions base)
    growth hRange

theorem finalTargetCayley_from_basePromotionsGrowthArrows
    (base : FinalBasePromotionAssemblyInput)
    (growth : FinalRemainingTargetGrowthArrows)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayley_from_basePromotionGrowthArrows
    (finalTargetBasePromotionAssemblyInput_of_basePromotions base)
    growth hRange

theorem finalTargetTorus_from_basePromotionsGrowthAssembly
    (base : FinalBasePromotionAssemblyInput)
    (growth : FinalTargetGrowthAssemblyInput)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorus_from_basePromotionGrowthAssembly
    (finalTargetBasePromotionAssemblyInput_of_basePromotions base)
    growth hRange

theorem finalTargetMarkedTorus_from_basePromotionsGrowthAssembly
    (base : FinalBasePromotionAssemblyInput)
    (growth : FinalTargetGrowthAssemblyInput)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorus_from_basePromotionGrowthAssembly
    (finalTargetBasePromotionAssemblyInput_of_basePromotions base)
    growth hRange

theorem finalTargetCayley_from_basePromotionsGrowthAssembly
    (base : FinalBasePromotionAssemblyInput)
    (growth : FinalTargetGrowthAssemblyInput)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayley_from_basePromotionGrowthAssembly
    (finalTargetBasePromotionAssemblyInput_of_basePromotions base)
    growth hRange

end FinalTargetD3BaseBridge

export FinalTargetD3BaseBridge
  (FinalD3EvenBaseClosedInputs FinalD3EvenBasePromotion
   FinalBasePromotionAssemblyInput finalD3EvenBaseClosedInputs_holds
   finalD3EvenBaseOrdinaryRange finalD3EvenBaseReturnCriterionInput
   finalD3EvenBaseLayeredHamiltonianInput
   finalD3EvenBasePromotion_of_ordinaryTargetFamily
   finalD3EvenBasePromotion_of_cayleyFamily
   finalOrdinaryThreeBaseObligation_of_d3Promotion
   finalTargetBasePromotionAssemblyInput_of_basePromotions
   finalRemainingBase_of_basePromotions
   finalTargetTorus_from_basePromotionsGrowthArrows
   finalTargetMarkedTorus_from_basePromotionsGrowthArrows
   finalTargetCayley_from_basePromotionsGrowthArrows
   finalTargetTorus_from_basePromotionsGrowthAssembly
   finalTargetMarkedTorus_from_basePromotionsGrowthAssembly
   finalTargetCayley_from_basePromotionsGrowthAssembly)

end EvenV11
