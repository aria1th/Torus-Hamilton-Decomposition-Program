import EvenV11.FinalTargetD2BaseBridge

namespace EvenV11
namespace FinalTargetBaseAssemblyBridge

structure FinalRemainingTargetBaseObligations : Prop where
  ordinaryThree :
    ∀ {m : Nat}, EvenModulusRange m → FinalOrdinaryTarget 3 m
  markedD5M4 : FinalMarkedTarget 5 4
  markedD7M4 : FinalMarkedTarget 7 4
  markedD7M6 : FinalMarkedTarget 7 6

theorem finalTargetBaseObligations_of_remainingBase
    (remaining : FinalRemainingTargetBaseObligations) :
    FinalTargetBaseObligations where
  ordinaryTwo := finalTargetD2BaseInput_holds.ordinaryTwo
  ordinaryThree := remaining.ordinaryThree
  markedD5M4 := remaining.markedD5M4
  markedD7M4 := remaining.markedD7M4
  markedD7M6 := remaining.markedD7M6

theorem finalTargetTorusConclusionFromRemainingBaseAndGrowth
    (remaining : FinalRemainingTargetBaseObligations)
    (growth : FinalTargetGrowthObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorusConclusionFromTargetObligations
    (finalTargetBaseObligations_of_remainingBase remaining)
    growth (d := d) (m := m) hRange

theorem finalTargetMarkedTorusConclusionFromRemainingBaseAndGrowth
    (remaining : FinalRemainingTargetBaseObligations)
    (growth : FinalTargetGrowthObligations)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorusConclusionFromTargetObligations
    (finalTargetBaseObligations_of_remainingBase remaining)
    growth (d := d) (m := m) hRange

theorem finalTargetCayleyConclusionFromRemainingBaseAndGrowth
    (remaining : FinalRemainingTargetBaseObligations)
    (growth : FinalTargetGrowthObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayleyConclusionFromTargetObligations
    (finalTargetBaseObligations_of_remainingBase remaining)
    growth (d := d) (m := m) hRange

end FinalTargetBaseAssemblyBridge

export FinalTargetBaseAssemblyBridge
  (FinalRemainingTargetBaseObligations
   finalTargetBaseObligations_of_remainingBase
   finalTargetTorusConclusionFromRemainingBaseAndGrowth
   finalTargetMarkedTorusConclusionFromRemainingBaseAndGrowth
   finalTargetCayleyConclusionFromRemainingBaseAndGrowth)

end EvenV11
