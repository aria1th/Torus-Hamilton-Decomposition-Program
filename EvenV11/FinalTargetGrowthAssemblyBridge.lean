import EvenV11.FinalTargetBaseAssemblyBridge
import EvenV11.FinalInductionBridge

namespace EvenV11
namespace FinalTargetGrowthAssemblyBridge

structure FinalTargetClosedGrowthLocalInputs : Prop where
  inductionInterface : FinalInductionInterfaceInput

theorem finalTargetClosedGrowthLocalInputs_holds :
    FinalTargetClosedGrowthLocalInputs where
  inductionInterface := finalInductionInterfaceInput_holds

structure FinalRemainingTargetGrowthArrows : Prop where
  evenPhaseDoubling :
    ∀ {a m : Nat}, 2 ≤ a → EvenModulusRange m →
      FinalOrdinaryTarget a m → FinalMarkedTarget (2 * a) m
  oddHighModulus :
    ∀ {d m : Nat}, 5 ≤ d → (∃ b : Nat, d = 2 * b + 1) →
      EvenModulusRange m → d < m → FinalMarkedTarget d m
  oddEndpoint :
    ∀ {b m : Nat}, 4 ≤ b → MarkedDimensionRange b m →
      FinalMarkedTarget b m → FinalMarkedTarget (2 * b + 1) m

theorem finalTargetGrowthObligations_of_remainingGrowthArrows
    (remaining : FinalRemainingTargetGrowthArrows) :
    FinalTargetGrowthObligations where
  evenPhaseDoubling := remaining.evenPhaseDoubling
  oddHighModulus := remaining.oddHighModulus
  oddEndpoint := remaining.oddEndpoint

structure FinalTargetGrowthAssemblyInput : Prop where
  closedLocalInputs : FinalTargetClosedGrowthLocalInputs
  remainingArrows : FinalRemainingTargetGrowthArrows

theorem finalTargetGrowthAssemblyInput_of_remainingGrowthArrows
    (remaining : FinalRemainingTargetGrowthArrows) :
    FinalTargetGrowthAssemblyInput where
  closedLocalInputs := finalTargetClosedGrowthLocalInputs_holds
  remainingArrows := remaining

theorem finalTargetGrowthObligations_of_growthAssemblyInput
    (input : FinalTargetGrowthAssemblyInput) :
    FinalTargetGrowthObligations :=
  finalTargetGrowthObligations_of_remainingGrowthArrows
    input.remainingArrows

theorem finalTargetTorusConclusionFromRemainingBaseAndGrowthArrows
    (base : FinalRemainingTargetBaseObligations)
    (growth : FinalRemainingTargetGrowthArrows)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorusConclusionFromRemainingBaseAndGrowth
    base
    (finalTargetGrowthObligations_of_remainingGrowthArrows growth)
    hRange

theorem finalTargetMarkedTorusConclusionFromRemainingBaseAndGrowthArrows
    (base : FinalRemainingTargetBaseObligations)
    (growth : FinalRemainingTargetGrowthArrows)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorusConclusionFromRemainingBaseAndGrowth
    base
    (finalTargetGrowthObligations_of_remainingGrowthArrows growth)
    hRange

theorem finalTargetCayleyConclusionFromRemainingBaseAndGrowthArrows
    (base : FinalRemainingTargetBaseObligations)
    (growth : FinalRemainingTargetGrowthArrows)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayleyConclusionFromRemainingBaseAndGrowth
    base
    (finalTargetGrowthObligations_of_remainingGrowthArrows growth)
    hRange

theorem finalTargetTorusConclusionFromRemainingBaseAndGrowthAssembly
    (base : FinalRemainingTargetBaseObligations)
    (growth : FinalTargetGrowthAssemblyInput)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorusConclusionFromRemainingBaseAndGrowth
    base
    (finalTargetGrowthObligations_of_growthAssemblyInput growth)
    hRange

theorem finalTargetMarkedTorusConclusionFromRemainingBaseAndGrowthAssembly
    (base : FinalRemainingTargetBaseObligations)
    (growth : FinalTargetGrowthAssemblyInput)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorusConclusionFromRemainingBaseAndGrowth
    base
    (finalTargetGrowthObligations_of_growthAssemblyInput growth)
    hRange

theorem finalTargetCayleyConclusionFromRemainingBaseAndGrowthAssembly
    (base : FinalRemainingTargetBaseObligations)
    (growth : FinalTargetGrowthAssemblyInput)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayleyConclusionFromRemainingBaseAndGrowth
    base
    (finalTargetGrowthObligations_of_growthAssemblyInput growth)
    hRange

end FinalTargetGrowthAssemblyBridge

export FinalTargetGrowthAssemblyBridge
  (FinalTargetClosedGrowthLocalInputs FinalRemainingTargetGrowthArrows
   FinalTargetGrowthAssemblyInput finalTargetClosedGrowthLocalInputs_holds
   finalTargetGrowthObligations_of_remainingGrowthArrows
   finalTargetGrowthAssemblyInput_of_remainingGrowthArrows
   finalTargetGrowthObligations_of_growthAssemblyInput
   finalTargetTorusConclusionFromRemainingBaseAndGrowthArrows
   finalTargetMarkedTorusConclusionFromRemainingBaseAndGrowthArrows
   finalTargetCayleyConclusionFromRemainingBaseAndGrowthArrows
   finalTargetTorusConclusionFromRemainingBaseAndGrowthAssembly
   finalTargetMarkedTorusConclusionFromRemainingBaseAndGrowthAssembly
   finalTargetCayleyConclusionFromRemainingBaseAndGrowthAssembly)

end EvenV11
