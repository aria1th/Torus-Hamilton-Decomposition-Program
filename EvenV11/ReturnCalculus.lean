import EvenV11.Basic

namespace EvenV11
namespace ReturnCalculus

theorem edgePartitionOfRowLatin
    {Color Direction RootState : Type*} {m : Nat}
    {S : Shared.RootFlatSchedule Color Direction RootState m}
    (hRow : S.rowLatin) :
    S.edgePartition :=
  Shared.RootFlatSchedule.edgePartition_of_rowLatin hRow

theorem fullStepsHamiltonianOfReturn
    {Color Direction RootState : Type*} {m : Nat} [NeZero m]
    {S : Shared.RootFlatSchedule Color Direction RootState m}
    (hLayer : S.layerBijective)
    (hReturn : S.returnsSingleCycle) :
    S.fullStepsHamiltonian :=
  Shared.RootFlatSchedule.fullStepsHamiltonian_of_return hLayer hReturn

theorem rootFlatReturnCriterion
    {Color Direction RootState : Type*} {m : Nat} [NeZero m]
    {S : Shared.RootFlatSchedule Color Direction RootState m}
    (hRow : S.rowLatin) (hLayer : S.layerBijective)
    (hReturn : S.returnsSingleCycle) :
    Shared.RootFlatReturnCriterion Color Direction RootState m :=
  Shared.rootFlatReturnCriterion_of_schedule hRow hLayer hReturn

theorem rootFlatLayeredHamiltonian
    {Color Direction RootState : Type*} {m : Nat} [NeZero m]
    {S : Shared.RootFlatSchedule Color Direction RootState m}
    (hRow : S.rowLatin) (hLayer : S.layerBijective)
    (hReturn : S.returnsSingleCycle) :
    Shared.RootFlatLayeredHamiltonDecomposition Color Direction RootState m :=
  Shared.rootFlatLayeredDecomposition_of_schedule hRow hLayer hReturn

end ReturnCalculus

export ReturnCalculus
  (edgePartitionOfRowLatin fullStepsHamiltonianOfReturn
   rootFlatReturnCriterion rootFlatLayeredHamiltonian)

end EvenV11
