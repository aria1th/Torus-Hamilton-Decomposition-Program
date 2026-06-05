import Shared.D2Seed
import EvenV11.FinalTargetPredicateBridge

namespace EvenV11
namespace FinalTargetD2BaseBridge

theorem finalTargetOrdinaryTwoBase
    {m : Nat} (hm : EvenModulusRange m) :
    FinalOrdinaryTarget 2 m := by
  haveI : NeZero m := ⟨by omega⟩
  exact (Shared.torusHamiltonDecomposition_iff_cayley).mpr
    Shared.D2.cayleyHamiltonDecomposition

structure FinalTargetD2BaseInput : Prop where
  ordinaryTwo :
    ∀ {m : Nat}, EvenModulusRange m → FinalOrdinaryTarget 2 m

theorem finalTargetD2BaseInput_holds :
    FinalTargetD2BaseInput where
  ordinaryTwo := finalTargetOrdinaryTwoBase

end FinalTargetD2BaseBridge

export FinalTargetD2BaseBridge
  (finalTargetOrdinaryTwoBase FinalTargetD2BaseInput
   finalTargetD2BaseInput_holds)

end EvenV11
