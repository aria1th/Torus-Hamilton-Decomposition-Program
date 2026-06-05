import Shared.CayleyProduct
import EvenV11.FinalTargetD3BaseBridge

namespace EvenV11
namespace FinalTargetPhaseDoublingBridge

theorem finalTargetEvenPhaseDoubling
    {a m : Nat} (ha : 2 ≤ a) (hm : EvenModulusRange m)
    (parent : FinalOrdinaryTarget a m) :
    FinalMarkedTarget (2 * a) m := by
  haveI : NeZero m := ⟨by omega⟩
  haveI : NeZero (m ^ a) := ⟨by
    exact ne_of_gt
      (pow_pos (Nat.pos_of_ne_zero (NeZero.ne m)) a)⟩
  have hPowLarge : 1 < m ^ a := by
    have hmLarge : 1 < m := by omega
    exact one_lt_pow₀ hmLarge (by omega : a ≠ 0)
  have hParentCayley :
      Shared.CayleyHamiltonDecomposition a m :=
    (Shared.torusHamiltonDecomposition_iff_cayley).mp parent
  have hParentCoord :
      Shared.CoordinatizedCayleyHamiltonDecomposition a m :=
    Shared.coordinatizedCayleyHamiltonDecomposition_of_single_cycle
      hPowLarge hParentCayley
  have hFiber :
      Shared.CayleyHamiltonDecomposition 2 (m ^ a) :=
    Shared.D2.cayleyHamiltonDecomposition
  have hProduct :
      Shared.CayleyHamiltonDecomposition (a * 2) m :=
    Shared.cayleyHamiltonDecomposition_product_of_left_coordinatized
      hParentCoord hFiber
  have hTarget :
      Shared.CayleyHamiltonDecomposition (2 * a) m := by
    simpa [Nat.mul_comm] using hProduct
  exact (Shared.torusHamiltonDecomposition_iff_cayley).mpr hTarget

structure FinalRemainingTargetPostPhaseGrowthArrows : Prop where
  oddHighModulus :
    ∀ {d m : Nat}, 5 ≤ d → (∃ b : Nat, d = 2 * b + 1) →
      EvenModulusRange m → d < m → FinalMarkedTarget d m
  oddEndpoint :
    ∀ {b m : Nat}, 4 ≤ b → MarkedDimensionRange b m →
      FinalMarkedTarget b m → FinalMarkedTarget (2 * b + 1) m

theorem finalRemainingTargetGrowthArrows_of_postPhase
    (remaining : FinalRemainingTargetPostPhaseGrowthArrows) :
    FinalRemainingTargetGrowthArrows where
  evenPhaseDoubling := fun ha hm parent =>
    finalTargetEvenPhaseDoubling ha hm parent
  oddHighModulus := remaining.oddHighModulus
  oddEndpoint := remaining.oddEndpoint

structure FinalTargetPostPhaseGrowthAssemblyInput : Prop where
  closedLocalInputs : FinalTargetClosedGrowthLocalInputs
  remainingArrows : FinalRemainingTargetPostPhaseGrowthArrows

theorem finalTargetPostPhaseGrowthAssemblyInput_of_remaining
    (remaining : FinalRemainingTargetPostPhaseGrowthArrows) :
    FinalTargetPostPhaseGrowthAssemblyInput where
  closedLocalInputs := finalTargetClosedGrowthLocalInputs_holds
  remainingArrows := remaining

theorem finalTargetGrowthAssemblyInput_of_postPhase
    (input : FinalTargetPostPhaseGrowthAssemblyInput) :
    FinalTargetGrowthAssemblyInput :=
  finalTargetGrowthAssemblyInput_of_remainingGrowthArrows
    (finalRemainingTargetGrowthArrows_of_postPhase
      input.remainingArrows)

theorem finalTargetTorus_from_basePromotionsPostPhaseGrowth
    (base : FinalBasePromotionAssemblyInput)
    (growth : FinalRemainingTargetPostPhaseGrowthArrows)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorus_from_basePromotionsGrowthArrows
    base
    (finalRemainingTargetGrowthArrows_of_postPhase growth)
    hRange

theorem finalTargetMarkedTorus_from_basePromotionsPostPhaseGrowth
    (base : FinalBasePromotionAssemblyInput)
    (growth : FinalRemainingTargetPostPhaseGrowthArrows)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorus_from_basePromotionsGrowthArrows
    base
    (finalRemainingTargetGrowthArrows_of_postPhase growth)
    hRange

theorem finalTargetCayley_from_basePromotionsPostPhaseGrowth
    (base : FinalBasePromotionAssemblyInput)
    (growth : FinalRemainingTargetPostPhaseGrowthArrows)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayley_from_basePromotionsGrowthArrows
    base
    (finalRemainingTargetGrowthArrows_of_postPhase growth)
    hRange

theorem finalTargetTorus_from_basePromotionsPostPhaseAssembly
    (base : FinalBasePromotionAssemblyInput)
    (growth : FinalTargetPostPhaseGrowthAssemblyInput)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorus_from_basePromotionsGrowthAssembly
    base
    (finalTargetGrowthAssemblyInput_of_postPhase growth)
    hRange

theorem finalTargetMarkedTorus_from_basePromotionsPostPhaseAssembly
    (base : FinalBasePromotionAssemblyInput)
    (growth : FinalTargetPostPhaseGrowthAssemblyInput)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorus_from_basePromotionsGrowthAssembly
    base
    (finalTargetGrowthAssemblyInput_of_postPhase growth)
    hRange

theorem finalTargetCayley_from_basePromotionsPostPhaseAssembly
    (base : FinalBasePromotionAssemblyInput)
    (growth : FinalTargetPostPhaseGrowthAssemblyInput)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayley_from_basePromotionsGrowthAssembly
    base
    (finalTargetGrowthAssemblyInput_of_postPhase growth)
    hRange

end FinalTargetPhaseDoublingBridge

export FinalTargetPhaseDoublingBridge
  (finalTargetEvenPhaseDoubling
   FinalRemainingTargetPostPhaseGrowthArrows
   FinalTargetPostPhaseGrowthAssemblyInput
   finalRemainingTargetGrowthArrows_of_postPhase
   finalTargetPostPhaseGrowthAssemblyInput_of_remaining
   finalTargetGrowthAssemblyInput_of_postPhase
   finalTargetTorus_from_basePromotionsPostPhaseGrowth
   finalTargetMarkedTorus_from_basePromotionsPostPhaseGrowth
   finalTargetCayley_from_basePromotionsPostPhaseGrowth
   finalTargetTorus_from_basePromotionsPostPhaseAssembly
   finalTargetMarkedTorus_from_basePromotionsPostPhaseAssembly
   finalTargetCayley_from_basePromotionsPostPhaseAssembly)

end EvenV11
