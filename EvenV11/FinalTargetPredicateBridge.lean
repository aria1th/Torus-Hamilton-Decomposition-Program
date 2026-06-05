import EvenV11.FinalArrowObligationBridge

namespace EvenV11
namespace FinalTargetPredicateBridge

abbrev FinalOrdinaryTarget (d m : Nat) : Prop :=
  Shared.TorusHamiltonDecomposition d m

abbrev FinalMarkedTarget (d m : Nat) : Prop :=
  Shared.TorusHamiltonDecomposition d m

/-!
`FinalMarkedTarget` is kept as the ordinary target used by the current induction
spine.  The paper's marked assertion carries extra data: a comparison selector
and an endpoint reserve.  The next two structures expose that payload separately,
so paper-faithful constructions can be built and then forgotten back to the
ordinary target without disrupting the existing theorem spine.
-/

structure FinalMarkedEvidence (d m : Nat) where
  ComparisonSelector : Type
  comparisonSelectorWitness : Nonempty ComparisonSelector
  EndpointReserve : Type
  endpointReserveWitness : Nonempty EndpointReserve

structure FinalMarkedPayload (d m : Nat) : Prop where
  target : FinalMarkedTarget d m
  evidence : Nonempty (FinalMarkedEvidence d m)

structure FinalTargetBaseObligations : Prop where
  ordinaryTwo :
    ∀ {m : Nat}, EvenModulusRange m → FinalOrdinaryTarget 2 m
  ordinaryThree :
    ∀ {m : Nat}, EvenModulusRange m → FinalOrdinaryTarget 3 m
  markedD5M4 : FinalMarkedTarget 5 4
  markedD7M4 : FinalMarkedTarget 7 4
  markedD7M6 : FinalMarkedTarget 7 6

structure FinalTargetGrowthObligations : Prop where
  evenPhaseDoubling :
    ∀ {a m : Nat}, 2 ≤ a → EvenModulusRange m →
      FinalOrdinaryTarget a m → FinalMarkedTarget (2 * a) m
  oddHighModulus :
    ∀ {d m : Nat}, 5 ≤ d → (∃ b : Nat, d = 2 * b + 1) →
      EvenModulusRange m → d < m → FinalMarkedTarget d m
  oddEndpoint :
    ∀ {b m : Nat}, 4 ≤ b → MarkedDimensionRange b m →
      FinalMarkedTarget b m → FinalMarkedTarget (2 * b + 1) m

theorem finalTargetMarkedToOrdinary
    {d m : Nat} :
    FinalMarkedTarget d m → FinalOrdinaryTarget d m :=
  fun h => h

theorem finalMarkedPayload_forget
    {d m : Nat} :
    FinalMarkedPayload d m → FinalMarkedTarget d m :=
  fun payload => payload.target

theorem finalMarkedPayload_forgetOrdinary
    {d m : Nat} :
    FinalMarkedPayload d m → FinalOrdinaryTarget d m :=
  fun payload => finalTargetMarkedToOrdinary payload.target

/-- Compatibility constructor for legacy ordinary-only components. New
paper-faithful code should prefer a construction-specific `FinalMarkedEvidence`
instead of this weak witness. -/
theorem finalMarkedPayload_weakOfTarget
    {d m : Nat} (target : FinalMarkedTarget d m) :
    FinalMarkedPayload d m where
  target := target
  evidence :=
    ⟨{ ComparisonSelector := PUnit
       comparisonSelectorWitness := ⟨PUnit.unit⟩
       EndpointReserve := PUnit
       endpointReserveWitness := ⟨PUnit.unit⟩ }⟩

theorem finalTargetBaseArrowObligations_of_targetBase
    (base : FinalTargetBaseObligations) :
    FinalBaseArrowObligations FinalOrdinaryTarget FinalMarkedTarget where
  ordinaryTwo := base.ordinaryTwo
  ordinaryThree := base.ordinaryThree
  markedD5M4 := base.markedD5M4
  markedD7M4 := base.markedD7M4
  markedD7M6 := base.markedD7M6

theorem finalTargetSuccessorArrowObligations_of_targetGrowth
    (growth : FinalTargetGrowthObligations) :
    FinalSuccessorArrowObligations FinalOrdinaryTarget FinalMarkedTarget where
  markedToOrdinary := finalTargetMarkedToOrdinary
  evenPhaseDoubling := growth.evenPhaseDoubling
  oddHighModulus := growth.oddHighModulus
  oddEndpoint := growth.oddEndpoint

theorem finalTargetArrowObligationInput_of_targetObligations
    (base : FinalTargetBaseObligations)
    (growth : FinalTargetGrowthObligations) :
    FinalArrowObligationInput FinalOrdinaryTarget FinalMarkedTarget where
  base := finalTargetBaseArrowObligations_of_targetBase base
  successor := finalTargetSuccessorArrowObligations_of_targetGrowth growth

theorem finalTargetTorusConclusionFromTargetObligations
    (base : FinalTargetBaseObligations)
    (growth : FinalTargetGrowthObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  ordinaryConclusionFromArrowObligations
    (finalTargetArrowObligationInput_of_targetObligations base growth)
    (d := d) (m := m) hRange

theorem finalTargetMarkedTorusConclusionFromTargetObligations
    (base : FinalTargetBaseObligations)
    (growth : FinalTargetGrowthObligations)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  markedConclusionFromArrowObligations
    (finalTargetArrowObligationInput_of_targetObligations base growth)
    (d := d) (m := m) hRange

theorem finalTargetCayleyConclusionFromTargetObligations
    (base : FinalTargetBaseObligations)
    (growth : FinalTargetGrowthObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  (Shared.torusHamiltonDecomposition_iff_cayley).mp
    (finalTargetTorusConclusionFromTargetObligations
      base growth (d := d) (m := m) hRange)

end FinalTargetPredicateBridge

export FinalTargetPredicateBridge
  (FinalOrdinaryTarget FinalMarkedTarget FinalMarkedEvidence
   FinalMarkedPayload FinalTargetBaseObligations
   FinalTargetGrowthObligations finalTargetMarkedToOrdinary
   finalMarkedPayload_forget finalMarkedPayload_forgetOrdinary
   finalMarkedPayload_weakOfTarget
   finalTargetBaseArrowObligations_of_targetBase
   finalTargetSuccessorArrowObligations_of_targetGrowth
   finalTargetArrowObligationInput_of_targetObligations
   finalTargetTorusConclusionFromTargetObligations
   finalTargetMarkedTorusConclusionFromTargetObligations
   finalTargetCayleyConclusionFromTargetObligations)

end EvenV11
