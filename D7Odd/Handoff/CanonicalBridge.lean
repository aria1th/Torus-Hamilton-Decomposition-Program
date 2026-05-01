import D7Odd.Handoff.CanonicalWords
import D7Odd.Handoff.SmallBranches

namespace D7Odd
namespace Handoff

structure CanonicalScheduleRealization (m : Nat) [NeZero m]
    (P : CountMatrixSchedule m) where
  schedule : RootFlatSchedule m
  rowLatin : schedule.rowLatin
  layerBijective : schedule.layerBijective
  returnsSingleCycle :
    (∀ c : Fin 7, CanonicalWordCertified m (canonicalWord P.schedule c)) →
      schedule.returnsSingleCycle

def CanonicalScheduleRealizationTheorem : Prop :=
  ∀ {m : Nat} [NeZero m] (P : CountMatrixSchedule m),
    Nonempty (CanonicalScheduleRealization m P)

def CanonicalScheduleHamiltonianTheorem : Prop :=
  ∀ {m : Nat} [NeZero m] (P : CountMatrixSchedule m),
    (∀ c : Fin 7, CanonicalWordCertified m (canonicalWord P.schedule c)) →
      HamiltonDecompositionD7 m

theorem hamilton_of_canonical_realization {m : Nat} [NeZero m]
    {P : CountMatrixSchedule m}
    (R : CanonicalScheduleRealization m P)
    (hwords : ∀ c : Fin 7, CanonicalWordCertified m (canonicalWord P.schedule c)) :
    HamiltonDecompositionD7 m := by
  exact certificate_implies_hamilton
    { schedule := R.schedule
      rowLatin := R.rowLatin
      layerBijective := R.layerBijective
      returnsSingleCycle := R.returnsSingleCycle hwords }

theorem canonical_hamiltonian_of_realization_theorem
    (hrealize : CanonicalScheduleRealizationTheorem) :
    CanonicalScheduleHamiltonianTheorem := by
  intro m _ P hwords
  rcases hrealize P with ⟨R⟩
  exact hamilton_of_canonical_realization R hwords

theorem generic_odd_from_canonical_schedule
    (hcanonical : CanonicalScheduleHamiltonianTheorem) :
    GenericOddBranchResult := by
  refine ⟨?_⟩
  intro m _ hm7 hodd
  rcases generic_count_matrix_schedule hm7 hodd with ⟨P⟩
  exact hcanonical P (fun c => countMatrixSchedule_word_certified P c)

theorem main_odd_from_canonical_schedule
    (hcanonical : CanonicalScheduleHamiltonianTheorem) :
    MainOddTheoremTarget := by
  intro m _ hm3 hodd
  exact odd_from_branches smallBranchResults
    (generic_odd_from_canonical_schedule hcanonical) hm3 hodd

theorem generic_odd_from_canonical_realization
    (hrealize : CanonicalScheduleRealizationTheorem) :
    GenericOddBranchResult :=
  generic_odd_from_canonical_schedule
    (canonical_hamiltonian_of_realization_theorem hrealize)

theorem main_odd_from_canonical_realization
    (hrealize : CanonicalScheduleRealizationTheorem) :
    MainOddTheoremTarget :=
  main_odd_from_canonical_schedule
    (canonical_hamiltonian_of_realization_theorem hrealize)

end Handoff
end D7Odd
