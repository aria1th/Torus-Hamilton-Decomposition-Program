-- STATUS: attic (Route E "all even from large + m=4" adapters; superseded 2026-09-10)
import TorusEvenAttic.D5RouteE
import D5Odd.EvenRouteEM4

namespace D5Odd

theorem D5EvenRouteEM4FiniteTarget_unconditional :
    D5EvenRouteEM4FiniteTarget :=
  ⟨D5_even_m4_hamiltonDecomposition⟩

theorem D5EvenRouteEAllEvenHamiltonTarget.of_large_unconditional_m4
    (hlarge : D5EvenRouteEAllLargeEvenTarget) :
    D5EvenRouteEAllEvenHamiltonTarget :=
  D5EvenRouteEAllEvenHamiltonTarget.of_large_and_m4
    D5EvenRouteEM4FiniteTarget_unconditional hlarge

theorem D5EvenRouteEAllEvenHamiltonTarget.of_nonopen_unconditional_m4
    (hlarge : D5EvenRouteENonopenAllLargeEvenTarget) :
    D5EvenRouteEAllEvenHamiltonTarget :=
  D5EvenRouteEAllEvenHamiltonTarget.of_nonopen_and_m4
    D5EvenRouteEM4FiniteTarget_unconditional hlarge

theorem D5EvenRouteEAllEvenHamiltonTarget.of_theta_unconditional_m4
    (hlarge : D5EvenRouteEThetaAllLargeEvenTarget) :
    D5EvenRouteEAllEvenHamiltonTarget :=
  D5EvenRouteEAllEvenHamiltonTarget.of_theta_and_m4
    D5EvenRouteEM4FiniteTarget_unconditional hlarge

theorem D5EvenRouteEAllEvenHamiltonTarget.of_ranked_unconditional_m4
    (hlarge : D5EvenRouteEThetaRankedAllLargeEvenTarget) :
    D5EvenRouteEAllEvenHamiltonTarget :=
  D5EvenRouteEAllEvenHamiltonTarget.of_ranked_and_m4
    D5EvenRouteEM4FiniteTarget_unconditional hlarge

theorem D5EvenRouteEAllEvenHamiltonTarget.of_piecewise_unconditional_m4
    (hlarge : D5EvenRouteEThetaPiecewiseAllLargeEvenTarget) :
    D5EvenRouteEAllEvenHamiltonTarget :=
  D5EvenRouteEAllEvenHamiltonTarget.of_piecewise_and_m4
    D5EvenRouteEM4FiniteTarget_unconditional hlarge

theorem D5EvenRouteEAllEvenHamiltonTarget.of_ranked_piecewise_unconditional_m4
    (hlarge : D5EvenRouteEThetaRankedPiecewiseAllLargeEvenTarget) :
    D5EvenRouteEAllEvenHamiltonTarget :=
  D5EvenRouteEAllEvenHamiltonTarget.of_ranked_piecewise_and_m4
    D5EvenRouteEM4FiniteTarget_unconditional hlarge

theorem D5EvenRouteEAllEvenTorusTarget.of_large_unconditional_m4
    (hlarge : D5EvenRouteEAllLargeEvenTarget) :
    D5EvenRouteEAllEvenTorusTarget :=
  D5EvenRouteEAllEvenTorusTarget.of_large_and_m4
    D5EvenRouteEM4FiniteTarget_unconditional hlarge

theorem D5EvenRouteEAllEvenTorusTarget.of_nonopen_unconditional_m4
    (hlarge : D5EvenRouteENonopenAllLargeEvenTarget) :
    D5EvenRouteEAllEvenTorusTarget :=
  D5EvenRouteEAllEvenTorusTarget.of_nonopen_and_m4
    D5EvenRouteEM4FiniteTarget_unconditional hlarge

theorem D5EvenRouteEAllEvenTorusTarget.of_theta_unconditional_m4
    (hlarge : D5EvenRouteEThetaAllLargeEvenTarget) :
    D5EvenRouteEAllEvenTorusTarget :=
  D5EvenRouteEAllEvenTorusTarget.of_theta_and_m4
    D5EvenRouteEM4FiniteTarget_unconditional hlarge

theorem D5EvenRouteEAllEvenTorusTarget.of_ranked_unconditional_m4
    (hlarge : D5EvenRouteEThetaRankedAllLargeEvenTarget) :
    D5EvenRouteEAllEvenTorusTarget :=
  D5EvenRouteEAllEvenTorusTarget.of_ranked_and_m4
    D5EvenRouteEM4FiniteTarget_unconditional hlarge

theorem D5EvenRouteEAllEvenTorusTarget.of_piecewise_unconditional_m4
    (hlarge : D5EvenRouteEThetaPiecewiseAllLargeEvenTarget) :
    D5EvenRouteEAllEvenTorusTarget :=
  D5EvenRouteEAllEvenTorusTarget.of_piecewise_and_m4
    D5EvenRouteEM4FiniteTarget_unconditional hlarge

theorem D5EvenRouteEAllEvenTorusTarget.of_ranked_piecewise_unconditional_m4
    (hlarge : D5EvenRouteEThetaRankedPiecewiseAllLargeEvenTarget) :
    D5EvenRouteEAllEvenTorusTarget :=
  D5EvenRouteEAllEvenTorusTarget.of_ranked_piecewise_and_m4
    D5EvenRouteEM4FiniteTarget_unconditional hlarge

theorem D5EvenRouteEAllEvenCayleyTarget.of_large_unconditional_m4
    (hlarge : D5EvenRouteEAllLargeEvenTarget) :
    D5EvenRouteEAllEvenCayleyTarget :=
  D5EvenRouteEAllEvenCayleyTarget.of_large_and_m4
    D5EvenRouteEM4FiniteTarget_unconditional hlarge

theorem D5EvenRouteEAllEvenCayleyTarget.of_nonopen_unconditional_m4
    (hlarge : D5EvenRouteENonopenAllLargeEvenTarget) :
    D5EvenRouteEAllEvenCayleyTarget :=
  D5EvenRouteEAllEvenCayleyTarget.of_nonopen_and_m4
    D5EvenRouteEM4FiniteTarget_unconditional hlarge

theorem D5EvenRouteEAllEvenCayleyTarget.of_theta_unconditional_m4
    (hlarge : D5EvenRouteEThetaAllLargeEvenTarget) :
    D5EvenRouteEAllEvenCayleyTarget :=
  D5EvenRouteEAllEvenCayleyTarget.of_theta_and_m4
    D5EvenRouteEM4FiniteTarget_unconditional hlarge

theorem D5EvenRouteEAllEvenCayleyTarget.of_ranked_unconditional_m4
    (hlarge : D5EvenRouteEThetaRankedAllLargeEvenTarget) :
    D5EvenRouteEAllEvenCayleyTarget :=
  D5EvenRouteEAllEvenCayleyTarget.of_ranked_and_m4
    D5EvenRouteEM4FiniteTarget_unconditional hlarge

theorem D5EvenRouteEAllEvenCayleyTarget.of_piecewise_unconditional_m4
    (hlarge : D5EvenRouteEThetaPiecewiseAllLargeEvenTarget) :
    D5EvenRouteEAllEvenCayleyTarget :=
  D5EvenRouteEAllEvenCayleyTarget.of_piecewise_and_m4
    D5EvenRouteEM4FiniteTarget_unconditional hlarge

theorem D5EvenRouteEAllEvenCayleyTarget.of_ranked_piecewise_unconditional_m4
    (hlarge : D5EvenRouteEThetaRankedPiecewiseAllLargeEvenTarget) :
    D5EvenRouteEAllEvenCayleyTarget :=
  D5EvenRouteEAllEvenCayleyTarget.of_ranked_piecewise_and_m4
    D5EvenRouteEM4FiniteTarget_unconditional hlarge

end D5Odd
