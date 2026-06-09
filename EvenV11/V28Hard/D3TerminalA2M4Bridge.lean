import EvenV11.V28Hard.D3TerminalA2Parametric
import EvenV11.D54ReturnCore

/-!
# H2 terminal `m = 4` bridge into the A₂ realization interface

`D54ReturnCore` already isolates the paper-facing terminal `A₂` realization
needed by H2 at `m = 4`: a D3 root-flat schedule, an explicit return-section
equivalence, RF1/RF2, and return conjugacy to the collapsed terminal carriers.

This file repackages that pointwise H2 object into the A₂ interface used by the
v28 hard-slot wiring.
-/

namespace EvenV11
namespace V28Hard
namespace D3TerminalA2Parametric

/-- Convert the H2/D54 terminal physical realization at `m = 4` into the
single-modulus A₂ realization interface. -/
def terminalA2M4RealizationAt_of_physical
    (H : H2.D54.TerminalA2M4PhysicalRealization) :
    TerminalA2RootFlatRealizationAt 4 where
  dir := H.rows.dir
  sectionEquiv := H.eT
  rowLatin := by
    have hrows : H.rows = RootFlatCycle.schedule H.rows.dir := by
      exact Eq.trans H.rows_eq_terminalStandardSchedule rfl
    exact hrows ▸ H.rowLatin
  layerBijective := by
    have hrows : H.rows = RootFlatCycle.schedule H.rows.dir := by
      exact Eq.trans H.rows_eq_terminalStandardSchedule rfl
    exact hrows ▸ H.layerBijective
  return_eq_terminal := by
    intro c q
    have hrows : H.rows = RootFlatCycle.schedule H.rows.dir := by
      exact Eq.trans H.rows_eq_terminalStandardSchedule rfl
    exact hrows ▸ H.return_eq_terminalReturn c q

/-- An H2/D54 terminal realization at `m = 4` supplies the standard D3
root-flat cycle data for the terminal A₂ block. -/
def terminalA2M4CycleData_of_physical
    (H : H2.D54.TerminalA2M4PhysicalRealization) :
    RootFlatCycle.RootFlatCycleData 2 4 :=
  cycleData_of_finiteCyclicity_and_realizationAt
    terminalA2M4FiniteCyclicity
    (terminalA2M4RealizationAt_of_physical H)

end D3TerminalA2Parametric
end V28Hard
end EvenV11
