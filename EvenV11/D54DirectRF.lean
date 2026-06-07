import EvenV11.D54ReturnCore
import EvenV11.LowD5M4Finite

/-!
# D5(4) direct root-flat H2 closure

This module keeps the generated/direct RF closure separate from the
paper-realization interfaces in `D54ReturnCore`.

The finite certificate in `LowD5M4Finite` proves RF1/RF2/RF3 on a 256-state
model and supplies a root-step conjugacy to the standard D5(4) chart.  Packaging
it as `D54ConjugateDirectRFInput` lets the main theorem use the same generic
direct-RF bridge as any future generated certificate, without claiming that this
finite schedule realizes the paper's `LowD5M4.fullReturn` ribbon handoff.
-/

namespace EvenV11
namespace H2
namespace D54

/-- Active finite D5(4) direct-RF witness, packaged through the generic
conjugate-schedule bridge used for direct/generated certificates. -/
def lowD5M4FiniteConjugateDirectRFInput :
    D54ConjugateDirectRFInput where
  State := LowD5M4Finite.RootState
  schedule := LowD5M4Finite.schedule
  e := LowD5M4Finite.rootIndexEquiv
  rowLatin := LowD5M4Finite.schedule_rowLatin
  layerBijective := LowD5M4Finite.schedule_layerBijective
  returnsSingleCycle := LowD5M4Finite.schedule_returnsSingleCycle
  stepConj := LowD5M4Finite.step_rootStep

/-- H2 direct RF certificate from the active finite schedule. -/
theorem finalLowD5M4RootFlatCertificateFamily_of_lowD5M4Finite :
    FinalLowD5M4RootFlatCertificateFamily :=
  lowD5M4FiniteConjugateDirectRFInput.lowBaseFamily

end D54
end H2
end EvenV11
