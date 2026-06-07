import EvenV11.V28PaperInterface
import EvenV11.V28Hard.D3TerminalA2Parametric
import EvenV11.V28Hard.D5M4RibbonRows
import EvenV11.V28Hard.D7Checkpoint
import EvenV11.V28Hard.D7TwoRailRelay
import EvenV11.V28Hard.HighEvenEndpointPromotions

/-!
# Assemble v28 hard-part code into the paper checklist

This file is the handoff layer: it shows exactly how the hard-part modules feed
`V28PaperInterface.PaperFaithfulChecklist` and therefore the full even-modulus
theorem.

There are two useful constructors:

* `paperChecklist_checkpoint_finiteBackedD7` uses `D7Checkpoint`, i.e. the old
generated D7 audits behind an explicit checkpoint wrapper transported into the structural `RootFlatCycleData` target.
This is the best practical stepping stone while the handwritten two-rail proof is
being repaired.
* `paperChecklist_structuralD7` takes handwritten D7 RF1/RF2/RF3 data.  This is
the final paper-faithful shape.
-/

namespace EvenV11
namespace V28Hard
namespace ChecklistFromHardParts

open V28PaperInterface

/-- Practical checklist: H3/H4 use finite-generated checks transported into the
structural root-flat interface; H2 is supplied by a paper-table reset input; H5
and H6 use the candidate engine sites from `HighEvenEndpointPromotions`. -/
def paperChecklist_checkpoint_finiteBackedD7
    (h2 : D5M4RibbonRows.H2PaperTableInput) :
    PaperFaithfulChecklist where
  d3TerminalA2 :=
    { family := D3TerminalA2Parametric.rootFlatCertificateFamily }
  d5m4Reset :=
    { data := D5M4RibbonRows.nonemptyRibbonData_of_paperTableInput h2 }
  d7m4TwoRail :=
    { data := D7Checkpoint.generatedD7M4CheckpointInput.data }
  d7m6TwoRail :=
    { data := D7Checkpoint.generatedD7M6CheckpointInput.data }
  oddHighModulus :=
    { promotion :=
        HighEvenEndpointPromotions.oddHighModulusPromotion_of_engine
          HighEvenEndpointPromotions.candidate_oddHighModulusEngine }
  oddEndpoint :=
    { promotion :=
        HighEvenEndpointPromotions.endpointTargetPromotion_of_engine
          HighEvenEndpointPromotions.candidate_oddEndpointPayloadEngine }

/-- Same practical checklist, starting from the stronger D5 reset-table
certificate package. -/
def paperChecklist_checkpoint_finiteBackedD7_from_D5Certificate
    (h2 : D5M4RibbonRows.H2PaperCertificateInput) :
    PaperFaithfulChecklist :=
  paperChecklist_checkpoint_finiteBackedD7
    (D5M4RibbonRows.paperTableInput_of_certificateInput h2)

/-- Full theorem from the practical hard-part candidates plus finite-backed D7
structural cycle data.  This theorem is expected to compile only after repairing
the local `sorry`s in the candidate modules, but its statement is the intended
handoff into the existing theorem spine. -/
theorem evenModulusToriAllDimensions_checkpoint_finiteBackedD7
    (h2 : D5M4RibbonRows.H2PaperTableInput) :
    V28EvenModulusToriAllDimensionsGoal :=
  evenModulusToriAllDimensions_of_paperChecklist
    (paperChecklist_checkpoint_finiteBackedD7 h2)

/-- Full theorem from stronger D5 certificate data. -/
theorem evenModulusToriAllDimensions_checkpoint_finiteBackedD7_from_D5Certificate
    (h2 : D5M4RibbonRows.H2PaperCertificateInput) :
    V28EvenModulusToriAllDimensionsGoal :=
  evenModulusToriAllDimensions_of_paperChecklist
    (paperChecklist_checkpoint_finiteBackedD7_from_D5Certificate h2)

/-- Backward-compatible alias for the earlier practical checkpoint name.
The theorem name is intentionally less preferred than the `checkpoint` spelling. -/
def paperChecklist_with_finiteBackedD7
    (h2 : D5M4RibbonRows.H2PaperTableInput) :
    PaperFaithfulChecklist :=
  paperChecklist_checkpoint_finiteBackedD7 h2

/-- Backward-compatible alias for the earlier practical checkpoint theorem name. -/
theorem evenModulusToriAllDimensions_with_finiteBackedD7
    (h2 : D5M4RibbonRows.H2PaperTableInput) :
    V28EvenModulusToriAllDimensionsGoal :=
  evenModulusToriAllDimensions_checkpoint_finiteBackedD7 h2

/-- Backward-compatible alias for the earlier practical checkpoint constructor
starting from the stronger D5 certificate package. -/
def paperChecklist_with_finiteBackedD7_from_D5Certificate
    (h2 : D5M4RibbonRows.H2PaperCertificateInput) :
    PaperFaithfulChecklist :=
  paperChecklist_checkpoint_finiteBackedD7_from_D5Certificate h2

/-- Backward-compatible alias for the earlier practical checkpoint theorem
starting from the stronger D5 certificate package. -/
theorem evenModulusToriAllDimensions_with_finiteBackedD7_from_D5Certificate
    (h2 : D5M4RibbonRows.H2PaperCertificateInput) :
    V28EvenModulusToriAllDimensionsGoal :=
  evenModulusToriAllDimensions_checkpoint_finiteBackedD7_from_D5Certificate h2

/-- Fully paper-faithful checklist constructor: this version does not use the
finite D7 audits.  Supply handwritten two-rail RF1/RF2/RF3 cycle data for
`D₇(4)` and `D₇(6)`. -/
def paperChecklist_structuralD7
    (d3 : FinalD3EvenRootFlatCertificateFamily)
    (d5 : Nonempty LowD5M4Structural.ResetPortH2RowEquivRibbonRealizationData)
    (d7m4 : Nonempty (RootFlatCycle.RootFlatCycleData 6 4))
    (d7m6 : Nonempty (RootFlatCycle.RootFlatCycleData 6 6))
    (high : FinalOddHighModulusTargetPromotion)
    (endpoint : FinalOddEndpointPhaseProductTargetPromotion) :
    PaperFaithfulChecklist where
  d3TerminalA2 := { family := d3 }
  d5m4Reset := { data := d5 }
  d7m4TwoRail := { data := d7m4 }
  d7m6TwoRail := { data := d7m6 }
  oddHighModulus := { promotion := high }
  oddEndpoint := { promotion := endpoint }

/-- The final no-finite-D7 theorem shape. -/
theorem evenModulusToriAllDimensions_structuralD7
    (d3 : FinalD3EvenRootFlatCertificateFamily)
    (d5 : Nonempty LowD5M4Structural.ResetPortH2RowEquivRibbonRealizationData)
    (d7m4 : Nonempty (RootFlatCycle.RootFlatCycleData 6 4))
    (d7m6 : Nonempty (RootFlatCycle.RootFlatCycleData 6 6))
    (high : FinalOddHighModulusTargetPromotion)
    (endpoint : FinalOddEndpointPhaseProductTargetPromotion) :
    V28EvenModulusToriAllDimensionsGoal :=
  evenModulusToriAllDimensions_of_paperChecklist
    (paperChecklist_structuralD7 d3 d5 d7m4 d7m6 high endpoint)

end ChecklistFromHardParts
end V28Hard
end EvenV11
