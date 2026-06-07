import EvenV11.V28PaperInterface
import EvenV11.V28Hard.D5M4H2Skeleton
import EvenV11.V28Hard.D7Checkpoint
import EvenV11.V28Hard.D3TerminalA2Parametric
import EvenV11.V28Hard.D7TwoRailRelay
import EvenV11.V28Hard.HighEvenEndpointPromotions

/-!
# Checklist variant with H2 as direct root-flat cycle data

`V28PaperInterface.PaperFaithfulChecklist` deliberately mirrors the current
`Main.lean` H2 slot: `ResetPortH2RowEquivRibbonRealizationData`.  During H2
repair, however, it is useful to use the weaker/healthier target
`ResetPortH2RootFlatCycleData`: RF1, RF2, and RF3 for the actual reset-port
root-flat schedule.

This file records that alternate checklist.  It does not import into the default
spine.  It is a staging target for the H2 work described in
`D5M4H2Skeleton.lean`.
-/

namespace EvenV11
namespace V28Hard
namespace ChecklistH2RootFlat

open V28PaperInterface
open D5M4H2Skeleton

/-- H2 input in the relaxed paper-faithful form: direct root-flat cycle data for
`D₅(4)`, rather than the stronger return-realization equality. -/
structure D5M4RootFlatResetInput where
  data : Nonempty LowD5M4Structural.ResetPortH2RootFlatCycleData

/-- H2 input obtained from the skeleton's direct root-flat route. -/
def d5m4RootFlatResetInput_of_route
    (input : H2RootFlatRouteSkeleton) : D5M4RootFlatResetInput where
  data := input.nonemptyCycleData

/-- Current `V28PaperInterface` H2 slot obtained from the stronger
ribbon-collapse route.  This is the drop-in replacement for
`assume_lowD5M4RibbonRealizationData` once RF2 and the return-section
realization have been filled. -/
def currentD5M4ParityResetInput_of_ribbonCollapse
    (input : H2RibbonCollapseInput) : D5M4ParityResetInput where
  data := input.nonemptyRibbonData

/-- H2 input obtained from the stronger ribbon-collapse route. -/
def d5m4RootFlatResetInput_of_ribbonCollapse
    (input : H2RibbonCollapseInput) : D5M4RootFlatResetInput where
  data :=
    ⟨LowD5M4Structural.rootFlatCycleData_of_ribbonRealizationData
      (LowD5M4Structural.ribbonRealizationData_of_rowEquivRibbonRealizationData
        input.toRowEquivRibbonData)⟩

/-- Low-base family adapter for the relaxed H2 input. -/
theorem d5m4RootFlatFamily_of_rootFlatResetInput
    (input : D5M4RootFlatResetInput) :
    FinalLowD5M4RootFlatCertificateFamily :=
  LowD5M4Structural.finalLowD5M4RootFlatCertificateFamily_of_rootFlatCycleData
    (Classical.choice input.data)

/-- Six-obligation checklist with H2 relaxed to direct D5(4) root-flat cycle
data.  H3/H4 remain structural D7 inputs, not generated finite facts. -/
structure PaperFaithfulChecklistWithH2RootFlat where
  d3TerminalA2 : D3TerminalA2Input
  d5m4Reset : D5M4RootFlatResetInput
  d7m4TwoRail : D7M4TwoRailInput
  d7m6TwoRail : D7M6TwoRailInput
  oddHighModulus : OddHighModulusInput
  oddEndpoint : OddEndpointInput

/-- Low-base family package for the alternate checklist. -/
theorem lowBaseRootFlatFamilies_of_h2RootFlatChecklist
    (checklist : PaperFaithfulChecklistWithH2RootFlat) :
    FinalLowBaseRootFlatCertificateFamilies where
  d5m4 := d5m4RootFlatFamily_of_rootFlatResetInput checklist.d5m4Reset
  d7m4 := d7m4RootFlatFamily_of_input checklist.d7m4TwoRail
  d7m6 := d7m6RootFlatFamily_of_input checklist.d7m6TwoRail

/-- Convert the alternate checklist into the existing final target checklist. -/
theorem finalTargetChecklist_of_h2RootFlatChecklist
    (checklist : PaperFaithfulChecklistWithH2RootFlat) :
    FinalTargetCertificateChecklistWithD3AndLowRootFlat where
  d3RootFlatFamily := checklist.d3TerminalA2.family
  lowRootFlatFamilies := lowBaseRootFlatFamilies_of_h2RootFlatChecklist checklist
  oddHighModulusPromotion := checklist.oddHighModulus.promotion
  oddEndpointPromotion := checklist.oddEndpoint.promotion

/-- Final theorem from the alternate H2-root-flat checklist. -/
theorem evenModulusToriAllDimensions_of_h2RootFlatChecklist
    (checklist : PaperFaithfulChecklistWithH2RootFlat) :
    V28EvenModulusToriAllDimensionsGoal := by
  intro d m hd hm hm4
  obtain ⟨r, hr⟩ := hm
  exact finalTargetCayley_from_d3AndLowRootFlatChecklist
    (finalTargetChecklist_of_h2RootFlatChecklist checklist)
    ⟨hd, hm4, r, by omega⟩

/-- Practical checkpoint theorem: H2 uses the relaxed D5 root-flat skeleton;
D7 uses the quarantined finite-backed checkpoint.  This is for wiring checks,
not for the final paper-faithful theorem name. -/
def checkpointChecklist_with_H2RootFlat_finiteBackedD7
    (h2 : H2RootFlatRouteSkeleton) :
    PaperFaithfulChecklistWithH2RootFlat where
  d3TerminalA2 :=
    { family := D3TerminalA2Parametric.rootFlatCertificateFamily }
  d5m4Reset := d5m4RootFlatResetInput_of_route h2
  d7m4TwoRail := D7Checkpoint.generatedD7M4CheckpointInput
  d7m6TwoRail := D7Checkpoint.generatedD7M6CheckpointInput
  oddHighModulus :=
    { promotion :=
        HighEvenEndpointPromotions.oddHighModulusPromotion_of_engine
          HighEvenEndpointPromotions.candidate_oddHighModulusEngine }
  oddEndpoint :=
    { promotion :=
        HighEvenEndpointPromotions.endpointTargetPromotion_of_engine
          HighEvenEndpointPromotions.candidate_oddEndpointPayloadEngine }

/-- Full wiring theorem for the checkpoint route.  The name advertises both
choices that are not final: relaxed H2 root-flat staging and finite-backed D7. -/
theorem evenModulusToriAllDimensions_checkpoint_H2RootFlat_finiteBackedD7
    (h2 : H2RootFlatRouteSkeleton) :
    V28EvenModulusToriAllDimensionsGoal :=
  evenModulusToriAllDimensions_of_h2RootFlatChecklist
    (checkpointChecklist_with_H2RootFlat_finiteBackedD7 h2)

/-- Same checkpoint, but starting from the stronger current-spine ribbon-collapse
H2 input. -/
def checkpointChecklist_with_H2RibbonCollapse_finiteBackedD7
    (h2 : H2RibbonCollapseInput) :
    PaperFaithfulChecklistWithH2RootFlat where
  d3TerminalA2 :=
    { family := D3TerminalA2Parametric.rootFlatCertificateFamily }
  d5m4Reset := d5m4RootFlatResetInput_of_ribbonCollapse h2
  d7m4TwoRail := D7Checkpoint.generatedD7M4CheckpointInput
  d7m6TwoRail := D7Checkpoint.generatedD7M6CheckpointInput
  oddHighModulus :=
    { promotion :=
        HighEvenEndpointPromotions.oddHighModulusPromotion_of_engine
          HighEvenEndpointPromotions.candidate_oddHighModulusEngine }
  oddEndpoint :=
    { promotion :=
        HighEvenEndpointPromotions.endpointTargetPromotion_of_engine
          HighEvenEndpointPromotions.candidate_oddEndpointPayloadEngine }

/-- Full wiring theorem for the stronger H2 ribbon-collapse checkpoint route. -/
theorem evenModulusToriAllDimensions_checkpoint_H2RibbonCollapse_finiteBackedD7
    (h2 : H2RibbonCollapseInput) :
    V28EvenModulusToriAllDimensionsGoal :=
  evenModulusToriAllDimensions_of_h2RootFlatChecklist
    (checkpointChecklist_with_H2RibbonCollapse_finiteBackedD7 h2)

end ChecklistH2RootFlat
end V28Hard
end EvenV11
