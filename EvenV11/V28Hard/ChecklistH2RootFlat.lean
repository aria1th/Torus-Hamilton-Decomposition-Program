import EvenV11.V28PaperInterface
import EvenV11.LowD5M4Structural
import EvenV11.V28Hard.D3TerminalA2Parametric
import EvenV11.V28Hard.D7TwoRailRelay
import EvenV11.V28Hard.HighEvenEndpointPromotions

/-!
# Checklist variant with H2 as direct root-flat cycle data

This is an active, archive-free staging target.  It deliberately does not import
the retired H2 paper-table skeleton or the generated D7 finite checkpoints.
-/

namespace EvenV11
namespace V28Hard
namespace ChecklistH2RootFlat

open V28PaperInterface

/-- H2 input in the relaxed form: direct RF1/RF2/RF3 data for the D5(4)
root-flat schedule.  The main theorem still uses the stronger ribbon handoff,
but this is useful as an intermediate H2 target. -/
structure D5M4RootFlatResetInput where
  data : Nonempty LowD5M4Structural.ResetPortH2RootFlatCycleData

def d5m4RootFlatResetInput_of_data
    (data : LowD5M4Structural.ResetPortH2RootFlatCycleData) :
    D5M4RootFlatResetInput where
  data := ⟨data⟩

def d5m4RootFlatResetInput_of_ribbonData
    (h2 :
      Nonempty LowD5M4Structural.ResetPortH2RowEquivRibbonRealizationData) :
    D5M4RootFlatResetInput where
  data :=
    h2.elim fun data =>
      ⟨LowD5M4Structural.rootFlatCycleData_of_ribbonRealizationData
        (LowD5M4Structural.ribbonRealizationData_of_rowEquivRibbonRealizationData
          data)⟩

theorem d5m4RootFlatFamily_of_rootFlatResetInput
    (input : D5M4RootFlatResetInput) :
    FinalLowD5M4RootFlatCertificateFamily :=
  LowD5M4Structural.finalLowD5M4RootFlatCertificateFamily_of_rootFlatCycleData
    (Classical.choice input.data)

/-- Six-obligation checklist with H2 relaxed to direct D5(4) root-flat cycle
data.  H3/H4 remain structural D7 inputs. -/
structure PaperFaithfulChecklistWithH2RootFlat where
  d3TerminalA2 : D3TerminalA2Input
  d5m4Reset : D5M4RootFlatResetInput
  d7m4TwoRail : D7M4TwoRailInput
  d7m6TwoRail : D7M6TwoRailInput
  oddHighModulus : OddHighModulusInput
  oddEndpoint : OddEndpointInput

theorem lowBaseRootFlatFamilies_of_h2RootFlatChecklist
    (checklist : PaperFaithfulChecklistWithH2RootFlat) :
    FinalLowBaseRootFlatCertificateFamilies where
  d5m4 := d5m4RootFlatFamily_of_rootFlatResetInput checklist.d5m4Reset
  d7m4 := d7m4RootFlatFamily_of_input checklist.d7m4TwoRail
  d7m6 := d7m6RootFlatFamily_of_input checklist.d7m6TwoRail

theorem finalTargetChecklist_of_h2RootFlatChecklist
    (checklist : PaperFaithfulChecklistWithH2RootFlat) :
    FinalTargetCertificateChecklistWithD3AndLowRootFlat where
  d3RootFlatFamily := checklist.d3TerminalA2.family
  lowRootFlatFamilies := lowBaseRootFlatFamilies_of_h2RootFlatChecklist checklist
  oddHighModulusPromotion := checklist.oddHighModulus.promotion
  oddEndpointPromotion := checklist.oddEndpoint.promotion

theorem evenModulusToriAllDimensions_of_h2RootFlatChecklist
    (checklist : PaperFaithfulChecklistWithH2RootFlat) :
    V28EvenModulusToriAllDimensionsGoal := by
  intro d m hd hm hm4
  obtain ⟨r, hr⟩ := hm
  exact finalTargetCayley_from_d3AndLowRootFlatChecklist
    (finalTargetChecklist_of_h2RootFlatChecklist checklist)
    ⟨hd, hm4, r, by omega⟩

def checkpointChecklist_with_H2RootFlat_structuralD7
    (h2 : D5M4RootFlatResetInput)
    (d7m4 : Nonempty (RootFlatCycle.RootFlatCycleData 6 4))
    (d7m6 : Nonempty (RootFlatCycle.RootFlatCycleData 6 6)) :
    PaperFaithfulChecklistWithH2RootFlat where
  d3TerminalA2 :=
    { family := D3TerminalA2Parametric.rootFlatCertificateFamily }
  d5m4Reset := h2
  d7m4TwoRail := { data := d7m4 }
  d7m6TwoRail := { data := d7m6 }
  oddHighModulus :=
    { promotion :=
        HighEvenEndpointPromotions.oddHighModulusPromotion_of_engine
          HighEvenEndpointPromotions.candidate_oddHighModulusEngine }
  oddEndpoint :=
    { promotion :=
        HighEvenEndpointPromotions.endpointTargetPromotion_of_engine
          HighEvenEndpointPromotions.candidate_oddEndpointPayloadEngine }

theorem evenModulusToriAllDimensions_checkpoint_H2RootFlat_structuralD7
    (h2 : D5M4RootFlatResetInput)
    (d7m4 : Nonempty (RootFlatCycle.RootFlatCycleData 6 4))
    (d7m6 : Nonempty (RootFlatCycle.RootFlatCycleData 6 6)) :
    V28EvenModulusToriAllDimensionsGoal :=
  evenModulusToriAllDimensions_of_h2RootFlatChecklist
    (checkpointChecklist_with_H2RootFlat_structuralD7 h2 d7m4 d7m6)

end ChecklistH2RootFlat
end V28Hard
end EvenV11
