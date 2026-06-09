import EvenV11.V28PaperInterface
import EvenV11.V28Hard.D3TerminalA2Parametric
import EvenV11.LowD5M4RibbonInterface
import EvenV11.V28Hard.D7TwoRailRelay
import EvenV11.V28Hard.HighEvenEndpointPromotions

/-!
# Assemble active v28 hard-part code into the paper checklist

The archived H2 paper-table route and generated D7 finite checkpoints are no
longer imported by the active hard-part surface.  This file keeps only the
paper-faithful handoff shape:

* H2 is the active physical-row ribbon input
  `LowD5M4RibbonInterface.PhysicalRowsSingletonSwitchMapConjInput`.
* H3/H4 are structural `RootFlatCycleData` inputs.
* H5/H6 are supplied as explicit promotion inputs.
-/

namespace EvenV11
namespace V28Hard
namespace ChecklistFromHardParts

open V28PaperInterface

abbrev H2PhysicalRibbonInput :=
  LowD5M4RibbonInterface.PhysicalRowsSingletonSwitchMapConjInput

theorem nonemptyD5RibbonData_of_physicalInput
    (h2 : H2PhysicalRibbonInput) :
    Nonempty LowD5M4Structural.ResetPortH2RowEquivRibbonRealizationData :=
  h2.nonemptyRibbonData

/-- Fully paper-faithful checklist constructor: no generated finite checkpoint is
hidden here.  H2 is supplied by the active physical-row ribbon interface, and D7
is supplied as structural root-flat cycle data. -/
def paperChecklist_from_physicalH2_structuralD7
    (d3 : FinalD3EvenRootFlatCertificateFamily)
    (h2 : H2PhysicalRibbonInput)
    (d7m4 : Nonempty (RootFlatCycle.RootFlatCycleData 6 4))
    (d7m6 : Nonempty (RootFlatCycle.RootFlatCycleData 6 6))
    (high : FinalOddHighModulusTargetPromotion)
    (endpoint : FinalOddEndpointPhaseProductTargetPromotion) :
    PaperFaithfulChecklist where
  d3TerminalA2 := { family := d3 }
  d5m4Reset := { data := nonemptyD5RibbonData_of_physicalInput h2 }
  d7m4TwoRail := { data := d7m4 }
  d7m6TwoRail := { data := d7m6 }
  oddHighModulus := { promotion := high }
  oddEndpoint := { promotion := endpoint }

theorem evenModulusToriAllDimensions_from_physicalH2_structuralD7
    (d3 : FinalD3EvenRootFlatCertificateFamily)
    (h2 : H2PhysicalRibbonInput)
    (d7m4 : Nonempty (RootFlatCycle.RootFlatCycleData 6 4))
    (d7m6 : Nonempty (RootFlatCycle.RootFlatCycleData 6 6))
    (high : FinalOddHighModulusTargetPromotion)
    (endpoint : FinalOddEndpointPhaseProductTargetPromotion) :
    V28EvenModulusToriAllDimensionsGoal :=
  evenModulusToriAllDimensions_of_paperChecklist
    (paperChecklist_from_physicalH2_structuralD7
      d3 h2 d7m4 d7m6 high endpoint)

/-- Generic structural-D7 checklist constructor, useful when H2 has already been
converted to the current `Main.lean` ribbon-data slot. -/
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

/-- Practical wiring constructor that keeps H2 explicit, leaves H3/H4 as
structural inputs, and also takes the terminal and promotion pieces explicitly. -/
def paperChecklist_from_activeHardSurfaceComponents
    (terminalA2 : D3TerminalA2Parametric.TerminalA2ParametricSolution)
    (h2 : H2PhysicalRibbonInput)
    (d7m4 : Nonempty (RootFlatCycle.RootFlatCycleData 6 4))
    (d7m6 : Nonempty (RootFlatCycle.RootFlatCycleData 6 6))
    (engines : HighEvenEndpointPromotions.HardPromotionEngines) :
    PaperFaithfulChecklist :=
  paperChecklist_from_physicalH2_structuralD7
    (D3TerminalA2Parametric.rootFlatCertificateFamily_of_solution terminalA2)
    h2 d7m4 d7m6
    (HighEvenEndpointPromotions.oddHighModulusPromotion_of_engine
      engines.highEven)
    (HighEvenEndpointPromotions.endpointTargetPromotion_of_engine
      engines.endpoint)

theorem evenModulusToriAllDimensions_from_activeHardSurfaceComponents
    (terminalA2 : D3TerminalA2Parametric.TerminalA2ParametricSolution)
    (h2 : H2PhysicalRibbonInput)
    (d7m4 : Nonempty (RootFlatCycle.RootFlatCycleData 6 4))
    (d7m6 : Nonempty (RootFlatCycle.RootFlatCycleData 6 6))
    (engines : HighEvenEndpointPromotions.HardPromotionEngines) :
    V28EvenModulusToriAllDimensionsGoal :=
  evenModulusToriAllDimensions_of_paperChecklist
    (paperChecklist_from_activeHardSurfaceComponents
      terminalA2 h2 d7m4 d7m6 engines)

end ChecklistFromHardParts
end V28Hard
end EvenV11
