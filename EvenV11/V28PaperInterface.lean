import EvenV11.FinalTargetLowBaseRootFlatCertificateBridge
import EvenV11.LowD5M4Structural
import EvenV11.RootFlatCycleData

/-!
# v28 paper-facing interface

This file is intentionally an interface, not a new proof of the remaining
mathematics.  It records the paper-faithful dependency shape for the even
modulus theorem after auditing the v28 manuscript against the current Lean
workspace.

The important difference from `EvenV11.Main` is that the `D₇(4)` low base is
exposed as the same structural root-flat cycle-data obligation as `D₇(6)`,
instead of being consumed from the generated `LowD7M4Finite` blob.  The finite
blob can remain as a regression artifact, but the paper spine should eventually
fill the structural field below.
-/

namespace EvenV11
namespace V28PaperInterface

/-- The v28 paper target, repeated here without importing `EvenV11.Main` so this
interface can stay independent of the current generated `LowD7M4Finite` spine. -/
def V28EvenModulusToriAllDimensionsGoal : Prop :=
  ∀ {d m : Nat}, 2 ≤ d → Even m → 4 ≤ m →
    Shared.CayleyHamiltonDecomposition d m


/-- H1: the paper's parametric terminal `A₂` proof for the three-dimensional
even base. -/
structure D3TerminalA2Input : Prop where
  family : FinalD3EvenRootFlatCertificateFamily

/-- H2: the paper-facing `D₅(4)` reset handoff.  RF1 is encoded by row
equivalences; the remaining content is RF2 plus the ribbon/run-collapse return
realization. -/
structure D5M4ParityResetInput : Prop where
  data : Nonempty LowD5M4Structural.ResetPortH2RowEquivRibbonRealizationData

/-- H3, paper-faithful form: the `D₇(4)` two-rail base as concrete RF1/RF2/RF3
root-flat data, not as a generated finite blob. -/
structure D7M4TwoRailInput : Prop where
  data : Nonempty (RootFlatCycle.RootFlatCycleData 6 4)

/-- H4: the `D₇(6)` two-rail base in the same structural form as `D₇(4)`. -/
structure D7M6TwoRailInput : Prop where
  data : Nonempty (RootFlatCycle.RootFlatCycleData 6 6)

/-- H5: odd high-even anchor/growth promotion. -/
structure OddHighModulusInput : Prop where
  promotion : FinalOddHighModulusTargetPromotion

/-- H6: low-modulus endpoint successor promotion, including the phase-product
support layer used by the v28 manuscript. -/
structure OddEndpointInput : Prop where
  promotion : FinalOddEndpointPhaseProductTargetPromotion

/-- The six paper-facing obligations.  Filling these fields, with no generated
finite blob in the theorem spine, is the v28 formalization target. -/
structure PaperFaithfulChecklist : Prop where
  d3TerminalA2 : D3TerminalA2Input
  d5m4Reset : D5M4ParityResetInput
  d7m4TwoRail : D7M4TwoRailInput
  d7m6TwoRail : D7M6TwoRailInput
  oddHighModulus : OddHighModulusInput
  oddEndpoint : OddEndpointInput

/-- Closed adapter: H2 data gives the low-base `D₅(4)` root-flat family. -/
theorem d5m4RootFlatFamily_of_input
    (input : D5M4ParityResetInput) :
    FinalLowD5M4RootFlatCertificateFamily :=
  LowD5M4Structural.finalLowD5M4RootFlatCertificateFamily_of_nonemptyRowEquivRibbonRealizationData
    input.data

/-- Closed adapter: structural H3 data gives the low-base `D₇(4)` family. -/
theorem d7m4RootFlatFamily_of_input
    (input : D7M4TwoRailInput) :
    FinalLowD7M4RootFlatCertificateFamily :=
  RootFlatCycle.finalLowD7M4RootFlatCertificateFamily_of_nonemptyCycleData
    input.data

/-- Closed adapter: structural H4 data gives the low-base `D₇(6)` family. -/
theorem d7m6RootFlatFamily_of_input
    (input : D7M6TwoRailInput) :
    FinalLowD7M6RootFlatCertificateFamily :=
  RootFlatCycle.finalLowD7M6RootFlatCertificateFamily_of_nonemptyCycleData
    input.data

/-- Package the three low-base structural certificates in the shape consumed by
the already-formalized final induction. -/
theorem lowBaseRootFlatFamilies_of_paperChecklist
    (checklist : PaperFaithfulChecklist) :
    FinalLowBaseRootFlatCertificateFamilies where
  d5m4 := d5m4RootFlatFamily_of_input checklist.d5m4Reset
  d7m4 := d7m4RootFlatFamily_of_input checklist.d7m4TwoRail
  d7m6 := d7m6RootFlatFamily_of_input checklist.d7m6TwoRail

/-- Convert the paper-facing six-field checklist into the existing final target
checklist. -/
theorem finalTargetChecklist_of_paperChecklist
    (checklist : PaperFaithfulChecklist) :
    FinalTargetCertificateChecklistWithD3AndLowRootFlat where
  d3RootFlatFamily := checklist.d3TerminalA2.family
  lowRootFlatFamilies := lowBaseRootFlatFamilies_of_paperChecklist checklist
  oddHighModulusPromotion := checklist.oddHighModulus.promotion
  oddEndpointPromotion := checklist.oddEndpoint.promotion

/-- Conditional theorem with exactly the paper-facing obligations.  This theorem
has no additional mathematical content: it proves that the existing final
induction spine consumes the six v28 obligations. -/
theorem evenModulusToriAllDimensions_of_paperChecklist
    (checklist : PaperFaithfulChecklist) :
    V28EvenModulusToriAllDimensionsGoal := by
  intro d m hd hm hm4
  obtain ⟨r, hr⟩ := hm
  exact finalTargetCayley_from_d3AndLowRootFlatChecklist
    (finalTargetChecklist_of_paperChecklist checklist)
    ⟨hd, hm4, r, by omega⟩

end V28PaperInterface
end EvenV11
