import EvenV11.V28PaperInterface
import EvenV11.V28Hard.D3TerminalA2Parametric
import EvenV11.V28Hard.D7TwoRailRelay
import EvenV11.V28Hard.HighEvenEndpointPromotions
import EvenV11.V28Hard.JsonProof

/-!
# v28 constructive proof shape

This file records the paper-facing data flow without installing global proof
constants.  A `ConstructiveV28Solution` contains exactly the six manuscript
handoffs and the theorem below shows that those handoffs are sufficient for the
main even-modulus target.
-/

namespace EvenV11
namespace V28Hard
namespace PaperExactStructure

open V28PaperInterface

abbrev AnchorLabel (D : Nat) := Fin D
abbrev AnchorEdge (D : Nat) := AnchorLabel D × AnchorLabel D

/-- Paper Definition 5.1 in Lean-facing form: finite coforest-splice anchor data
for an odd high-even anchor.  The fields mirror the manuscript list: a Latin
skeleton, simultaneous rooted coforest supports, rank-one tail/head identities,
and terminal alignment with separated endpoint reserves. -/
structure FiniteCoforestSpliceAnchorDatum (D : Nat) where
  five_le : 5 ≤ D
  odd : ∃ b : Nat, D = 2 * b + 1
  chronologicalRows : Type
  shiftedColorForest : AnchorLabel D → List (AnchorEdge D)
  terminalTriple : AnchorLabel D × AnchorLabel D × AnchorLabel D
  terminalA2Form : Prop
  supportRows : List (List (AnchorEdge D))
  activeRows : List (List (AnchorEdge D))
  simultaneousRootedCoforestSupports : Prop
  descendantCutTailHeadIdentities : Prop
  primitiveClosingColumns : Prop
  separatedEndpointReserveSites : Prop

/-- Section-level manuscript data that sit below the final six-field checklist.
These fields mirror the audited v28 proof: coforest-splice anchors, ordinary and
chained high-even growth rows, endpoint phase-product rows, and the D7 finite
audit evidence. -/
structure ManuscriptHardSectionData where
  finiteCoforestAnchor :
    ∀ {D : Nat}, 5 ≤ D → (∃ b : Nat, D = 2 * b + 1) →
      Nonempty (FiniteCoforestSpliceAnchorDatum D)
  ordinaryHighEvenGrowthRow :
    ∀ {D : Nat}, 11 ≤ D →
      Nonempty (HighEvenEndpointPromotions.HighEvenFourPointGrowthRow D)
  chainedSevenToNineGrowthRow :
    Nonempty (HighEvenEndpointPromotions.HighEvenFourPointGrowthRow 9)
  endpointPhaseProduct :
    ∀ {b m : Nat}, 4 ≤ b → Even m → 4 ≤ m → m ≤ 2 * b + 1 →
      HighEvenEndpointPromotions.EndpointSuccessorPhaseProductDatum b m
  d7FiniteAudit : D7TwoRailRelay.RelayFiniteAuditEvidence

/-- The exact H1--H6 package read from the manuscript.  It does not hide any
unfilled proof as a global declaration; each field is an explicit input. -/
structure ConstructiveV28Solution where
  sectionData : ManuscriptHardSectionData
  terminalA2 : D3TerminalA2Parametric.TerminalA2ParametricSolution
  d5m4Reset : D5M4ParityResetInput
  d7TwoRail : D7TwoRailRelay.TwoRailRelaySolutions
  promotions : HighEvenEndpointPromotions.HardPromotionEngines

/-- Closed finite-audit evidence for the D7 hard sections, extracted from the
JSON values ported to `FiniteAudit.lean`. -/
def d7FiniteAuditEvidence : D7TwoRailRelay.RelayFiniteAuditEvidence :=
  JsonProof.d7FiniteAuditEvidence

/-- Closed finite terminal-carrier cyclicity at the two low moduli used by the
paper's terminal block. -/
noncomputable def terminalA2LowModFiniteBundle :
    D3TerminalA2Parametric.TerminalA2LowModFiniteBundle :=
  D3TerminalA2Parametric.terminalA2LowModFiniteBundle

/-- Closed finite terminal-carrier cyclicity at the two low moduli used by the
paper's terminal block, kept in the older pair shape for static checkers and
call sites. -/
theorem terminalLowModFiniteCyclicity :
    D3TerminalA2Parametric.TerminalA2FiniteCyclicity 4 ∧
      D3TerminalA2Parametric.TerminalA2FiniteCyclicity 6 :=
  ⟨terminalA2LowModFiniteBundle.m4, terminalA2LowModFiniteBundle.m6⟩

/-- Convert the exact constructive package to the existing six-field paper
checklist. -/
def paperChecklist_of_constructiveSolution
    (solution : ConstructiveV28Solution) :
    PaperFaithfulChecklist where
  d3TerminalA2 :=
    { family :=
        D3TerminalA2Parametric.rootFlatCertificateFamily_of_solution
          solution.terminalA2 }
  d5m4Reset := solution.d5m4Reset
  d7m4TwoRail :=
    { data :=
        D7TwoRailRelay.d7m4CycleData_of_solutions solution.d7TwoRail }
  d7m6TwoRail :=
    { data :=
        D7TwoRailRelay.d7m6CycleData_of_solutions solution.d7TwoRail }
  oddHighModulus :=
    HighEvenEndpointPromotions.oddHighModulusInput_of_engine
      solution.promotions.highEven
  oddEndpoint :=
    HighEvenEndpointPromotions.oddEndpointInput_of_engine
      solution.promotions.endpoint

/-- Main theorem from the exact paper data.  The final induction and all
checklist adapters are closed; the only inputs are the six constructive fields
above. -/
theorem evenModulusToriAllDimensions_of_constructiveSolution
    (solution : ConstructiveV28Solution) :
    V28EvenModulusToriAllDimensionsGoal :=
  evenModulusToriAllDimensions_of_paperChecklist
    (paperChecklist_of_constructiveSolution solution)

/-- A version with the six fields expanded as arguments, convenient while
formalizing each manuscript section independently. -/
theorem evenModulusToriAllDimensions_of_components
    (sectionData : ManuscriptHardSectionData)
    (terminalA2 : D3TerminalA2Parametric.TerminalA2ParametricSolution)
    (d5m4Reset : D5M4ParityResetInput)
    (d7TwoRail : D7TwoRailRelay.TwoRailRelaySolutions)
    (promotions : HighEvenEndpointPromotions.HardPromotionEngines) :
    V28EvenModulusToriAllDimensionsGoal :=
  evenModulusToriAllDimensions_of_constructiveSolution
    { sectionData := sectionData
      terminalA2 := terminalA2
      d5m4Reset := d5m4Reset
      d7TwoRail := d7TwoRail
      promotions := promotions }

end PaperExactStructure
end V28Hard
end EvenV11
