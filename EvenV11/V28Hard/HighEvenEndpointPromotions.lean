import EvenV11.FinalTargetHighEvenCertificateBridge
import EvenV11.FinalTargetPhaseProductCertificateBridge
import EvenV11.V28PaperInterface

/-!
# Hard slots H5/H6: high-even and endpoint promotion engines

The final induction spine consumes two promotion records:

* `FinalOddHighModulusTargetPromotion` for the odd high-modulus branch `d < m`;
* `FinalOddEndpointPhaseProductTargetPromotion` for the endpoint branch
  `d = 2b+1` with `m ≤ d`.

This file gives the proof code skeleton in the direction of the manuscript: a
paper construction should first build stronger *engines* carrying marked payloads
and local support data, then forget those payloads to the old target interface.
-/

namespace EvenV11
namespace V28Hard
namespace HighEvenEndpointPromotions

open FinalTargetHighEvenCertificateBridge

/-- The high-even branch should not directly manufacture the final target from
opaque closed inputs.  It should expose the finite anchor/coforest audit, the
projection kernel, and the guide-locality facts as separate arguments. -/
structure OddHighModulusEngine : Prop where
  run :
    ∀ {d m : Nat}, 5 ≤ d → (∃ b : Nat, d = 2 * b + 1) →
      EvenModulusRange m → d < m →
      TypeA.v28FiniteInputCoforestAudit →
      HighEvenProjectionKernelInput →
      HighEvenGuideLocalityInput →
      FinalReturnCoreInput →
      FinalWordCoreInput →
      FinalRangeInput →
      FinalMarkedTarget d m

/-- Forgetful adapter from the paper high-even engine to the current promotion
record. -/
theorem oddHighModulusPromotion_of_engine
    (engine : OddHighModulusEngine) :
    FinalOddHighModulusTargetPromotion where
  oddHighModulus := by
    intro d m hd hodd hm hdm input
    exact engine.run hd hodd hm hdm
      input.finiteAnchorInput.v28FiniteInput
      input.projectionKernelInput
      input.guideLocalityInput
      input.returnCoreInput
      input.wordCoreInput
      input.rangeInput

/-- A more concrete proof plan for H5.  The hard parts are exactly the local
support/quotient claims that make the Type-A splice invisible outside the guide
boundary. -/
structure OddHighModulusProofPlan : Prop where
  finiteAnchor : HighEvenFiniteAnchorInput
  projectionKernel : HighEvenProjectionKernelInput
  guideLocality : HighEvenGuideLocalityInput
  returnCore : FinalReturnCoreInput
  wordCore : FinalWordCoreInput
  rangeInput : FinalRangeInput
  /-- This is the actual coforest-splice construction in the high-even branch. -/
  spliceConstruction : OddHighModulusEngine

/-- H5 in one object, ready to feed the paper checklist. -/
theorem oddHighModulusInput_of_engine
    (engine : OddHighModulusEngine) :
    V28PaperInterface.OddHighModulusInput where
  promotion := oddHighModulusPromotion_of_engine engine

/-- Endpoint successor engine in the stronger marked-payload form.  Unlike the
current induction spine, this keeps the parent comparison selector/reserve alive
while constructing the child payload. -/
structure OddEndpointPayloadEngine : Prop where
  run :
    ∀ {b m : Nat}, 4 ≤ b → MarkedDimensionRange b m →
      FinalMarkedPayload b m →
      FinalOddEndpointPhaseProductCertificateInputs →
      FinalMarkedPayload (2 * b + 1) m

/-- Convert the payload engine to the phase-product marked-payload promotion. -/
theorem endpointMarkedPayloadPromotion_of_engine
    (engine : OddEndpointPayloadEngine) :
    FinalOddEndpointPhaseProductMarkedPayloadPromotion where
  oddEndpoint := engine.run

/-- Forget the endpoint payload to the current target-only interface. -/
theorem endpointTargetPromotion_of_engine
    (engine : OddEndpointPayloadEngine) :
    FinalOddEndpointPhaseProductTargetPromotion :=
  finalOddEndpointPhaseProductTargetPromotion_of_markedPayloadPromotion
    (endpointMarkedPayloadPromotion_of_engine engine)

/-- H6 in one object, ready to feed the paper checklist. -/
theorem oddEndpointInput_of_engine
    (engine : OddEndpointPayloadEngine) :
    V28PaperInterface.OddEndpointInput where
  promotion := endpointTargetPromotion_of_engine engine

/-- The paper endpoint proof should be decomposed into these pieces.  Most of the
underlying bridges already exist in `EndpointCompletion`, `PhaseProductSupport`,
and `FinalTargetPhaseProductCertificateBridge`; the missing work is choosing and
threading the marked payload. -/
structure OddEndpointProofPlan : Prop where
  terminalInput : FinalTerminalInput
  markedTransferInput :
    EndpointMarkedTransferBridge.foldedEndpointMarkedTransferInputAudit
  phaseProductInput : FinalPhaseProductCertificateInputs
  completionCarryInput :
    ∀ {Base Coord : Type} [Finite Base]
      {N m : Nat} [NeZero N] [NeZero m]
      (baseStep : Base → Base) (rank : Base ≃ ZMod N)
      (_base : Base) (C : CompletionCarryCertificate Base Coord m),
      (∀ x : Base, rank (baseStep x) = rank x + 1) →
      IsUnit C.epsilon →
      Shared.IsSingleCycleMap
        (additiveSkewMap baseStep
          (completionCarry C.coordRead C.row C.tail))
  b4FirstCompletionInput :
    ∀ {m : Nat} [NeZero m],
      Shared.IsSingleCycleMap
        (additiveSkewMap finCompletionBaseStep
          (completionCarry
            (endpointB4FirstCompletionOnePointCertificate m).coordRead
            (cyclicCompletionRow
              (endpointB4FirstCompletionOnePointCertificate m).shift)
            (endpointB4FirstCompletionOnePointCertificate m).tail))
  rangeInput : FinalRangeInput
  payloadEngine : OddEndpointPayloadEngine

/-- Repackage the endpoint proof plan as the certificate input consumed by the
old bridge layer. -/
theorem phaseProductCertificateInputs_of_endpointPlan
    (plan : OddEndpointProofPlan) :
    FinalOddEndpointPhaseProductCertificateInputs where
  terminalInput := plan.terminalInput
  markedTransferInput := plan.markedTransferInput
  phaseProductInput := plan.phaseProductInput
  completionCarryInput := plan.completionCarryInput
  b4FirstCompletionInput := plan.b4FirstCompletionInput
  rangeInput := plan.rangeInput

/-- A combined hard-promotion bundle.  This is the object that should eventually
replace both H5 and H6 assumptions in `Main.lean`/`V28PaperInterface.lean`. -/
structure HardPromotionEngines : Prop where
  highEven : OddHighModulusEngine
  endpoint : OddEndpointPayloadEngine

/-- Convert hard-promotion engines to the two paper checklist inputs. -/
theorem paperGrowthInputs_of_engines
    (engines : HardPromotionEngines) :
    V28PaperInterface.OddHighModulusInput ∧
      V28PaperInterface.OddEndpointInput :=
  ⟨oddHighModulusInput_of_engine engines.highEven,
   oddEndpointInput_of_engine engines.endpoint⟩

/-- Candidate H5 theorem.  The body is intentionally the exact construction site:
instantiate the coforest splice, projection kernel, and guide-locality lemmas. -/
theorem candidate_oddHighModulusEngine :
    OddHighModulusEngine := by
  sorry

/-- Candidate H6 theorem.  The body is intentionally the exact construction site:
thread a real marked payload through endpoint completion and phase-product
support instead of using the weak payload adapter. -/
theorem candidate_oddEndpointPayloadEngine :
    OddEndpointPayloadEngine := by
  sorry

/-- Candidate growth-promotion bundle. -/
theorem candidate_hardPromotionEngines : HardPromotionEngines where
  highEven := candidate_oddHighModulusEngine
  endpoint := candidate_oddEndpointPayloadEngine

end HighEvenEndpointPromotions
end V28Hard
end EvenV11
