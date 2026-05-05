import RoundComposite.OddCore

set_option linter.style.longLine false

namespace RoundComposite
namespace Concrete

/--
v7.5 direct modular-trade input package.

This is the paper-facing small-modulus route after the active-Hall
count-matrix branch has been demoted from the live path.  The remaining inputs
are the high-modulus trellis/count branch and the successor-scoped canonical
active local-trade scheduler.  The lower-triangular base-tail lift is now
proved in `BaseTail`.
-/
def OddModulusToriV75DirectModularTradeInputsGoal : Prop :=
  OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal ∧
  BaseTail.Trades.SuccessorActiveBlockCanonicalLocalSymbolTradeGoal

/--
v7.5 input package using the paper-facing finite coactive-site reservoir name.
-/
def OddModulusToriV75ReservoirInputsGoal : Prop :=
  OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal ∧
  BaseTail.Trades.SuccessorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal

/--
v7.5/v7.6 input package using the paper-facing active residue scheduling
theorem: compatible residue targets on the successor active cylinder are
realized directly by local symbol trades.
-/
def OddModulusToriV75CompatibleResidueSchedulingInputsGoal : Prop :=
  OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal ∧
  BaseTail.Trades.SuccessorActiveBlockCompatibleResidueSchedulingGoal

/--
v7.6 input package reducing compatible residue scheduling to a finite reservoir
swap schedule.
-/
def OddModulusToriV75ReservoirSwapScheduleInputsGoal : Prop :=
  OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal ∧
  BaseTail.Trades.SuccessorActiveBlockReservoirSwapScheduleGoal

/--
v7.5 input package using the one-site pre-correction reservoir surface.
-/
def OddModulusToriV75PreCorrectionInputsGoal : Prop :=
  OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal ∧
  BaseTail.Trades.SuccessorActiveBlockCanonicalPreCorrectionGoal

/--
v7.5 input package kept for the earlier return-residual route name.  The
base-tail return theorem is now proved in `BaseTail`, so this package only
contains the remaining one-site pre-correction trade input.
-/
def OddModulusToriV75PreCorrectionReturnInputsGoal : Prop :=
  OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal ∧
  BaseTail.Trades.SuccessorActiveBlockCanonicalPreCorrectionGoal

/--
v7.5 input package after the lower-triangular return side is closed in
`BaseTailGeometry`: only the high-modulus branch and the successor
pre-correction/local-trade theorem remain as inputs.
-/
def OddModulusToriV75PreCorrectionClosedInputsGoal : Prop :=
  OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal ∧
  BaseTail.Trades.SuccessorActiveBlockCanonicalPreCorrectionGoal

/--
v7.5 input package splitting the Worker A local-trade surface into the
canonical feasible residue endpoint and the successor-scoped feasible local
symboling theorem.
-/
def OddModulusToriV75FeasibleLocalTradeReturnInputsGoal : Prop :=
  OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal ∧
  BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleResidueGoal ∧
  BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal

/--
v7.5 feasible-local-trade package after the lower-triangular return side is
closed.  The remaining Worker A inputs are canonical feasibility and the
successor-scoped feasible local symboling theorem.
-/
def OddModulusToriV75FeasibleLocalTradeInputsGoal : Prop :=
  OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal ∧
  BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleResidueGoal ∧
  BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal

/--
v7.5 feasible reservoir package using the paper-facing finite coactive-site
reservoir theorem name for the feasible local-trade layer.
-/
def OddModulusToriV75FeasibleFiniteCoactiveSiteReservoirReturnInputsGoal :
    Prop :=
  OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal ∧
  BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleResidueGoal ∧
  BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleFiniteCoactiveSiteReservoirGoal

/--
v7.5 feasible reservoir package after the lower-triangular return side is
closed.
-/
def OddModulusToriV75FeasibleFiniteCoactiveSiteReservoirInputsGoal : Prop :=
  OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal ∧
  BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleResidueGoal ∧
  BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleFiniteCoactiveSiteReservoirGoal

/--
v7.5 input package reducing the canonical feasible-residue side to a concrete
scaled proper-cut witness, paired with the successor-scoped feasible local
symboling theorem.
-/
def OddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal : Prop :=
  OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal ∧
  BaseTail.Trades.SuccessorActiveBlockCanonicalScaledFeasibleResidueGoal ∧
  BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal

/--
v7.5 scaled feasible-local-trade package after the lower-triangular return
side is closed.
-/
def OddModulusToriV75ScaledFeasibleLocalTradeInputsGoal : Prop :=
  OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal ∧
  BaseTail.Trades.SuccessorActiveBlockCanonicalScaledFeasibleResidueGoal ∧
  BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal

/--
v7.5 input package using the existing mixed controlled rounding endpoint as
the residue-side input, paired with the successor-scoped feasible local
symboling theorem.
-/
def OddModulusToriV75MixedControlledFeasibleLocalTradeReturnInputsGoal : Prop :=
  OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal ∧
  OddSuccessorBaseTailActiveBlockMixedControlledResidueRoundingGoal ∧
  BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal

/--
v7.5 mixed-controlled feasible-local-trade package after the lower-triangular
return side is closed.
-/
def OddModulusToriV75MixedControlledFeasibleLocalTradeInputsGoal : Prop :=
  OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal ∧
  OddSuccessorBaseTailActiveBlockMixedControlledResidueRoundingGoal ∧
  BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal

/--
v7.5 direct modular-trade block goal.

This is definitionally the already-wired v7.3 canonical local-trade
lower-triangular block route, exposed under the theorem label used by the v7.5
paper architecture.
-/
def OddModulusToriV75DirectModularTradeBlocksGoal : Prop :=
  OddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeLowerTriangularBlocksGoal

theorem oddModulusToriV75DirectModularTradeBlocksGoal_of_inputs
    (h : OddModulusToriV75DirectModularTradeInputsGoal) :
    OddModulusToriV75DirectModularTradeBlocksGoal :=
  oddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeLowerTriangularBlocksGoal_of_localTrade_lowerTriangular
    h.1 h.2 BaseTail.primitiveActivePrefixLowerTriangularLiftAssemblyGoal

theorem oddModulusToriV75DirectModularTradeInputsGoal_of_reservoirInputs
    (h : OddModulusToriV75ReservoirInputsGoal) :
    OddModulusToriV75DirectModularTradeInputsGoal :=
  ⟨h.1,
    BaseTail.Trades.successorActiveBlockCanonicalLocalSymbolTradeGoal_of_finiteCoactiveSiteReservoir
      h.2⟩

theorem oddModulusToriV75ReservoirInputsGoal_of_directInputs
    (h : OddModulusToriV75DirectModularTradeInputsGoal) :
    OddModulusToriV75ReservoirInputsGoal :=
  ⟨h.1,
    BaseTail.Trades.successorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal_of_preCorrection
      (BaseTail.Trades.successorActiveBlockCanonicalPreCorrectionGoal_of_canonicalLocalTrade
        h.2)⟩

theorem oddModulusToriV75ReservoirInputsGoal_iff_directInputs :
    OddModulusToriV75ReservoirInputsGoal ↔
      OddModulusToriV75DirectModularTradeInputsGoal :=
  ⟨oddModulusToriV75DirectModularTradeInputsGoal_of_reservoirInputs,
    oddModulusToriV75ReservoirInputsGoal_of_directInputs⟩

theorem oddModulusToriV75DirectModularTradeInputsGoal_of_compatibleResidueSchedulingInputs
    (h : OddModulusToriV75CompatibleResidueSchedulingInputsGoal) :
    OddModulusToriV75DirectModularTradeInputsGoal :=
  ⟨h.1,
    BaseTail.Trades.successorActiveBlockCanonicalLocalSymbolTradeGoal_of_compatibleResidueScheduling
      h.2⟩

theorem oddModulusToriV75ReservoirInputsGoal_of_compatibleResidueSchedulingInputs
    (h : OddModulusToriV75CompatibleResidueSchedulingInputsGoal) :
    OddModulusToriV75ReservoirInputsGoal :=
  ⟨h.1,
    BaseTail.Trades.successorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal_of_compatibleResidueScheduling
      h.2⟩

theorem oddModulusToriV75CompatibleResidueSchedulingInputsGoal_of_reservoirSwapScheduleInputs
    (h : OddModulusToriV75ReservoirSwapScheduleInputsGoal) :
    OddModulusToriV75CompatibleResidueSchedulingInputsGoal :=
  ⟨h.1,
    BaseTail.Trades.successorActiveBlockCompatibleResidueSchedulingGoal_of_reservoirSwapSchedule
      h.2⟩

theorem oddModulusToriV75DirectModularTradeInputsGoal_of_reservoirSwapScheduleInputs
    (h : OddModulusToriV75ReservoirSwapScheduleInputsGoal) :
    OddModulusToriV75DirectModularTradeInputsGoal :=
  oddModulusToriV75DirectModularTradeInputsGoal_of_compatibleResidueSchedulingInputs
    (oddModulusToriV75CompatibleResidueSchedulingInputsGoal_of_reservoirSwapScheduleInputs
      h)

theorem oddModulusToriV75ReservoirInputsGoal_of_reservoirSwapScheduleInputs
    (h : OddModulusToriV75ReservoirSwapScheduleInputsGoal) :
    OddModulusToriV75ReservoirInputsGoal :=
  oddModulusToriV75ReservoirInputsGoal_of_compatibleResidueSchedulingInputs
    (oddModulusToriV75CompatibleResidueSchedulingInputsGoal_of_reservoirSwapScheduleInputs
      h)

theorem oddModulusToriV75DirectModularTradeInputsGoal_of_preCorrectionInputs
    (h : OddModulusToriV75PreCorrectionInputsGoal) :
    OddModulusToriV75DirectModularTradeInputsGoal :=
  ⟨h.1,
    BaseTail.Trades.successorActiveBlockCanonicalLocalSymbolTradeGoal_of_preCorrection
      h.2⟩

theorem oddModulusToriV75DirectModularTradeInputsGoal_of_canonicalLocalTrade
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hTrade : BaseTail.Trades.SuccessorActiveBlockCanonicalLocalSymbolTradeGoal) :
    OddModulusToriV75DirectModularTradeInputsGoal :=
  ⟨hHigh, hTrade⟩

theorem oddModulusToriV75PreCorrectionInputsGoal_of_preCorrection
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hTrade : BaseTail.Trades.SuccessorActiveBlockCanonicalPreCorrectionGoal) :
    OddModulusToriV75PreCorrectionInputsGoal :=
  ⟨hHigh, hTrade⟩

theorem oddModulusToriV75PreCorrectionInputsGoal_of_directInputs
    (h : OddModulusToriV75DirectModularTradeInputsGoal) :
    OddModulusToriV75PreCorrectionInputsGoal :=
  ⟨h.1,
    BaseTail.Trades.successorActiveBlockCanonicalPreCorrectionGoal_of_canonicalLocalTrade
      h.2⟩

theorem oddModulusToriV75PreCorrectionInputsGoal_iff_directInputs :
    OddModulusToriV75PreCorrectionInputsGoal ↔
      OddModulusToriV75DirectModularTradeInputsGoal :=
  ⟨oddModulusToriV75DirectModularTradeInputsGoal_of_preCorrectionInputs,
    oddModulusToriV75PreCorrectionInputsGoal_of_directInputs⟩

theorem oddModulusToriV75PreCorrectionInputsGoal_of_preCorrectionReturnInputs
    (h : OddModulusToriV75PreCorrectionReturnInputsGoal) :
    OddModulusToriV75PreCorrectionInputsGoal :=
  h

theorem oddModulusToriV75DirectModularTradeInputsGoal_of_preCorrectionReturnInputs
    (h : OddModulusToriV75PreCorrectionReturnInputsGoal) :
    OddModulusToriV75DirectModularTradeInputsGoal :=
  oddModulusToriV75DirectModularTradeInputsGoal_of_preCorrectionInputs
    (oddModulusToriV75PreCorrectionInputsGoal_of_preCorrectionReturnInputs h)

theorem oddModulusToriV75PreCorrectionReturnInputsGoal_of_preCorrectionClosedInputs
    (h : OddModulusToriV75PreCorrectionClosedInputsGoal) :
    OddModulusToriV75PreCorrectionReturnInputsGoal :=
  h

theorem oddModulusToriV75PreCorrectionReturnInputsGoal_of_preCorrection
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hTrade : BaseTail.Trades.SuccessorActiveBlockCanonicalPreCorrectionGoal) :
    OddModulusToriV75PreCorrectionReturnInputsGoal :=
  oddModulusToriV75PreCorrectionReturnInputsGoal_of_preCorrectionClosedInputs
    ⟨hHigh, hTrade⟩

theorem oddModulusToriV75PreCorrectionReturnInputsGoal_of_preCorrection_return
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hTrade : BaseTail.Trades.SuccessorActiveBlockCanonicalPreCorrectionGoal) :
    OddModulusToriV75PreCorrectionReturnInputsGoal :=
  ⟨hHigh, hTrade⟩

theorem oddModulusToriV75PreCorrectionReturnInputsGoal_of_canonicalLocalTrade_return
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hTrade : BaseTail.Trades.SuccessorActiveBlockCanonicalLocalSymbolTradeGoal) :
    OddModulusToriV75PreCorrectionReturnInputsGoal :=
  oddModulusToriV75PreCorrectionReturnInputsGoal_of_preCorrection_return
    hHigh
    (BaseTail.Trades.successorActiveBlockCanonicalPreCorrectionGoal_of_canonicalLocalTrade
      hTrade)

theorem oddModulusToriV75PreCorrectionReturnInputsGoal_of_canonicalLocalTrade
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hTrade : BaseTail.Trades.SuccessorActiveBlockCanonicalLocalSymbolTradeGoal) :
    OddModulusToriV75PreCorrectionReturnInputsGoal :=
  oddModulusToriV75PreCorrectionReturnInputsGoal_of_canonicalLocalTrade_return
    hHigh hTrade

theorem oddModulusToriV75PreCorrectionReturnInputsGoal_of_reservoir_return
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hReservoir :
      BaseTail.Trades.SuccessorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal) :
    OddModulusToriV75PreCorrectionReturnInputsGoal :=
  oddModulusToriV75PreCorrectionReturnInputsGoal_of_preCorrection_return
    hHigh
    (BaseTail.Trades.successorActiveBlockCanonicalPreCorrectionGoal_of_finiteCoactiveSiteReservoir
      hReservoir)

theorem oddModulusToriV75PreCorrectionReturnInputsGoal_of_reservoir
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hReservoir :
      BaseTail.Trades.SuccessorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal) :
    OddModulusToriV75PreCorrectionReturnInputsGoal :=
  oddModulusToriV75PreCorrectionReturnInputsGoal_of_reservoir_return
    hHigh hReservoir

theorem oddModulusToriV75PreCorrectionReturnInputsGoal_of_worker1Residuals
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (h : OddSuccessorBaseTailWorker1CanonicalPreCorrectionReturnResidualGoal) :
    OddModulusToriV75PreCorrectionReturnInputsGoal :=
  ⟨hHigh, h.1⟩

theorem oddModulusToriV75PreCorrectionReturnInputsGoal_of_feasibleLocalTrade_return
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hFeasible : BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleResidueGoal)
    (hTrade :
      BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal) :
    OddModulusToriV75PreCorrectionReturnInputsGoal :=
  oddModulusToriV75PreCorrectionReturnInputsGoal_of_canonicalLocalTrade_return
    hHigh
    (BaseTail.Trades.successorActiveBlockCanonicalLocalSymbolTradeGoal_of_feasible_and_feasibleLocalTrade
      hFeasible hTrade)

theorem oddModulusToriV75PreCorrectionReturnInputsGoal_of_feasibleLocalTrade
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hFeasible : BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleResidueGoal)
    (hTrade :
      BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal) :
    OddModulusToriV75PreCorrectionReturnInputsGoal :=
  oddModulusToriV75PreCorrectionReturnInputsGoal_of_feasibleLocalTrade_return
    hHigh hFeasible hTrade

theorem oddModulusToriV75FeasibleLocalTradeReturnInputsGoal_of_feasibleLocalTradeInputs
    (h : OddModulusToriV75FeasibleLocalTradeInputsGoal) :
    OddModulusToriV75FeasibleLocalTradeReturnInputsGoal :=
  h

theorem oddModulusToriV75FeasibleFiniteCoactiveSiteReservoirReturnInputsGoal_of_feasibleFiniteCoactiveSiteReservoirInputs
    (h : OddModulusToriV75FeasibleFiniteCoactiveSiteReservoirInputsGoal) :
    OddModulusToriV75FeasibleFiniteCoactiveSiteReservoirReturnInputsGoal :=
  h

theorem oddModulusToriV75FeasibleLocalTradeReturnInputsGoal_of_feasibleFiniteCoactiveSiteReservoirReturnInputs
    (h : OddModulusToriV75FeasibleFiniteCoactiveSiteReservoirReturnInputsGoal) :
    OddModulusToriV75FeasibleLocalTradeReturnInputsGoal :=
  ⟨h.1, h.2.1,
    BaseTail.Trades.successorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal_of_feasibleFiniteCoactiveSiteReservoir
      h.2.2⟩

theorem oddModulusToriV75FeasibleLocalTradeReturnInputsGoal_of_feasibleFiniteCoactiveSiteReservoirInputs
    (h : OddModulusToriV75FeasibleFiniteCoactiveSiteReservoirInputsGoal) :
    OddModulusToriV75FeasibleLocalTradeReturnInputsGoal :=
  oddModulusToriV75FeasibleLocalTradeReturnInputsGoal_of_feasibleFiniteCoactiveSiteReservoirReturnInputs
    (oddModulusToriV75FeasibleFiniteCoactiveSiteReservoirReturnInputsGoal_of_feasibleFiniteCoactiveSiteReservoirInputs
      h)

theorem oddModulusToriV75FeasibleFiniteCoactiveSiteReservoirReturnInputsGoal_of_feasibleLocalTradeReturnInputs
    (h : OddModulusToriV75FeasibleLocalTradeReturnInputsGoal) :
    OddModulusToriV75FeasibleFiniteCoactiveSiteReservoirReturnInputsGoal :=
  ⟨h.1, h.2.1,
    BaseTail.Trades.successorActiveBlockCanonicalFeasibleFiniteCoactiveSiteReservoirGoal_of_feasibleLocalTrade
      h.2.2⟩

theorem oddModulusToriV75FeasibleFiniteCoactiveSiteReservoirReturnInputsGoal_iff_feasibleLocalTradeReturnInputs :
    OddModulusToriV75FeasibleFiniteCoactiveSiteReservoirReturnInputsGoal ↔
      OddModulusToriV75FeasibleLocalTradeReturnInputsGoal :=
  ⟨oddModulusToriV75FeasibleLocalTradeReturnInputsGoal_of_feasibleFiniteCoactiveSiteReservoirReturnInputs,
    oddModulusToriV75FeasibleFiniteCoactiveSiteReservoirReturnInputsGoal_of_feasibleLocalTradeReturnInputs⟩

theorem oddModulusToriV75PreCorrectionReturnInputsGoal_of_feasibleLocalTradeReturnInputs
    (h : OddModulusToriV75FeasibleLocalTradeReturnInputsGoal) :
    OddModulusToriV75PreCorrectionReturnInputsGoal :=
  oddModulusToriV75PreCorrectionReturnInputsGoal_of_feasibleLocalTrade_return
    h.1 h.2.1 h.2.2

theorem oddModulusToriV75PreCorrectionReturnInputsGoal_of_feasibleLocalTradeInputs
    (h : OddModulusToriV75FeasibleLocalTradeInputsGoal) :
    OddModulusToriV75PreCorrectionReturnInputsGoal :=
  oddModulusToriV75PreCorrectionReturnInputsGoal_of_feasibleLocalTradeReturnInputs
    (oddModulusToriV75FeasibleLocalTradeReturnInputsGoal_of_feasibleLocalTradeInputs
      h)

theorem oddModulusToriV75FeasibleLocalTradeReturnInputsGoal_of_scaledFeasibleLocalTradeReturnInputs
    (h : OddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal) :
    OddModulusToriV75FeasibleLocalTradeReturnInputsGoal :=
  ⟨h.1,
    BaseTail.Trades.successorActiveBlockCanonicalFeasibleResidueGoal_of_scaledFeasibleResidue
      h.2.1,
    h.2.2⟩

theorem oddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal_of_scaledFeasibleLocalTradeInputs
    (h : OddModulusToriV75ScaledFeasibleLocalTradeInputsGoal) :
    OddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal :=
  h

theorem oddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal_of_scaledFeasibleLocalTrade_return
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hScaled :
      BaseTail.Trades.SuccessorActiveBlockCanonicalScaledFeasibleResidueGoal)
    (hTrade :
      BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal) :
    OddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal :=
  ⟨hHigh, hScaled, hTrade⟩

theorem oddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal_of_scaledFeasibleLocalTrade
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hScaled :
      BaseTail.Trades.SuccessorActiveBlockCanonicalScaledFeasibleResidueGoal)
    (hTrade :
      BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal) :
    OddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal :=
  oddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal_of_scaledFeasibleLocalTrade_return
    hHigh hScaled hTrade

theorem oddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal_of_mixedControlledFeasibleLocalTradeReturnInputs
    (h : OddModulusToriV75MixedControlledFeasibleLocalTradeReturnInputsGoal) :
    OddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal := by
  refine ⟨h.1, ?_, h.2.2⟩
  intro b m T _inst packets Cyl hb5 hmodd hm3 hsmall hlen htotal
    hpacketSum hpacketUnits hPrefix hT hSlack hT2 hCyl hBlock
  have hMix : BaseTail.MixedExpansionData Cyl :=
    hBlock.mixedExpansionData_of_successor hT
  rcases
      BaseTail.Trades.activeBlockResidueSpec_compatible_primitive
        hCyl hBlock hT2 with
    ⟨hRow, hCol, hPrim⟩
  exact
    h.2.1 hb5 hmodd hm3 hsmall packets hlen htotal
      hpacketSum hpacketUnits hPrefix hT hSlack hCyl hBlock hMix hT2
      (BaseTail.Trades.activeBlockResidueSpec hBlock)
      hRow hCol hPrim.1 hPrim.2

theorem oddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal_of_mixedControlledFeasibleLocalTrade_return
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hRound : OddSuccessorBaseTailActiveBlockMixedControlledResidueRoundingGoal)
    (hTrade :
      BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal) :
    OddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal :=
  oddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal_of_mixedControlledFeasibleLocalTradeReturnInputs
    ⟨hHigh, hRound, hTrade⟩

theorem oddModulusToriV75MixedControlledFeasibleLocalTradeReturnInputsGoal_of_mixedControlledFeasibleLocalTradeInputs
    (h : OddModulusToriV75MixedControlledFeasibleLocalTradeInputsGoal) :
    OddModulusToriV75MixedControlledFeasibleLocalTradeReturnInputsGoal :=
  h

theorem oddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal_of_mixedControlledFeasibleLocalTradeInputs
    (h : OddModulusToriV75MixedControlledFeasibleLocalTradeInputsGoal) :
    OddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal :=
  oddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal_of_mixedControlledFeasibleLocalTradeReturnInputs
    (oddModulusToriV75MixedControlledFeasibleLocalTradeReturnInputsGoal_of_mixedControlledFeasibleLocalTradeInputs
      h)

theorem oddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal_of_mixedControlledFeasibleLocalTrade
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hRound : OddSuccessorBaseTailActiveBlockMixedControlledResidueRoundingGoal)
    (hTrade :
      BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal) :
    OddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal :=
  oddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal_of_mixedControlledFeasibleLocalTrade_return
    hHigh hRound hTrade

theorem oddModulusToriV75PreCorrectionReturnInputsGoal_of_scaledFeasibleLocalTradeReturnInputs
    (h : OddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal) :
    OddModulusToriV75PreCorrectionReturnInputsGoal :=
  oddModulusToriV75PreCorrectionReturnInputsGoal_of_feasibleLocalTradeReturnInputs
    (oddModulusToriV75FeasibleLocalTradeReturnInputsGoal_of_scaledFeasibleLocalTradeReturnInputs
      h)

theorem oddModulusToriV75DirectModularTradeBlocksGoal_of_reservoirInputs
    (h : OddModulusToriV75ReservoirInputsGoal) :
    OddModulusToriV75DirectModularTradeBlocksGoal :=
  oddModulusToriV75DirectModularTradeBlocksGoal_of_inputs
    (oddModulusToriV75DirectModularTradeInputsGoal_of_reservoirInputs h)

theorem oddModulusToriV75DirectModularTradeBlocksGoal_of_compatibleResidueSchedulingInputs
    (h : OddModulusToriV75CompatibleResidueSchedulingInputsGoal) :
    OddModulusToriV75DirectModularTradeBlocksGoal :=
  oddModulusToriV75DirectModularTradeBlocksGoal_of_inputs
    (oddModulusToriV75DirectModularTradeInputsGoal_of_compatibleResidueSchedulingInputs
      h)

theorem oddModulusToriV75DirectModularTradeBlocksGoal_of_reservoirSwapScheduleInputs
    (h : OddModulusToriV75ReservoirSwapScheduleInputsGoal) :
    OddModulusToriV75DirectModularTradeBlocksGoal :=
  oddModulusToriV75DirectModularTradeBlocksGoal_of_inputs
    (oddModulusToriV75DirectModularTradeInputsGoal_of_reservoirSwapScheduleInputs
      h)

theorem oddModulusToriV75DirectModularTradeBlocksGoal_of_preCorrectionInputs
    (h : OddModulusToriV75PreCorrectionInputsGoal) :
    OddModulusToriV75DirectModularTradeBlocksGoal :=
  oddModulusToriV75DirectModularTradeBlocksGoal_of_inputs
    (oddModulusToriV75DirectModularTradeInputsGoal_of_preCorrectionInputs h)

theorem oddModulusToriV75DirectModularTradeBlocksGoal_of_preCorrectionReturnInputs
    (h : OddModulusToriV75PreCorrectionReturnInputsGoal) :
    OddModulusToriV75DirectModularTradeBlocksGoal :=
  oddModulusToriV75DirectModularTradeBlocksGoal_of_inputs
    (oddModulusToriV75DirectModularTradeInputsGoal_of_preCorrectionReturnInputs h)

theorem oddModulusToriV75DirectModularTradeBlocksGoal_of_worker1Residuals
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (h : OddSuccessorBaseTailWorker1CanonicalPreCorrectionReturnResidualGoal) :
    OddModulusToriV75DirectModularTradeBlocksGoal :=
  oddModulusToriV75DirectModularTradeBlocksGoal_of_preCorrectionReturnInputs
    (oddModulusToriV75PreCorrectionReturnInputsGoal_of_worker1Residuals
      hHigh h)

theorem oddModulusToriV75DirectModularTradeBlocksGoal_of_feasibleLocalTradeReturnInputs
    (h : OddModulusToriV75FeasibleLocalTradeReturnInputsGoal) :
    OddModulusToriV75DirectModularTradeBlocksGoal :=
  oddModulusToriV75DirectModularTradeBlocksGoal_of_preCorrectionReturnInputs
    (oddModulusToriV75PreCorrectionReturnInputsGoal_of_feasibleLocalTradeReturnInputs
      h)

theorem oddModulusToriV75DirectModularTradeBlocksGoal_of_feasibleFiniteCoactiveSiteReservoirReturnInputs
    (h : OddModulusToriV75FeasibleFiniteCoactiveSiteReservoirReturnInputsGoal) :
    OddModulusToriV75DirectModularTradeBlocksGoal :=
  oddModulusToriV75DirectModularTradeBlocksGoal_of_feasibleLocalTradeReturnInputs
    (oddModulusToriV75FeasibleLocalTradeReturnInputsGoal_of_feasibleFiniteCoactiveSiteReservoirReturnInputs
      h)

theorem oddModulusToriV75DirectModularTradeBlocksGoal_of_feasibleFiniteCoactiveSiteReservoirInputs
    (h : OddModulusToriV75FeasibleFiniteCoactiveSiteReservoirInputsGoal) :
    OddModulusToriV75DirectModularTradeBlocksGoal :=
  oddModulusToriV75DirectModularTradeBlocksGoal_of_feasibleFiniteCoactiveSiteReservoirReturnInputs
    (oddModulusToriV75FeasibleFiniteCoactiveSiteReservoirReturnInputsGoal_of_feasibleFiniteCoactiveSiteReservoirInputs
      h)

theorem oddModulusToriV75DirectModularTradeBlocksGoal_of_scaledFeasibleLocalTradeReturnInputs
    (h : OddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal) :
    OddModulusToriV75DirectModularTradeBlocksGoal :=
  oddModulusToriV75DirectModularTradeBlocksGoal_of_feasibleLocalTradeReturnInputs
    (oddModulusToriV75FeasibleLocalTradeReturnInputsGoal_of_scaledFeasibleLocalTradeReturnInputs
      h)

theorem oddModulusToriV75DirectModularTradeBlocksGoal_of_scaledFeasibleLocalTrade_return
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hScaled :
      BaseTail.Trades.SuccessorActiveBlockCanonicalScaledFeasibleResidueGoal)
    (hTrade :
      BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal) :
    OddModulusToriV75DirectModularTradeBlocksGoal :=
  oddModulusToriV75DirectModularTradeBlocksGoal_of_scaledFeasibleLocalTradeReturnInputs
    (oddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal_of_scaledFeasibleLocalTrade_return
      hHigh hScaled hTrade)

theorem oddModulusToriV75DirectModularTradeBlocksGoal_of_scaledFeasibleLocalTrade
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hScaled :
      BaseTail.Trades.SuccessorActiveBlockCanonicalScaledFeasibleResidueGoal)
    (hTrade :
      BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal) :
    OddModulusToriV75DirectModularTradeBlocksGoal :=
  oddModulusToriV75DirectModularTradeBlocksGoal_of_scaledFeasibleLocalTradeReturnInputs
    (oddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal_of_scaledFeasibleLocalTrade
      hHigh hScaled hTrade)

theorem oddModulusToriV75DirectModularTradeBlocksGoal_of_mixedControlledFeasibleLocalTrade_return
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hRound : OddSuccessorBaseTailActiveBlockMixedControlledResidueRoundingGoal)
    (hTrade :
      BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal) :
    OddModulusToriV75DirectModularTradeBlocksGoal :=
  oddModulusToriV75DirectModularTradeBlocksGoal_of_scaledFeasibleLocalTradeReturnInputs
    (oddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal_of_mixedControlledFeasibleLocalTrade_return
      hHigh hRound hTrade)

theorem oddModulusToriV75DirectModularTradeBlocksGoal_of_mixedControlledFeasibleLocalTrade
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hRound : OddSuccessorBaseTailActiveBlockMixedControlledResidueRoundingGoal)
    (hTrade :
      BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal) :
    OddModulusToriV75DirectModularTradeBlocksGoal :=
  oddModulusToriV75DirectModularTradeBlocksGoal_of_scaledFeasibleLocalTradeReturnInputs
    (oddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal_of_mixedControlledFeasibleLocalTrade
      hHigh hRound hTrade)

theorem oddModulusToriV75DirectModularTradeBlocksGoal_of_canonicalLocalTrade_return
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hTrade : BaseTail.Trades.SuccessorActiveBlockCanonicalLocalSymbolTradeGoal) :
    OddModulusToriV75DirectModularTradeBlocksGoal :=
  oddModulusToriV75DirectModularTradeBlocksGoal_of_preCorrectionReturnInputs
    (oddModulusToriV75PreCorrectionReturnInputsGoal_of_canonicalLocalTrade_return
      hHigh hTrade)

theorem oddModulusToriV75DirectModularTradeBlocksGoal_of_canonicalLocalTrade
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hTrade : BaseTail.Trades.SuccessorActiveBlockCanonicalLocalSymbolTradeGoal) :
    OddModulusToriV75DirectModularTradeBlocksGoal :=
  oddModulusToriV75DirectModularTradeBlocksGoal_of_canonicalLocalTrade_return
    hHigh hTrade

theorem oddModulusToriV75DirectModularTradeBlocksGoal_of_compatibleResidueScheduling
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hSchedule :
      BaseTail.Trades.SuccessorActiveBlockCompatibleResidueSchedulingGoal) :
    OddModulusToriV75DirectModularTradeBlocksGoal :=
  oddModulusToriV75DirectModularTradeBlocksGoal_of_canonicalLocalTrade
    hHigh
    (BaseTail.Trades.successorActiveBlockCanonicalLocalSymbolTradeGoal_of_compatibleResidueScheduling
      hSchedule)

theorem oddModulusToriV75DirectModularTradeBlocksGoal_of_reservoirSwapSchedule
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hSchedule :
      BaseTail.Trades.SuccessorActiveBlockReservoirSwapScheduleGoal) :
    OddModulusToriV75DirectModularTradeBlocksGoal :=
  oddModulusToriV75DirectModularTradeBlocksGoal_of_reservoirSwapScheduleInputs
    ⟨hHigh, hSchedule⟩

theorem oddModulusToriV75DirectModularTradeBlocksGoal_of_localTrade_lowerTriangular
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hTrade : BaseTail.Trades.SuccessorActiveBlockCanonicalLocalSymbolTradeGoal) :
    OddModulusToriV75DirectModularTradeBlocksGoal :=
  oddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeLowerTriangularBlocksGoal_of_localTrade_lowerTriangular
    hHigh hTrade BaseTail.primitiveActivePrefixLowerTriangularLiftAssemblyGoal

/--
Broader v7.5 input package for a proof that realizes every compatible
successor residue schedule, not only the canonical active-block schedule.
-/
def OddModulusToriV75GeneralLocalTradeInputsGoal : Prop :=
  OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal ∧
  BaseTail.Trades.SuccessorActiveBlockLocalSymbolTradeGoal

theorem oddModulusToriV75DirectModularTradeBlocksGoal_of_generalLocalTrade
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hTrade : BaseTail.Trades.SuccessorActiveBlockLocalSymbolTradeGoal) :
    OddModulusToriV75DirectModularTradeBlocksGoal :=
  oddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeLowerTriangularBlocksGoal_of_successorLocalTrade_lowerTriangular
    hHigh hTrade BaseTail.primitiveActivePrefixLowerTriangularLiftAssemblyGoal

theorem oddModulusToriV75DirectModularTradeBlocksGoal_of_generalInputs
    (h : OddModulusToriV75GeneralLocalTradeInputsGoal) :
    OddModulusToriV75DirectModularTradeBlocksGoal :=
  oddModulusToriV75DirectModularTradeBlocksGoal_of_generalLocalTrade
    h.1 h.2

theorem oddSuccessorClosureGoal_of_v75_directModularTrade_blocks
    (hBlocks : OddModulusToriV75DirectModularTradeBlocksGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v73_returnTailClosedFullSupportTrellisCanonicalLocalTradeLowerTriangular_blocks
    hBlocks

theorem oddSuccessorClosureGoal_of_v75_worker1PreCorrectionReturnResiduals
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (h : OddSuccessorBaseTailWorker1CanonicalPreCorrectionReturnResidualGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v75_directModularTrade_blocks
    (oddModulusToriV75DirectModularTradeBlocksGoal_of_worker1Residuals
      hHigh h)

theorem oddSuccessorClosureGoal_of_v75_compatibleResidueScheduling_inputs
    (h : OddModulusToriV75CompatibleResidueSchedulingInputsGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v75_directModularTrade_blocks
    (oddModulusToriV75DirectModularTradeBlocksGoal_of_compatibleResidueSchedulingInputs
      h)

theorem oddSuccessorClosureGoal_of_v75_compatibleResidueScheduling
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hSchedule :
      BaseTail.Trades.SuccessorActiveBlockCompatibleResidueSchedulingGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v75_compatibleResidueScheduling_inputs
    ⟨hHigh, hSchedule⟩

theorem oddSuccessorClosureGoal_of_v75_reservoirSwapSchedule_inputs
    (h : OddModulusToriV75ReservoirSwapScheduleInputsGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v75_directModularTrade_blocks
    (oddModulusToriV75DirectModularTradeBlocksGoal_of_reservoirSwapScheduleInputs
      h)

theorem oddSuccessorClosureGoal_of_v75_reservoirSwapSchedule
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hSchedule :
      BaseTail.Trades.SuccessorActiveBlockReservoirSwapScheduleGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v75_reservoirSwapSchedule_inputs
    ⟨hHigh, hSchedule⟩

theorem oddSuccessorClosureGoal_of_v75_feasibleLocalTrade_return_inputs
    (h : OddModulusToriV75FeasibleLocalTradeReturnInputsGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v75_directModularTrade_blocks
    (oddModulusToriV75DirectModularTradeBlocksGoal_of_feasibleLocalTradeReturnInputs
      h)

theorem oddSuccessorClosureGoal_of_v75_feasibleFiniteCoactiveSiteReservoir_return_inputs
    (h : OddModulusToriV75FeasibleFiniteCoactiveSiteReservoirReturnInputsGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v75_feasibleLocalTrade_return_inputs
    (oddModulusToriV75FeasibleLocalTradeReturnInputsGoal_of_feasibleFiniteCoactiveSiteReservoirReturnInputs
      h)

theorem oddSuccessorClosureGoal_of_v75_feasibleFiniteCoactiveSiteReservoir_inputs
    (h : OddModulusToriV75FeasibleFiniteCoactiveSiteReservoirInputsGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v75_feasibleFiniteCoactiveSiteReservoir_return_inputs
    (oddModulusToriV75FeasibleFiniteCoactiveSiteReservoirReturnInputsGoal_of_feasibleFiniteCoactiveSiteReservoirInputs
      h)

theorem oddSuccessorClosureGoal_of_v75_scaledFeasibleLocalTrade_return_inputs
    (h : OddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v75_feasibleLocalTrade_return_inputs
    (oddModulusToriV75FeasibleLocalTradeReturnInputsGoal_of_scaledFeasibleLocalTradeReturnInputs
      h)

theorem oddSuccessorClosureGoal_of_v75_scaledFeasibleLocalTrade_return
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hScaled :
      BaseTail.Trades.SuccessorActiveBlockCanonicalScaledFeasibleResidueGoal)
    (hTrade :
      BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v75_scaledFeasibleLocalTrade_return_inputs
    (oddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal_of_scaledFeasibleLocalTrade_return
      hHigh hScaled hTrade)

theorem oddSuccessorClosureGoal_of_v75_scaledFeasibleLocalTrade
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hScaled :
      BaseTail.Trades.SuccessorActiveBlockCanonicalScaledFeasibleResidueGoal)
    (hTrade :
      BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v75_scaledFeasibleLocalTrade_return_inputs
    (oddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal_of_scaledFeasibleLocalTrade
      hHigh hScaled hTrade)

theorem oddSuccessorClosureGoal_of_v75_mixedControlledFeasibleLocalTrade_return
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hRound : OddSuccessorBaseTailActiveBlockMixedControlledResidueRoundingGoal)
    (hTrade :
      BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v75_scaledFeasibleLocalTrade_return_inputs
    (oddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal_of_mixedControlledFeasibleLocalTrade_return
      hHigh hRound hTrade)

theorem oddSuccessorClosureGoal_of_v75_mixedControlledFeasibleLocalTrade
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hRound : OddSuccessorBaseTailActiveBlockMixedControlledResidueRoundingGoal)
    (hTrade :
      BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v75_scaledFeasibleLocalTrade_return_inputs
    (oddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal_of_mixedControlledFeasibleLocalTrade
      hHigh hRound hTrade)

theorem odd_modulus_tori_all_dimensions_of_v75_directModularTrade_blocks
    (hBlocks : OddModulusToriV75DirectModularTradeBlocksGoal)
    {d m : Nat} (hd2 : 2 ≤ d)
    (hmodd : Odd m) (hm3 : 3 ≤ m) :
    Shared.CayleyHamiltonDecomposition d m :=
  odd_modulus_tori_all_dimensions_of_v73_returnTailClosedFullSupportTrellisCanonicalLocalTradeLowerTriangular_blocks
    hBlocks hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v75_directModularTrade_blocks
    (hBlocks : OddModulusToriV75DirectModularTradeBlocksGoal) :
    OddModulusToriAllDimensionsGoal := by
  intro d m hd2 hmodd hm3
  exact
    odd_modulus_tori_all_dimensions_of_v75_directModularTrade_blocks
      hBlocks hd2 hmodd hm3

theorem oddModulusToriAllDimensionsGoal_of_v75_directModularTrade_inputs
    (h : OddModulusToriV75DirectModularTradeInputsGoal) :
    OddModulusToriAllDimensionsGoal :=
  oddModulusToriAllDimensionsGoal_of_v75_directModularTrade_blocks
    (oddModulusToriV75DirectModularTradeBlocksGoal_of_inputs h)

theorem oddModulusToriAllDimensionsGoal_of_v75_reservoir_inputs
    (h : OddModulusToriV75ReservoirInputsGoal) :
    OddModulusToriAllDimensionsGoal :=
  oddModulusToriAllDimensionsGoal_of_v75_directModularTrade_inputs
    (oddModulusToriV75DirectModularTradeInputsGoal_of_reservoirInputs h)

theorem oddModulusToriAllDimensionsGoal_of_v75_compatibleResidueScheduling_inputs
    (h : OddModulusToriV75CompatibleResidueSchedulingInputsGoal) :
    OddModulusToriAllDimensionsGoal :=
  oddModulusToriAllDimensionsGoal_of_v75_directModularTrade_inputs
    (oddModulusToriV75DirectModularTradeInputsGoal_of_compatibleResidueSchedulingInputs
      h)

theorem oddModulusToriAllDimensionsGoal_of_v75_compatibleResidueScheduling
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hSchedule :
      BaseTail.Trades.SuccessorActiveBlockCompatibleResidueSchedulingGoal) :
    OddModulusToriAllDimensionsGoal :=
  oddModulusToriAllDimensionsGoal_of_v75_compatibleResidueScheduling_inputs
    ⟨hHigh, hSchedule⟩

theorem oddModulusToriAllDimensionsGoal_of_v75_reservoirSwapSchedule_inputs
    (h : OddModulusToriV75ReservoirSwapScheduleInputsGoal) :
    OddModulusToriAllDimensionsGoal :=
  oddModulusToriAllDimensionsGoal_of_v75_directModularTrade_inputs
    (oddModulusToriV75DirectModularTradeInputsGoal_of_reservoirSwapScheduleInputs
      h)

theorem oddModulusToriAllDimensionsGoal_of_v75_reservoirSwapSchedule
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hSchedule :
      BaseTail.Trades.SuccessorActiveBlockReservoirSwapScheduleGoal) :
    OddModulusToriAllDimensionsGoal :=
  oddModulusToriAllDimensionsGoal_of_v75_reservoirSwapSchedule_inputs
    ⟨hHigh, hSchedule⟩

theorem oddModulusToriAllDimensionsGoal_of_v75_preCorrection_inputs
    (h : OddModulusToriV75PreCorrectionInputsGoal) :
    OddModulusToriAllDimensionsGoal :=
  oddModulusToriAllDimensionsGoal_of_v75_directModularTrade_inputs
    (oddModulusToriV75DirectModularTradeInputsGoal_of_preCorrectionInputs h)

theorem oddModulusToriAllDimensionsGoal_of_v75_preCorrection_return_inputs
    (h : OddModulusToriV75PreCorrectionReturnInputsGoal) :
    OddModulusToriAllDimensionsGoal :=
  oddModulusToriAllDimensionsGoal_of_v75_directModularTrade_inputs
    (oddModulusToriV75DirectModularTradeInputsGoal_of_preCorrectionReturnInputs h)

theorem oddModulusToriAllDimensionsGoal_of_v75_feasibleLocalTrade_return_inputs
    (h : OddModulusToriV75FeasibleLocalTradeReturnInputsGoal) :
    OddModulusToriAllDimensionsGoal :=
  oddModulusToriAllDimensionsGoal_of_v75_preCorrection_return_inputs
    (oddModulusToriV75PreCorrectionReturnInputsGoal_of_feasibleLocalTradeReturnInputs
      h)

theorem oddModulusToriAllDimensionsGoal_of_v75_feasibleFiniteCoactiveSiteReservoir_return_inputs
    (h : OddModulusToriV75FeasibleFiniteCoactiveSiteReservoirReturnInputsGoal) :
    OddModulusToriAllDimensionsGoal :=
  oddModulusToriAllDimensionsGoal_of_v75_feasibleLocalTrade_return_inputs
    (oddModulusToriV75FeasibleLocalTradeReturnInputsGoal_of_feasibleFiniteCoactiveSiteReservoirReturnInputs
      h)

theorem oddModulusToriAllDimensionsGoal_of_v75_feasibleFiniteCoactiveSiteReservoir_inputs
    (h : OddModulusToriV75FeasibleFiniteCoactiveSiteReservoirInputsGoal) :
    OddModulusToriAllDimensionsGoal :=
  oddModulusToriAllDimensionsGoal_of_v75_feasibleFiniteCoactiveSiteReservoir_return_inputs
    (oddModulusToriV75FeasibleFiniteCoactiveSiteReservoirReturnInputsGoal_of_feasibleFiniteCoactiveSiteReservoirInputs
      h)

theorem oddModulusToriAllDimensionsGoal_of_v75_scaledFeasibleLocalTrade_return_inputs
    (h : OddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal) :
    OddModulusToriAllDimensionsGoal :=
  oddModulusToriAllDimensionsGoal_of_v75_feasibleLocalTrade_return_inputs
    (oddModulusToriV75FeasibleLocalTradeReturnInputsGoal_of_scaledFeasibleLocalTradeReturnInputs
      h)

theorem oddModulusToriAllDimensionsGoal_of_v75_scaledFeasibleLocalTrade_return
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hScaled :
      BaseTail.Trades.SuccessorActiveBlockCanonicalScaledFeasibleResidueGoal)
    (hTrade :
      BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal) :
    OddModulusToriAllDimensionsGoal :=
  oddModulusToriAllDimensionsGoal_of_v75_scaledFeasibleLocalTrade_return_inputs
    (oddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal_of_scaledFeasibleLocalTrade_return
      hHigh hScaled hTrade)

theorem oddModulusToriAllDimensionsGoal_of_v75_scaledFeasibleLocalTrade
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hScaled :
      BaseTail.Trades.SuccessorActiveBlockCanonicalScaledFeasibleResidueGoal)
    (hTrade :
      BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal) :
    OddModulusToriAllDimensionsGoal :=
  oddModulusToriAllDimensionsGoal_of_v75_scaledFeasibleLocalTrade_return_inputs
    (oddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal_of_scaledFeasibleLocalTrade
      hHigh hScaled hTrade)

theorem oddModulusToriAllDimensionsGoal_of_v75_mixedControlledFeasibleLocalTrade_return
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hRound : OddSuccessorBaseTailActiveBlockMixedControlledResidueRoundingGoal)
    (hTrade :
      BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal) :
    OddModulusToriAllDimensionsGoal :=
  oddModulusToriAllDimensionsGoal_of_v75_scaledFeasibleLocalTrade_return_inputs
    (oddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal_of_mixedControlledFeasibleLocalTrade_return
      hHigh hRound hTrade)

theorem oddModulusToriAllDimensionsGoal_of_v75_mixedControlledFeasibleLocalTrade
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hRound : OddSuccessorBaseTailActiveBlockMixedControlledResidueRoundingGoal)
    (hTrade :
      BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal) :
    OddModulusToriAllDimensionsGoal :=
  oddModulusToriAllDimensionsGoal_of_v75_scaledFeasibleLocalTrade_return_inputs
    (oddModulusToriV75ScaledFeasibleLocalTradeReturnInputsGoal_of_mixedControlledFeasibleLocalTrade
      hHigh hRound hTrade)

theorem oddModulusToriAllDimensionsGoal_of_v75_canonicalLocalTrade_return
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hTrade : BaseTail.Trades.SuccessorActiveBlockCanonicalLocalSymbolTradeGoal) :
    OddModulusToriAllDimensionsGoal :=
  oddModulusToriAllDimensionsGoal_of_v75_preCorrection_return_inputs
    (oddModulusToriV75PreCorrectionReturnInputsGoal_of_canonicalLocalTrade_return
      hHigh hTrade)

theorem oddModulusToriAllDimensionsGoal_of_v75_canonicalLocalTrade
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hTrade : BaseTail.Trades.SuccessorActiveBlockCanonicalLocalSymbolTradeGoal) :
    OddModulusToriAllDimensionsGoal :=
  oddModulusToriAllDimensionsGoal_of_v75_canonicalLocalTrade_return
    hHigh hTrade

theorem oddModulusToriAllDimensionsGoal_of_v75_reservoir_return
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hReservoir :
      BaseTail.Trades.SuccessorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal) :
    OddModulusToriAllDimensionsGoal :=
  oddModulusToriAllDimensionsGoal_of_v75_preCorrection_return_inputs
    (oddModulusToriV75PreCorrectionReturnInputsGoal_of_reservoir_return
      hHigh hReservoir)

theorem oddModulusToriAllDimensionsGoal_of_v75_worker1PreCorrectionReturnResiduals
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (h : OddSuccessorBaseTailWorker1CanonicalPreCorrectionReturnResidualGoal) :
    OddModulusToriAllDimensionsGoal :=
  oddModulusToriAllDimensionsGoal_of_v75_preCorrection_return_inputs
    (oddModulusToriV75PreCorrectionReturnInputsGoal_of_worker1Residuals
      hHigh h)

end Concrete
end RoundComposite
