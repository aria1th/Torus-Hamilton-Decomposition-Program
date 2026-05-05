import RoundComposite.OddCore

set_option linter.style.longLine false

namespace RoundComposite
namespace Concrete

/--
v7.5 direct modular-trade input package.

This is the paper-facing small-modulus route after the active-Hall
count-matrix branch has been demoted from the live path.  The remaining inputs
are the high-modulus trellis/count branch, the successor-scoped canonical
active local-trade scheduler, and the lower-triangular base-tail lift.
-/
def OddModulusToriV75DirectModularTradeInputsGoal : Prop :=
  OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal ∧
  BaseTail.Trades.SuccessorActiveBlockCanonicalLocalSymbolTradeGoal ∧
  BaseTail.PrimitiveActivePrefixLowerTriangularLiftAssemblyGoal

/--
v7.5 input package using the paper-facing finite coactive-site reservoir name.
-/
def OddModulusToriV75ReservoirInputsGoal : Prop :=
  OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal ∧
  BaseTail.Trades.SuccessorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal ∧
  BaseTail.PrimitiveActivePrefixLowerTriangularLiftAssemblyGoal

/--
v7.5 input package using the one-site pre-correction reservoir surface.
-/
def OddModulusToriV75PreCorrectionInputsGoal : Prop :=
  OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal ∧
  BaseTail.Trades.SuccessorActiveBlockCanonicalPreCorrectionGoal ∧
  BaseTail.PrimitiveActivePrefixLowerTriangularLiftAssemblyGoal

/--
v7.5 input package using both narrowed live residuals: one-site
pre-correction on the trade side and return-only lower-triangular data on the
base-tail side.
-/
def OddModulusToriV75PreCorrectionReturnInputsGoal : Prop :=
  OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal ∧
  BaseTail.Trades.SuccessorActiveBlockCanonicalPreCorrectionGoal ∧
  BaseTail.ActivePrefixPermutedColorDirFiberLowerTriangularReturnGoal

/--
v7.5 input package splitting the Worker A local-trade surface into the
canonical feasible residue endpoint and the successor-scoped feasible local
symboling theorem, while keeping Worker B's return-only lift residual.
-/
def OddModulusToriV75FeasibleLocalTradeReturnInputsGoal : Prop :=
  OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal ∧
  BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleResidueGoal ∧
  BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal ∧
  BaseTail.ActivePrefixPermutedColorDirFiberLowerTriangularReturnGoal

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
    h.1 h.2.1 h.2.2

theorem oddModulusToriV75DirectModularTradeInputsGoal_of_reservoirInputs
    (h : OddModulusToriV75ReservoirInputsGoal) :
    OddModulusToriV75DirectModularTradeInputsGoal :=
  ⟨h.1,
    BaseTail.Trades.successorActiveBlockCanonicalLocalSymbolTradeGoal_of_finiteCoactiveSiteReservoir
      h.2.1,
    h.2.2⟩

theorem oddModulusToriV75ReservoirInputsGoal_of_directInputs
    (h : OddModulusToriV75DirectModularTradeInputsGoal) :
    OddModulusToriV75ReservoirInputsGoal :=
  ⟨h.1, h.2.1, h.2.2⟩

theorem oddModulusToriV75ReservoirInputsGoal_iff_directInputs :
    OddModulusToriV75ReservoirInputsGoal ↔
      OddModulusToriV75DirectModularTradeInputsGoal :=
  ⟨oddModulusToriV75DirectModularTradeInputsGoal_of_reservoirInputs,
    oddModulusToriV75ReservoirInputsGoal_of_directInputs⟩

theorem oddModulusToriV75DirectModularTradeInputsGoal_of_preCorrectionInputs
    (h : OddModulusToriV75PreCorrectionInputsGoal) :
    OddModulusToriV75DirectModularTradeInputsGoal :=
  ⟨h.1,
    BaseTail.Trades.successorActiveBlockCanonicalLocalSymbolTradeGoal_of_preCorrection
      h.2.1,
    h.2.2⟩

theorem oddModulusToriV75PreCorrectionInputsGoal_of_directInputs
    (h : OddModulusToriV75DirectModularTradeInputsGoal) :
    OddModulusToriV75PreCorrectionInputsGoal :=
  ⟨h.1,
    BaseTail.Trades.successorActiveBlockCanonicalPreCorrectionGoal_of_canonicalLocalTrade
      h.2.1,
    h.2.2⟩

theorem oddModulusToriV75PreCorrectionInputsGoal_iff_directInputs :
    OddModulusToriV75PreCorrectionInputsGoal ↔
      OddModulusToriV75DirectModularTradeInputsGoal :=
  ⟨oddModulusToriV75DirectModularTradeInputsGoal_of_preCorrectionInputs,
    oddModulusToriV75PreCorrectionInputsGoal_of_directInputs⟩

theorem oddModulusToriV75PreCorrectionInputsGoal_of_preCorrectionReturnInputs
    (h : OddModulusToriV75PreCorrectionReturnInputsGoal) :
    OddModulusToriV75PreCorrectionInputsGoal :=
  ⟨h.1,
    h.2.1,
    BaseTail.primitiveActivePrefixLowerTriangularLiftAssemblyGoal_of_activePrefixPermutedFiberReturn
      h.2.2⟩

theorem oddModulusToriV75DirectModularTradeInputsGoal_of_preCorrectionReturnInputs
    (h : OddModulusToriV75PreCorrectionReturnInputsGoal) :
    OddModulusToriV75DirectModularTradeInputsGoal :=
  oddModulusToriV75DirectModularTradeInputsGoal_of_preCorrectionInputs
    (oddModulusToriV75PreCorrectionInputsGoal_of_preCorrectionReturnInputs h)

theorem oddModulusToriV75PreCorrectionReturnInputsGoal_of_preCorrection_return
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hTrade : BaseTail.Trades.SuccessorActiveBlockCanonicalPreCorrectionGoal)
    (hReturn : BaseTail.ActivePrefixPermutedColorDirFiberLowerTriangularReturnGoal) :
    OddModulusToriV75PreCorrectionReturnInputsGoal :=
  ⟨hHigh, hTrade, hReturn⟩

theorem oddModulusToriV75PreCorrectionReturnInputsGoal_of_canonicalLocalTrade_return
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hTrade : BaseTail.Trades.SuccessorActiveBlockCanonicalLocalSymbolTradeGoal)
    (hReturn : BaseTail.ActivePrefixPermutedColorDirFiberLowerTriangularReturnGoal) :
    OddModulusToriV75PreCorrectionReturnInputsGoal :=
  oddModulusToriV75PreCorrectionReturnInputsGoal_of_preCorrection_return
    hHigh
    (BaseTail.Trades.successorActiveBlockCanonicalPreCorrectionGoal_of_canonicalLocalTrade
      hTrade)
    hReturn

theorem oddModulusToriV75PreCorrectionReturnInputsGoal_of_reservoir_return
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hReservoir :
      BaseTail.Trades.SuccessorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal)
    (hReturn : BaseTail.ActivePrefixPermutedColorDirFiberLowerTriangularReturnGoal) :
    OddModulusToriV75PreCorrectionReturnInputsGoal :=
  oddModulusToriV75PreCorrectionReturnInputsGoal_of_preCorrection_return
    hHigh
    (BaseTail.Trades.successorActiveBlockCanonicalPreCorrectionGoal_of_finiteCoactiveSiteReservoir
      hReservoir)
    hReturn

theorem oddModulusToriV75PreCorrectionReturnInputsGoal_of_worker1Residuals
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (h : OddSuccessorBaseTailWorker1CanonicalPreCorrectionReturnResidualGoal) :
    OddModulusToriV75PreCorrectionReturnInputsGoal :=
  ⟨hHigh, h.1, h.2⟩

theorem oddModulusToriV75PreCorrectionReturnInputsGoal_of_feasibleLocalTrade_return
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hFeasible : BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleResidueGoal)
    (hTrade :
      BaseTail.Trades.SuccessorActiveBlockCanonicalFeasibleLocalSymbolTradeGoal)
    (hReturn : BaseTail.ActivePrefixPermutedColorDirFiberLowerTriangularReturnGoal) :
    OddModulusToriV75PreCorrectionReturnInputsGoal :=
  oddModulusToriV75PreCorrectionReturnInputsGoal_of_canonicalLocalTrade_return
    hHigh
    (BaseTail.Trades.successorActiveBlockCanonicalLocalSymbolTradeGoal_of_feasible_and_feasibleLocalTrade
      hFeasible hTrade)
    hReturn

theorem oddModulusToriV75PreCorrectionReturnInputsGoal_of_feasibleLocalTradeReturnInputs
    (h : OddModulusToriV75FeasibleLocalTradeReturnInputsGoal) :
    OddModulusToriV75PreCorrectionReturnInputsGoal :=
  oddModulusToriV75PreCorrectionReturnInputsGoal_of_feasibleLocalTrade_return
    h.1 h.2.1 h.2.2.1 h.2.2.2

theorem oddModulusToriV75DirectModularTradeBlocksGoal_of_reservoirInputs
    (h : OddModulusToriV75ReservoirInputsGoal) :
    OddModulusToriV75DirectModularTradeBlocksGoal :=
  oddModulusToriV75DirectModularTradeBlocksGoal_of_inputs
    (oddModulusToriV75DirectModularTradeInputsGoal_of_reservoirInputs h)

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

theorem oddModulusToriV75DirectModularTradeBlocksGoal_of_canonicalLocalTrade_return
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hTrade : BaseTail.Trades.SuccessorActiveBlockCanonicalLocalSymbolTradeGoal)
    (hReturn : BaseTail.ActivePrefixPermutedColorDirFiberLowerTriangularReturnGoal) :
    OddModulusToriV75DirectModularTradeBlocksGoal :=
  oddModulusToriV75DirectModularTradeBlocksGoal_of_preCorrectionReturnInputs
    (oddModulusToriV75PreCorrectionReturnInputsGoal_of_canonicalLocalTrade_return
      hHigh hTrade hReturn)

theorem oddModulusToriV75DirectModularTradeBlocksGoal_of_localTrade_lowerTriangular
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hTrade : BaseTail.Trades.SuccessorActiveBlockCanonicalLocalSymbolTradeGoal)
    (hLift : BaseTail.PrimitiveActivePrefixLowerTriangularLiftAssemblyGoal) :
    OddModulusToriV75DirectModularTradeBlocksGoal :=
  oddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeLowerTriangularBlocksGoal_of_localTrade_lowerTriangular
    hHigh hTrade hLift

/--
Broader v7.5 input package for a proof that realizes every compatible
successor residue schedule, not only the canonical active-block schedule.
-/
def OddModulusToriV75GeneralLocalTradeInputsGoal : Prop :=
  OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal ∧
  BaseTail.Trades.SuccessorActiveBlockLocalSymbolTradeGoal ∧
  BaseTail.PrimitiveActivePrefixLowerTriangularLiftAssemblyGoal

theorem oddModulusToriV75DirectModularTradeBlocksGoal_of_generalLocalTrade
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hTrade : BaseTail.Trades.SuccessorActiveBlockLocalSymbolTradeGoal)
    (hLift : BaseTail.PrimitiveActivePrefixLowerTriangularLiftAssemblyGoal) :
    OddModulusToriV75DirectModularTradeBlocksGoal :=
  oddModulusToriV73ReturnTailClosedFullSupportTrellisCanonicalLocalTradeLowerTriangularBlocksGoal_of_successorLocalTrade_lowerTriangular
    hHigh hTrade hLift

theorem oddModulusToriV75DirectModularTradeBlocksGoal_of_generalInputs
    (h : OddModulusToriV75GeneralLocalTradeInputsGoal) :
    OddModulusToriV75DirectModularTradeBlocksGoal :=
  oddModulusToriV75DirectModularTradeBlocksGoal_of_generalLocalTrade
    h.1 h.2.1 h.2.2

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

theorem oddSuccessorClosureGoal_of_v75_feasibleLocalTrade_return_inputs
    (h : OddModulusToriV75FeasibleLocalTradeReturnInputsGoal) :
    OddSuccessorClosureGoal :=
  oddSuccessorClosureGoal_of_v75_directModularTrade_blocks
    (oddModulusToriV75DirectModularTradeBlocksGoal_of_feasibleLocalTradeReturnInputs
      h)

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

theorem oddModulusToriAllDimensionsGoal_of_v75_canonicalLocalTrade_return
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hTrade : BaseTail.Trades.SuccessorActiveBlockCanonicalLocalSymbolTradeGoal)
    (hReturn : BaseTail.ActivePrefixPermutedColorDirFiberLowerTriangularReturnGoal) :
    OddModulusToriAllDimensionsGoal :=
  oddModulusToriAllDimensionsGoal_of_v75_preCorrection_return_inputs
    (oddModulusToriV75PreCorrectionReturnInputsGoal_of_canonicalLocalTrade_return
      hHigh hTrade hReturn)

theorem oddModulusToriAllDimensionsGoal_of_v75_reservoir_return
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (hReservoir :
      BaseTail.Trades.SuccessorActiveBlockCanonicalFiniteCoactiveSiteReservoirGoal)
    (hReturn : BaseTail.ActivePrefixPermutedColorDirFiberLowerTriangularReturnGoal) :
    OddModulusToriAllDimensionsGoal :=
  oddModulusToriAllDimensionsGoal_of_v75_preCorrection_return_inputs
    (oddModulusToriV75PreCorrectionReturnInputsGoal_of_reservoir_return
      hHigh hReservoir hReturn)

theorem oddModulusToriAllDimensionsGoal_of_v75_worker1PreCorrectionReturnResiduals
    (hHigh : OddCoreHighModulusReturnTailClosedFullSupportTrellisBlocksGoal)
    (h : OddSuccessorBaseTailWorker1CanonicalPreCorrectionReturnResidualGoal) :
    OddModulusToriAllDimensionsGoal :=
  oddModulusToriAllDimensionsGoal_of_v75_preCorrection_return_inputs
    (oddModulusToriV75PreCorrectionReturnInputsGoal_of_worker1Residuals
      hHigh h)

end Concrete
end RoundComposite
