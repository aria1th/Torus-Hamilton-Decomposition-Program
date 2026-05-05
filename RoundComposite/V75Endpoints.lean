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

theorem oddModulusToriV75DirectModularTradeBlocksGoal_of_reservoirInputs
    (h : OddModulusToriV75ReservoirInputsGoal) :
    OddModulusToriV75DirectModularTradeBlocksGoal :=
  oddModulusToriV75DirectModularTradeBlocksGoal_of_inputs
    (oddModulusToriV75DirectModularTradeInputsGoal_of_reservoirInputs h)

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

end Concrete
end RoundComposite
