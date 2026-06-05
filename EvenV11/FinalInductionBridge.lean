import EvenV11.ReturnCalculus
import EvenV11.UnitCarry
import EvenV11.WordSkew
import EvenV11.TerminalA2LowMod
import EvenV11.D54Reset
import EvenV11.EndpointCompletion
import EvenV11.EndpointMarkedTransferBridge
import EvenV11.PhaseProductRealizationBridge
import EvenV11.HighEvenSuccessorBridge

namespace EvenV11
namespace FinalInductionBridge

structure FinalReturnCoreInput : Prop where
  rootFlatReturnCriterionInput :
    ∀ {Color Direction RootState : Type} {m : Nat} [NeZero m]
      {S : Shared.RootFlatSchedule Color Direction RootState m},
      S.rowLatin →
      S.layerBijective →
      S.returnsSingleCycle →
      Shared.RootFlatReturnCriterion Color Direction RootState m
  rootFlatLayeredHamiltonianInput :
    ∀ {Color Direction RootState : Type} {m : Nat} [NeZero m]
      {S : Shared.RootFlatSchedule Color Direction RootState m},
      S.rowLatin →
      S.layerBijective →
      S.returnsSingleCycle →
      Shared.RootFlatLayeredHamiltonDecomposition
        Color Direction RootState m
  unitCarryInput :
    ∀ {Base : Type} {m : Nat} [NeZero m]
      (baseStep : Base → Base) (carry : Base → ZMod m)
      (base : Base) (period : Nat) (a : ZMod m),
      Function.Bijective baseStep →
      (baseStep^[period]) base = base →
      (∀ b : Base, ∃ k : Nat,
        k < period ∧ (baseStep^[k]) base = b) →
      IsUnit a →
      Shared.skewFiberAdditiveCarry baseStep carry period base = a →
      Shared.IsSingleCycleMap (additiveSkewMap baseStep carry)
  rankUnitCarryInput :
    ∀ {Base : Type} [Fintype Base]
      {N m : Nat} [NeZero N] [NeZero m]
      (baseStep : Base → Base) (rank : Base ≃ ZMod N)
      (carry : Base → ZMod m) (_base : Base),
      (∀ x : Base, rank (baseStep x) = rank x + 1) →
      IsUnit (∑ x : Base, carry x) →
      Shared.IsSingleCycleMap (additiveSkewMap baseStep carry)

theorem finalReturnCoreInput_holds :
    FinalReturnCoreInput where
  rootFlatReturnCriterionInput := rootFlatReturnCriterion
  rootFlatLayeredHamiltonianInput := rootFlatLayeredHamiltonian
  unitCarryInput := unitCarrySingleCycle
  rankUnitCarryInput := rankUnitCarrySingleCycle

structure FinalWordCoreInput : Prop where
  wordEvalBijectiveInput :
    ∀ {ι α : Type} (step : ι → α → α),
      (∀ i : ι, Function.Bijective (step i)) →
      ∀ word : List ι, Function.Bijective (wordEval step word)
  supportedWordInput :
    ∀ {ι α : Type} {S : Set α} (step : ι → α → α),
      (∀ i : ι, SupportedOn S (step i)) →
      ∀ word : List ι, SupportedOn S (wordEval step word)
  disjointWordCommuteInput :
    ∀ {ι κ α : Type} {S T : Set α}
      (leftStep : ι → α → α) (rightStep : κ → α → α),
      (∀ i : ι, SupportedOn S (leftStep i)) →
      (∀ j : κ, SupportedOn T (rightStep j)) →
      SetsDisjoint S T →
      (leftWord : List ι) →
      (rightWord : List κ) →
      Function.Commute
        (wordEval leftStep leftWord) (wordEval rightStep rightWord)
  disjointWordIterateCommuteInput :
    ∀ {ι κ α : Type} {S T : Set α}
      (leftStep : ι → α → α) (rightStep : κ → α → α),
      (∀ i : ι, SupportedOn S (leftStep i)) →
      (∀ j : κ, SupportedOn T (rightStep j)) →
      SetsDisjoint S T →
      (leftWord : List ι) →
      (rightWord : List κ) →
      (n k : Nat) →
      Function.Commute
        ((wordEval leftStep leftWord)^[n])
        ((wordEval rightStep rightWord)^[k])

theorem finalWordCoreInput_holds :
    FinalWordCoreInput where
  wordEvalBijectiveInput := wordEval_bijective
  supportedWordInput := supportedOn_wordEval
  disjointWordCommuteInput := commuteOfDisjointSupportedWordEvals
  disjointWordIterateCommuteInput :=
    commuteOfDisjointSupportedWordEvalIterates

structure FinalTerminalInput : Prop where
  terminalTrace4Cycle :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4) terminalTrace4)
  terminalTrace6Cycle :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 6) terminalTrace6)
  terminalResetTrace4Cycle :
    Shared.IsSingleCycleMap
      (wordEval (terminalSymbolStep 4) terminalResetTrace4)

theorem finalTerminalInput_holds :
    FinalTerminalInput where
  terminalTrace4Cycle := terminalTrace4_singleCycle
  terminalTrace6Cycle := terminalTrace6_singleCycle
  terminalResetTrace4Cycle := terminalResetTrace4_singleCycle

structure FinalEndpointInput : Prop where
  endpointMarkedTransferInput :
    EndpointMarkedTransferBridge.foldedEndpointMarkedTransferInputAudit
  phaseProductSupportInput :
    ∀ {Parent : Type} (parent : Parent)
      (h a m : Nat) [NeZero h] [NeZero m]
      (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m),
      PhaseDoublingProductSupportInput parent h a m hh ha hm
  phaseProductRealizationInput :
    ∀ {ι κ Parent : Type} (parent : Parent)
      (h a m : Nat) [NeZero h] [NeZero m]
      (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
      (T : Set Parent)
      (reserveStep : ι → Parent × PhaseSection h (m ^ a) →
        Parent × PhaseSection h (m ^ a))
      (protectedStep : κ → Parent × PhaseSection h (m ^ a) →
        Parent × PhaseSection h (m ^ a)),
      (∀ i : ι, SupportedOn
        (phaseProductReserveSupportCertificate
          parent h a m hh ha hm).supportSet (reserveStep i)) →
      (∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
        (protectedStep j)) →
      (reserveWord : List ι) →
      (protectedWord : List κ) →
      (n k : Nat) →
      PhaseDoublingProductRealizationInput parent h a m hh ha hm T
        reserveStep protectedStep reserveWord protectedWord n k
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

theorem finalEndpointInput_holds :
    FinalEndpointInput where
  endpointMarkedTransferInput :=
    foldedEndpointMarkedTransferInputAudit_holds
  phaseProductSupportInput :=
    phaseDoublingProductSupportInput_holds
  phaseProductRealizationInput :=
    phaseDoublingProductRealizationInput_holds
  completionCarryInput :=
    completionCarryCertificate_singleCycle
  b4FirstCompletionInput :=
    endpointB4FirstCompletionOnePointCertificate_singleCycle

structure FinalHighEvenInput : Prop where
  highEvenSuccessorInput : HighEvenSuccessorBridgeInput

theorem finalHighEvenInput_holds :
    FinalHighEvenInput where
  highEvenSuccessorInput := highEvenSuccessorBridgeInput_holds

structure FinalInductionInterfaceInput : Prop where
  returnCoreInput : FinalReturnCoreInput
  wordCoreInput : FinalWordCoreInput
  terminalInput : FinalTerminalInput
  endpointInput : FinalEndpointInput
  highEvenInput : FinalHighEvenInput

theorem finalInductionInterfaceInput_holds :
    FinalInductionInterfaceInput where
  returnCoreInput := finalReturnCoreInput_holds
  wordCoreInput := finalWordCoreInput_holds
  terminalInput := finalTerminalInput_holds
  endpointInput := finalEndpointInput_holds
  highEvenInput := finalHighEvenInput_holds

end FinalInductionBridge

export FinalInductionBridge
  (FinalReturnCoreInput FinalWordCoreInput FinalTerminalInput
   FinalEndpointInput FinalHighEvenInput FinalInductionInterfaceInput
   finalReturnCoreInput_holds finalWordCoreInput_holds
   finalTerminalInput_holds finalEndpointInput_holds
   finalHighEvenInput_holds finalInductionInterfaceInput_holds)

end EvenV11
