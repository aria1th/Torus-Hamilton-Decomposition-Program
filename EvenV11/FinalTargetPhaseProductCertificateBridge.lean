import EvenV11.FinalTargetHighEvenCertificateBridge

namespace EvenV11
namespace FinalTargetPhaseProductCertificateBridge

structure FinalPhaseProductCertificateInputs : Prop where
  supportInput :
    ∀ {Parent : Type} (parent : Parent)
      (h a m : Nat) [NeZero h] [NeZero m]
      (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m),
      PhaseDoublingProductSupportInput parent h a m hh ha hm
  realizationInput :
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

theorem finalPhaseProductCertificateInputs_of_endpointCertificate
    (input : FinalOddEndpointCertificateInputs) :
    FinalPhaseProductCertificateInputs where
  supportInput := input.phaseProductSupportInput
  realizationInput := input.phaseProductRealizationInput

theorem finalPhaseProductCertificateInputs_holds :
    FinalPhaseProductCertificateInputs :=
  finalPhaseProductCertificateInputs_of_endpointCertificate
    finalOddEndpointCertificateInputs_holds

theorem finalPhaseProductCertificateSupport
    (input : FinalPhaseProductCertificateInputs)
    {Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    PhaseDoublingProductSupportInput parent h a m hh ha hm :=
  input.supportInput parent h a m hh ha hm

theorem finalPhaseProductCertificateSupportSetEq
    (input : FinalPhaseProductCertificateInputs)
    {Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    (phaseProductReserveSupportCertificate parent h a m hh ha hm).supportSet =
      phaseProductReserveLineSlotPointSet parent h a m ha hm :=
  (finalPhaseProductCertificateSupport input parent h a m hh ha hm).supportSet_eq

theorem finalPhaseProductCertificateSupportPointListLength
    (input : FinalPhaseProductCertificateInputs)
    {Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    (phaseProductReserveLineSlotPointList parent h a m ha hm).length =
      2 * a + 3 :=
  (finalPhaseProductCertificateSupport input parent h a m hh ha hm).supportPointList_length

theorem finalPhaseProductCertificateSupportPointListNodup
    (input : FinalPhaseProductCertificateInputs)
    {Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    (phaseProductReserveLineSlotPointList parent h a m ha hm).Nodup :=
  (finalPhaseProductCertificateSupport input parent h a m hh ha hm).supportPointList_nodup

theorem finalPhaseProductCertificateSubsetReserveCylinder
    (input : FinalPhaseProductCertificateInputs)
    {Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    (phaseProductReserveSupportCertificate parent h a m hh ha hm).supportSet ⊆
      ProductCylinder ({parent} : Set Parent)
        (PhaseLine (h := h) (M := m ^ a) (2 : ZMod h)) :=
  (finalPhaseProductCertificateSupport input parent h a m hh ha hm).subsetReserveCylinder

theorem finalPhaseProductCertificateConstantParentProjection
    (input : FinalPhaseProductCertificateInputs)
    {Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    ProjectionConstantOn
      (fun x : Parent × PhaseSection h (m ^ a) => x.1)
      (phaseProductReserveSupportCertificate parent h a m hh ha hm).supportSet
      parent :=
  (finalPhaseProductCertificateSupport input parent h a m hh ha hm).constantParentProjection

theorem finalPhaseProductCertificateConstantPhaseProjection
    (input : FinalPhaseProductCertificateInputs)
    {Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    ProjectionConstantOn
      (fun x : Parent × PhaseSection h (m ^ a) => phaseProjection x.2)
      (phaseProductReserveSupportCertificate parent h a m hh ha hm).supportSet
      (2 : ZMod h) :=
  (finalPhaseProductCertificateSupport input parent h a m hh ha hm).constantPhaseProjection

theorem finalPhaseProductCertificateDisjointFromProtectedCylinder
    (input : FinalPhaseProductCertificateInputs)
    {Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent) :
    SetsDisjoint
      (phaseProductReserveSupportCertificate parent h a m hh ha hm).supportSet
      (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :=
  (finalPhaseProductCertificateSupport input parent h a m hh ha hm).disjointFromProtectedCylinder T

theorem finalPhaseProductCertificateExistsUniqueSlot
    (input : FinalPhaseProductCertificateInputs)
    {Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈
      (phaseProductReserveSupportCertificate parent h a m hh ha hm).supportSet) :
    ∃! i : Fin (2 * a + 3),
      (phaseProductReserveLineSlot parent h a m ha hm i).1 = x :=
  (finalPhaseProductCertificateSupport input parent h a m hh ha hm).existsUniqueSlot hx

theorem finalPhaseProductCertificatePointInjective
    (input : FinalPhaseProductCertificateInputs)
    {Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    Function.Injective
      (fun i : Fin (2 * a + 3) =>
        (phaseProductReserveLineSlot parent h a m ha hm i).1) :=
  (finalPhaseProductCertificateSupport input parent h a m hh ha hm).pointInjective

theorem finalPhaseProductCertificatePairInjective
    (input : FinalPhaseProductCertificateInputs)
    {Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    Function.Injective
      (fun i : Fin (2 * a + 3) =>
        (parent, (phaseProductReserveLineSlot parent h a m ha hm i).1.2)) :=
  (finalPhaseProductCertificateSupport input parent h a m hh ha hm).pairInjective

theorem finalPhaseProductCertificateRealization
    (input : FinalPhaseProductCertificateInputs)
    {ι κ Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (reserveStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (protectedStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hreserve :
      ∀ i : ι, SupportedOn
        (phaseProductReserveSupportCertificate
          parent h a m hh ha hm).supportSet (reserveStep i))
    (hprotected :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
        (protectedStep j))
    (reserveWord : List ι) (protectedWord : List κ)
    (n k : Nat) :
    PhaseDoublingProductRealizationInput parent h a m hh ha hm T
      reserveStep protectedStep reserveWord protectedWord n k :=
  input.realizationInput parent h a m hh ha hm T reserveStep
    protectedStep hreserve hprotected reserveWord protectedWord n k

theorem finalPhaseProductCertificateRealizationSupport
    (input : FinalPhaseProductCertificateInputs)
    {ι κ Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (reserveStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (protectedStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hreserve :
      ∀ i : ι, SupportedOn
        (phaseProductReserveSupportCertificate
          parent h a m hh ha hm).supportSet (reserveStep i))
    (hprotected :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
        (protectedStep j))
    (reserveWord : List ι) (protectedWord : List κ)
    (n k : Nat) :
    PhaseDoublingProductSupportInput parent h a m hh ha hm :=
  (finalPhaseProductCertificateRealization input parent h a m hh ha hm T
    reserveStep protectedStep hreserve hprotected reserveWord protectedWord
    n k).supportInput

theorem finalPhaseProductCertificateProtectedWordFixesReserveSupport
    (input : FinalPhaseProductCertificateInputs)
    {ι κ Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (reserveStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (protectedStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hreserve :
      ∀ i : ι, SupportedOn
        (phaseProductReserveSupportCertificate
          parent h a m hh ha hm).supportSet (reserveStep i))
    (hprotected :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
        (protectedStep j))
    (reserveWord : List ι) (protectedWord : List κ)
    (n k : Nat)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈
      (phaseProductReserveSupportCertificate parent h a m hh ha hm).supportSet) :
    wordEval protectedStep protectedWord x = x :=
  (finalPhaseProductCertificateRealization input parent h a m hh ha hm T
    reserveStep protectedStep hreserve hprotected reserveWord protectedWord
    n k).protectedWordFixesReserveSupport hx

theorem finalPhaseProductCertificateProtectedWordIterFixesReserveSupport
    (input : FinalPhaseProductCertificateInputs)
    {ι κ Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (reserveStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (protectedStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hreserve :
      ∀ i : ι, SupportedOn
        (phaseProductReserveSupportCertificate
          parent h a m hh ha hm).supportSet (reserveStep i))
    (hprotected :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
        (protectedStep j))
    (reserveWord : List ι) (protectedWord : List κ)
    (n k : Nat)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈
      (phaseProductReserveSupportCertificate parent h a m hh ha hm).supportSet) :
    ((wordEval protectedStep protectedWord)^[k]) x = x :=
  (finalPhaseProductCertificateRealization input parent h a m hh ha hm T
    reserveStep protectedStep hreserve hprotected reserveWord protectedWord
    n k).protectedWordIterFixesReserveSupport hx

theorem finalPhaseProductCertificateProtectedWordMapsReserveSupport
    (input : FinalPhaseProductCertificateInputs)
    {ι κ Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (reserveStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (protectedStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hreserve :
      ∀ i : ι, SupportedOn
        (phaseProductReserveSupportCertificate
          parent h a m hh ha hm).supportSet (reserveStep i))
    (hprotected :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
        (protectedStep j))
    (reserveWord : List ι) (protectedWord : List κ)
    (n k : Nat) :
    MapsInto
      (phaseProductReserveSupportCertificate
        parent h a m hh ha hm).supportSet
      (wordEval protectedStep protectedWord) :=
  (finalPhaseProductCertificateRealization input parent h a m hh ha hm T
    reserveStep protectedStep hreserve hprotected reserveWord protectedWord
    n k).protectedWordMapsReserveSupport

theorem finalPhaseProductCertificateProtectedWordIterMapsReserveSupport
    (input : FinalPhaseProductCertificateInputs)
    {ι κ Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (reserveStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (protectedStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hreserve :
      ∀ i : ι, SupportedOn
        (phaseProductReserveSupportCertificate
          parent h a m hh ha hm).supportSet (reserveStep i))
    (hprotected :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
        (protectedStep j))
    (reserveWord : List ι) (protectedWord : List κ)
    (n k : Nat) :
    MapsInto
      (phaseProductReserveSupportCertificate
        parent h a m hh ha hm).supportSet
      ((wordEval protectedStep protectedWord)^[k]) :=
  (finalPhaseProductCertificateRealization input parent h a m hh ha hm T
    reserveStep protectedStep hreserve hprotected reserveWord protectedWord
    n k).protectedWordIterMapsReserveSupport

theorem finalPhaseProductCertificateReserveWordFixesProtectedCylinder
    (input : FinalPhaseProductCertificateInputs)
    {ι κ Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (reserveStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (protectedStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hreserve :
      ∀ i : ι, SupportedOn
        (phaseProductReserveSupportCertificate
          parent h a m hh ha hm).supportSet (reserveStep i))
    (hprotected :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
        (protectedStep j))
    (reserveWord : List ι) (protectedWord : List κ)
    (n k : Nat)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :
    wordEval reserveStep reserveWord x = x :=
  (finalPhaseProductCertificateRealization input parent h a m hh ha hm T
    reserveStep protectedStep hreserve hprotected reserveWord protectedWord
    n k).reserveWordFixesProtectedCylinder hx

theorem finalPhaseProductCertificateReserveWordIterFixesProtectedCylinder
    (input : FinalPhaseProductCertificateInputs)
    {ι κ Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (reserveStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (protectedStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hreserve :
      ∀ i : ι, SupportedOn
        (phaseProductReserveSupportCertificate
          parent h a m hh ha hm).supportSet (reserveStep i))
    (hprotected :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
        (protectedStep j))
    (reserveWord : List ι) (protectedWord : List κ)
    (n k : Nat)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :
    ((wordEval reserveStep reserveWord)^[n]) x = x :=
  (finalPhaseProductCertificateRealization input parent h a m hh ha hm T
    reserveStep protectedStep hreserve hprotected reserveWord protectedWord
    n k).reserveWordIterFixesProtectedCylinder hx

theorem finalPhaseProductCertificateReserveWordMapsProtectedCylinder
    (input : FinalPhaseProductCertificateInputs)
    {ι κ Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (reserveStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (protectedStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hreserve :
      ∀ i : ι, SupportedOn
        (phaseProductReserveSupportCertificate
          parent h a m hh ha hm).supportSet (reserveStep i))
    (hprotected :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
        (protectedStep j))
    (reserveWord : List ι) (protectedWord : List κ)
    (n k : Nat) :
    MapsInto (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
      (wordEval reserveStep reserveWord) :=
  (finalPhaseProductCertificateRealization input parent h a m hh ha hm T
    reserveStep protectedStep hreserve hprotected reserveWord protectedWord
    n k).reserveWordMapsProtectedCylinder

theorem finalPhaseProductCertificateReserveWordIterMapsProtectedCylinder
    (input : FinalPhaseProductCertificateInputs)
    {ι κ Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (reserveStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (protectedStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hreserve :
      ∀ i : ι, SupportedOn
        (phaseProductReserveSupportCertificate
          parent h a m hh ha hm).supportSet (reserveStep i))
    (hprotected :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
        (protectedStep j))
    (reserveWord : List ι) (protectedWord : List κ)
    (n k : Nat) :
    MapsInto (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
      ((wordEval reserveStep reserveWord)^[n]) :=
  (finalPhaseProductCertificateRealization input parent h a m hh ha hm T
    reserveStep protectedStep hreserve hprotected reserveWord protectedWord
    n k).reserveWordIterMapsProtectedCylinder

theorem finalPhaseProductCertificateReserveWordCommutesProtectedWord
    (input : FinalPhaseProductCertificateInputs)
    {ι κ Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (reserveStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (protectedStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hreserve :
      ∀ i : ι, SupportedOn
        (phaseProductReserveSupportCertificate
          parent h a m hh ha hm).supportSet (reserveStep i))
    (hprotected :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
        (protectedStep j))
    (reserveWord : List ι) (protectedWord : List κ)
    (n k : Nat) :
    Function.Commute
      (wordEval reserveStep reserveWord) (wordEval protectedStep protectedWord) :=
  (finalPhaseProductCertificateRealization input parent h a m hh ha hm T
    reserveStep protectedStep hreserve hprotected reserveWord protectedWord
    n k).reserveWordCommutesProtectedWord

theorem finalPhaseProductCertificateProtectedWordCommutesReserveWord
    (input : FinalPhaseProductCertificateInputs)
    {ι κ Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (reserveStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (protectedStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hreserve :
      ∀ i : ι, SupportedOn
        (phaseProductReserveSupportCertificate
          parent h a m hh ha hm).supportSet (reserveStep i))
    (hprotected :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
        (protectedStep j))
    (reserveWord : List ι) (protectedWord : List κ)
    (n k : Nat) :
    Function.Commute
      (wordEval protectedStep protectedWord) (wordEval reserveStep reserveWord) :=
  (finalPhaseProductCertificateRealization input parent h a m hh ha hm T
    reserveStep protectedStep hreserve hprotected reserveWord protectedWord
    n k).protectedWordCommutesReserveWord

theorem finalPhaseProductCertificateReserveWordIterCommutesProtectedWordIter
    (input : FinalPhaseProductCertificateInputs)
    {ι κ Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (reserveStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (protectedStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hreserve :
      ∀ i : ι, SupportedOn
        (phaseProductReserveSupportCertificate
          parent h a m hh ha hm).supportSet (reserveStep i))
    (hprotected :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
        (protectedStep j))
    (reserveWord : List ι) (protectedWord : List κ)
    (n k : Nat) :
    Function.Commute
      ((wordEval reserveStep reserveWord)^[n])
      ((wordEval protectedStep protectedWord)^[k]) :=
  (finalPhaseProductCertificateRealization input parent h a m hh ha hm T
    reserveStep protectedStep hreserve hprotected reserveWord protectedWord
    n k).reserveWordIterCommutesProtectedWordIter

theorem finalPhaseProductCertificateProtectedWordIterCommutesReserveWordIter
    (input : FinalPhaseProductCertificateInputs)
    {ι κ Parent : Type} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (reserveStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (protectedStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hreserve :
      ∀ i : ι, SupportedOn
        (phaseProductReserveSupportCertificate
          parent h a m hh ha hm).supportSet (reserveStep i))
    (hprotected :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
        (protectedStep j))
    (reserveWord : List ι) (protectedWord : List κ)
    (n k : Nat) :
    Function.Commute
      ((wordEval protectedStep protectedWord)^[k])
      ((wordEval reserveStep reserveWord)^[n]) :=
  (finalPhaseProductCertificateRealization input parent h a m hh ha hm T
    reserveStep protectedStep hreserve hprotected reserveWord protectedWord
    n k).protectedWordIterCommutesReserveWordIter

structure FinalOddEndpointPhaseProductCertificateInputs : Prop where
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

theorem finalOddEndpointPhaseProductCertificateInputs_of_endpointCertificate
    (input : FinalOddEndpointCertificateInputs) :
    FinalOddEndpointPhaseProductCertificateInputs where
  terminalInput := input.terminalInput
  markedTransferInput := input.markedTransferInput
  phaseProductInput :=
    finalPhaseProductCertificateInputs_of_endpointCertificate input
  completionCarryInput := input.completionCarryInput
  b4FirstCompletionInput := input.b4FirstCompletionInput
  rangeInput := input.rangeInput

theorem finalOddEndpointPhaseProductCertificateInputs_holds :
    FinalOddEndpointPhaseProductCertificateInputs :=
  finalOddEndpointPhaseProductCertificateInputs_of_endpointCertificate
    finalOddEndpointCertificateInputs_holds

theorem finalOddEndpointPhaseProductCertificatePhaseProductInput
    (input : FinalOddEndpointPhaseProductCertificateInputs) :
    FinalPhaseProductCertificateInputs :=
  input.phaseProductInput

theorem finalOddEndpointCertificateInputs_of_phaseProductCertificate
    (input : FinalOddEndpointPhaseProductCertificateInputs) :
    FinalOddEndpointCertificateInputs where
  terminalInput := input.terminalInput
  markedTransferInput := input.markedTransferInput
  phaseProductSupportInput :=
    input.phaseProductInput.supportInput
  phaseProductRealizationInput :=
    input.phaseProductInput.realizationInput
  completionCarryInput := input.completionCarryInput
  b4FirstCompletionInput := input.b4FirstCompletionInput
  rangeInput := input.rangeInput

structure FinalOddEndpointPhaseProductTargetPromotion : Prop where
  oddEndpoint :
    ∀ {b m : Nat}, 4 ≤ b → MarkedDimensionRange b m →
      FinalMarkedTarget b m →
      FinalOddEndpointPhaseProductCertificateInputs →
      FinalMarkedTarget (2 * b + 1) m

/-- Paper-faithful endpoint successor shape: the parent marked selector/reserve
payload is consumed and a renewed marked payload is produced.  The current
ordinary theorem spine still consumes `FinalOddEndpointPhaseProductTargetPromotion`;
`finalOddEndpointPhaseProductTargetPromotion_of_markedPayloadPromotion` forgets this
payload back to that old interface. -/
structure FinalOddEndpointPhaseProductMarkedPayloadPromotion : Prop where
  oddEndpoint :
    ∀ {b m : Nat}, 4 ≤ b → MarkedDimensionRange b m →
      FinalMarkedPayload b m →
      FinalOddEndpointPhaseProductCertificateInputs →
      FinalMarkedPayload (2 * b + 1) m

theorem finalOddEndpointPhaseProductTarget_of_markedPayloadPromotion
    (promotion : FinalOddEndpointPhaseProductMarkedPayloadPromotion)
    {b m : Nat} (hb : 4 ≤ b) (hRange : MarkedDimensionRange b m)
    (parent : FinalMarkedPayload b m)
    (input : FinalOddEndpointPhaseProductCertificateInputs) :
    FinalMarkedTarget (2 * b + 1) m :=
  finalMarkedPayload_forget
    (promotion.oddEndpoint hb hRange parent input)

/-- Compatibility adapter from the paper-faithful endpoint payload promotion to
the current ordinary-only endpoint target interface.  The parent payload is weakly
reconstructed from the old target because the current induction spine does not
yet carry real marked payloads. -/
theorem finalOddEndpointPhaseProductTargetPromotion_of_markedPayloadPromotion
    (promotion : FinalOddEndpointPhaseProductMarkedPayloadPromotion) :
    FinalOddEndpointPhaseProductTargetPromotion where
  oddEndpoint := fun hb hRange parent input =>
    finalOddEndpointPhaseProductTarget_of_markedPayloadPromotion
      promotion hb hRange (finalMarkedPayload_weakOfTarget parent) input

/-- Weak reverse adapter for legacy endpoint promotions.  It preserves the old
ordinary theorem flow while making the loss of paper marked data explicit. -/
theorem finalOddEndpointPhaseProductMarkedPayloadPromotion_weakOfTargetPromotion
    (promotion : FinalOddEndpointPhaseProductTargetPromotion) :
    FinalOddEndpointPhaseProductMarkedPayloadPromotion where
  oddEndpoint := fun hb hRange parent input =>
    finalMarkedPayload_weakOfTarget
      (promotion.oddEndpoint hb hRange (finalMarkedPayload_forget parent) input)

theorem finalOddEndpointTargetPromotion_of_phaseProductPromotion
    (promotion : FinalOddEndpointPhaseProductTargetPromotion) :
    FinalOddEndpointTargetPromotion where
  oddEndpoint := fun hb hRange parent input =>
    promotion.oddEndpoint hb hRange parent
      (finalOddEndpointPhaseProductCertificateInputs_of_endpointCertificate
        input)

theorem finalOddEndpointPhaseProductPromotion_of_targetPromotion
    (promotion : FinalOddEndpointTargetPromotion) :
    FinalOddEndpointPhaseProductTargetPromotion where
  oddEndpoint := fun hb hRange parent input =>
    promotion.oddEndpoint hb hRange parent
      (finalOddEndpointCertificateInputs_of_phaseProductCertificate input)

theorem finalOddEndpointClosedInputs_of_phaseProductCertificate
    (input : FinalOddEndpointPhaseProductCertificateInputs) :
    FinalOddEndpointClosedInputs where
  returnCoreInput := finalReturnCoreInput_holds
  wordCoreInput := finalWordCoreInput_holds
  terminalInput := input.terminalInput
  endpointInput :=
    { endpointMarkedTransferInput := input.markedTransferInput
      phaseProductSupportInput := input.phaseProductInput.supportInput
      phaseProductRealizationInput := input.phaseProductInput.realizationInput
      completionCarryInput := input.completionCarryInput
      b4FirstCompletionInput := input.b4FirstCompletionInput }
  rangeInput := input.rangeInput

theorem finalOddEndpointPhaseProductPromotion_of_closedPromotion
    (promotion : FinalOddEndpointPromotion) :
    FinalOddEndpointPhaseProductTargetPromotion where
  oddEndpoint := fun hb hRange parent input =>
    promotion.oddEndpoint hb hRange parent
      (finalOddEndpointClosedInputs_of_phaseProductCertificate input)

structure FinalRefinedPhaseProductGrowthPromotions : Prop where
  oddHighModulusPromotion : FinalOddHighModulusTargetPromotion
  oddEndpointPromotion : FinalOddEndpointPhaseProductTargetPromotion

theorem finalRefinedHighEvenGrowthPromotions_of_phaseProduct
    (promotions : FinalRefinedPhaseProductGrowthPromotions) :
    FinalRefinedHighEvenGrowthPromotions where
  oddHighModulusPromotion := promotions.oddHighModulusPromotion
  oddEndpointPromotion :=
    finalOddEndpointTargetPromotion_of_phaseProductPromotion
      promotions.oddEndpointPromotion

structure FinalSixRefinedPhaseProductPromotionObligations : Prop where
  d3EvenPromotion : FinalD3EvenBasePromotion
  lowPromotions : FinalRefinedLowBasePromotions
  growthPromotions : FinalRefinedPhaseProductGrowthPromotions

theorem finalSixRefinedHighEvenPromotionObligations_of_phaseProduct
    (remaining : FinalSixRefinedPhaseProductPromotionObligations) :
    FinalSixRefinedHighEvenPromotionObligations where
  d3EvenPromotion := remaining.d3EvenPromotion
  lowPromotions := remaining.lowPromotions
  growthPromotions :=
    finalRefinedHighEvenGrowthPromotions_of_phaseProduct
      remaining.growthPromotions

theorem finalTargetTorus_from_refinedPhaseProduct
    (remaining : FinalSixRefinedPhaseProductPromotionObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetTorus_from_refinedHighEven
    (finalSixRefinedHighEvenPromotionObligations_of_phaseProduct
      remaining)
    hRange

theorem finalTargetMarkedTorus_from_refinedPhaseProduct
    (remaining : FinalSixRefinedPhaseProductPromotionObligations)
    {d m : Nat} (hRange : MarkedDimensionRange d m) :
    Shared.TorusHamiltonDecomposition d m :=
  finalTargetMarkedTorus_from_refinedHighEven
    (finalSixRefinedHighEvenPromotionObligations_of_phaseProduct
      remaining)
    hRange

theorem finalTargetCayley_from_refinedPhaseProduct
    (remaining : FinalSixRefinedPhaseProductPromotionObligations)
    {d m : Nat} (hRange : OrdinaryDimensionRange d m) :
    Shared.CayleyHamiltonDecomposition d m :=
  finalTargetCayley_from_refinedHighEven
    (finalSixRefinedHighEvenPromotionObligations_of_phaseProduct
      remaining)
    hRange

end FinalTargetPhaseProductCertificateBridge

export FinalTargetPhaseProductCertificateBridge
  (FinalPhaseProductCertificateInputs
   FinalOddEndpointPhaseProductCertificateInputs
   FinalOddEndpointPhaseProductTargetPromotion
   FinalOddEndpointPhaseProductMarkedPayloadPromotion
   FinalRefinedPhaseProductGrowthPromotions
   FinalSixRefinedPhaseProductPromotionObligations
   finalPhaseProductCertificateInputs_of_endpointCertificate
   finalPhaseProductCertificateInputs_holds
   finalPhaseProductCertificateSupport
   finalPhaseProductCertificateSupportSetEq
   finalPhaseProductCertificateSupportPointListLength
   finalPhaseProductCertificateSupportPointListNodup
   finalPhaseProductCertificateSubsetReserveCylinder
   finalPhaseProductCertificateConstantParentProjection
   finalPhaseProductCertificateConstantPhaseProjection
   finalPhaseProductCertificateDisjointFromProtectedCylinder
   finalPhaseProductCertificateExistsUniqueSlot
   finalPhaseProductCertificatePointInjective
   finalPhaseProductCertificatePairInjective
   finalPhaseProductCertificateRealization
   finalPhaseProductCertificateRealizationSupport
   finalPhaseProductCertificateProtectedWordFixesReserveSupport
   finalPhaseProductCertificateProtectedWordIterFixesReserveSupport
   finalPhaseProductCertificateProtectedWordMapsReserveSupport
   finalPhaseProductCertificateProtectedWordIterMapsReserveSupport
   finalPhaseProductCertificateReserveWordFixesProtectedCylinder
   finalPhaseProductCertificateReserveWordIterFixesProtectedCylinder
   finalPhaseProductCertificateReserveWordMapsProtectedCylinder
   finalPhaseProductCertificateReserveWordIterMapsProtectedCylinder
   finalPhaseProductCertificateReserveWordCommutesProtectedWord
   finalPhaseProductCertificateProtectedWordCommutesReserveWord
   finalPhaseProductCertificateReserveWordIterCommutesProtectedWordIter
   finalPhaseProductCertificateProtectedWordIterCommutesReserveWordIter
   finalOddEndpointPhaseProductCertificateInputs_of_endpointCertificate
   finalOddEndpointPhaseProductCertificateInputs_holds
   finalOddEndpointPhaseProductCertificatePhaseProductInput
   finalOddEndpointCertificateInputs_of_phaseProductCertificate
   finalOddEndpointPhaseProductTarget_of_markedPayloadPromotion
   finalOddEndpointPhaseProductTargetPromotion_of_markedPayloadPromotion
   finalOddEndpointPhaseProductMarkedPayloadPromotion_weakOfTargetPromotion
   finalOddEndpointTargetPromotion_of_phaseProductPromotion
   finalOddEndpointPhaseProductPromotion_of_targetPromotion
   finalOddEndpointClosedInputs_of_phaseProductCertificate
   finalOddEndpointPhaseProductPromotion_of_closedPromotion
   finalRefinedHighEvenGrowthPromotions_of_phaseProduct
   finalSixRefinedHighEvenPromotionObligations_of_phaseProduct
   finalTargetTorus_from_refinedPhaseProduct
   finalTargetMarkedTorus_from_refinedPhaseProduct
   finalTargetCayley_from_refinedPhaseProduct)

end EvenV11
