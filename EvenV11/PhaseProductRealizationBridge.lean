import EvenV11.PhaseProductSupport

namespace EvenV11
namespace PhaseProductRealizationBridge

structure PhaseDoublingProductSupportInput {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) : Prop where
  supportSet_eq :
    (phaseProductReserveSupportCertificate parent h a m hh ha hm).supportSet =
      phaseProductReserveLineSlotPointSet parent h a m ha hm
  supportPointList_length :
    (phaseProductReserveLineSlotPointList parent h a m ha hm).length =
      2 * a + 3
  supportPointList_nodup :
    (phaseProductReserveLineSlotPointList parent h a m ha hm).Nodup
  subsetReserveCylinder :
    (phaseProductReserveSupportCertificate parent h a m hh ha hm).supportSet ⊆
      ProductCylinder ({parent} : Set Parent)
        (PhaseLine (h := h) (M := m ^ a) (2 : ZMod h))
  constantParentProjection :
    ProjectionConstantOn
      (fun x : Parent × PhaseSection h (m ^ a) => x.1)
      (phaseProductReserveSupportCertificate parent h a m hh ha hm).supportSet
      parent
  constantPhaseProjection :
    ProjectionConstantOn
      (fun x : Parent × PhaseSection h (m ^ a) => phaseProjection x.2)
      (phaseProductReserveSupportCertificate parent h a m hh ha hm).supportSet
      (2 : ZMod h)
  disjointFromProtectedCylinder :
    ∀ T : Set Parent,
      SetsDisjoint
        (phaseProductReserveSupportCertificate parent h a m hh ha hm).supportSet
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
  existsUniqueSlot :
    ∀ {x : Parent × PhaseSection h (m ^ a)},
      x ∈ (phaseProductReserveSupportCertificate
        parent h a m hh ha hm).supportSet →
      ∃! i : Fin (2 * a + 3),
        (phaseProductReserveLineSlot parent h a m ha hm i).1 = x
  pointInjective :
    Function.Injective
      (fun i : Fin (2 * a + 3) =>
        (phaseProductReserveLineSlot parent h a m ha hm i).1)
  pairInjective :
    Function.Injective
      (fun i : Fin (2 * a + 3) =>
        (parent, (phaseProductReserveLineSlot parent h a m ha hm i).1.2))

theorem phaseDoublingProductSupportInput_holds
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    PhaseDoublingProductSupportInput parent h a m hh ha hm where
  supportSet_eq :=
    phaseProductReserveSupportCertificate_supportSet parent h a m hh ha hm
  supportPointList_length :=
    phaseProductReserveLineSlotPointList_length parent h a m ha hm
  supportPointList_nodup :=
    phaseProductReserveLineSlotPointList_nodup parent h a m ha hm
  subsetReserveCylinder :=
    phaseProductReserveSupportCertificate_subsetReserveCylinder
      parent h a m hh ha hm
  constantParentProjection :=
    phaseProductReserveSupportCertificate_constantParentProjection
      parent h a m hh ha hm
  constantPhaseProjection :=
    phaseProductReserveSupportCertificate_constantPhaseProjection
      parent h a m hh ha hm
  disjointFromProtectedCylinder :=
    phaseProductReserveSupportCertificate_disjointProtected
      parent h a m hh ha hm
  existsUniqueSlot :=
    phaseProductReserveSupportCertificate_existsUniqueSlot
      parent h a m hh ha hm
  pointInjective :=
    phaseProductReserveSupportCertificate_pointInjective
      parent h a m hh ha hm
  pairInjective :=
    phaseProductReserveSupportCertificate_pairInjective
      parent h a m hh ha hm

structure PhaseDoublingProductRealizationInput
    {ι κ Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (reserveStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (protectedStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (reserveWord : List ι) (protectedWord : List κ)
    (n k : Nat) : Prop where
  supportInput :
    PhaseDoublingProductSupportInput parent h a m hh ha hm
  protectedWordFixesReserveSupport :
    ∀ {x : Parent × PhaseSection h (m ^ a)},
      x ∈ (phaseProductReserveSupportCertificate
        parent h a m hh ha hm).supportSet →
      wordEval protectedStep protectedWord x = x
  protectedWordIterFixesReserveSupport :
    ∀ {x : Parent × PhaseSection h (m ^ a)},
      x ∈ (phaseProductReserveSupportCertificate
        parent h a m hh ha hm).supportSet →
      ((wordEval protectedStep protectedWord)^[k]) x = x
  protectedWordMapsReserveSupport :
    MapsInto
      (phaseProductReserveSupportCertificate
        parent h a m hh ha hm).supportSet
      (wordEval protectedStep protectedWord)
  protectedWordIterMapsReserveSupport :
    MapsInto
      (phaseProductReserveSupportCertificate
        parent h a m hh ha hm).supportSet
      ((wordEval protectedStep protectedWord)^[k])
  reserveWordFixesProtectedCylinder :
    ∀ {x : Parent × PhaseSection h (m ^ a)},
      x ∈ ProductCylinder T (PhaseProtectedStrips h (m ^ a)) →
      wordEval reserveStep reserveWord x = x
  reserveWordIterFixesProtectedCylinder :
    ∀ {x : Parent × PhaseSection h (m ^ a)},
      x ∈ ProductCylinder T (PhaseProtectedStrips h (m ^ a)) →
      ((wordEval reserveStep reserveWord)^[n]) x = x
  reserveWordMapsProtectedCylinder :
    MapsInto (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
      (wordEval reserveStep reserveWord)
  reserveWordIterMapsProtectedCylinder :
    MapsInto (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
      ((wordEval reserveStep reserveWord)^[n])
  reserveWordCommutesProtectedWord :
    Function.Commute
      (wordEval reserveStep reserveWord) (wordEval protectedStep protectedWord)
  protectedWordCommutesReserveWord :
    Function.Commute
      (wordEval protectedStep protectedWord) (wordEval reserveStep reserveWord)
  reserveWordIterCommutesProtectedWordIter :
    Function.Commute
      ((wordEval reserveStep reserveWord)^[n])
      ((wordEval protectedStep protectedWord)^[k])
  protectedWordIterCommutesReserveWordIter :
    Function.Commute
      ((wordEval protectedStep protectedWord)^[k])
      ((wordEval reserveStep reserveWord)^[n])

theorem phaseDoublingProductRealizationInput_holds
    {ι κ Parent : Type*} (parent : Parent)
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
      reserveStep protectedStep reserveWord protectedWord n k where
  supportInput :=
    phaseDoublingProductSupportInput_holds parent h a m hh ha hm
  protectedWordFixesReserveSupport := by
    intro x hx
    exact phaseProductReserveSupportCertificate_fixedByProtectedWordEval
      (phaseProductReserveSupportCertificate parent h a m hh ha hm)
      T protectedStep hprotected protectedWord hx
  protectedWordIterFixesReserveSupport := by
    intro x hx
    exact phaseProductReserveSupportCertificate_fixedByProtectedWordIter
      (phaseProductReserveSupportCertificate parent h a m hh ha hm)
      T protectedStep hprotected protectedWord k hx
  protectedWordMapsReserveSupport :=
    phaseProductReserveSupportCertificate_mapsIntoProtectedWordEval
      (phaseProductReserveSupportCertificate parent h a m hh ha hm)
      T protectedStep hprotected protectedWord
  protectedWordIterMapsReserveSupport :=
    phaseProductReserveSupportCertificate_mapsIntoProtectedWordIter
      (phaseProductReserveSupportCertificate parent h a m hh ha hm)
      T protectedStep hprotected protectedWord k
  reserveWordFixesProtectedCylinder := by
    intro x hx
    exact phaseProductProtectedCylinder_fixedByReserveSupportCertificateWordEval
      (phaseProductReserveSupportCertificate parent h a m hh ha hm)
      T reserveStep hreserve reserveWord hx
  reserveWordIterFixesProtectedCylinder := by
    intro x hx
    exact phaseProductProtectedCylinder_fixedByReserveSupportCertificateWordIter
      (phaseProductReserveSupportCertificate parent h a m hh ha hm)
      T reserveStep hreserve reserveWord n hx
  reserveWordMapsProtectedCylinder :=
    phaseProductProtectedCylinder_mapsIntoReserveSupportCertificateWordEval
      (phaseProductReserveSupportCertificate parent h a m hh ha hm)
      T reserveStep hreserve reserveWord
  reserveWordIterMapsProtectedCylinder :=
    phaseProductProtectedCylinder_mapsIntoReserveSupportCertificateWordIter
      (phaseProductReserveSupportCertificate parent h a m hh ha hm)
      T reserveStep hreserve reserveWord n
  reserveWordCommutesProtectedWord :=
    phaseProductReserveSupportCertificateProtectedWordEvalsCommute
      (phaseProductReserveSupportCertificate parent h a m hh ha hm)
      T reserveStep protectedStep hreserve hprotected
      reserveWord protectedWord
  protectedWordCommutesReserveWord :=
    phaseProductReserveSupportCertificateProtectedWordEvalsCommute_symmSupports
      (phaseProductReserveSupportCertificate parent h a m hh ha hm)
      T protectedStep reserveStep hprotected hreserve
      protectedWord reserveWord
  reserveWordIterCommutesProtectedWordIter :=
    phaseProductReserveSupportCertificateProtectedWordItersCommute
      (phaseProductReserveSupportCertificate parent h a m hh ha hm)
      T reserveStep protectedStep hreserve hprotected
      reserveWord protectedWord n k
  protectedWordIterCommutesReserveWordIter :=
    phaseProductReserveSupportCertificateProtectedWordItersCommute_symmSupports
      (phaseProductReserveSupportCertificate parent h a m hh ha hm)
      T protectedStep reserveStep hprotected hreserve
      protectedWord reserveWord k n

end PhaseProductRealizationBridge

export PhaseProductRealizationBridge
  (PhaseDoublingProductSupportInput
   PhaseDoublingProductRealizationInput
   phaseDoublingProductSupportInput_holds
   phaseDoublingProductRealizationInput_holds)

end EvenV11
