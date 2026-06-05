import EvenV11.EndpointRowPlacement
import EvenV11.PhaseProductSupport

namespace EvenV11
namespace EndpointReservePlacement

def endpointReservePlacement {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m) :
    Fin (2 * a + 3) -> Parent × PhaseSection h (m ^ a) :=
  fun i => (phaseProductReserveLineSlot parent h a m ha hm i).1

theorem endpointReservePlacement_parent {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m)
    (i : Fin (2 * a + 3)) :
    (endpointReservePlacement parent h a m ha hm i).1 = parent :=
  phaseProductReserveLineSlot_parent parent h a m ha hm i

theorem endpointReservePlacement_phase {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m)
    (i : Fin (2 * a + 3)) :
    phaseProjection (endpointReservePlacement parent h a m ha hm i).2 =
      (2 : ZMod h) :=
  phaseProductReserveLineSlot_phase parent h a m ha hm i

theorem endpointReservePlacement_injective {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m) :
    Function.Injective (endpointReservePlacement parent h a m ha hm) :=
  phaseProductReserveLineSlotPoint_injective parent h a m ha hm

theorem endpointReservePlacement_newCoord_ne
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j) :
    (endpointReservePlacement parent h a m ha hm i).2 ≠
      (endpointReservePlacement parent h a m ha hm j).2 := by
  intro hcoord
  apply hij
  apply endpointReservePlacement_injective parent h a m ha hm
  apply Prod.ext
  · rw [endpointReservePlacement_parent, endpointReservePlacement_parent]
  · exact hcoord

theorem endpointReservePlacement_coordinateSeparated
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j) :
    (endpointReservePlacement parent h a m ha hm i).1 ≠
        (endpointReservePlacement parent h a m ha hm j).1 ∨
      (endpointReservePlacement parent h a m ha hm i).2 ≠
        (endpointReservePlacement parent h a m ha hm j).2 :=
  Or.inr (endpointReservePlacement_newCoord_ne parent h a m ha hm hij)

abbrev endpointReservePlacementList {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m) :
    List (Parent × PhaseSection h (m ^ a)) :=
  phaseProductReserveLineSlotPointList parent h a m ha hm

theorem endpointReservePlacementList_length {Parent : Type*}
    (parent : Parent) (h a m : Nat) [NeZero m]
    (ha : 2 <= a) (hm : 4 <= m) :
    (endpointReservePlacementList parent h a m ha hm).length =
      2 * a + 3 :=
  phaseProductReserveLineSlotPointList_length parent h a m ha hm

theorem endpointReservePlacementList_nodup {Parent : Type*}
    (parent : Parent) (h a m : Nat) [NeZero m]
    (ha : 2 <= a) (hm : 4 <= m) :
    (endpointReservePlacementList parent h a m ha hm).Nodup :=
  phaseProductReserveLineSlotPointList_nodup parent h a m ha hm

theorem endpointReservePlacementList_parent {Parent : Type*}
    (parent : Parent) (h a m : Nat) [NeZero m]
    (ha : 2 <= a) (hm : 4 <= m)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ endpointReservePlacementList parent h a m ha hm) :
    x.1 = parent :=
  phaseProductReserveLineSlotPointList_parent parent h a m ha hm hx

theorem endpointReservePlacementList_phase {Parent : Type*}
    (parent : Parent) (h a m : Nat) [NeZero m]
    (ha : 2 <= a) (hm : 4 <= m)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ endpointReservePlacementList parent h a m ha hm) :
    phaseProjection x.2 = (2 : ZMod h) :=
  phaseProductReserveLineSlotPointList_phase parent h a m ha hm hx

theorem endpointReservePlacementList_not_mem_protectedCylinder
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 <= a) (hm : 4 <= m)
    (T : Set Parent)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ endpointReservePlacementList parent h a m ha hm) :
    x ∉ ProductCylinder T (PhaseProtectedStrips h (m ^ a)) :=
  phaseProductReserveLineSlotPointList_not_mem_protectedCylinder
    parent h a m hh ha hm T hx

theorem endpointReservePlacementList_mem_iff_exists_slot
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m)
    (x : Parent × PhaseSection h (m ^ a)) :
    x ∈ endpointReservePlacementList parent h a m ha hm ↔
      ∃ i : Fin (2 * a + 3),
        endpointReservePlacement parent h a m ha hm i = x := by
  simpa [endpointReservePlacementList, endpointReservePlacement,
    phaseProductReserveLineSlotPointSet_mem] using
    (phaseProductReserveLineSlotPointSet_mem_iff_exists_slot
      parent h a m ha hm x)

theorem endpointReservePlacementList_exists_unique_slot
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ endpointReservePlacementList parent h a m ha hm) :
    ∃! i : Fin (2 * a + 3),
      endpointReservePlacement parent h a m ha hm i = x := by
  rcases (endpointReservePlacementList_mem_iff_exists_slot
      parent h a m ha hm x).mp hx with ⟨i, hi⟩
  refine ⟨i, hi, ?_⟩
  intro j hj
  exact endpointReservePlacement_injective parent h a m ha hm
    (hj.trans hi.symm)

def endpointReservePlacementSupportSet {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m) :
    Set (Parent × PhaseSection h (m ^ a)) :=
  phaseProductReserveLineSlotPointSet parent h a m ha hm

theorem endpointReservePlacementSupportSet_eq_phaseProduct
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m) :
    endpointReservePlacementSupportSet parent h a m ha hm =
      phaseProductReserveLineSlotPointSet parent h a m ha hm :=
  rfl

theorem endpointReservePlacementSupportSet_mem_iff_exists_row
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m)
    (x : Parent × PhaseSection h (m ^ a)) :
    x ∈ endpointReservePlacementSupportSet parent h a m ha hm ↔
      ∃ i : Fin (2 * a + 3),
        endpointReservePlacement parent h a m ha hm i = x := by
  simpa [endpointReservePlacementSupportSet, endpointReservePlacement] using
    (phaseProductReserveLineSlotPointSet_mem_iff_exists_slot
      parent h a m ha hm x)

theorem endpointReservePlacementSupportSet_exists_unique_row
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ endpointReservePlacementSupportSet parent h a m ha hm) :
    ∃! i : Fin (2 * a + 3),
      endpointReservePlacement parent h a m ha hm i = x := by
  rcases (endpointReservePlacementSupportSet_mem_iff_exists_row
      parent h a m ha hm x).mp hx with ⟨i, hi⟩
  refine ⟨i, hi, ?_⟩
  intro j hj
  exact endpointReservePlacement_injective parent h a m ha hm
    (hj.trans hi.symm)

theorem endpointReservePlacementSupportSet_eq_iUnion_rowPlacementSupport
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m) :
    endpointReservePlacementSupportSet parent h a m ha hm =
      ⋃ i : Fin (2 * a + 3),
        rowPlacementSupport (endpointReservePlacement parent h a m ha hm) i := by
  ext x
  constructor
  · intro hx
    rcases (endpointReservePlacementSupportSet_mem_iff_exists_row
        parent h a m ha hm x).mp hx with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, by
      rw [rowPlacementSupport_mem]
      exact hi.symm⟩
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
    rw [rowPlacementSupport_mem] at hxi
    exact (endpointReservePlacementSupportSet_mem_iff_exists_row
      parent h a m ha hm x).mpr ⟨i, hxi.symm⟩

theorem endpointReservePlacementSupportSet_subsetReserveCylinder
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m) :
    endpointReservePlacementSupportSet parent h a m ha hm ⊆
      ProductCylinder ({parent} : Set Parent)
        (PhaseLine (h := h) (M := m ^ a) (2 : ZMod h)) :=
  phaseProductReserveLineSlotPointSet_subsetReserveCylinder
    parent h a m ha hm

theorem endpointReservePlacementSupportSet_constantParentProjection
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m) :
    ProjectionConstantOn
      (fun x : Parent × PhaseSection h (m ^ a) => x.1)
      (endpointReservePlacementSupportSet parent h a m ha hm)
      parent :=
  phaseProductReserveLineSlotPointSet_constantParentProjection
    parent h a m ha hm

theorem endpointReservePlacementSupportSet_constantPhaseProjection
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m) :
    ProjectionConstantOn
      (fun x : Parent × PhaseSection h (m ^ a) => phaseProjection x.2)
      (endpointReservePlacementSupportSet parent h a m ha hm)
      (2 : ZMod h) :=
  phaseProductReserveLineSlotPointSet_constantPhaseProjection
    parent h a m ha hm

theorem endpointReservePlacementSupportSet_disjointProtected
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 <= a) (hm : 4 <= m)
    (T : Set Parent) :
    SetsDisjoint
      (endpointReservePlacementSupportSet parent h a m ha hm)
      (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :=
  phaseProductReserveLineSlotPointSet_disjointFromProtectedCylinder
    parent h a m hh ha hm T

structure EndpointReservePlacementSupportCertificate
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 <= a) (hm : 4 <= m) where
  supportSet : Set (Parent × PhaseSection h (m ^ a))
  supportSet_eq :
    supportSet = endpointReservePlacementSupportSet parent h a m ha hm
  supportSet_eq_phaseProduct :
    supportSet = phaseProductReserveLineSlotPointSet parent h a m ha hm
  supportSet_eq_iUnionRows :
    supportSet =
      ⋃ i : Fin (2 * a + 3),
        rowPlacementSupport (endpointReservePlacement parent h a m ha hm) i
  subsetReserveCylinder :
    supportSet ⊆
      ProductCylinder ({parent} : Set Parent)
        (PhaseLine (h := h) (M := m ^ a) (2 : ZMod h))
  constantParentProjection :
    ProjectionConstantOn
      (fun x : Parent × PhaseSection h (m ^ a) => x.1)
      supportSet parent
  constantPhaseProjection :
    ProjectionConstantOn
      (fun x : Parent × PhaseSection h (m ^ a) => phaseProjection x.2)
      supportSet (2 : ZMod h)
  disjointFromProtectedCylinder :
    ∀ T : Set Parent,
      SetsDisjoint supportSet
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
  existsUniqueRow :
    ∀ {x : Parent × PhaseSection h (m ^ a)}, x ∈ supportSet →
      ∃! i : Fin (2 * a + 3),
        endpointReservePlacement parent h a m ha hm i = x
  placementInjective :
    Function.Injective (endpointReservePlacement parent h a m ha hm)

def endpointReservePlacementSupportCertificate
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 <= a) (hm : 4 <= m) :
    EndpointReservePlacementSupportCertificate parent h a m hh ha hm where
  supportSet := endpointReservePlacementSupportSet parent h a m ha hm
  supportSet_eq := rfl
  supportSet_eq_phaseProduct := rfl
  supportSet_eq_iUnionRows :=
    endpointReservePlacementSupportSet_eq_iUnion_rowPlacementSupport
      parent h a m ha hm
  subsetReserveCylinder :=
    endpointReservePlacementSupportSet_subsetReserveCylinder
      parent h a m ha hm
  constantParentProjection :=
    endpointReservePlacementSupportSet_constantParentProjection
      parent h a m ha hm
  constantPhaseProjection :=
    endpointReservePlacementSupportSet_constantPhaseProjection
      parent h a m ha hm
  disjointFromProtectedCylinder :=
    endpointReservePlacementSupportSet_disjointProtected
      parent h a m hh ha hm
  existsUniqueRow :=
    endpointReservePlacementSupportSet_exists_unique_row
      parent h a m ha hm
  placementInjective :=
    endpointReservePlacement_injective parent h a m ha hm

theorem endpointReservePlacementSupportCertificate_supportSet
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 <= a) (hm : 4 <= m) :
    (endpointReservePlacementSupportCertificate
      parent h a m hh ha hm).supportSet =
      endpointReservePlacementSupportSet parent h a m ha hm :=
  (endpointReservePlacementSupportCertificate
    parent h a m hh ha hm).supportSet_eq

theorem endpointReservePlacementSupportCertificate_supportSet_phaseProduct
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 <= a) (hm : 4 <= m) :
    (endpointReservePlacementSupportCertificate
      parent h a m hh ha hm).supportSet =
      phaseProductReserveLineSlotPointSet parent h a m ha hm :=
  (endpointReservePlacementSupportCertificate
    parent h a m hh ha hm).supportSet_eq_phaseProduct

theorem endpointReservePlacementSupportCertificate_supportSet_iUnionRows
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 <= a) (hm : 4 <= m) :
    (endpointReservePlacementSupportCertificate
      parent h a m hh ha hm).supportSet =
      ⋃ i : Fin (2 * a + 3),
        rowPlacementSupport (endpointReservePlacement parent h a m ha hm) i :=
  (endpointReservePlacementSupportCertificate
    parent h a m hh ha hm).supportSet_eq_iUnionRows

theorem endpointReservePlacementSupportCertificate_subsetReserveCylinder
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 <= a) (hm : 4 <= m) :
    (endpointReservePlacementSupportCertificate
      parent h a m hh ha hm).supportSet ⊆
      ProductCylinder ({parent} : Set Parent)
        (PhaseLine (h := h) (M := m ^ a) (2 : ZMod h)) :=
  (endpointReservePlacementSupportCertificate
    parent h a m hh ha hm).subsetReserveCylinder

theorem endpointReservePlacementSupportCertificate_constantParentProjection
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 <= a) (hm : 4 <= m) :
    ProjectionConstantOn
      (fun x : Parent × PhaseSection h (m ^ a) => x.1)
      (endpointReservePlacementSupportCertificate
        parent h a m hh ha hm).supportSet
      parent :=
  (endpointReservePlacementSupportCertificate
    parent h a m hh ha hm).constantParentProjection

theorem endpointReservePlacementSupportCertificate_constantPhaseProjection
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 <= a) (hm : 4 <= m) :
    ProjectionConstantOn
      (fun x : Parent × PhaseSection h (m ^ a) => phaseProjection x.2)
      (endpointReservePlacementSupportCertificate
        parent h a m hh ha hm).supportSet
      (2 : ZMod h) :=
  (endpointReservePlacementSupportCertificate
    parent h a m hh ha hm).constantPhaseProjection

theorem endpointReservePlacementSupportCertificate_disjointProtected
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 <= a) (hm : 4 <= m)
    (T : Set Parent) :
    SetsDisjoint
      (endpointReservePlacementSupportCertificate
        parent h a m hh ha hm).supportSet
      (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :=
  (endpointReservePlacementSupportCertificate
    parent h a m hh ha hm).disjointFromProtectedCylinder T

theorem endpointReservePlacementSupportCertificate_existsUniqueRow
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 <= a) (hm : 4 <= m)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx :
      x ∈ (endpointReservePlacementSupportCertificate
        parent h a m hh ha hm).supportSet) :
    ∃! i : Fin (2 * a + 3),
      endpointReservePlacement parent h a m ha hm i = x :=
  (endpointReservePlacementSupportCertificate
    parent h a m hh ha hm).existsUniqueRow hx

theorem endpointReservePlacementSupportCertificate_placementInjective
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 <= a) (hm : 4 <= m) :
    Function.Injective (endpointReservePlacement parent h a m ha hm) :=
  (endpointReservePlacementSupportCertificate
    parent h a m hh ha hm).placementInjective

def EndpointReservePlacementSupportCertificate.toPhaseProductCert
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm) :
    PhaseProductReserveSupportCertificate parent h a m hh ha hm where
  supportSet := C.supportSet
  supportSet_eq := C.supportSet_eq_phaseProduct
  subsetReserveCylinder := C.subsetReserveCylinder
  constantParentProjection := C.constantParentProjection
  constantPhaseProjection := C.constantPhaseProjection
  disjointFromProtectedCylinder := C.disjointFromProtectedCylinder
  existsUniqueSlot := by
    intro x hx
    simpa [endpointReservePlacement] using C.existsUniqueRow hx
  pointInjective := by
    simpa [endpointReservePlacement] using C.placementInjective
  pairInjective :=
    phaseProductReserveLineSlotPair_injective parent h a m ha hm

theorem endpointReservePlacementSupportCertificate_toPhaseProductCert_supportSet
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm) :
    C.toPhaseProductCert.supportSet = C.supportSet :=
  rfl

theorem endpointReservePlacementSupportCertificate_toPhaseProductCert_phaseProduct
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm) :
    C.toPhaseProductCert.supportSet =
      phaseProductReserveLineSlotPointSet parent h a m ha hm :=
  C.supportSet_eq_phaseProduct

theorem endpointReservePlacementSupportCertificate_toPhaseProductCert_disjointProtected
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent) :
    SetsDisjoint C.toPhaseProductCert.supportSet
      (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :=
  C.disjointFromProtectedCylinder T

theorem endpointReservePlacementSupportCertificate_toPhaseProductCert_existsUniqueSlot
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ C.toPhaseProductCert.supportSet) :
    ∃! i : Fin (2 * a + 3),
      (phaseProductReserveLineSlot parent h a m ha hm i).1 = x :=
  C.toPhaseProductCert.existsUniqueSlot hx

theorem endpointReservePlacementSupportCertificate_toPhaseProductCert_pointInjective
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm) :
    Function.Injective
      (fun i : Fin (2 * a + 3) =>
        (phaseProductReserveLineSlot parent h a m ha hm i).1) :=
  C.toPhaseProductCert.pointInjective

theorem endpointReservePlacementSupportCertificate_toPhaseProductCert_pairInjective
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm) :
    Function.Injective
      (fun i : Fin (2 * a + 3) =>
        (parent, (phaseProductReserveLineSlot parent h a m ha hm i).1.2)) :=
  C.toPhaseProductCert.pairInjective

theorem endpointReservePlacementSupportCertificate_fixedByProtectedMap
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) -> Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ C.supportSet) :
    f x = x :=
  phaseProductReserveSupportCertificate_fixedByProtectedMap
    C.toPhaseProductCert T hf hx

theorem endpointReservePlacementSupportCertificate_fixedByProtectedIter
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) -> Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    (n : Nat) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ C.supportSet) :
    (f^[n]) x = x :=
  phaseProductReserveSupportCertificate_fixedByProtectedIter
    C.toPhaseProductCert T hf n hx

theorem endpointReservePlacementSupportCertificate_fixedByProtectedWordEval
    {ι Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (step : ι -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ C.supportSet) :
    wordEval step word x = x :=
  phaseProductReserveSupportCertificate_fixedByProtectedWordEval
    C.toPhaseProductCert T step hstep word hx

theorem endpointReservePlacementSupportCertificate_fixedByProtectedWordIter
    {ι Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (step : ι -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι) (n : Nat) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ C.supportSet) :
    ((wordEval step word)^[n]) x = x :=
  phaseProductReserveSupportCertificate_fixedByProtectedWordIter
    C.toPhaseProductCert T step hstep word n hx

theorem endpointReservePlacementSupportCertificate_mapsIntoProtectedMap
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) -> Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f) :
    MapsInto C.supportSet f :=
  phaseProductReserveSupportCertificate_mapsIntoProtectedMap
    C.toPhaseProductCert T hf

theorem endpointReservePlacementSupportCertificate_mapsIntoProtectedIter
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) -> Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    (n : Nat) :
    MapsInto C.supportSet (f^[n]) :=
  phaseProductReserveSupportCertificate_mapsIntoProtectedIter
    C.toPhaseProductCert T hf n

theorem endpointReservePlacementSupportCertificate_mapsIntoProtectedWordEval
    {ι Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (step : ι -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι) :
    MapsInto C.supportSet (wordEval step word) :=
  phaseProductReserveSupportCertificate_mapsIntoProtectedWordEval
    C.toPhaseProductCert T step hstep word

theorem endpointReservePlacementSupportCertificate_mapsIntoProtectedWordIter
    {ι Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (step : ι -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι) (n : Nat) :
    MapsInto C.supportSet ((wordEval step word)^[n]) :=
  phaseProductReserveSupportCertificate_mapsIntoProtectedWordIter
    C.toPhaseProductCert T step hstep word n

theorem endpointProtectedCylinder_fixedByReservePlacementSupportCertificateMap
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) -> Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn C.supportSet f)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :
    f x = x :=
  phaseProductProtectedCylinder_fixedByReserveSupportCertificateMap
    C.toPhaseProductCert T hf hx

theorem endpointProtectedCylinder_fixedByReservePlacementSupportCertificateIter
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) -> Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn C.supportSet f)
    (n : Nat) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :
    (f^[n]) x = x :=
  phaseProductProtectedCylinder_fixedByReserveSupportCertificateIter
    C.toPhaseProductCert T hf n hx

theorem endpointProtectedCylinder_fixedByReservePlacementSupportCertificateWordEval
    {ι Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (step : ι -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (hstep : ∀ j : ι, SupportedOn C.supportSet (step j))
    (word : List ι) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :
    wordEval step word x = x :=
  phaseProductProtectedCylinder_fixedByReserveSupportCertificateWordEval
    C.toPhaseProductCert T step hstep word hx

theorem endpointProtectedCylinder_fixedByReservePlacementSupportCertificateWordIter
    {ι Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (step : ι -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (hstep : ∀ j : ι, SupportedOn C.supportSet (step j))
    (word : List ι) (n : Nat) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :
    ((wordEval step word)^[n]) x = x :=
  phaseProductProtectedCylinder_fixedByReserveSupportCertificateWordIter
    C.toPhaseProductCert T step hstep word n hx

theorem endpointProtectedCylinder_mapsIntoReservePlacementSupportCertificateMap
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) -> Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn C.supportSet f) :
    MapsInto (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f :=
  phaseProductProtectedCylinder_mapsIntoReserveSupportCertificateMap
    C.toPhaseProductCert T hf

theorem endpointProtectedCylinder_mapsIntoReservePlacementSupportCertificateIter
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) -> Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn C.supportSet f)
    (n : Nat) :
    MapsInto (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (f^[n]) :=
  phaseProductProtectedCylinder_mapsIntoReserveSupportCertificateIter
    C.toPhaseProductCert T hf n

theorem endpointProtectedCylinder_mapsIntoReservePlacementSupportCertificateWordEval
    {ι Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (step : ι -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (hstep : ∀ j : ι, SupportedOn C.supportSet (step j))
    (word : List ι) :
    MapsInto (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
      (wordEval step word) :=
  phaseProductProtectedCylinder_mapsIntoReserveSupportCertificateWordEval
    C.toPhaseProductCert T step hstep word

theorem endpointProtectedCylinder_mapsIntoReservePlacementSupportCertificateWordIter
    {ι Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (step : ι -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (hstep : ∀ j : ι, SupportedOn C.supportSet (step j))
    (word : List ι) (n : Nat) :
    MapsInto (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
      ((wordEval step word)^[n]) :=
  phaseProductProtectedCylinder_mapsIntoReserveSupportCertificateWordIter
    C.toPhaseProductCert T step hstep word n

theorem endpointReservePlacementSupportCertificateProtectedMapsCommute
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f g : Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn C.supportSet f)
    (hg : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) g) :
    Function.Commute f g :=
  phaseProductReserveSupportCertificateProtectedMapsCommute
    C.toPhaseProductCert T hf hg

theorem endpointReservePlacementSupportCertificateProtectedMapsCommute_symmSupports
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f g : Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    (hg : SupportedOn C.supportSet g) :
    Function.Commute f g :=
  phaseProductReserveSupportCertificateProtectedMapsCommute_symmSupports
    C.toPhaseProductCert T hf hg

theorem endpointReservePlacementSupportCertificateProtectedItersCommute
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f g : Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn C.supportSet f)
    (hg : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  phaseProductReserveSupportCertificateProtectedItersCommute
    C.toPhaseProductCert T hf hg n k

theorem endpointReservePlacementSupportCertificateProtectedItersCommute_symmSupports
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f g : Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    (hg : SupportedOn C.supportSet g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  phaseProductReserveSupportCertificateProtectedItersCommute_symmSupports
    C.toPhaseProductCert T hf hg n k

theorem endpointReservePlacementSupportCertificateProtectedWordEvalsCommute
    {ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (leftStep : ι -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn C.supportSet (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  phaseProductReserveSupportCertificateProtectedWordEvalsCommute
    C.toPhaseProductCert T leftStep rightStep hleft hright
    leftWord rightWord

theorem endpointReservePlacementSupportCertificateProtectedWordEvalsCommute_symmSupports
    {ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (leftStep : ι -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ i : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (leftStep i))
    (hright : ∀ j : κ, SupportedOn C.supportSet (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  phaseProductReserveSupportCertificateProtectedWordEvalsCommute_symmSupports
    C.toPhaseProductCert T leftStep rightStep hleft hright
    leftWord rightWord

theorem endpointReservePlacementSupportCertificateProtectedWordItersCommute
    {ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (leftStep : ι -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn C.supportSet (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  phaseProductReserveSupportCertificateProtectedWordItersCommute
    C.toPhaseProductCert T leftStep rightStep hleft hright
    leftWord rightWord n k

theorem endpointReservePlacementSupportCertificateProtectedWordItersCommute_symmSupports
    {ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C : EndpointReservePlacementSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (leftStep : ι -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ i : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (leftStep i))
    (hright : ∀ j : κ, SupportedOn C.supportSet (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  phaseProductReserveSupportCertificateProtectedWordItersCommute_symmSupports
    C.toPhaseProductCert T leftStep rightStep hleft hright
    leftWord rightWord n k

def endpointReserveAugmentedPlacement
    {ExtraRow Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m)
    (extraPlacement : ExtraRow -> Parent × PhaseSection h (m ^ a)) :
    Sum (Fin (2 * a + 3)) ExtraRow ->
      Parent × PhaseSection h (m ^ a)
  | Sum.inl row => endpointReservePlacement parent h a m ha hm row
  | Sum.inr row => extraPlacement row

theorem endpointReserveAugmentedPlacement_inl
    {ExtraRow Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m)
    (extraPlacement : ExtraRow -> Parent × PhaseSection h (m ^ a))
    (row : Fin (2 * a + 3)) :
    endpointReserveAugmentedPlacement
      parent h a m ha hm extraPlacement (Sum.inl row) =
      endpointReservePlacement parent h a m ha hm row :=
  rfl

theorem endpointReserveAugmentedPlacement_inr
    {ExtraRow Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m)
    (extraPlacement : ExtraRow -> Parent × PhaseSection h (m ^ a))
    (row : ExtraRow) :
    endpointReserveAugmentedPlacement
      parent h a m ha hm extraPlacement (Sum.inr row) =
      extraPlacement row :=
  rfl

theorem endpointReserveAugmentedPlacement_injective
    {ExtraRow Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 <= a) (hm : 4 <= m)
    (extraPlacement : ExtraRow -> Parent × PhaseSection h (m ^ a))
    (extraInjective : Function.Injective extraPlacement)
    (extraProtected :
      ∀ row : ExtraRow,
        extraPlacement row ∈
          ProductCylinder (Set.univ : Set Parent)
            (PhaseProtectedStrips h (m ^ a))) :
    Function.Injective
      (endpointReserveAugmentedPlacement
        parent h a m ha hm extraPlacement) := by
  intro leftRow rightRow hplacement
  cases leftRow with
  | inl leftReserve =>
      cases rightRow with
      | inl rightReserve =>
          exact congrArg Sum.inl
            (endpointReservePlacement_injective
              parent h a m ha hm hplacement)
      | inr rightExtra =>
          exfalso
          have hmemAug :
              endpointReserveAugmentedPlacement
                parent h a m ha hm extraPlacement (Sum.inl leftReserve) ∈
                ProductCylinder (Set.univ : Set Parent)
                  (PhaseProtectedStrips h (m ^ a)) := by
            rw [hplacement]
            simpa [endpointReserveAugmentedPlacement] using
              extraProtected rightExtra
          have hmem :
              endpointReservePlacement parent h a m ha hm leftReserve ∈
                ProductCylinder (Set.univ : Set Parent)
                  (PhaseProtectedStrips h (m ^ a)) := by
            simpa [endpointReserveAugmentedPlacement] using hmemAug
          have hnot :
              endpointReservePlacement parent h a m ha hm leftReserve ∉
                ProductCylinder (Set.univ : Set Parent)
                  (PhaseProtectedStrips h (m ^ a)) := by
            simpa [endpointReservePlacement] using
              phaseProductReserveLineSlot_not_mem_protectedCylinder
                parent h a m hh ha hm (Set.univ : Set Parent)
                leftReserve
          exact hnot hmem
  | inr leftExtra =>
      cases rightRow with
      | inl rightReserve =>
          exfalso
          have hmemAug :
              endpointReserveAugmentedPlacement
                parent h a m ha hm extraPlacement (Sum.inl rightReserve) ∈
                ProductCylinder (Set.univ : Set Parent)
                  (PhaseProtectedStrips h (m ^ a)) := by
            rw [← hplacement]
            simpa [endpointReserveAugmentedPlacement] using
              extraProtected leftExtra
          have hmem :
              endpointReservePlacement parent h a m ha hm rightReserve ∈
                ProductCylinder (Set.univ : Set Parent)
                  (PhaseProtectedStrips h (m ^ a)) := by
            simpa [endpointReserveAugmentedPlacement] using hmemAug
          have hnot :
              endpointReservePlacement parent h a m ha hm rightReserve ∉
                ProductCylinder (Set.univ : Set Parent)
                  (PhaseProtectedStrips h (m ^ a)) := by
            simpa [endpointReservePlacement] using
              phaseProductReserveLineSlot_not_mem_protectedCylinder
                parent h a m hh ha hm (Set.univ : Set Parent)
                rightReserve
          exact hnot hmem
      | inr rightExtra =>
          exact congrArg Sum.inr (extraInjective hplacement)

def endpointExtraPlacementSupportSet
    {ExtraRow Parent : Type*} {h a m : Nat}
    (extraPlacement : ExtraRow -> Parent × PhaseSection h (m ^ a)) :
    Set (Parent × PhaseSection h (m ^ a)) :=
  ⋃ row : ExtraRow, rowPlacementSupport extraPlacement row

theorem endpointExtraPlacementSupportSet_mem_iff_exists_row
    {ExtraRow Parent : Type*} {h a m : Nat}
    (extraPlacement : ExtraRow -> Parent × PhaseSection h (m ^ a))
    (x : Parent × PhaseSection h (m ^ a)) :
    x ∈ endpointExtraPlacementSupportSet extraPlacement ↔
      ∃ row : ExtraRow, extraPlacement row = x := by
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨row, hxrow⟩
    rw [rowPlacementSupport_mem] at hxrow
    exact ⟨row, hxrow.symm⟩
  · intro hx
    rcases hx with ⟨row, hrow⟩
    exact Set.mem_iUnion.mpr ⟨row, by
      rw [rowPlacementSupport_mem]
      exact hrow.symm⟩

theorem endpointExtraPlacementSupportSet_subsetProtected
    {ExtraRow Parent : Type*} {h a m : Nat}
    (extraPlacement : ExtraRow -> Parent × PhaseSection h (m ^ a))
    (extraProtected :
      ∀ row : ExtraRow,
        extraPlacement row ∈
          ProductCylinder (Set.univ : Set Parent)
            (PhaseProtectedStrips h (m ^ a))) :
    endpointExtraPlacementSupportSet extraPlacement ⊆
      ProductCylinder (Set.univ : Set Parent)
        (PhaseProtectedStrips h (m ^ a)) := by
  intro x hx
  rcases (endpointExtraPlacementSupportSet_mem_iff_exists_row
      extraPlacement x).mp hx with ⟨row, hrow⟩
  rw [← hrow]
  exact extraProtected row

def endpointReserveAugmentedSupportSet
    {ExtraRow Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m)
    (extraPlacement : ExtraRow -> Parent × PhaseSection h (m ^ a)) :
    Set (Parent × PhaseSection h (m ^ a)) :=
  ⋃ row : Sum (Fin (2 * a + 3)) ExtraRow,
    rowPlacementSupport
      (endpointReserveAugmentedPlacement
        parent h a m ha hm extraPlacement) row

theorem endpointReserveAugmentedSupportSet_eq_iUnionRows
    {ExtraRow Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m)
    (extraPlacement : ExtraRow -> Parent × PhaseSection h (m ^ a)) :
    endpointReserveAugmentedSupportSet
      parent h a m ha hm extraPlacement =
      ⋃ row : Sum (Fin (2 * a + 3)) ExtraRow,
        rowPlacementSupport
          (endpointReserveAugmentedPlacement
            parent h a m ha hm extraPlacement) row :=
  rfl

theorem endpointReserveAugmentedSupportSet_mem_iff_exists_row
    {ExtraRow Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m)
    (extraPlacement : ExtraRow -> Parent × PhaseSection h (m ^ a))
    (x : Parent × PhaseSection h (m ^ a)) :
    x ∈ endpointReserveAugmentedSupportSet
      parent h a m ha hm extraPlacement ↔
      ∃ row : Sum (Fin (2 * a + 3)) ExtraRow,
        endpointReserveAugmentedPlacement
          parent h a m ha hm extraPlacement row = x := by
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨row, hxrow⟩
    rw [rowPlacementSupport_mem] at hxrow
    exact ⟨row, hxrow.symm⟩
  · intro hx
    rcases hx with ⟨row, hrow⟩
    exact Set.mem_iUnion.mpr ⟨row, by
      rw [rowPlacementSupport_mem]
      exact hrow.symm⟩

theorem endpointReserveAugmentedSupportSet_eq_union
    {ExtraRow Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m)
    (extraPlacement : ExtraRow -> Parent × PhaseSection h (m ^ a)) :
    endpointReserveAugmentedSupportSet
        parent h a m ha hm extraPlacement =
      endpointReservePlacementSupportSet parent h a m ha hm ∪
        endpointExtraPlacementSupportSet extraPlacement := by
  ext x
  constructor
  · intro hx
    rcases (endpointReserveAugmentedSupportSet_mem_iff_exists_row
        parent h a m ha hm extraPlacement x).mp hx with ⟨row, hrow⟩
    cases row with
    | inl reserveRow =>
        left
        exact (endpointReservePlacementSupportSet_mem_iff_exists_row
          parent h a m ha hm x).mpr
          ⟨reserveRow, by
            simpa [endpointReserveAugmentedPlacement] using hrow⟩
    | inr extraRow =>
        right
        exact (endpointExtraPlacementSupportSet_mem_iff_exists_row
          extraPlacement x).mpr
          ⟨extraRow, by
            simpa [endpointReserveAugmentedPlacement] using hrow⟩
  · intro hx
    cases hx with
    | inl hreserve =>
        rcases (endpointReservePlacementSupportSet_mem_iff_exists_row
            parent h a m ha hm x).mp hreserve with ⟨row, hrow⟩
        exact (endpointReserveAugmentedSupportSet_mem_iff_exists_row
          parent h a m ha hm extraPlacement x).mpr
          ⟨Sum.inl row, by
            simpa [endpointReserveAugmentedPlacement] using hrow⟩
    | inr hextra =>
        rcases (endpointExtraPlacementSupportSet_mem_iff_exists_row
            extraPlacement x).mp hextra with ⟨row, hrow⟩
        exact (endpointReserveAugmentedSupportSet_mem_iff_exists_row
          parent h a m ha hm extraPlacement x).mpr
          ⟨Sum.inr row, by
            simpa [endpointReserveAugmentedPlacement] using hrow⟩

theorem endpointReserveAugmentedSupportSet_reserveSubset
    {ExtraRow Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m)
    (extraPlacement : ExtraRow -> Parent × PhaseSection h (m ^ a)) :
    endpointReservePlacementSupportSet parent h a m ha hm ⊆
      endpointReserveAugmentedSupportSet
        parent h a m ha hm extraPlacement := by
  intro x hx
  rw [endpointReserveAugmentedSupportSet_eq_union]
  exact Or.inl hx

theorem endpointReserveAugmentedSupportSet_extraSubset
    {ExtraRow Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m)
    (extraPlacement : ExtraRow -> Parent × PhaseSection h (m ^ a)) :
    endpointExtraPlacementSupportSet extraPlacement ⊆
      endpointReserveAugmentedSupportSet
        parent h a m ha hm extraPlacement := by
  intro x hx
  rw [endpointReserveAugmentedSupportSet_eq_union]
  exact Or.inr hx

theorem endpointReserveAugmentedSupportSet_extraSubsetProtected
    {ExtraRow Parent : Type*} (h a m : Nat) [NeZero m]
    (extraPlacement : ExtraRow -> Parent × PhaseSection h (m ^ a))
    (extraProtected :
      ∀ row : ExtraRow,
        extraPlacement row ∈
          ProductCylinder (Set.univ : Set Parent)
            (PhaseProtectedStrips h (m ^ a))) :
    endpointExtraPlacementSupportSet extraPlacement ⊆
      ProductCylinder (Set.univ : Set Parent)
        (PhaseProtectedStrips h (m ^ a)) :=
  endpointExtraPlacementSupportSet_subsetProtected
    extraPlacement extraProtected

theorem endpointReserveAugmentedSupportSet_exists_unique_row
    {ExtraRow Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m)
    (extraPlacement : ExtraRow -> Parent × PhaseSection h (m ^ a))
    (placementInjective :
      Function.Injective
        (endpointReserveAugmentedPlacement
          parent h a m ha hm extraPlacement))
    {x : Parent × PhaseSection h (m ^ a)}
    (hx :
      x ∈ endpointReserveAugmentedSupportSet
        parent h a m ha hm extraPlacement) :
    ∃! row : Sum (Fin (2 * a + 3)) ExtraRow,
      endpointReserveAugmentedPlacement
        parent h a m ha hm extraPlacement row = x := by
  rcases (endpointReserveAugmentedSupportSet_mem_iff_exists_row
      parent h a m ha hm extraPlacement x).mp hx with ⟨row, hrow⟩
  refine ⟨row, hrow, ?_⟩
  intro otherRow hother
  exact placementInjective (hother.trans hrow.symm)

theorem endpointReserveAugmentedSupportSet_supports_disjoint
    {ExtraRow Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 <= a) (hm : 4 <= m)
    (extraPlacement : ExtraRow -> Parent × PhaseSection h (m ^ a))
    (extraInjective : Function.Injective extraPlacement)
    (extraProtected :
      ∀ row : ExtraRow,
        extraPlacement row ∈
          ProductCylinder (Set.univ : Set Parent)
            (PhaseProtectedStrips h (m ^ a)))
    {leftRow rightRow : Sum (Fin (2 * a + 3)) ExtraRow}
    (hrow : leftRow ≠ rightRow) :
    SetsDisjoint
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm extraPlacement) leftRow)
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm extraPlacement) rightRow) :=
  rowPlacementSupports_disjoint_of_injective
    (endpointReserveAugmentedPlacement_injective
      parent h a m hh ha hm extraPlacement
      extraInjective extraProtected)
    hrow

structure EndpointReserveAugmentedSupportCertificate
    (ExtraRow Parent : Type*) (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 <= a) (hm : 4 <= m) where
  extraPlacement : ExtraRow -> Parent × PhaseSection h (m ^ a)
  extraPlacementInjective : Function.Injective extraPlacement
  extraProtected :
    ∀ row : ExtraRow,
      extraPlacement row ∈
        ProductCylinder (Set.univ : Set Parent)
          (PhaseProtectedStrips h (m ^ a))
  supportSet : Set (Parent × PhaseSection h (m ^ a))
  supportSet_eq :
    supportSet =
      endpointReserveAugmentedSupportSet
        parent h a m ha hm extraPlacement
  supportSet_eq_union :
    supportSet =
      endpointReservePlacementSupportSet parent h a m ha hm ∪
        endpointExtraPlacementSupportSet extraPlacement
  supportSet_eq_iUnionRows :
    supportSet =
      ⋃ row : Sum (Fin (2 * a + 3)) ExtraRow,
        rowPlacementSupport
          (endpointReserveAugmentedPlacement
            parent h a m ha hm extraPlacement) row

def endpointReserveAugmentedSupportCertificate
    {ExtraRow Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 <= a) (hm : 4 <= m)
    (extraPlacement : ExtraRow -> Parent × PhaseSection h (m ^ a))
    (extraPlacementInjective : Function.Injective extraPlacement)
    (extraProtected :
      ∀ row : ExtraRow,
        extraPlacement row ∈
          ProductCylinder (Set.univ : Set Parent)
            (PhaseProtectedStrips h (m ^ a))) :
    EndpointReserveAugmentedSupportCertificate
      ExtraRow Parent parent h a m hh ha hm where
  extraPlacement := extraPlacement
  extraPlacementInjective := extraPlacementInjective
  extraProtected := extraProtected
  supportSet :=
    endpointReserveAugmentedSupportSet
      parent h a m ha hm extraPlacement
  supportSet_eq := rfl
  supportSet_eq_union :=
    endpointReserveAugmentedSupportSet_eq_union
      parent h a m ha hm extraPlacement
  supportSet_eq_iUnionRows := rfl

theorem endpointReserveAugmentedSupportCertificate_supportSet
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm) :
    C.supportSet =
      endpointReserveAugmentedSupportSet
        parent h a m ha hm C.extraPlacement :=
  C.supportSet_eq

theorem endpointReserveAugmentedSupportCertificate_supportSet_union
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm) :
    C.supportSet =
      endpointReservePlacementSupportSet parent h a m ha hm ∪
        endpointExtraPlacementSupportSet C.extraPlacement :=
  C.supportSet_eq_union

theorem endpointReserveAugmentedSupportCertificate_supportSet_iUnionRows
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm) :
    C.supportSet =
      ⋃ row : Sum (Fin (2 * a + 3)) ExtraRow,
        rowPlacementSupport
          (endpointReserveAugmentedPlacement
            parent h a m ha hm C.extraPlacement) row :=
  C.supportSet_eq_iUnionRows

theorem endpointReserveAugmentedSupportCertificate_placement_injective
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm) :
    Function.Injective
      (endpointReserveAugmentedPlacement
        parent h a m ha hm C.extraPlacement) :=
  endpointReserveAugmentedPlacement_injective
    parent h a m hh ha hm C.extraPlacement
    C.extraPlacementInjective C.extraProtected

theorem endpointReserveAugmentedSupportCertificate_reserveSubset
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm) :
    endpointReservePlacementSupportSet parent h a m ha hm ⊆
      C.supportSet := by
  rw [C.supportSet_eq]
  exact endpointReserveAugmentedSupportSet_reserveSubset
    parent h a m ha hm C.extraPlacement

theorem endpointReserveAugmentedSupportCertificate_extraSubset
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm) :
    endpointExtraPlacementSupportSet C.extraPlacement ⊆ C.supportSet := by
  rw [C.supportSet_eq]
  exact endpointReserveAugmentedSupportSet_extraSubset
    parent h a m ha hm C.extraPlacement

theorem endpointReserveAugmentedSupportCertificate_extraSubsetProtected
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm) :
    endpointExtraPlacementSupportSet C.extraPlacement ⊆
      ProductCylinder (Set.univ : Set Parent)
        (PhaseProtectedStrips h (m ^ a)) :=
  endpointExtraPlacementSupportSet_subsetProtected
    C.extraPlacement C.extraProtected

theorem endpointReserveAugmentedSupportCertificate_existsUniqueRow
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ C.supportSet) :
    ∃! row : Sum (Fin (2 * a + 3)) ExtraRow,
      endpointReserveAugmentedPlacement
        parent h a m ha hm C.extraPlacement row = x :=
  endpointReserveAugmentedSupportSet_exists_unique_row
    parent h a m ha hm C.extraPlacement
    (endpointReserveAugmentedSupportCertificate_placement_injective C)
    (by
      rw [← C.supportSet_eq]
      exact hx)

theorem endpointReserveAugmentedSupportCertificate_supports_disjoint
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm)
    {leftRow rightRow : Sum (Fin (2 * a + 3)) ExtraRow}
    (hrow : leftRow ≠ rightRow) :
    SetsDisjoint
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) leftRow)
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) rightRow) :=
  endpointReserveAugmentedSupportSet_supports_disjoint
    parent h a m hh ha hm C.extraPlacement
    C.extraPlacementInjective C.extraProtected hrow

theorem endpointReserveAugmentedSupportCertificate_rowSupportSubset
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm)
    (row : Sum (Fin (2 * a + 3)) ExtraRow) :
    rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) row ⊆
      C.supportSet := by
  intro x hx
  rw [endpointReserveAugmentedSupportCertificate_supportSet_iUnionRows C]
  exact Set.mem_iUnion.mpr ⟨row, hx⟩

theorem endpointReserveAugmentedSupportCertificate_reserveRowSupportSubset
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm)
    (reserveRow : Fin (2 * a + 3)) :
    rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) (Sum.inl reserveRow) ⊆
      endpointReservePlacementSupportSet parent h a m ha hm := by
  intro x hx
  have hxEq :
      x =
        endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement (Sum.inl reserveRow) :=
    (rowPlacementSupport_mem
      (endpointReserveAugmentedPlacement
        parent h a m ha hm C.extraPlacement)
      (Sum.inl reserveRow) x).mp hx
  exact (endpointReservePlacementSupportSet_mem_iff_exists_row
    parent h a m ha hm x).mpr
    ⟨reserveRow, by
      simpa [endpointReserveAugmentedPlacement] using hxEq.symm⟩

theorem endpointReserveAugmentedSupportCertificate_extraRowSupportSubset
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm)
    (extraRow : ExtraRow) :
    rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) (Sum.inr extraRow) ⊆
      endpointExtraPlacementSupportSet C.extraPlacement := by
  intro x hx
  have hxEq :
      x =
        endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement (Sum.inr extraRow) :=
    (rowPlacementSupport_mem
      (endpointReserveAugmentedPlacement
        parent h a m ha hm C.extraPlacement)
      (Sum.inr extraRow) x).mp hx
  exact (endpointExtraPlacementSupportSet_mem_iff_exists_row
    C.extraPlacement x).mpr
    ⟨extraRow, by
      simpa [endpointReserveAugmentedPlacement] using hxEq.symm⟩

theorem endpointReserveAugmentedSupportCertificate_reserveExtraDisjoint
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm) :
    SetsDisjoint
      (endpointReservePlacementSupportSet parent h a m ha hm)
      (endpointExtraPlacementSupportSet C.extraPlacement) := by
  intro x hxReserve hxExtra
  have hxProtected :
      x ∈ ProductCylinder (Set.univ : Set Parent)
        (PhaseProtectedStrips h (m ^ a)) :=
    endpointReserveAugmentedSupportCertificate_extraSubsetProtected C hxExtra
  exact
    (endpointReservePlacementSupportSet_disjointProtected
      parent h a m hh ha hm (Set.univ : Set Parent))
      x hxReserve hxProtected

theorem endpointReserveAugmentedSupportCertificate_reserveExtraDisjoint_symm
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm) :
    SetsDisjoint
      (endpointExtraPlacementSupportSet C.extraPlacement)
      (endpointReservePlacementSupportSet parent h a m ha hm) :=
  setsDisjoint_symm
    (endpointReserveAugmentedSupportCertificate_reserveExtraDisjoint C)

theorem endpointReserveAugmentedSupportCertificate_reserveExtraMapsCommute
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm)
    {f g : Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) f)
    (hg : SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement) g) :
    Function.Commute f g :=
  commuteOfDisjointSupportedOn hf hg
    (endpointReserveAugmentedSupportCertificate_reserveExtraDisjoint C)

theorem endpointReserveAugmentedSupportCertificate_reserveExtraMapsCommute_symmSupports
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm)
    {f g : Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement) f)
    (hg : SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) g) :
    Function.Commute f g :=
  commuteOfDisjointSupportedOn_symmSupports hf hg
    (endpointReserveAugmentedSupportCertificate_reserveExtraDisjoint C)

theorem endpointReserveAugmentedSupportCertificate_reserveExtraItersCommute
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm)
    {f g : Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) f)
    (hg : SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  commuteOfDisjointSupportedOn_iterates hf hg
    (endpointReserveAugmentedSupportCertificate_reserveExtraDisjoint C) n k

theorem endpointReserveAugmentedSupportCertificate_reserveExtraItersCommute_symmSupports
    {ExtraRow Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm)
    {f g : Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement) f)
    (hg : SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  commuteOfDisjointSupportedOn_iterates_symmSupports hf hg
    (endpointReserveAugmentedSupportCertificate_reserveExtraDisjoint C) n k

theorem endpointReserveAugmentedSupportCertificate_reserveExtraWordEvalsCommute
    {ExtraRow ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm)
    (leftStep : ι -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) (leftStep i))
    (hright : ∀ j : κ, SupportedOn
      (endpointExtraPlacementSupportSet C.extraPlacement) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  commuteOfDisjointSupportedWordEvals
    leftStep rightStep hleft hright
    (endpointReserveAugmentedSupportCertificate_reserveExtraDisjoint C)
    leftWord rightWord

theorem endpointReserveAugmentedSupportCertificate_reserveExtraWordEvalsCommute_symmSupports
    {ExtraRow ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm)
    (leftStep : ι -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn
      (endpointExtraPlacementSupportSet C.extraPlacement) (leftStep i))
    (hright : ∀ j : κ, SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  commuteOfDisjointSupportedWordEvals_symmSupports
    leftStep rightStep hleft hright
    (endpointReserveAugmentedSupportCertificate_reserveExtraDisjoint C)
    leftWord rightWord

theorem endpointReserveAugmentedSupportCertificate_reserveExtraWordItersCommute
    {ExtraRow ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm)
    (leftStep : ι -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) (leftStep i))
    (hright : ∀ j : κ, SupportedOn
      (endpointExtraPlacementSupportSet C.extraPlacement) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  commuteOfDisjointSupportedWordEvalIterates
    leftStep rightStep hleft hright
    (endpointReserveAugmentedSupportCertificate_reserveExtraDisjoint C)
    leftWord rightWord n k

theorem endpointReserveAugmentedSupportCertificate_reserveExtraWordItersCommute_symmSupports
    {ExtraRow ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedSupportCertificate
        ExtraRow Parent parent h a m hh ha hm)
    (leftStep : ι -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn
      (endpointExtraPlacementSupportSet C.extraPlacement) (leftStep i))
    (hright : ∀ j : κ, SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  commuteOfDisjointSupportedWordEvalIterates_symmSupports
    leftStep rightStep hleft hright
    (endpointReserveAugmentedSupportCertificate_reserveExtraDisjoint C)
    leftWord rightWord n k

structure EndpointReserveAugmentedRowWordCertificate
    (ExtraRow Symbol Parent : Type*) (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 <= a) (hm : 4 <= m) where
  extraPlacement : ExtraRow -> Parent × PhaseSection h (m ^ a)
  step :
    Sum (Fin (2 * a + 3)) ExtraRow -> Symbol ->
      Parent × PhaseSection h (m ^ a) ->
        Parent × PhaseSection h (m ^ a)
  word : Sum (Fin (2 * a + 3)) ExtraRow -> List Symbol
  extraPlacementInjective : Function.Injective extraPlacement
  extraProtected :
    ∀ row : ExtraRow,
      extraPlacement row ∈
        ProductCylinder (Set.univ : Set Parent)
          (PhaseProtectedStrips h (m ^ a))
  supported :
    ∀ row : Sum (Fin (2 * a + 3)) ExtraRow, ∀ symbol : Symbol,
      SupportedOn
        (rowPlacementSupport
          (endpointReserveAugmentedPlacement
            parent h a m ha hm extraPlacement) row)
        (step row symbol)

theorem endpointReserveAugmentedRowWordCertificate_placement_injective
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm) :
    Function.Injective
      (endpointReserveAugmentedPlacement
        parent h a m ha hm C.extraPlacement) :=
  endpointReserveAugmentedPlacement_injective
    parent h a m hh ha hm C.extraPlacement
    C.extraPlacementInjective C.extraProtected

def EndpointReserveAugmentedRowWordCertificate.toRowWordPlacementCertificate
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm) :
    RowWordPlacementCertificate
      (Sum (Fin (2 * a + 3)) ExtraRow)
      Symbol Parent (PhaseSection h (m ^ a)) where
  placement :=
    endpointReserveAugmentedPlacement
      parent h a m ha hm C.extraPlacement
  step := C.step
  word := C.word
  placementInjective :=
    endpointReserveAugmentedRowWordCertificate_placement_injective C
  supported := C.supported

def EndpointReserveAugmentedRowWordCertificate.toSupportCertificate
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm) :
    EndpointReserveAugmentedSupportCertificate
      ExtraRow Parent parent h a m hh ha hm :=
  endpointReserveAugmentedSupportCertificate
    parent h a m hh ha hm C.extraPlacement
    C.extraPlacementInjective C.extraProtected

theorem endpointReserveAugmentedRowWordCertificate_supportSet_union
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm) :
    C.toSupportCertificate.supportSet =
      endpointReservePlacementSupportSet parent h a m ha hm ∪
        endpointExtraPlacementSupportSet C.extraPlacement :=
  endpointReserveAugmentedSupportCertificate_supportSet_union
    C.toSupportCertificate

theorem endpointReserveAugmentedRowWordCertificate_supportSet_iUnionRows
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm) :
    C.toSupportCertificate.supportSet =
      ⋃ row : Sum (Fin (2 * a + 3)) ExtraRow,
        rowPlacementSupport
          (endpointReserveAugmentedPlacement
            parent h a m ha hm C.extraPlacement) row :=
  endpointReserveAugmentedSupportCertificate_supportSet_iUnionRows
    C.toSupportCertificate

theorem endpointReserveAugmentedRowWordCertificate_supportExtraProtected
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm) :
    endpointExtraPlacementSupportSet C.extraPlacement ⊆
      ProductCylinder (Set.univ : Set Parent)
        (PhaseProtectedStrips h (m ^ a)) :=
  endpointReserveAugmentedSupportCertificate_extraSubsetProtected
    C.toSupportCertificate

theorem endpointReserveAugmentedRowWordCertificate_supportExistsUniqueRow
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ C.toSupportCertificate.supportSet) :
    ∃! row : Sum (Fin (2 * a + 3)) ExtraRow,
      endpointReserveAugmentedPlacement
        parent h a m ha hm C.extraPlacement row = x :=
  endpointReserveAugmentedSupportCertificate_existsUniqueRow
    C.toSupportCertificate hx

theorem endpointReserveAugmentedRowWordCertificate_eval
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (row : Sum (Fin (2 * a + 3)) ExtraRow) :
    C.toRowWordPlacementCertificate.eval row =
      wordEval (C.step row) (C.word row) :=
  rfl

theorem endpointReserveAugmentedRowWordCertificate_eval_supported
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (row : Sum (Fin (2 * a + 3)) ExtraRow) :
    SupportedOn
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) row)
      (C.toRowWordPlacementCertificate.eval row) :=
  rowWordPlacementCertificate_eval_supported
    C.toRowWordPlacementCertificate row

theorem endpointReserveAugmentedRowWordCertificate_step_supportedOn_supportSet
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (row : Sum (Fin (2 * a + 3)) ExtraRow) (symbol : Symbol) :
    SupportedOn C.toSupportCertificate.supportSet (C.step row symbol) :=
  supportedOn_mono
    (endpointReserveAugmentedSupportCertificate_rowSupportSubset
      C.toSupportCertificate row)
    (C.supported row symbol)

theorem endpointReserveAugmentedRowWordCertificate_eval_supportedOn_supportSet
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (row : Sum (Fin (2 * a + 3)) ExtraRow) :
    SupportedOn C.toSupportCertificate.supportSet
      (C.toRowWordPlacementCertificate.eval row) :=
  supportedOn_mono
    (endpointReserveAugmentedSupportCertificate_rowSupportSubset
      C.toSupportCertificate row)
    (endpointReserveAugmentedRowWordCertificate_eval_supported C row)

theorem endpointReserveAugmentedRowWordCertificate_evalWord_supportedOn_supportSet
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (rows : List (Sum (Fin (2 * a + 3)) ExtraRow)) :
    SupportedOn C.toSupportCertificate.supportSet
      (wordEval (fun row => C.toRowWordPlacementCertificate.eval row) rows) :=
  supportedOn_wordEval
    (fun row => C.toRowWordPlacementCertificate.eval row)
    (endpointReserveAugmentedRowWordCertificate_eval_supportedOn_supportSet C)
    rows

theorem endpointReserveAugmentedRowWordCertificate_evalWord_iterate_supportedOn_supportSet
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (rows : List (Sum (Fin (2 * a + 3)) ExtraRow)) (n : Nat) :
    SupportedOn C.toSupportCertificate.supportSet
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval row) rows)^[n]) :=
  supportedOn_iterate
    (endpointReserveAugmentedRowWordCertificate_evalWord_supportedOn_supportSet
      C rows)
    n

theorem endpointReserveAugmentedRowWordCertificate_supports_disjoint
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    {leftRow rightRow : Sum (Fin (2 * a + 3)) ExtraRow}
    (hrow : leftRow ≠ rightRow) :
    SetsDisjoint
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) leftRow)
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) rightRow) :=
  rowWordPlacementCertificate_supports_disjoint
    C.toRowWordPlacementCertificate hrow

theorem endpointReserveAugmentedRowWordCertificate_evalsCommute
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    {leftRow rightRow : Sum (Fin (2 * a + 3)) ExtraRow}
    (hrow : leftRow ≠ rightRow) :
    Function.Commute
      (C.toRowWordPlacementCertificate.eval leftRow)
      (C.toRowWordPlacementCertificate.eval rightRow) :=
  rowWordPlacementCertificate_evalsCommute
    C.toRowWordPlacementCertificate hrow

theorem endpointReserveAugmentedRowWordCertificate_evalIteratesCommute
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    {leftRow rightRow : Sum (Fin (2 * a + 3)) ExtraRow}
    (hrow : leftRow ≠ rightRow) (n k : Nat) :
    Function.Commute
      ((C.toRowWordPlacementCertificate.eval leftRow)^[n])
      ((C.toRowWordPlacementCertificate.eval rightRow)^[k]) :=
  rowWordPlacementCertificate_evalIteratesCommute
    C.toRowWordPlacementCertificate hrow n k

theorem endpointReserveAugmentedRowWordCertificate_reserveExtraRowSupportsDisjoint
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (reserveRow : Fin (2 * a + 3)) (extraRow : ExtraRow) :
    SetsDisjoint
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) (Sum.inl reserveRow))
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) (Sum.inr extraRow)) :=
  endpointReserveAugmentedRowWordCertificate_supports_disjoint C
    (by intro hsum; cases hsum)

theorem endpointReserveAugmentedRowWordCertificate_extraReserveRowSupportsDisjoint
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (extraRow : ExtraRow) (reserveRow : Fin (2 * a + 3)) :
    SetsDisjoint
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) (Sum.inr extraRow))
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) (Sum.inl reserveRow)) :=
  endpointReserveAugmentedRowWordCertificate_supports_disjoint C
    (by intro hsum; cases hsum)

theorem endpointReserveAugmentedRowWordCertificate_reserveExtraRowEvalsCommute
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (reserveRow : Fin (2 * a + 3)) (extraRow : ExtraRow) :
    Function.Commute
      (C.toRowWordPlacementCertificate.eval (Sum.inl reserveRow))
      (C.toRowWordPlacementCertificate.eval (Sum.inr extraRow)) :=
  endpointReserveAugmentedRowWordCertificate_evalsCommute C
    (by intro hsum; cases hsum)

theorem endpointReserveAugmentedRowWordCertificate_extraReserveRowEvalsCommute
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (extraRow : ExtraRow) (reserveRow : Fin (2 * a + 3)) :
    Function.Commute
      (C.toRowWordPlacementCertificate.eval (Sum.inr extraRow))
      (C.toRowWordPlacementCertificate.eval (Sum.inl reserveRow)) :=
  endpointReserveAugmentedRowWordCertificate_evalsCommute C
    (by intro hsum; cases hsum)

theorem endpointReserveAugmentedRowWordCertificate_reserveExtraRowEvalIteratesCommute
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (reserveRow : Fin (2 * a + 3)) (extraRow : ExtraRow) (n k : Nat) :
    Function.Commute
      ((C.toRowWordPlacementCertificate.eval (Sum.inl reserveRow))^[n])
      ((C.toRowWordPlacementCertificate.eval (Sum.inr extraRow))^[k]) :=
  endpointReserveAugmentedRowWordCertificate_evalIteratesCommute C
    (by intro hsum; cases hsum) n k

theorem endpointReserveAugmentedRowWordCertificate_extraReserveRowEvalIteratesCommute
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (extraRow : ExtraRow) (reserveRow : Fin (2 * a + 3)) (n k : Nat) :
    Function.Commute
      ((C.toRowWordPlacementCertificate.eval (Sum.inr extraRow))^[n])
      ((C.toRowWordPlacementCertificate.eval (Sum.inl reserveRow))^[k]) :=
  endpointReserveAugmentedRowWordCertificate_evalIteratesCommute C
    (by intro hsum; cases hsum) n k

theorem endpointReserveAugmentedRowWordCertificate_reserveEval_onReserve
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (reserveRow : Fin (2 * a + 3)) :
    SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm)
      (C.toRowWordPlacementCertificate.eval (Sum.inl reserveRow)) :=
  supportedOn_mono
    (endpointReserveAugmentedSupportCertificate_reserveRowSupportSubset
      C.toSupportCertificate reserveRow)
    (endpointReserveAugmentedRowWordCertificate_eval_supported
      C (Sum.inl reserveRow))

theorem endpointReserveAugmentedRowWordCertificate_extraEval_onExtra
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (extraRow : ExtraRow) :
    SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement)
      (C.toRowWordPlacementCertificate.eval (Sum.inr extraRow)) :=
  supportedOn_mono
    (endpointReserveAugmentedSupportCertificate_extraRowSupportSubset
      C.toSupportCertificate extraRow)
    (endpointReserveAugmentedRowWordCertificate_eval_supported
      C (Sum.inr extraRow))

theorem endpointReserveAugmentedRowWordCertificate_reserveWord_onReserve
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (reserveRows : List (Fin (2 * a + 3))) :
    SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm)
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows) :=
  supportedOn_wordEval
    (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
    (endpointReserveAugmentedRowWordCertificate_reserveEval_onReserve C)
    reserveRows

theorem endpointReserveAugmentedRowWordCertificate_extraWord_onExtra
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (extraRows : List ExtraRow) :
    SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement)
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows) :=
  supportedOn_wordEval
    (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
    (endpointReserveAugmentedRowWordCertificate_extraEval_onExtra C)
    extraRows

theorem endpointReserveAugmentedRowWordCertificate_reserveWordIter_onReserve
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (reserveRows : List (Fin (2 * a + 3))) (n : Nat) :
    SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm)
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows)^[n]) :=
  supportedOn_iterate
    (endpointReserveAugmentedRowWordCertificate_reserveWord_onReserve
      C reserveRows)
    n

theorem endpointReserveAugmentedRowWordCertificate_extraWordIter_onExtra
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (extraRows : List ExtraRow) (n : Nat) :
    SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement)
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows)^[n]) :=
  supportedOn_iterate
    (endpointReserveAugmentedRowWordCertificate_extraWord_onExtra
      C extraRows)
    n

theorem endpointReserveAugmentedRowWordCertificate_reserveExtraWordsCommute
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (reserveRows : List (Fin (2 * a + 3))) (extraRows : List ExtraRow) :
    Function.Commute
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows)
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows) :=
  endpointReserveAugmentedSupportCertificate_reserveExtraMapsCommute
    C.toSupportCertificate
    (endpointReserveAugmentedRowWordCertificate_reserveWord_onReserve
      C reserveRows)
    (endpointReserveAugmentedRowWordCertificate_extraWord_onExtra
      C extraRows)

theorem endpointReserveAugmentedRowWordCertificate_extraReserveWordsCommute
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (extraRows : List ExtraRow) (reserveRows : List (Fin (2 * a + 3))) :
    Function.Commute
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows)
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows) :=
  endpointReserveAugmentedSupportCertificate_reserveExtraMapsCommute_symmSupports
    C.toSupportCertificate
    (endpointReserveAugmentedRowWordCertificate_extraWord_onExtra
      C extraRows)
    (endpointReserveAugmentedRowWordCertificate_reserveWord_onReserve
      C reserveRows)

theorem endpointReserveAugmentedRowWordCertificate_reserveExtraWordItersCommute
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (reserveRows : List (Fin (2 * a + 3))) (extraRows : List ExtraRow)
    (n k : Nat) :
    Function.Commute
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows)^[n])
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows)^[k]) :=
  endpointReserveAugmentedSupportCertificate_reserveExtraItersCommute
    C.toSupportCertificate
    (endpointReserveAugmentedRowWordCertificate_reserveWord_onReserve
      C reserveRows)
    (endpointReserveAugmentedRowWordCertificate_extraWord_onExtra
      C extraRows)
    n k

theorem endpointReserveAugmentedRowWordCertificate_extraReserveWordItersCommute
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (extraRows : List ExtraRow) (reserveRows : List (Fin (2 * a + 3)))
    (n k : Nat) :
    Function.Commute
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows)^[n])
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows)^[k]) :=
  endpointReserveAugmentedSupportCertificate_reserveExtraItersCommute_symmSupports
    C.toSupportCertificate
    (endpointReserveAugmentedRowWordCertificate_extraWord_onExtra
      C extraRows)
    (endpointReserveAugmentedRowWordCertificate_reserveWord_onReserve
      C reserveRows)
    n k

theorem endpointReserveAugmentedRowWordCertificate_reserveExtraDisjoint
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm) :
    SetsDisjoint
      (endpointReservePlacementSupportSet parent h a m ha hm)
      (endpointExtraPlacementSupportSet C.extraPlacement) :=
  endpointReserveAugmentedSupportCertificate_reserveExtraDisjoint
    C.toSupportCertificate

theorem endpointReserveAugmentedRowWordCertificate_reserveExtraDisjoint_symm
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm) :
    SetsDisjoint
      (endpointExtraPlacementSupportSet C.extraPlacement)
      (endpointReservePlacementSupportSet parent h a m ha hm) :=
  endpointReserveAugmentedSupportCertificate_reserveExtraDisjoint_symm
    C.toSupportCertificate

theorem endpointReserveAugmentedRowWordCertificate_reserveExtraMapCommute
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    {f g : Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) f)
    (hg : SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement) g) :
    Function.Commute f g :=
  endpointReserveAugmentedSupportCertificate_reserveExtraMapsCommute
    C.toSupportCertificate hf hg

theorem endpointReserveAugmentedRowWordCertificate_reserveExtraMapCommute_symm
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    {f g : Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement) f)
    (hg : SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) g) :
    Function.Commute f g :=
  endpointReserveAugmentedSupportCertificate_reserveExtraMapsCommute_symmSupports
    C.toSupportCertificate hf hg

theorem endpointReserveAugmentedRowWordCertificate_reserveExtraIterCommute
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    {f g : Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) f)
    (hg : SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  endpointReserveAugmentedSupportCertificate_reserveExtraItersCommute
    C.toSupportCertificate hf hg n k

theorem endpointReserveAugmentedRowWordCertificate_reserveExtraIterCommute_symm
    {ExtraRow Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    {f g : Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement) f)
    (hg : SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  endpointReserveAugmentedSupportCertificate_reserveExtraItersCommute_symmSupports
    C.toSupportCertificate hf hg n k

theorem endpointReserveAugmentedRowWordCertificate_reserveExtraWordCommute
    {ExtraRow Symbol ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (leftStep : ι -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) (leftStep i))
    (hright : ∀ j : κ, SupportedOn
      (endpointExtraPlacementSupportSet C.extraPlacement) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  endpointReserveAugmentedSupportCertificate_reserveExtraWordEvalsCommute
    C.toSupportCertificate leftStep rightStep hleft hright
    leftWord rightWord

theorem endpointReserveAugmentedRowWordCertificate_reserveExtraWordCommute_symm
    {ExtraRow Symbol ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (leftStep : ι -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn
      (endpointExtraPlacementSupportSet C.extraPlacement) (leftStep i))
    (hright : ∀ j : κ, SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  endpointReserveAugmentedSupportCertificate_reserveExtraWordEvalsCommute_symmSupports
    C.toSupportCertificate leftStep rightStep hleft hright
    leftWord rightWord

theorem endpointReserveAugmentedRowWordCertificate_reserveExtraWordIterCommute
    {ExtraRow Symbol ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (leftStep : ι -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) (leftStep i))
    (hright : ∀ j : κ, SupportedOn
      (endpointExtraPlacementSupportSet C.extraPlacement) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  endpointReserveAugmentedSupportCertificate_reserveExtraWordItersCommute
    C.toSupportCertificate leftStep rightStep hleft hright
    leftWord rightWord n k

theorem endpointReserveAugmentedRowWordCertificate_reserveExtraWordIterCommute_symm
    {ExtraRow Symbol ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedRowWordCertificate
        ExtraRow Symbol Parent parent h a m hh ha hm)
    (leftStep : ι -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn
      (endpointExtraPlacementSupportSet C.extraPlacement) (leftStep i))
    (hright : ∀ j : κ, SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  endpointReserveAugmentedSupportCertificate_reserveExtraWordItersCommute_symmSupports
    C.toSupportCertificate leftStep rightStep hleft hright
    leftWord rightWord n k

structure EndpointReserveAugmentedFinRowWordCertificate
    (extraCount : Nat) (Symbol Parent : Type*) (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 <= a) (hm : 4 <= m) where
  extraPlacement : Fin extraCount -> Parent × PhaseSection h (m ^ a)
  step :
    Sum (Fin (2 * a + 3)) (Fin extraCount) -> Symbol ->
      Parent × PhaseSection h (m ^ a) ->
        Parent × PhaseSection h (m ^ a)
  word : Sum (Fin (2 * a + 3)) (Fin extraCount) -> List Symbol
  extraPlacementNe :
    ∀ leftRow rightRow : Fin extraCount,
      leftRow ≠ rightRow ->
        extraPlacement leftRow ≠ extraPlacement rightRow
  extraProtected :
    ∀ row : Fin extraCount,
      extraPlacement row ∈
        ProductCylinder (Set.univ : Set Parent)
          (PhaseProtectedStrips h (m ^ a))
  supported :
    ∀ row : Sum (Fin (2 * a + 3)) (Fin extraCount),
      ∀ symbol : Symbol,
        SupportedOn
          (rowPlacementSupport
            (endpointReserveAugmentedPlacement
              parent h a m ha hm extraPlacement) row)
          (step row symbol)

theorem endpointReserveAugmentedFinRowWordCertificate_extraPlacement_injective
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm) :
    Function.Injective C.extraPlacement := by
  intro leftRow rightRow hplacement
  by_cases hrow : leftRow = rightRow
  · exact hrow
  · exact False.elim
      (C.extraPlacementNe leftRow rightRow hrow hplacement)

def EndpointReserveAugmentedFinRowWordCertificate.toEndpointReserveAugmentedRowWordCertificate
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm) :
    EndpointReserveAugmentedRowWordCertificate
      (Fin extraCount) Symbol Parent parent h a m hh ha hm where
  extraPlacement := C.extraPlacement
  step := C.step
  word := C.word
  extraPlacementInjective :=
    endpointReserveAugmentedFinRowWordCertificate_extraPlacement_injective C
  extraProtected := C.extraProtected
  supported := C.supported

def EndpointReserveAugmentedFinRowWordCertificate.toRowWordPlacementCertificate
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm) :
    RowWordPlacementCertificate
      (Sum (Fin (2 * a + 3)) (Fin extraCount))
      Symbol Parent (PhaseSection h (m ^ a)) :=
  C.toEndpointReserveAugmentedRowWordCertificate
    |>.toRowWordPlacementCertificate

def EndpointReserveAugmentedFinRowWordCertificate.toSupportCertificate
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm) :
    EndpointReserveAugmentedSupportCertificate
      (Fin extraCount) Parent parent h a m hh ha hm :=
  C.toEndpointReserveAugmentedRowWordCertificate
    |>.toSupportCertificate

theorem endpointReserveAugmentedFinRowWordCertificate_supportSet_union
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm) :
    C.toSupportCertificate.supportSet =
      endpointReservePlacementSupportSet parent h a m ha hm ∪
        endpointExtraPlacementSupportSet C.extraPlacement :=
  endpointReserveAugmentedSupportCertificate_supportSet_union
    C.toSupportCertificate

theorem endpointReserveAugmentedFinRowWordCertificate_supportSet_iUnionRows
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm) :
    C.toSupportCertificate.supportSet =
      ⋃ row : Sum (Fin (2 * a + 3)) (Fin extraCount),
        rowPlacementSupport
          (endpointReserveAugmentedPlacement
            parent h a m ha hm C.extraPlacement) row :=
  endpointReserveAugmentedSupportCertificate_supportSet_iUnionRows
    C.toSupportCertificate

theorem endpointReserveAugmentedFinRowWordCertificate_supportExtraProtected
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm) :
    endpointExtraPlacementSupportSet C.extraPlacement ⊆
      ProductCylinder (Set.univ : Set Parent)
        (PhaseProtectedStrips h (m ^ a)) :=
  endpointReserveAugmentedSupportCertificate_extraSubsetProtected
    C.toSupportCertificate

theorem endpointReserveAugmentedFinRowWordCertificate_supportExistsUniqueRow
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ C.toSupportCertificate.supportSet) :
    ∃! row : Sum (Fin (2 * a + 3)) (Fin extraCount),
      endpointReserveAugmentedPlacement
        parent h a m ha hm C.extraPlacement row = x :=
  endpointReserveAugmentedSupportCertificate_existsUniqueRow
    C.toSupportCertificate hx

theorem endpointReserveAugmentedFinRowWordCertificate_eval
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (row : Sum (Fin (2 * a + 3)) (Fin extraCount)) :
    C.toRowWordPlacementCertificate.eval row =
      wordEval (C.step row) (C.word row) :=
  rfl

theorem endpointReserveAugmentedFinRowWordCertificate_eval_supported
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (row : Sum (Fin (2 * a + 3)) (Fin extraCount)) :
    SupportedOn
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) row)
      (C.toRowWordPlacementCertificate.eval row) :=
  endpointReserveAugmentedRowWordCertificate_eval_supported
    C.toEndpointReserveAugmentedRowWordCertificate row

theorem endpointReserveAugmentedFinRowWordCertificate_step_supportedOn_supportSet
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (row : Sum (Fin (2 * a + 3)) (Fin extraCount))
    (symbol : Symbol) :
    SupportedOn C.toSupportCertificate.supportSet (C.step row symbol) :=
  endpointReserveAugmentedRowWordCertificate_step_supportedOn_supportSet
    C.toEndpointReserveAugmentedRowWordCertificate row symbol

theorem endpointReserveAugmentedFinRowWordCertificate_eval_supportedOn_supportSet
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (row : Sum (Fin (2 * a + 3)) (Fin extraCount)) :
    SupportedOn C.toSupportCertificate.supportSet
      (C.toRowWordPlacementCertificate.eval row) :=
  endpointReserveAugmentedRowWordCertificate_eval_supportedOn_supportSet
    C.toEndpointReserveAugmentedRowWordCertificate row

theorem endpointReserveAugmentedFinRowWordCertificate_evalWord_supportedOn_supportSet
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (rows : List (Sum (Fin (2 * a + 3)) (Fin extraCount))) :
    SupportedOn C.toSupportCertificate.supportSet
      (wordEval (fun row => C.toRowWordPlacementCertificate.eval row) rows) :=
  endpointReserveAugmentedRowWordCertificate_evalWord_supportedOn_supportSet
    C.toEndpointReserveAugmentedRowWordCertificate rows

theorem endpointReserveAugmentedFinRowWordCertificate_evalWord_iterate_supportedOn_supportSet
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (rows : List (Sum (Fin (2 * a + 3)) (Fin extraCount))) (n : Nat) :
    SupportedOn C.toSupportCertificate.supportSet
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval row) rows)^[n]) :=
  endpointReserveAugmentedRowWordCertificate_evalWord_iterate_supportedOn_supportSet
    C.toEndpointReserveAugmentedRowWordCertificate rows n

theorem endpointReserveAugmentedFinRowWordCertificate_supports_disjoint
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    {leftRow rightRow : Sum (Fin (2 * a + 3)) (Fin extraCount)}
    (hrow : leftRow ≠ rightRow) :
    SetsDisjoint
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) leftRow)
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) rightRow) :=
  endpointReserveAugmentedRowWordCertificate_supports_disjoint
    C.toEndpointReserveAugmentedRowWordCertificate hrow

theorem endpointReserveAugmentedFinRowWordCertificate_evalsCommute
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    {leftRow rightRow : Sum (Fin (2 * a + 3)) (Fin extraCount)}
    (hrow : leftRow ≠ rightRow) :
    Function.Commute
      (C.toRowWordPlacementCertificate.eval leftRow)
      (C.toRowWordPlacementCertificate.eval rightRow) :=
  endpointReserveAugmentedRowWordCertificate_evalsCommute
    C.toEndpointReserveAugmentedRowWordCertificate hrow

theorem endpointReserveAugmentedFinRowWordCertificate_evalIteratesCommute
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    {leftRow rightRow : Sum (Fin (2 * a + 3)) (Fin extraCount)}
    (hrow : leftRow ≠ rightRow) (n k : Nat) :
    Function.Commute
      ((C.toRowWordPlacementCertificate.eval leftRow)^[n])
      ((C.toRowWordPlacementCertificate.eval rightRow)^[k]) :=
  endpointReserveAugmentedRowWordCertificate_evalIteratesCommute
    C.toEndpointReserveAugmentedRowWordCertificate hrow n k

theorem endpointReserveAugmentedFinRowWordCertificate_reserveExtraRowSupportsDisjoint
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (reserveRow : Fin (2 * a + 3)) (extraRow : Fin extraCount) :
    SetsDisjoint
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) (Sum.inl reserveRow))
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) (Sum.inr extraRow)) :=
  endpointReserveAugmentedRowWordCertificate_reserveExtraRowSupportsDisjoint
    C.toEndpointReserveAugmentedRowWordCertificate reserveRow extraRow

theorem endpointReserveAugmentedFinRowWordCertificate_extraReserveRowSupportsDisjoint
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (extraRow : Fin extraCount) (reserveRow : Fin (2 * a + 3)) :
    SetsDisjoint
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) (Sum.inr extraRow))
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) (Sum.inl reserveRow)) :=
  endpointReserveAugmentedRowWordCertificate_extraReserveRowSupportsDisjoint
    C.toEndpointReserveAugmentedRowWordCertificate extraRow reserveRow

theorem endpointReserveAugmentedFinRowWordCertificate_reserveExtraRowEvalsCommute
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (reserveRow : Fin (2 * a + 3)) (extraRow : Fin extraCount) :
    Function.Commute
      (C.toRowWordPlacementCertificate.eval (Sum.inl reserveRow))
      (C.toRowWordPlacementCertificate.eval (Sum.inr extraRow)) :=
  endpointReserveAugmentedRowWordCertificate_reserveExtraRowEvalsCommute
    C.toEndpointReserveAugmentedRowWordCertificate reserveRow extraRow

theorem endpointReserveAugmentedFinRowWordCertificate_extraReserveRowEvalsCommute
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (extraRow : Fin extraCount) (reserveRow : Fin (2 * a + 3)) :
    Function.Commute
      (C.toRowWordPlacementCertificate.eval (Sum.inr extraRow))
      (C.toRowWordPlacementCertificate.eval (Sum.inl reserveRow)) :=
  endpointReserveAugmentedRowWordCertificate_extraReserveRowEvalsCommute
    C.toEndpointReserveAugmentedRowWordCertificate extraRow reserveRow

theorem endpointReserveAugmentedFinRowWordCertificate_reserveExtraRowEvalIteratesCommute
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (reserveRow : Fin (2 * a + 3)) (extraRow : Fin extraCount)
    (n k : Nat) :
    Function.Commute
      ((C.toRowWordPlacementCertificate.eval (Sum.inl reserveRow))^[n])
      ((C.toRowWordPlacementCertificate.eval (Sum.inr extraRow))^[k]) :=
  endpointReserveAugmentedRowWordCertificate_reserveExtraRowEvalIteratesCommute
    C.toEndpointReserveAugmentedRowWordCertificate reserveRow extraRow n k

theorem endpointReserveAugmentedFinRowWordCertificate_extraReserveRowEvalIteratesCommute
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (extraRow : Fin extraCount) (reserveRow : Fin (2 * a + 3))
    (n k : Nat) :
    Function.Commute
      ((C.toRowWordPlacementCertificate.eval (Sum.inr extraRow))^[n])
      ((C.toRowWordPlacementCertificate.eval (Sum.inl reserveRow))^[k]) :=
  endpointReserveAugmentedRowWordCertificate_extraReserveRowEvalIteratesCommute
    C.toEndpointReserveAugmentedRowWordCertificate extraRow reserveRow n k

theorem endpointReserveAugmentedFinRowWordCertificate_reserveEval_onReserve
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (reserveRow : Fin (2 * a + 3)) :
    SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm)
      (C.toRowWordPlacementCertificate.eval (Sum.inl reserveRow)) :=
  endpointReserveAugmentedRowWordCertificate_reserveEval_onReserve
    C.toEndpointReserveAugmentedRowWordCertificate reserveRow

theorem endpointReserveAugmentedFinRowWordCertificate_extraEval_onExtra
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (extraRow : Fin extraCount) :
    SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement)
      (C.toRowWordPlacementCertificate.eval (Sum.inr extraRow)) :=
  endpointReserveAugmentedRowWordCertificate_extraEval_onExtra
    C.toEndpointReserveAugmentedRowWordCertificate extraRow

theorem endpointReserveAugmentedFinRowWordCertificate_reserveWord_onReserve
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (reserveRows : List (Fin (2 * a + 3))) :
    SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm)
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows) :=
  endpointReserveAugmentedRowWordCertificate_reserveWord_onReserve
    C.toEndpointReserveAugmentedRowWordCertificate reserveRows

theorem endpointReserveAugmentedFinRowWordCertificate_extraWord_onExtra
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (extraRows : List (Fin extraCount)) :
    SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement)
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows) :=
  endpointReserveAugmentedRowWordCertificate_extraWord_onExtra
    C.toEndpointReserveAugmentedRowWordCertificate extraRows

theorem endpointReserveAugmentedFinRowWordCertificate_reserveWordIter_onReserve
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (reserveRows : List (Fin (2 * a + 3))) (n : Nat) :
    SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm)
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows)^[n]) :=
  endpointReserveAugmentedRowWordCertificate_reserveWordIter_onReserve
    C.toEndpointReserveAugmentedRowWordCertificate reserveRows n

theorem endpointReserveAugmentedFinRowWordCertificate_extraWordIter_onExtra
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (extraRows : List (Fin extraCount)) (n : Nat) :
    SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement)
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows)^[n]) :=
  endpointReserveAugmentedRowWordCertificate_extraWordIter_onExtra
    C.toEndpointReserveAugmentedRowWordCertificate extraRows n

theorem endpointReserveAugmentedFinRowWordCertificate_reserveExtraWordsCommute
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (reserveRows : List (Fin (2 * a + 3)))
    (extraRows : List (Fin extraCount)) :
    Function.Commute
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows)
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows) :=
  endpointReserveAugmentedRowWordCertificate_reserveExtraWordsCommute
    C.toEndpointReserveAugmentedRowWordCertificate reserveRows extraRows

theorem endpointReserveAugmentedFinRowWordCertificate_extraReserveWordsCommute
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (extraRows : List (Fin extraCount))
    (reserveRows : List (Fin (2 * a + 3))) :
    Function.Commute
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows)
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows) :=
  endpointReserveAugmentedRowWordCertificate_extraReserveWordsCommute
    C.toEndpointReserveAugmentedRowWordCertificate extraRows reserveRows

theorem endpointReserveAugmentedFinRowWordCertificate_reserveExtraWordItersCommute
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (reserveRows : List (Fin (2 * a + 3)))
    (extraRows : List (Fin extraCount)) (n k : Nat) :
    Function.Commute
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows)^[n])
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows)^[k]) :=
  endpointReserveAugmentedRowWordCertificate_reserveExtraWordItersCommute
    C.toEndpointReserveAugmentedRowWordCertificate reserveRows extraRows n k

theorem endpointReserveAugmentedFinRowWordCertificate_extraReserveWordItersCommute
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (extraRows : List (Fin extraCount))
    (reserveRows : List (Fin (2 * a + 3))) (n k : Nat) :
    Function.Commute
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows)^[n])
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows)^[k]) :=
  endpointReserveAugmentedRowWordCertificate_extraReserveWordItersCommute
    C.toEndpointReserveAugmentedRowWordCertificate extraRows reserveRows n k

theorem endpointReserveAugmentedFinRowWordCertificate_reserveExtraDisjoint
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm) :
    SetsDisjoint
      (endpointReservePlacementSupportSet parent h a m ha hm)
      (endpointExtraPlacementSupportSet C.extraPlacement) :=
  endpointReserveAugmentedRowWordCertificate_reserveExtraDisjoint
    C.toEndpointReserveAugmentedRowWordCertificate

theorem endpointReserveAugmentedFinRowWordCertificate_reserveExtraDisjoint_symm
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm) :
    SetsDisjoint
      (endpointExtraPlacementSupportSet C.extraPlacement)
      (endpointReservePlacementSupportSet parent h a m ha hm) :=
  endpointReserveAugmentedRowWordCertificate_reserveExtraDisjoint_symm
    C.toEndpointReserveAugmentedRowWordCertificate

theorem endpointReserveAugmentedFinRowWordCertificate_reserveExtraMapCommute
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    {f g : Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) f)
    (hg : SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement) g) :
    Function.Commute f g :=
  endpointReserveAugmentedRowWordCertificate_reserveExtraMapCommute
    C.toEndpointReserveAugmentedRowWordCertificate hf hg

theorem endpointReserveAugmentedFinRowWordCertificate_reserveExtraMapCommute_symm
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    {f g : Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement) f)
    (hg : SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) g) :
    Function.Commute f g :=
  endpointReserveAugmentedRowWordCertificate_reserveExtraMapCommute_symm
    C.toEndpointReserveAugmentedRowWordCertificate hf hg

theorem endpointReserveAugmentedFinRowWordCertificate_reserveExtraIterCommute
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    {f g : Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) f)
    (hg : SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  endpointReserveAugmentedRowWordCertificate_reserveExtraIterCommute
    C.toEndpointReserveAugmentedRowWordCertificate hf hg n k

theorem endpointReserveAugmentedFinRowWordCertificate_reserveExtraIterCommute_symm
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    {f g : Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement) f)
    (hg : SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  endpointReserveAugmentedRowWordCertificate_reserveExtraIterCommute_symm
    C.toEndpointReserveAugmentedRowWordCertificate hf hg n k

theorem endpointReserveAugmentedFinRowWordCertificate_reserveExtraWordCommute
    {extraCount : Nat} {Symbol ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (leftStep : ι -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) (leftStep i))
    (hright : ∀ j : κ, SupportedOn
      (endpointExtraPlacementSupportSet C.extraPlacement) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  endpointReserveAugmentedRowWordCertificate_reserveExtraWordCommute
    C.toEndpointReserveAugmentedRowWordCertificate
    leftStep rightStep hleft hright leftWord rightWord

theorem endpointReserveAugmentedFinRowWordCertificate_reserveExtraWordCommute_symm
    {extraCount : Nat} {Symbol ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (leftStep : ι -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn
      (endpointExtraPlacementSupportSet C.extraPlacement) (leftStep i))
    (hright : ∀ j : κ, SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  endpointReserveAugmentedRowWordCertificate_reserveExtraWordCommute_symm
    C.toEndpointReserveAugmentedRowWordCertificate
    leftStep rightStep hleft hright leftWord rightWord

theorem endpointReserveAugmentedFinRowWordCertificate_reserveExtraWordIterCommute
    {extraCount : Nat} {Symbol ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (leftStep : ι -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) (leftStep i))
    (hright : ∀ j : κ, SupportedOn
      (endpointExtraPlacementSupportSet C.extraPlacement) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  endpointReserveAugmentedRowWordCertificate_reserveExtraWordIterCommute
    C.toEndpointReserveAugmentedRowWordCertificate
    leftStep rightStep hleft hright leftWord rightWord n k

theorem endpointReserveAugmentedFinRowWordCertificate_reserveExtraWordIterCommute_symm
    {extraCount : Nat} {Symbol ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (leftStep : ι -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn
      (endpointExtraPlacementSupportSet C.extraPlacement) (leftStep i))
    (hright : ∀ j : κ, SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  endpointReserveAugmentedRowWordCertificate_reserveExtraWordIterCommute_symm
    C.toEndpointReserveAugmentedRowWordCertificate
    leftStep rightStep hleft hright leftWord rightWord n k

structure EndpointReserveAugmentedCoordFinRowWordCertificate
    (extraCount : Nat) (Symbol Parent : Type*) (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 <= a) (hm : 4 <= m) where
  extraPlacement : Fin extraCount -> Parent × PhaseSection h (m ^ a)
  step :
    Sum (Fin (2 * a + 3)) (Fin extraCount) -> Symbol ->
      Parent × PhaseSection h (m ^ a) ->
        Parent × PhaseSection h (m ^ a)
  word : Sum (Fin (2 * a + 3)) (Fin extraCount) -> List Symbol
  extraCoordinateSeparated :
    ∀ leftRow rightRow : Fin extraCount,
      leftRow ≠ rightRow ->
        (extraPlacement leftRow).1 ≠ (extraPlacement rightRow).1 ∨
          (extraPlacement leftRow).2 ≠ (extraPlacement rightRow).2
  extraProtected :
    ∀ row : Fin extraCount,
      extraPlacement row ∈
        ProductCylinder (Set.univ : Set Parent)
          (PhaseProtectedStrips h (m ^ a))
  supported :
    ∀ row : Sum (Fin (2 * a + 3)) (Fin extraCount),
      ∀ symbol : Symbol,
        SupportedOn
          (rowPlacementSupport
            (endpointReserveAugmentedPlacement
              parent h a m ha hm extraPlacement) row)
          (step row symbol)

theorem endpointReserveAugmentedCoordFinRowWordCertificate_extraPlacement_ne
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    {leftRow rightRow : Fin extraCount} (hrow : leftRow ≠ rightRow) :
    C.extraPlacement leftRow ≠ C.extraPlacement rightRow := by
  cases C.extraCoordinateSeparated leftRow rightRow hrow with
  | inl hparent => exact rowPlacement_ne_of_parent_ne hparent
  | inr hnewCoord => exact rowPlacement_ne_of_newCoord_ne hnewCoord

def EndpointReserveAugmentedCoordFinRowWordCertificate.toFinCertificate
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm) :
    EndpointReserveAugmentedFinRowWordCertificate
      extraCount Symbol Parent parent h a m hh ha hm where
  extraPlacement := C.extraPlacement
  step := C.step
  word := C.word
  extraPlacementNe :=
    fun leftRow rightRow hrow =>
      endpointReserveAugmentedCoordFinRowWordCertificate_extraPlacement_ne
        C (leftRow := leftRow) (rightRow := rightRow) hrow
  extraProtected := C.extraProtected
  supported := C.supported

def EndpointReserveAugmentedCoordFinRowWordCertificate.toRowWordPlacementCertificate
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm) :
    RowWordPlacementCertificate
      (Sum (Fin (2 * a + 3)) (Fin extraCount))
      Symbol Parent (PhaseSection h (m ^ a)) :=
  C.toFinCertificate
    |>.toRowWordPlacementCertificate

def EndpointReserveAugmentedCoordFinRowWordCertificate.toSupportCertificate
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm) :
    EndpointReserveAugmentedSupportCertificate
      (Fin extraCount) Parent parent h a m hh ha hm :=
  C.toFinCertificate
    |>.toSupportCertificate

theorem endpointReserveAugmentedCoordFinRowWordCertificate_supportSet_union
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm) :
    C.toSupportCertificate.supportSet =
      endpointReservePlacementSupportSet parent h a m ha hm ∪
        endpointExtraPlacementSupportSet C.extraPlacement :=
  endpointReserveAugmentedSupportCertificate_supportSet_union
    C.toSupportCertificate

theorem endpointReserveAugmentedCoordFinRowWordCertificate_supportSet_iUnionRows
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm) :
    C.toSupportCertificate.supportSet =
      ⋃ row : Sum (Fin (2 * a + 3)) (Fin extraCount),
        rowPlacementSupport
          (endpointReserveAugmentedPlacement
            parent h a m ha hm C.extraPlacement) row :=
  endpointReserveAugmentedSupportCertificate_supportSet_iUnionRows
    C.toSupportCertificate

theorem endpointReserveAugmentedCoordFinRowWordCertificate_supportExtraProtected
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm) :
    endpointExtraPlacementSupportSet C.extraPlacement ⊆
      ProductCylinder (Set.univ : Set Parent)
        (PhaseProtectedStrips h (m ^ a)) :=
  endpointReserveAugmentedSupportCertificate_extraSubsetProtected
    C.toSupportCertificate

theorem endpointReserveAugmentedCoordFinRowWordCertificate_supportExistsUniqueRow
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ C.toSupportCertificate.supportSet) :
    ∃! row : Sum (Fin (2 * a + 3)) (Fin extraCount),
      endpointReserveAugmentedPlacement
        parent h a m ha hm C.extraPlacement row = x :=
  endpointReserveAugmentedSupportCertificate_existsUniqueRow
    C.toSupportCertificate hx

theorem endpointReserveAugmentedCoordFinRowWordCertificate_extraPlacement_injective
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm) :
    Function.Injective C.extraPlacement :=
  endpointReserveAugmentedFinRowWordCertificate_extraPlacement_injective
    C.toFinCertificate

theorem endpointReserveAugmentedCoordFinRowWordCertificate_eval
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (row : Sum (Fin (2 * a + 3)) (Fin extraCount)) :
    C.toRowWordPlacementCertificate.eval row =
      wordEval (C.step row) (C.word row) :=
  rfl

theorem endpointReserveAugmentedCoordFinRowWordCertificate_eval_supported
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (row : Sum (Fin (2 * a + 3)) (Fin extraCount)) :
    SupportedOn
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) row)
      (C.toRowWordPlacementCertificate.eval row) :=
  endpointReserveAugmentedFinRowWordCertificate_eval_supported
    C.toFinCertificate row

theorem endpointReserveAugmentedCoordFinRowWordCertificate_step_supportedOn_supportSet
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (row : Sum (Fin (2 * a + 3)) (Fin extraCount))
    (symbol : Symbol) :
    SupportedOn C.toSupportCertificate.supportSet (C.step row symbol) :=
  endpointReserveAugmentedFinRowWordCertificate_step_supportedOn_supportSet
    C.toFinCertificate row symbol

theorem endpointReserveAugmentedCoordFinRowWordCertificate_eval_supportedOn_supportSet
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (row : Sum (Fin (2 * a + 3)) (Fin extraCount)) :
    SupportedOn C.toSupportCertificate.supportSet
      (C.toRowWordPlacementCertificate.eval row) :=
  endpointReserveAugmentedFinRowWordCertificate_eval_supportedOn_supportSet
    C.toFinCertificate row

theorem endpointReserveAugmentedCoordFinRowWordCertificate_evalWord_supportedOn_supportSet
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (rows : List (Sum (Fin (2 * a + 3)) (Fin extraCount))) :
    SupportedOn C.toSupportCertificate.supportSet
      (wordEval (fun row => C.toRowWordPlacementCertificate.eval row) rows) :=
  endpointReserveAugmentedFinRowWordCertificate_evalWord_supportedOn_supportSet
    C.toFinCertificate rows

theorem endpointReserveAugmentedCoordFinRowWordCertificate_evalWordIter_supportedOn_support
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (rows : List (Sum (Fin (2 * a + 3)) (Fin extraCount))) (n : Nat) :
    SupportedOn C.toSupportCertificate.supportSet
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval row) rows)^[n]) :=
  endpointReserveAugmentedFinRowWordCertificate_evalWord_iterate_supportedOn_supportSet
    C.toFinCertificate rows n

theorem endpointReserveAugmentedCoordFinRowWordCertificate_supports_disjoint
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    {leftRow rightRow : Sum (Fin (2 * a + 3)) (Fin extraCount)}
    (hrow : leftRow ≠ rightRow) :
    SetsDisjoint
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) leftRow)
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) rightRow) :=
  endpointReserveAugmentedFinRowWordCertificate_supports_disjoint
    C.toFinCertificate hrow

theorem endpointReserveAugmentedCoordFinRowWordCertificate_evalsCommute
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    {leftRow rightRow : Sum (Fin (2 * a + 3)) (Fin extraCount)}
    (hrow : leftRow ≠ rightRow) :
    Function.Commute
      (C.toRowWordPlacementCertificate.eval leftRow)
      (C.toRowWordPlacementCertificate.eval rightRow) :=
  endpointReserveAugmentedFinRowWordCertificate_evalsCommute
    C.toFinCertificate hrow

theorem endpointReserveAugmentedCoordFinRowWordCertificate_evalIteratesCommute
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    {leftRow rightRow : Sum (Fin (2 * a + 3)) (Fin extraCount)}
    (hrow : leftRow ≠ rightRow) (n k : Nat) :
    Function.Commute
      ((C.toRowWordPlacementCertificate.eval leftRow)^[n])
      ((C.toRowWordPlacementCertificate.eval rightRow)^[k]) :=
  endpointReserveAugmentedFinRowWordCertificate_evalIteratesCommute
    C.toFinCertificate hrow n k

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraRowSupportsDisjoint
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (reserveRow : Fin (2 * a + 3)) (extraRow : Fin extraCount) :
    SetsDisjoint
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) (Sum.inl reserveRow))
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) (Sum.inr extraRow)) :=
  endpointReserveAugmentedFinRowWordCertificate_reserveExtraRowSupportsDisjoint
    C.toFinCertificate reserveRow extraRow

theorem endpointReserveAugmentedCoordFinRowWordCertificate_extraReserveRowSupportsDisjoint
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (extraRow : Fin extraCount) (reserveRow : Fin (2 * a + 3)) :
    SetsDisjoint
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) (Sum.inr extraRow))
      (rowPlacementSupport
        (endpointReserveAugmentedPlacement
          parent h a m ha hm C.extraPlacement) (Sum.inl reserveRow)) :=
  endpointReserveAugmentedFinRowWordCertificate_extraReserveRowSupportsDisjoint
    C.toFinCertificate extraRow reserveRow

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraRowEvalsCommute
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (reserveRow : Fin (2 * a + 3)) (extraRow : Fin extraCount) :
    Function.Commute
      (C.toRowWordPlacementCertificate.eval (Sum.inl reserveRow))
      (C.toRowWordPlacementCertificate.eval (Sum.inr extraRow)) :=
  endpointReserveAugmentedFinRowWordCertificate_reserveExtraRowEvalsCommute
    C.toFinCertificate reserveRow extraRow

theorem endpointReserveAugmentedCoordFinRowWordCertificate_extraReserveRowEvalsCommute
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (extraRow : Fin extraCount) (reserveRow : Fin (2 * a + 3)) :
    Function.Commute
      (C.toRowWordPlacementCertificate.eval (Sum.inr extraRow))
      (C.toRowWordPlacementCertificate.eval (Sum.inl reserveRow)) :=
  endpointReserveAugmentedFinRowWordCertificate_extraReserveRowEvalsCommute
    C.toFinCertificate extraRow reserveRow

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraRowEvalIteratesCommute
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (reserveRow : Fin (2 * a + 3)) (extraRow : Fin extraCount)
    (n k : Nat) :
    Function.Commute
      ((C.toRowWordPlacementCertificate.eval (Sum.inl reserveRow))^[n])
      ((C.toRowWordPlacementCertificate.eval (Sum.inr extraRow))^[k]) :=
  endpointReserveAugmentedFinRowWordCertificate_reserveExtraRowEvalIteratesCommute
    C.toFinCertificate reserveRow extraRow n k

theorem endpointReserveAugmentedCoordFinRowWordCertificate_extraReserveRowEvalIteratesCommute
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (extraRow : Fin extraCount) (reserveRow : Fin (2 * a + 3))
    (n k : Nat) :
    Function.Commute
      ((C.toRowWordPlacementCertificate.eval (Sum.inr extraRow))^[n])
      ((C.toRowWordPlacementCertificate.eval (Sum.inl reserveRow))^[k]) :=
  endpointReserveAugmentedFinRowWordCertificate_extraReserveRowEvalIteratesCommute
    C.toFinCertificate extraRow reserveRow n k

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveEval_onReserve
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (reserveRow : Fin (2 * a + 3)) :
    SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm)
      (C.toRowWordPlacementCertificate.eval (Sum.inl reserveRow)) :=
  endpointReserveAugmentedFinRowWordCertificate_reserveEval_onReserve
    C.toFinCertificate reserveRow

theorem endpointReserveAugmentedCoordFinRowWordCertificate_extraEval_onExtra
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (extraRow : Fin extraCount) :
    SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement)
      (C.toRowWordPlacementCertificate.eval (Sum.inr extraRow)) :=
  endpointReserveAugmentedFinRowWordCertificate_extraEval_onExtra
    C.toFinCertificate extraRow

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveWord_onReserve
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (reserveRows : List (Fin (2 * a + 3))) :
    SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm)
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows) :=
  endpointReserveAugmentedFinRowWordCertificate_reserveWord_onReserve
    C.toFinCertificate reserveRows

theorem endpointReserveAugmentedCoordFinRowWordCertificate_extraWord_onExtra
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (extraRows : List (Fin extraCount)) :
    SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement)
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows) :=
  endpointReserveAugmentedFinRowWordCertificate_extraWord_onExtra
    C.toFinCertificate extraRows

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveWordIter_onReserve
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (reserveRows : List (Fin (2 * a + 3))) (n : Nat) :
    SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm)
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows)^[n]) :=
  endpointReserveAugmentedFinRowWordCertificate_reserveWordIter_onReserve
    C.toFinCertificate reserveRows n

theorem endpointReserveAugmentedCoordFinRowWordCertificate_extraWordIter_onExtra
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (extraRows : List (Fin extraCount)) (n : Nat) :
    SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement)
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows)^[n]) :=
  endpointReserveAugmentedFinRowWordCertificate_extraWordIter_onExtra
    C.toFinCertificate extraRows n

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraWordsCommute
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (reserveRows : List (Fin (2 * a + 3)))
    (extraRows : List (Fin extraCount)) :
    Function.Commute
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows)
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows) :=
  endpointReserveAugmentedFinRowWordCertificate_reserveExtraWordsCommute
    C.toFinCertificate reserveRows extraRows

theorem endpointReserveAugmentedCoordFinRowWordCertificate_extraReserveWordsCommute
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (extraRows : List (Fin extraCount))
    (reserveRows : List (Fin (2 * a + 3))) :
    Function.Commute
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows)
      (wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows) :=
  endpointReserveAugmentedFinRowWordCertificate_extraReserveWordsCommute
    C.toFinCertificate extraRows reserveRows

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraWordItersCommute
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (reserveRows : List (Fin (2 * a + 3)))
    (extraRows : List (Fin extraCount)) (n k : Nat) :
    Function.Commute
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows)^[n])
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows)^[k]) :=
  endpointReserveAugmentedFinRowWordCertificate_reserveExtraWordItersCommute
    C.toFinCertificate reserveRows extraRows n k

theorem endpointReserveAugmentedCoordFinRowWordCertificate_extraReserveWordItersCommute
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (extraRows : List (Fin extraCount))
    (reserveRows : List (Fin (2 * a + 3))) (n k : Nat) :
    Function.Commute
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inr row))
        extraRows)^[n])
      ((wordEval
        (fun row => C.toRowWordPlacementCertificate.eval (Sum.inl row))
        reserveRows)^[k]) :=
  endpointReserveAugmentedFinRowWordCertificate_extraReserveWordItersCommute
    C.toFinCertificate extraRows reserveRows n k

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraDisjoint
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm) :
    SetsDisjoint
      (endpointReservePlacementSupportSet parent h a m ha hm)
      (endpointExtraPlacementSupportSet C.extraPlacement) :=
  endpointReserveAugmentedFinRowWordCertificate_reserveExtraDisjoint
    C.toFinCertificate

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraDisjoint_symm
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm) :
    SetsDisjoint
      (endpointExtraPlacementSupportSet C.extraPlacement)
      (endpointReservePlacementSupportSet parent h a m ha hm) :=
  endpointReserveAugmentedFinRowWordCertificate_reserveExtraDisjoint_symm
    C.toFinCertificate

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraMapCommute
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    {f g : Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) f)
    (hg : SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement) g) :
    Function.Commute f g :=
  endpointReserveAugmentedFinRowWordCertificate_reserveExtraMapCommute
    C.toFinCertificate hf hg

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraMapCommute_symm
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    {f g : Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement) f)
    (hg : SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) g) :
    Function.Commute f g :=
  endpointReserveAugmentedFinRowWordCertificate_reserveExtraMapCommute_symm
    C.toFinCertificate hf hg

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraIterCommute
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    {f g : Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) f)
    (hg : SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  endpointReserveAugmentedFinRowWordCertificate_reserveExtraIterCommute
    C.toFinCertificate hf hg n k

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraIterCommute_symm
    {extraCount : Nat} {Symbol Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    {f g : Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (endpointExtraPlacementSupportSet C.extraPlacement) f)
    (hg : SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  endpointReserveAugmentedFinRowWordCertificate_reserveExtraIterCommute_symm
    C.toFinCertificate hf hg n k

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraWordCommute
    {extraCount : Nat} {Symbol ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (leftStep : ι -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) (leftStep i))
    (hright : ∀ j : κ, SupportedOn
      (endpointExtraPlacementSupportSet C.extraPlacement) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  endpointReserveAugmentedFinRowWordCertificate_reserveExtraWordCommute
    C.toFinCertificate
    leftStep rightStep hleft hright leftWord rightWord

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraWordCommute_symm
    {extraCount : Nat} {Symbol ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (leftStep : ι -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn
      (endpointExtraPlacementSupportSet C.extraPlacement) (leftStep i))
    (hright : ∀ j : κ, SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  endpointReserveAugmentedFinRowWordCertificate_reserveExtraWordCommute_symm
    C.toFinCertificate
    leftStep rightStep hleft hright leftWord rightWord

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraWordIterCommute
    {extraCount : Nat} {Symbol ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (leftStep : ι -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) (leftStep i))
    (hright : ∀ j : κ, SupportedOn
      (endpointExtraPlacementSupportSet C.extraPlacement) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  endpointReserveAugmentedFinRowWordCertificate_reserveExtraWordIterCommute
    C.toFinCertificate
    leftStep rightStep hleft hright leftWord rightWord n k

theorem endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraWordIterCommute_symm
    {extraCount : Nat} {Symbol ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 <= a} {hm : 4 <= m}
    (C :
      EndpointReserveAugmentedCoordFinRowWordCertificate
        extraCount Symbol Parent parent h a m hh ha hm)
    (leftStep : ι -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ -> Parent × PhaseSection h (m ^ a) ->
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn
      (endpointExtraPlacementSupportSet C.extraPlacement) (leftStep i))
    (hright : ∀ j : κ, SupportedOn
      (endpointReservePlacementSupportSet parent h a m ha hm) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  endpointReserveAugmentedFinRowWordCertificate_reserveExtraWordIterCommute_symm
    C.toFinCertificate
    leftStep rightStep hleft hright leftWord rightWord n k

def endpointReservePlacementCoordinateSeparatedCertificate
    {Symbol Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m)
    (step :
      Fin (2 * a + 3) → Symbol →
        Parent × PhaseSection h (m ^ a) →
          Parent × PhaseSection h (m ^ a))
    (word : Fin (2 * a + 3) → List Symbol)
    (supported :
      ∀ row : Fin (2 * a + 3), ∀ symbol : Symbol,
        SupportedOn
          (rowPlacementSupport
            (endpointReservePlacement parent h a m ha hm) row)
          (step row symbol)) :
    CoordinateSeparatedFinRowWordPlacementCertificate
      (2 * a + 3) Symbol Parent (PhaseSection h (m ^ a)) where
  placement := endpointReservePlacement parent h a m ha hm
  step := step
  word := word
  coordinateSeparated :=
    fun leftRow rightRow hrow =>
      endpointReservePlacement_coordinateSeparated
        parent h a m ha hm (i := leftRow) (j := rightRow) hrow
  supported := supported

theorem endpointReservePlacementCertificate_eval_supported
    {Symbol Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m)
    (step :
      Fin (2 * a + 3) → Symbol →
        Parent × PhaseSection h (m ^ a) →
          Parent × PhaseSection h (m ^ a))
    (word : Fin (2 * a + 3) → List Symbol)
    (supported :
      ∀ row : Fin (2 * a + 3), ∀ symbol : Symbol,
        SupportedOn
          (rowPlacementSupport
            (endpointReservePlacement parent h a m ha hm) row)
          (step row symbol))
    (row : Fin (2 * a + 3)) :
    SupportedOn
      (rowPlacementSupport
        (endpointReservePlacement parent h a m ha hm) row)
      ((endpointReservePlacementCoordinateSeparatedCertificate
        parent h a m ha hm step word supported).eval row) :=
  coordinateSeparatedFinRowWordPlacementCertificate_eval_supported
    (endpointReservePlacementCoordinateSeparatedCertificate
      parent h a m ha hm step word supported) row

theorem endpointReservePlacementCertificate_supports_disjoint
    {Symbol Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m)
    (step :
      Fin (2 * a + 3) → Symbol →
        Parent × PhaseSection h (m ^ a) →
          Parent × PhaseSection h (m ^ a))
    (word : Fin (2 * a + 3) → List Symbol)
    (supported :
      ∀ row : Fin (2 * a + 3), ∀ symbol : Symbol,
        SupportedOn
          (rowPlacementSupport
            (endpointReservePlacement parent h a m ha hm) row)
          (step row symbol))
    {leftRow rightRow : Fin (2 * a + 3)}
    (hrow : leftRow ≠ rightRow) :
    SetsDisjoint
      (rowPlacementSupport
        (endpointReservePlacement parent h a m ha hm) leftRow)
      (rowPlacementSupport
        (endpointReservePlacement parent h a m ha hm) rightRow) :=
  coordinateSeparatedFinRowWordPlacementCertificate_supports_disjoint
    (endpointReservePlacementCoordinateSeparatedCertificate
      parent h a m ha hm step word supported) hrow

theorem endpointReservePlacementCertificate_evalsCommute
    {Symbol Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m)
    (step :
      Fin (2 * a + 3) → Symbol →
        Parent × PhaseSection h (m ^ a) →
          Parent × PhaseSection h (m ^ a))
    (word : Fin (2 * a + 3) → List Symbol)
    (supported :
      ∀ row : Fin (2 * a + 3), ∀ symbol : Symbol,
        SupportedOn
          (rowPlacementSupport
            (endpointReservePlacement parent h a m ha hm) row)
          (step row symbol))
    {leftRow rightRow : Fin (2 * a + 3)}
    (hrow : leftRow ≠ rightRow) :
    Function.Commute
      ((endpointReservePlacementCoordinateSeparatedCertificate
        parent h a m ha hm step word supported).eval leftRow)
      ((endpointReservePlacementCoordinateSeparatedCertificate
        parent h a m ha hm step word supported).eval rightRow) :=
  coordinateSeparatedFinRowWordPlacementCertificate_evalsCommute
    (endpointReservePlacementCoordinateSeparatedCertificate
      parent h a m ha hm step word supported) hrow

theorem endpointReservePlacementCertificate_evalIteratesCommute
    {Symbol Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m)
    (step :
      Fin (2 * a + 3) → Symbol →
        Parent × PhaseSection h (m ^ a) →
          Parent × PhaseSection h (m ^ a))
    (word : Fin (2 * a + 3) → List Symbol)
    (supported :
      ∀ row : Fin (2 * a + 3), ∀ symbol : Symbol,
        SupportedOn
          (rowPlacementSupport
            (endpointReservePlacement parent h a m ha hm) row)
          (step row symbol))
    {leftRow rightRow : Fin (2 * a + 3)}
    (hrow : leftRow ≠ rightRow) (n k : Nat) :
    Function.Commute
      (((endpointReservePlacementCoordinateSeparatedCertificate
        parent h a m ha hm step word supported).eval leftRow)^[n])
      (((endpointReservePlacementCoordinateSeparatedCertificate
        parent h a m ha hm step word supported).eval rightRow)^[k]) :=
  coordinateSeparatedFinRowWordPlacementCertificate_evalIteratesCommute
    (endpointReservePlacementCoordinateSeparatedCertificate
      parent h a m ha hm step word supported) hrow n k

theorem endpointReservePlacement_not_mem_protectedCylinder
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 <= a) (hm : 4 <= m)
    (T : Set Parent) (i : Fin (2 * a + 3)) :
    endpointReservePlacement parent h a m ha hm i ∉
      ProductCylinder T (PhaseProtectedStrips h (m ^ a)) :=
  phaseProductReserveLineSlot_not_mem_protectedCylinder
    parent h a m hh ha hm T i

theorem endpointReservePlacementSupport_eq_singleton
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m)
    (i : Fin (2 * a + 3)) :
    rowPlacementSupport (endpointReservePlacement parent h a m ha hm) i =
      ({endpointReservePlacement parent h a m ha hm i} :
        Set (Parent × PhaseSection h (m ^ a))) :=
  rowPlacementSupport_eq_singleton
    (endpointReservePlacement parent h a m ha hm) i

theorem endpointReservePlacementSupport_eq_productCylinder
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m)
    (i : Fin (2 * a + 3)) :
    rowPlacementSupport (endpointReservePlacement parent h a m ha hm) i =
      ProductCylinder ({parent} : Set Parent)
        ({(endpointReservePlacement parent h a m ha hm i).2} :
          Set (PhaseSection h (m ^ a))) := by
  ext x
  constructor
  · intro hx
    rw [rowPlacementSupport_mem] at hx
    rw [hx]
    exact ⟨endpointReservePlacement_parent parent h a m ha hm i, rfl⟩
  · intro hx
    rw [rowPlacementSupport_mem]
    exact Prod.ext hx.1 hx.2

theorem endpointReservePlacementSupports_disjoint
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j) :
    SetsDisjoint
      (rowPlacementSupport (endpointReservePlacement parent h a m ha hm) i)
      (rowPlacementSupport (endpointReservePlacement parent h a m ha hm) j) :=
  rowPlacementSupports_disjoint_of_injective
    (endpointReservePlacement_injective parent h a m ha hm) hij

theorem endpointReservePlacementSupportedMapsCommute
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j)
    {leftMap rightMap :
      Parent × PhaseSection h (m ^ a) -> Parent × PhaseSection h (m ^ a)}
    (hleft :
      SupportedOn
        (ProductCylinder ({parent} : Set Parent)
          ({(endpointReservePlacement parent h a m ha hm i).2} :
            Set (PhaseSection h (m ^ a)))) leftMap)
    (hright :
      SupportedOn
        (ProductCylinder ({parent} : Set Parent)
          ({(endpointReservePlacement parent h a m ha hm j).2} :
            Set (PhaseSection h (m ^ a)))) rightMap) :
    Function.Commute leftMap rightMap :=
  rowPlacementSupportedMapsCommute_of_injective
    (endpointReservePlacement_injective parent h a m ha hm) hij
    (by simpa [endpointReservePlacementSupport_eq_productCylinder] using hleft)
    (by simpa [endpointReservePlacementSupport_eq_productCylinder] using hright)

theorem endpointReservePlacementSupportedMapsCommute_symm
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j)
    {leftMap rightMap :
      Parent × PhaseSection h (m ^ a) -> Parent × PhaseSection h (m ^ a)}
    (hleft :
      SupportedOn
        (ProductCylinder ({parent} : Set Parent)
          ({(endpointReservePlacement parent h a m ha hm j).2} :
            Set (PhaseSection h (m ^ a)))) leftMap)
    (hright :
      SupportedOn
        (ProductCylinder ({parent} : Set Parent)
          ({(endpointReservePlacement parent h a m ha hm i).2} :
            Set (PhaseSection h (m ^ a)))) rightMap) :
    Function.Commute leftMap rightMap :=
  rowPlacementSupportedMapsCommute_symmSupports_of_injective
    (endpointReservePlacement_injective parent h a m ha hm) hij
    (by simpa [endpointReservePlacementSupport_eq_productCylinder] using hleft)
    (by simpa [endpointReservePlacementSupport_eq_productCylinder] using hright)

theorem endpointReservePlacementSupportedIteratesCommute
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j)
    {leftMap rightMap :
      Parent × PhaseSection h (m ^ a) -> Parent × PhaseSection h (m ^ a)}
    (hleft :
      SupportedOn
        (ProductCylinder ({parent} : Set Parent)
          ({(endpointReservePlacement parent h a m ha hm i).2} :
            Set (PhaseSection h (m ^ a)))) leftMap)
    (hright :
      SupportedOn
        (ProductCylinder ({parent} : Set Parent)
          ({(endpointReservePlacement parent h a m ha hm j).2} :
            Set (PhaseSection h (m ^ a)))) rightMap)
    (n k : Nat) :
    Function.Commute (leftMap^[n]) (rightMap^[k]) :=
  rowPlacementSupportedIteratesCommute_of_injective
    (endpointReservePlacement_injective parent h a m ha hm) hij
    (by simpa [endpointReservePlacementSupport_eq_productCylinder] using hleft)
    (by simpa [endpointReservePlacementSupport_eq_productCylinder] using hright)
    n k

theorem endpointReservePlacementSupportedIteratesCommute_symm
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j)
    {leftMap rightMap :
      Parent × PhaseSection h (m ^ a) -> Parent × PhaseSection h (m ^ a)}
    (hleft :
      SupportedOn
        (ProductCylinder ({parent} : Set Parent)
          ({(endpointReservePlacement parent h a m ha hm j).2} :
            Set (PhaseSection h (m ^ a)))) leftMap)
    (hright :
      SupportedOn
        (ProductCylinder ({parent} : Set Parent)
          ({(endpointReservePlacement parent h a m ha hm i).2} :
            Set (PhaseSection h (m ^ a)))) rightMap)
    (n k : Nat) :
    Function.Commute (leftMap^[n]) (rightMap^[k]) :=
  rowPlacementSupportedIteratesCommute_symmSupports_of_injective
    (endpointReservePlacement_injective parent h a m ha hm) hij
    (by simpa [endpointReservePlacementSupport_eq_productCylinder] using hleft)
    (by simpa [endpointReservePlacementSupport_eq_productCylinder] using hright)
    n k

theorem endpointReservePlacementSupportedWordEvalsCommute
    {SymbolLeft SymbolRight Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j)
    (leftStep :
      SymbolLeft -> Parent × PhaseSection h (m ^ a) ->
        Parent × PhaseSection h (m ^ a))
    (rightStep :
      SymbolRight -> Parent × PhaseSection h (m ^ a) ->
        Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn
          (ProductCylinder ({parent} : Set Parent)
            ({(endpointReservePlacement parent h a m ha hm i).2} :
              Set (PhaseSection h (m ^ a)))) (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn
          (ProductCylinder ({parent} : Set Parent)
            ({(endpointReservePlacement parent h a m ha hm j).2} :
              Set (PhaseSection h (m ^ a)))) (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  rowPlacementSupportedWordEvalsCommute_of_injective
    (endpointReservePlacement_injective parent h a m ha hm) hij
    leftStep rightStep
    (fun symbol => by
      simpa [endpointReservePlacementSupport_eq_productCylinder]
        using hleft symbol)
    (fun symbol => by
      simpa [endpointReservePlacementSupport_eq_productCylinder]
        using hright symbol)
    leftWord rightWord

theorem endpointReservePlacementSupportedWordEvalsCommute_symm
    {SymbolLeft SymbolRight Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j)
    (leftStep :
      SymbolLeft -> Parent × PhaseSection h (m ^ a) ->
        Parent × PhaseSection h (m ^ a))
    (rightStep :
      SymbolRight -> Parent × PhaseSection h (m ^ a) ->
        Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn
          (ProductCylinder ({parent} : Set Parent)
            ({(endpointReservePlacement parent h a m ha hm j).2} :
              Set (PhaseSection h (m ^ a)))) (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn
          (ProductCylinder ({parent} : Set Parent)
            ({(endpointReservePlacement parent h a m ha hm i).2} :
              Set (PhaseSection h (m ^ a)))) (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  rowPlacementSupportedWordEvalsCommute_symmSupports_of_injective
    (endpointReservePlacement_injective parent h a m ha hm) hij
    leftStep rightStep
    (fun symbol => by
      simpa [endpointReservePlacementSupport_eq_productCylinder]
        using hleft symbol)
    (fun symbol => by
      simpa [endpointReservePlacementSupport_eq_productCylinder]
        using hright symbol)
    leftWord rightWord

theorem endpointReservePlacementSupportedWordEvalIteratesCommute
    {SymbolLeft SymbolRight Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j)
    (leftStep :
      SymbolLeft -> Parent × PhaseSection h (m ^ a) ->
        Parent × PhaseSection h (m ^ a))
    (rightStep :
      SymbolRight -> Parent × PhaseSection h (m ^ a) ->
        Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn
          (ProductCylinder ({parent} : Set Parent)
            ({(endpointReservePlacement parent h a m ha hm i).2} :
              Set (PhaseSection h (m ^ a)))) (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn
          (ProductCylinder ({parent} : Set Parent)
            ({(endpointReservePlacement parent h a m ha hm j).2} :
              Set (PhaseSection h (m ^ a)))) (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight)
    (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  rowPlacementSupportedWordEvalIteratesCommute_of_injective
    (endpointReservePlacement_injective parent h a m ha hm) hij
    leftStep rightStep
    (fun symbol => by
      simpa [endpointReservePlacementSupport_eq_productCylinder]
        using hleft symbol)
    (fun symbol => by
      simpa [endpointReservePlacementSupport_eq_productCylinder]
        using hright symbol)
    leftWord rightWord n k

theorem endpointReservePlacementSupportedWordEvalIteratesCommute_symm
    {SymbolLeft SymbolRight Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 <= a) (hm : 4 <= m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j)
    (leftStep :
      SymbolLeft -> Parent × PhaseSection h (m ^ a) ->
        Parent × PhaseSection h (m ^ a))
    (rightStep :
      SymbolRight -> Parent × PhaseSection h (m ^ a) ->
        Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ symbol : SymbolLeft,
        SupportedOn
          (ProductCylinder ({parent} : Set Parent)
            ({(endpointReservePlacement parent h a m ha hm j).2} :
              Set (PhaseSection h (m ^ a)))) (leftStep symbol))
    (hright :
      ∀ symbol : SymbolRight,
        SupportedOn
          (ProductCylinder ({parent} : Set Parent)
            ({(endpointReservePlacement parent h a m ha hm i).2} :
              Set (PhaseSection h (m ^ a)))) (rightStep symbol))
    (leftWord : List SymbolLeft) (rightWord : List SymbolRight)
    (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  rowPlacementSupportedWordEvalIteratesCommute_symmSupports_of_injective
    (endpointReservePlacement_injective parent h a m ha hm) hij
    leftStep rightStep
    (fun symbol => by
      simpa [endpointReservePlacementSupport_eq_productCylinder]
        using hleft symbol)
    (fun symbol => by
      simpa [endpointReservePlacementSupport_eq_productCylinder]
        using hright symbol)
    leftWord rightWord n k

end EndpointReservePlacement

export EndpointReservePlacement
  (endpointReservePlacement
   endpointReservePlacement_parent
   endpointReservePlacement_phase
   endpointReservePlacement_injective
   endpointReservePlacement_newCoord_ne
   endpointReservePlacement_coordinateSeparated
   endpointReservePlacementList
   endpointReservePlacementList_length
   endpointReservePlacementList_nodup
   endpointReservePlacementList_parent
   endpointReservePlacementList_phase
   endpointReservePlacementList_not_mem_protectedCylinder
   endpointReservePlacementList_mem_iff_exists_slot
   endpointReservePlacementList_exists_unique_slot
   endpointReservePlacementSupportSet
   endpointReservePlacementSupportSet_eq_phaseProduct
   endpointReservePlacementSupportSet_mem_iff_exists_row
   endpointReservePlacementSupportSet_exists_unique_row
   endpointReservePlacementSupportSet_eq_iUnion_rowPlacementSupport
   endpointReservePlacementSupportSet_subsetReserveCylinder
   endpointReservePlacementSupportSet_constantParentProjection
   endpointReservePlacementSupportSet_constantPhaseProjection
   endpointReservePlacementSupportSet_disjointProtected
   EndpointReservePlacementSupportCertificate
   endpointReservePlacementSupportCertificate
   endpointReservePlacementSupportCertificate_supportSet
   endpointReservePlacementSupportCertificate_supportSet_phaseProduct
   endpointReservePlacementSupportCertificate_supportSet_iUnionRows
   endpointReservePlacementSupportCertificate_subsetReserveCylinder
   endpointReservePlacementSupportCertificate_constantParentProjection
   endpointReservePlacementSupportCertificate_constantPhaseProjection
   endpointReservePlacementSupportCertificate_disjointProtected
   endpointReservePlacementSupportCertificate_existsUniqueRow
   endpointReservePlacementSupportCertificate_placementInjective
   EndpointReservePlacementSupportCertificate.toPhaseProductCert
   endpointReservePlacementSupportCertificate_toPhaseProductCert_supportSet
   endpointReservePlacementSupportCertificate_toPhaseProductCert_phaseProduct
   endpointReservePlacementSupportCertificate_toPhaseProductCert_disjointProtected
   endpointReservePlacementSupportCertificate_toPhaseProductCert_existsUniqueSlot
   endpointReservePlacementSupportCertificate_toPhaseProductCert_pointInjective
   endpointReservePlacementSupportCertificate_toPhaseProductCert_pairInjective
   endpointReservePlacementSupportCertificate_fixedByProtectedMap
   endpointReservePlacementSupportCertificate_fixedByProtectedIter
   endpointReservePlacementSupportCertificate_fixedByProtectedWordEval
   endpointReservePlacementSupportCertificate_fixedByProtectedWordIter
   endpointReservePlacementSupportCertificate_mapsIntoProtectedMap
   endpointReservePlacementSupportCertificate_mapsIntoProtectedIter
   endpointReservePlacementSupportCertificate_mapsIntoProtectedWordEval
   endpointReservePlacementSupportCertificate_mapsIntoProtectedWordIter
   endpointProtectedCylinder_fixedByReservePlacementSupportCertificateMap
   endpointProtectedCylinder_fixedByReservePlacementSupportCertificateIter
   endpointProtectedCylinder_fixedByReservePlacementSupportCertificateWordEval
   endpointProtectedCylinder_fixedByReservePlacementSupportCertificateWordIter
   endpointProtectedCylinder_mapsIntoReservePlacementSupportCertificateMap
   endpointProtectedCylinder_mapsIntoReservePlacementSupportCertificateIter
   endpointProtectedCylinder_mapsIntoReservePlacementSupportCertificateWordEval
   endpointProtectedCylinder_mapsIntoReservePlacementSupportCertificateWordIter
   endpointReservePlacementSupportCertificateProtectedMapsCommute
   endpointReservePlacementSupportCertificateProtectedMapsCommute_symmSupports
   endpointReservePlacementSupportCertificateProtectedItersCommute
   endpointReservePlacementSupportCertificateProtectedItersCommute_symmSupports
   endpointReservePlacementSupportCertificateProtectedWordEvalsCommute
   endpointReservePlacementSupportCertificateProtectedWordEvalsCommute_symmSupports
   endpointReservePlacementSupportCertificateProtectedWordItersCommute
   endpointReservePlacementSupportCertificateProtectedWordItersCommute_symmSupports
   endpointReserveAugmentedPlacement
   endpointReserveAugmentedPlacement_inl
   endpointReserveAugmentedPlacement_inr
   endpointReserveAugmentedPlacement_injective
   endpointExtraPlacementSupportSet
   endpointExtraPlacementSupportSet_mem_iff_exists_row
   endpointExtraPlacementSupportSet_subsetProtected
   endpointReserveAugmentedSupportSet
   endpointReserveAugmentedSupportSet_eq_iUnionRows
   endpointReserveAugmentedSupportSet_mem_iff_exists_row
   endpointReserveAugmentedSupportSet_eq_union
   endpointReserveAugmentedSupportSet_reserveSubset
   endpointReserveAugmentedSupportSet_extraSubset
   endpointReserveAugmentedSupportSet_extraSubsetProtected
   endpointReserveAugmentedSupportSet_exists_unique_row
   endpointReserveAugmentedSupportSet_supports_disjoint
   EndpointReserveAugmentedSupportCertificate
   endpointReserveAugmentedSupportCertificate
   endpointReserveAugmentedSupportCertificate_supportSet
   endpointReserveAugmentedSupportCertificate_supportSet_union
   endpointReserveAugmentedSupportCertificate_supportSet_iUnionRows
   endpointReserveAugmentedSupportCertificate_placement_injective
   endpointReserveAugmentedSupportCertificate_reserveSubset
   endpointReserveAugmentedSupportCertificate_extraSubset
   endpointReserveAugmentedSupportCertificate_extraSubsetProtected
   endpointReserveAugmentedSupportCertificate_existsUniqueRow
   endpointReserveAugmentedSupportCertificate_supports_disjoint
   endpointReserveAugmentedSupportCertificate_rowSupportSubset
   endpointReserveAugmentedSupportCertificate_reserveRowSupportSubset
   endpointReserveAugmentedSupportCertificate_extraRowSupportSubset
   endpointReserveAugmentedSupportCertificate_reserveExtraDisjoint
   endpointReserveAugmentedSupportCertificate_reserveExtraDisjoint_symm
   endpointReserveAugmentedSupportCertificate_reserveExtraMapsCommute
   endpointReserveAugmentedSupportCertificate_reserveExtraMapsCommute_symmSupports
   endpointReserveAugmentedSupportCertificate_reserveExtraItersCommute
   endpointReserveAugmentedSupportCertificate_reserveExtraItersCommute_symmSupports
   endpointReserveAugmentedSupportCertificate_reserveExtraWordEvalsCommute
   endpointReserveAugmentedSupportCertificate_reserveExtraWordEvalsCommute_symmSupports
   endpointReserveAugmentedSupportCertificate_reserveExtraWordItersCommute
   endpointReserveAugmentedSupportCertificate_reserveExtraWordItersCommute_symmSupports
   EndpointReserveAugmentedRowWordCertificate
   EndpointReserveAugmentedRowWordCertificate.toRowWordPlacementCertificate
   EndpointReserveAugmentedRowWordCertificate.toSupportCertificate
   endpointReserveAugmentedRowWordCertificate_placement_injective
   endpointReserveAugmentedRowWordCertificate_supportSet_union
   endpointReserveAugmentedRowWordCertificate_supportSet_iUnionRows
   endpointReserveAugmentedRowWordCertificate_supportExtraProtected
   endpointReserveAugmentedRowWordCertificate_supportExistsUniqueRow
   endpointReserveAugmentedRowWordCertificate_eval
   endpointReserveAugmentedRowWordCertificate_eval_supported
   endpointReserveAugmentedRowWordCertificate_step_supportedOn_supportSet
   endpointReserveAugmentedRowWordCertificate_eval_supportedOn_supportSet
   endpointReserveAugmentedRowWordCertificate_evalWord_supportedOn_supportSet
   endpointReserveAugmentedRowWordCertificate_evalWord_iterate_supportedOn_supportSet
   endpointReserveAugmentedRowWordCertificate_supports_disjoint
   endpointReserveAugmentedRowWordCertificate_evalsCommute
   endpointReserveAugmentedRowWordCertificate_evalIteratesCommute
   endpointReserveAugmentedRowWordCertificate_reserveExtraRowSupportsDisjoint
   endpointReserveAugmentedRowWordCertificate_extraReserveRowSupportsDisjoint
   endpointReserveAugmentedRowWordCertificate_reserveExtraRowEvalsCommute
   endpointReserveAugmentedRowWordCertificate_extraReserveRowEvalsCommute
   endpointReserveAugmentedRowWordCertificate_reserveExtraRowEvalIteratesCommute
   endpointReserveAugmentedRowWordCertificate_extraReserveRowEvalIteratesCommute
   endpointReserveAugmentedRowWordCertificate_reserveEval_onReserve
   endpointReserveAugmentedRowWordCertificate_extraEval_onExtra
   endpointReserveAugmentedRowWordCertificate_reserveWord_onReserve
   endpointReserveAugmentedRowWordCertificate_extraWord_onExtra
   endpointReserveAugmentedRowWordCertificate_reserveWordIter_onReserve
   endpointReserveAugmentedRowWordCertificate_extraWordIter_onExtra
   endpointReserveAugmentedRowWordCertificate_reserveExtraWordsCommute
   endpointReserveAugmentedRowWordCertificate_extraReserveWordsCommute
   endpointReserveAugmentedRowWordCertificate_reserveExtraWordItersCommute
   endpointReserveAugmentedRowWordCertificate_extraReserveWordItersCommute
   endpointReserveAugmentedRowWordCertificate_reserveExtraDisjoint
   endpointReserveAugmentedRowWordCertificate_reserveExtraDisjoint_symm
   endpointReserveAugmentedRowWordCertificate_reserveExtraMapCommute
   endpointReserveAugmentedRowWordCertificate_reserveExtraMapCommute_symm
   endpointReserveAugmentedRowWordCertificate_reserveExtraIterCommute
   endpointReserveAugmentedRowWordCertificate_reserveExtraIterCommute_symm
   endpointReserveAugmentedRowWordCertificate_reserveExtraWordCommute
   endpointReserveAugmentedRowWordCertificate_reserveExtraWordCommute_symm
   endpointReserveAugmentedRowWordCertificate_reserveExtraWordIterCommute
   endpointReserveAugmentedRowWordCertificate_reserveExtraWordIterCommute_symm
   EndpointReserveAugmentedFinRowWordCertificate
   EndpointReserveAugmentedFinRowWordCertificate.toEndpointReserveAugmentedRowWordCertificate
   EndpointReserveAugmentedFinRowWordCertificate.toRowWordPlacementCertificate
   EndpointReserveAugmentedFinRowWordCertificate.toSupportCertificate
   endpointReserveAugmentedFinRowWordCertificate_extraPlacement_injective
   endpointReserveAugmentedFinRowWordCertificate_supportSet_union
   endpointReserveAugmentedFinRowWordCertificate_supportSet_iUnionRows
   endpointReserveAugmentedFinRowWordCertificate_supportExtraProtected
   endpointReserveAugmentedFinRowWordCertificate_supportExistsUniqueRow
   endpointReserveAugmentedFinRowWordCertificate_eval
   endpointReserveAugmentedFinRowWordCertificate_eval_supported
   endpointReserveAugmentedFinRowWordCertificate_step_supportedOn_supportSet
   endpointReserveAugmentedFinRowWordCertificate_eval_supportedOn_supportSet
   endpointReserveAugmentedFinRowWordCertificate_evalWord_supportedOn_supportSet
   endpointReserveAugmentedFinRowWordCertificate_evalWord_iterate_supportedOn_supportSet
   endpointReserveAugmentedFinRowWordCertificate_supports_disjoint
   endpointReserveAugmentedFinRowWordCertificate_evalsCommute
   endpointReserveAugmentedFinRowWordCertificate_evalIteratesCommute
   endpointReserveAugmentedFinRowWordCertificate_reserveExtraRowSupportsDisjoint
   endpointReserveAugmentedFinRowWordCertificate_extraReserveRowSupportsDisjoint
   endpointReserveAugmentedFinRowWordCertificate_reserveExtraRowEvalsCommute
   endpointReserveAugmentedFinRowWordCertificate_extraReserveRowEvalsCommute
   endpointReserveAugmentedFinRowWordCertificate_reserveExtraRowEvalIteratesCommute
   endpointReserveAugmentedFinRowWordCertificate_extraReserveRowEvalIteratesCommute
   endpointReserveAugmentedFinRowWordCertificate_reserveEval_onReserve
   endpointReserveAugmentedFinRowWordCertificate_extraEval_onExtra
   endpointReserveAugmentedFinRowWordCertificate_reserveWord_onReserve
   endpointReserveAugmentedFinRowWordCertificate_extraWord_onExtra
   endpointReserveAugmentedFinRowWordCertificate_reserveWordIter_onReserve
   endpointReserveAugmentedFinRowWordCertificate_extraWordIter_onExtra
   endpointReserveAugmentedFinRowWordCertificate_reserveExtraWordsCommute
   endpointReserveAugmentedFinRowWordCertificate_extraReserveWordsCommute
   endpointReserveAugmentedFinRowWordCertificate_reserveExtraWordItersCommute
   endpointReserveAugmentedFinRowWordCertificate_extraReserveWordItersCommute
   endpointReserveAugmentedFinRowWordCertificate_reserveExtraDisjoint
   endpointReserveAugmentedFinRowWordCertificate_reserveExtraDisjoint_symm
   endpointReserveAugmentedFinRowWordCertificate_reserveExtraMapCommute
   endpointReserveAugmentedFinRowWordCertificate_reserveExtraMapCommute_symm
   endpointReserveAugmentedFinRowWordCertificate_reserveExtraIterCommute
   endpointReserveAugmentedFinRowWordCertificate_reserveExtraIterCommute_symm
   endpointReserveAugmentedFinRowWordCertificate_reserveExtraWordCommute
   endpointReserveAugmentedFinRowWordCertificate_reserveExtraWordCommute_symm
   endpointReserveAugmentedFinRowWordCertificate_reserveExtraWordIterCommute
   endpointReserveAugmentedFinRowWordCertificate_reserveExtraWordIterCommute_symm
   EndpointReserveAugmentedCoordFinRowWordCertificate
   EndpointReserveAugmentedCoordFinRowWordCertificate.toFinCertificate
   EndpointReserveAugmentedCoordFinRowWordCertificate.toRowWordPlacementCertificate
   EndpointReserveAugmentedCoordFinRowWordCertificate.toSupportCertificate
   endpointReserveAugmentedCoordFinRowWordCertificate_extraPlacement_ne
   endpointReserveAugmentedCoordFinRowWordCertificate_extraPlacement_injective
   endpointReserveAugmentedCoordFinRowWordCertificate_supportSet_union
   endpointReserveAugmentedCoordFinRowWordCertificate_supportSet_iUnionRows
   endpointReserveAugmentedCoordFinRowWordCertificate_supportExtraProtected
   endpointReserveAugmentedCoordFinRowWordCertificate_supportExistsUniqueRow
   endpointReserveAugmentedCoordFinRowWordCertificate_eval
   endpointReserveAugmentedCoordFinRowWordCertificate_eval_supported
   endpointReserveAugmentedCoordFinRowWordCertificate_step_supportedOn_supportSet
   endpointReserveAugmentedCoordFinRowWordCertificate_eval_supportedOn_supportSet
   endpointReserveAugmentedCoordFinRowWordCertificate_evalWord_supportedOn_supportSet
   endpointReserveAugmentedCoordFinRowWordCertificate_evalWordIter_supportedOn_support
   endpointReserveAugmentedCoordFinRowWordCertificate_supports_disjoint
   endpointReserveAugmentedCoordFinRowWordCertificate_evalsCommute
   endpointReserveAugmentedCoordFinRowWordCertificate_evalIteratesCommute
   endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraRowSupportsDisjoint
   endpointReserveAugmentedCoordFinRowWordCertificate_extraReserveRowSupportsDisjoint
   endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraRowEvalsCommute
   endpointReserveAugmentedCoordFinRowWordCertificate_extraReserveRowEvalsCommute
   endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraRowEvalIteratesCommute
   endpointReserveAugmentedCoordFinRowWordCertificate_extraReserveRowEvalIteratesCommute
   endpointReserveAugmentedCoordFinRowWordCertificate_reserveEval_onReserve
   endpointReserveAugmentedCoordFinRowWordCertificate_extraEval_onExtra
   endpointReserveAugmentedCoordFinRowWordCertificate_reserveWord_onReserve
   endpointReserveAugmentedCoordFinRowWordCertificate_extraWord_onExtra
   endpointReserveAugmentedCoordFinRowWordCertificate_reserveWordIter_onReserve
   endpointReserveAugmentedCoordFinRowWordCertificate_extraWordIter_onExtra
   endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraWordsCommute
   endpointReserveAugmentedCoordFinRowWordCertificate_extraReserveWordsCommute
   endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraWordItersCommute
   endpointReserveAugmentedCoordFinRowWordCertificate_extraReserveWordItersCommute
   endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraDisjoint
   endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraDisjoint_symm
   endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraMapCommute
   endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraMapCommute_symm
   endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraIterCommute
   endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraIterCommute_symm
   endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraWordCommute
   endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraWordCommute_symm
   endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraWordIterCommute
   endpointReserveAugmentedCoordFinRowWordCertificate_reserveExtraWordIterCommute_symm
   endpointReservePlacementCoordinateSeparatedCertificate
   endpointReservePlacementCertificate_eval_supported
   endpointReservePlacementCertificate_supports_disjoint
   endpointReservePlacementCertificate_evalsCommute
   endpointReservePlacementCertificate_evalIteratesCommute
   endpointReservePlacement_not_mem_protectedCylinder
   endpointReservePlacementSupport_eq_singleton
   endpointReservePlacementSupport_eq_productCylinder
   endpointReservePlacementSupports_disjoint
   endpointReservePlacementSupportedMapsCommute
   endpointReservePlacementSupportedMapsCommute_symm
   endpointReservePlacementSupportedIteratesCommute
   endpointReservePlacementSupportedIteratesCommute_symm
   endpointReservePlacementSupportedWordEvalsCommute
   endpointReservePlacementSupportedWordEvalsCommute_symm
   endpointReservePlacementSupportedWordEvalIteratesCommute
   endpointReservePlacementSupportedWordEvalIteratesCommute_symm)

end EvenV11
