import EvenV11.PhaseWordSupport

namespace EvenV11
namespace PhaseProductSupport

def phaseProductLineInitialSlot {Parent : Type*} (parent : Parent)
    {h M n : Nat} [NeZero M] (k : ZMod h) (hn : n ≤ M) :
    Fin n → {x : Parent × PhaseSection h M //
      x ∈ ProductCylinder ({parent} : Set Parent) (@PhaseLine h M k)} :=
  fun i =>
    ⟨(parent, (phaseLineInitialSlot k hn i).1),
      ⟨rfl, (phaseLineInitialSlot k hn i).2⟩⟩

theorem phaseProductLineInitialSlot_injective {Parent : Type*} (parent : Parent)
    {h M n : Nat} [NeZero M] (k : ZMod h) (hn : n ≤ M) :
    Function.Injective (phaseProductLineInitialSlot parent k hn) := by
  intro i j hij
  apply phaseLineInitialSlot_injective k hn
  apply Subtype.ext
  have hpair := congrArg Subtype.val hij
  exact congrArg Prod.snd hpair

theorem phaseProductLineInitialSlot_parent {Parent : Type*} (parent : Parent)
    {h M n : Nat} [NeZero M] (k : ZMod h) (hn : n ≤ M) (i : Fin n) :
    (phaseProductLineInitialSlot parent k hn i).1.1 = parent :=
  rfl

theorem phaseProductLineInitialSlot_phase {Parent : Type*} (parent : Parent)
    {h M n : Nat} [NeZero M] (k : ZMod h) (hn : n ≤ M) (i : Fin n) :
    phaseProjection (phaseProductLineInitialSlot parent k hn i).1.2 = k :=
  (phaseLineInitialSlot k hn i).2

def phaseProductReserveLineSlot {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    Fin (2 * a + 3) → {x : Parent × PhaseSection h (m ^ a) //
      x ∈ ProductCylinder ({parent} : Set Parent)
        (@PhaseLine h (m ^ a) (2 : ZMod h))} :=
  phaseProductLineInitialSlot parent (2 : ZMod h)
    (phaseReserveCapacity a m ha hm)

theorem phaseProductReserveLineSlot_injective {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    Function.Injective (phaseProductReserveLineSlot parent h a m ha hm) :=
  phaseProductLineInitialSlot_injective parent (2 : ZMod h)
    (phaseReserveCapacity a m ha hm)

theorem phaseProductReserveLineSlot_parent {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    (i : Fin (2 * a + 3)) :
    (phaseProductReserveLineSlot parent h a m ha hm i).1.1 = parent :=
  phaseProductLineInitialSlot_parent parent (2 : ZMod h)
    (phaseReserveCapacity a m ha hm) i

theorem phaseProductReserveLineSlot_phase {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    (i : Fin (2 * a + 3)) :
    phaseProjection (phaseProductReserveLineSlot parent h a m ha hm i).1.2 =
      (2 : ZMod h) :=
  phaseProductLineInitialSlot_phase parent (2 : ZMod h)
    (phaseReserveCapacity a m ha hm) i

theorem phaseProductReserveLineSlot_not_mem_protectedCylinder
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent) (i : Fin (2 * a + 3)) :
    (phaseProductReserveLineSlot parent h a m ha hm i).1 ∉
      ProductCylinder T (PhaseProtectedStrips h (m ^ a)) := by
  intro hxProtected
  exact phaseReserveLineDisjointFromProtectedStrips (M := m ^ a) hh
    (phaseProductReserveLineSlot parent h a m ha hm i).1.2
    (phaseProductReserveLineSlot parent h a m ha hm i).2.2
    hxProtected.2

def phaseProductReserveLineSlotList {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    List {x : Parent × PhaseSection h (m ^ a) //
      x ∈ ProductCylinder ({parent} : Set Parent)
        (@PhaseLine h (m ^ a) (2 : ZMod h))} :=
  (List.finRange (2 * a + 3)).map
    (phaseProductReserveLineSlot parent h a m ha hm)

theorem phaseProductReserveLineSlotList_length {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    (phaseProductReserveLineSlotList parent h a m ha hm).length = 2 * a + 3 := by
  rw [phaseProductReserveLineSlotList, List.length_map, List.length_finRange]

theorem phaseProductReserveLineSlotList_nodup {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    (phaseProductReserveLineSlotList parent h a m ha hm).Nodup :=
  List.Nodup.map
    (phaseProductReserveLineSlot_injective parent h a m ha hm)
    (List.nodup_finRange (2 * a + 3))

theorem phaseProductReserveLineSlotList_parent {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {x : {x : Parent × PhaseSection h (m ^ a) //
      x ∈ ProductCylinder ({parent} : Set Parent)
        (@PhaseLine h (m ^ a) (2 : ZMod h))}}
    (hx : x ∈ phaseProductReserveLineSlotList parent h a m ha hm) :
    x.1.1 = parent := by
  rcases (List.mem_map.mp hx) with ⟨i, hi, rfl⟩
  exact phaseProductReserveLineSlot_parent parent h a m ha hm i

theorem phaseProductReserveLineSlotList_phase {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {x : {x : Parent × PhaseSection h (m ^ a) //
      x ∈ ProductCylinder ({parent} : Set Parent)
        (@PhaseLine h (m ^ a) (2 : ZMod h))}}
    (hx : x ∈ phaseProductReserveLineSlotList parent h a m ha hm) :
    phaseProjection x.1.2 = (2 : ZMod h) := by
  rcases (List.mem_map.mp hx) with ⟨i, hi, rfl⟩
  exact phaseProductReserveLineSlot_phase parent h a m ha hm i

theorem phaseProductReserveLineSlotList_not_mem_protectedCylinder
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {x : {x : Parent × PhaseSection h (m ^ a) //
      x ∈ ProductCylinder ({parent} : Set Parent)
        (@PhaseLine h (m ^ a) (2 : ZMod h))}}
    (hx : x ∈ phaseProductReserveLineSlotList parent h a m ha hm) :
    x.1 ∉ ProductCylinder T (PhaseProtectedStrips h (m ^ a)) := by
  rcases (List.mem_map.mp hx) with ⟨i, hi, rfl⟩
  exact phaseProductReserveLineSlot_not_mem_protectedCylinder
    parent h a m hh ha hm T i

def phaseProductReserveLineSlotPointList {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    List (Parent × PhaseSection h (m ^ a)) :=
  (phaseProductReserveLineSlotList parent h a m ha hm).map Subtype.val

theorem phaseProductReserveLineSlotPointList_length {Parent : Type*}
    (parent : Parent) (h a m : Nat) [NeZero m]
    (ha : 2 ≤ a) (hm : 4 ≤ m) :
    (phaseProductReserveLineSlotPointList parent h a m ha hm).length =
      2 * a + 3 := by
  rw [phaseProductReserveLineSlotPointList, List.length_map,
    phaseProductReserveLineSlotList_length]

theorem phaseProductReserveLineSlotPointList_nodup {Parent : Type*}
    (parent : Parent) (h a m : Nat) [NeZero m]
    (ha : 2 ≤ a) (hm : 4 ≤ m) :
    (phaseProductReserveLineSlotPointList parent h a m ha hm).Nodup :=
  List.Nodup.map
    (fun _ _ hxy => Subtype.ext hxy)
    (phaseProductReserveLineSlotList_nodup parent h a m ha hm)

theorem phaseProductReserveLineSlotPointList_parent {Parent : Type*}
    (parent : Parent) (h a m : Nat) [NeZero m]
    (ha : 2 ≤ a) (hm : 4 ≤ m)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ phaseProductReserveLineSlotPointList parent h a m ha hm) :
    x.1 = parent := by
  rcases (List.mem_map.mp hx) with ⟨slot, hslot, rfl⟩
  exact phaseProductReserveLineSlotList_parent parent h a m ha hm hslot

theorem phaseProductReserveLineSlotPointList_phase {Parent : Type*}
    (parent : Parent) (h a m : Nat) [NeZero m]
    (ha : 2 ≤ a) (hm : 4 ≤ m)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ phaseProductReserveLineSlotPointList parent h a m ha hm) :
    phaseProjection x.2 = (2 : ZMod h) := by
  rcases (List.mem_map.mp hx) with ⟨slot, hslot, rfl⟩
  exact phaseProductReserveLineSlotList_phase parent h a m ha hm hslot

theorem phaseProductReserveLineSlotPointList_not_mem_protectedCylinder
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ phaseProductReserveLineSlotPointList parent h a m ha hm) :
    x ∉ ProductCylinder T (PhaseProtectedStrips h (m ^ a)) := by
  rcases (List.mem_map.mp hx) with ⟨slot, hslot, rfl⟩
  exact phaseProductReserveLineSlotList_not_mem_protectedCylinder
    parent h a m hh ha hm T hslot

def phaseProductReserveLineSlotPointSet {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    Set (Parent × PhaseSection h (m ^ a)) :=
  {x | x ∈ phaseProductReserveLineSlotPointList parent h a m ha hm}

theorem phaseProductReserveLineSlotPointSet_mem {Parent : Type*}
    (parent : Parent) (h a m : Nat) [NeZero m]
    (ha : 2 ≤ a) (hm : 4 ≤ m)
    (x : Parent × PhaseSection h (m ^ a)) :
    x ∈ phaseProductReserveLineSlotPointSet parent h a m ha hm ↔
      x ∈ phaseProductReserveLineSlotPointList parent h a m ha hm :=
  Iff.rfl

theorem phaseProductReserveLineSlotPointSet_subsetReserveCylinder
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    phaseProductReserveLineSlotPointSet parent h a m ha hm ⊆
      ProductCylinder ({parent} : Set Parent)
        (PhaseLine (h := h) (M := m ^ a) (2 : ZMod h)) := by
  intro x hx
  exact ⟨phaseProductReserveLineSlotPointList_parent parent h a m ha hm hx,
    phaseProductReserveLineSlotPointList_phase parent h a m ha hm hx⟩

theorem phaseProductReserveLineSlotPointSet_constantParentProjection
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    ProjectionConstantOn (fun x : Parent × PhaseSection h (m ^ a) => x.1)
      (phaseProductReserveLineSlotPointSet parent h a m ha hm) parent := by
  intro x hx
  exact phaseProductReserveLineSlotPointList_parent parent h a m ha hm hx

theorem phaseProductReserveLineSlotPointSet_constantPhaseProjection
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    ProjectionConstantOn
      (fun x : Parent × PhaseSection h (m ^ a) => phaseProjection x.2)
      (phaseProductReserveLineSlotPointSet parent h a m ha hm)
      (2 : ZMod h) := by
  intro x hx
  exact phaseProductReserveLineSlotPointList_phase parent h a m ha hm hx

theorem phaseProductReserveLineSlotPointSet_disjointFromProtectedCylinder
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent) :
    SetsDisjoint (phaseProductReserveLineSlotPointSet parent h a m ha hm)
      (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) := by
  intro x hxSet hxProtected
  exact phaseProductReserveLineSlotPointList_not_mem_protectedCylinder
    parent h a m hh ha hm T hxSet hxProtected

theorem phaseProductReserveLineSlotPointSet_mem_iff_exists_slot
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    (x : Parent × PhaseSection h (m ^ a)) :
    x ∈ phaseProductReserveLineSlotPointSet parent h a m ha hm ↔
      ∃ i : Fin (2 * a + 3),
        (phaseProductReserveLineSlot parent h a m ha hm i).1 = x := by
  constructor
  · intro hx
    rcases (List.mem_map.mp hx) with ⟨slot, hslot, hval⟩
    rcases (List.mem_map.mp hslot) with ⟨i, hi, hslotEq⟩
    refine ⟨i, ?_⟩
    rw [hslotEq]
    exact hval
  · intro hx
    rcases hx with ⟨i, rfl⟩
    exact List.mem_map.mpr
      ⟨phaseProductReserveLineSlot parent h a m ha hm i,
        List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩,
        rfl⟩

theorem phaseProductReserveLineSlotPointSet_slot_unique
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {i j : Fin (2 * a + 3)}
    (hij :
      (phaseProductReserveLineSlot parent h a m ha hm i).1 =
        (phaseProductReserveLineSlot parent h a m ha hm j).1) :
    i = j :=
  phaseProductReserveLineSlot_injective parent h a m ha hm (Subtype.ext hij)

theorem phaseProductReserveLineSlotPointSet_exists_unique_slot
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ phaseProductReserveLineSlotPointSet parent h a m ha hm) :
    ∃! i : Fin (2 * a + 3),
      (phaseProductReserveLineSlot parent h a m ha hm i).1 = x := by
  rcases (phaseProductReserveLineSlotPointSet_mem_iff_exists_slot
      parent h a m ha hm x).mp hx with ⟨i, hi⟩
  refine ⟨i, hi, ?_⟩
  intro j hj
  exact phaseProductReserveLineSlotPointSet_slot_unique
    parent h a m ha hm (hj.trans hi.symm)

theorem phaseProductReserveLineSlotPoint_injective
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    Function.Injective
      (fun i : Fin (2 * a + 3) =>
        (phaseProductReserveLineSlot parent h a m ha hm i).1) := by
  intro i j hij
  exact phaseProductReserveLineSlotPointSet_slot_unique
    parent h a m ha hm hij

theorem phaseProductReserveLineSlotPair_injective
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m) :
    Function.Injective
      (fun i : Fin (2 * a + 3) =>
        (parent, (phaseProductReserveLineSlot parent h a m ha hm i).1.2)) := by
  intro i j hij
  apply phaseProductReserveLineSlotPoint_injective parent h a m ha hm
  apply Prod.ext
  · rw [phaseProductReserveLineSlot_parent, phaseProductReserveLineSlot_parent]
  · exact congrArg Prod.snd hij

structure PhaseProductReserveSupportCertificate
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) where
  supportSet : Set (Parent × PhaseSection h (m ^ a))
  supportSet_eq :
    supportSet = phaseProductReserveLineSlotPointSet parent h a m ha hm
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
  existsUniqueSlot :
    ∀ {x : Parent × PhaseSection h (m ^ a)}, x ∈ supportSet →
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

def phaseProductReserveSupportCertificate
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    PhaseProductReserveSupportCertificate parent h a m hh ha hm where
  supportSet := phaseProductReserveLineSlotPointSet parent h a m ha hm
  supportSet_eq := rfl
  subsetReserveCylinder :=
    phaseProductReserveLineSlotPointSet_subsetReserveCylinder
      parent h a m ha hm
  constantParentProjection :=
    phaseProductReserveLineSlotPointSet_constantParentProjection
      parent h a m ha hm
  constantPhaseProjection :=
    phaseProductReserveLineSlotPointSet_constantPhaseProjection
      parent h a m ha hm
  disjointFromProtectedCylinder :=
    phaseProductReserveLineSlotPointSet_disjointFromProtectedCylinder
      parent h a m hh ha hm
  existsUniqueSlot :=
    phaseProductReserveLineSlotPointSet_exists_unique_slot
      parent h a m ha hm
  pointInjective :=
    phaseProductReserveLineSlotPoint_injective parent h a m ha hm
  pairInjective :=
    phaseProductReserveLineSlotPair_injective parent h a m ha hm

theorem phaseProductReserveSupportCertificate_supportSet
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    (phaseProductReserveSupportCertificate parent h a m hh ha hm).supportSet =
      phaseProductReserveLineSlotPointSet parent h a m ha hm :=
  (phaseProductReserveSupportCertificate
    parent h a m hh ha hm).supportSet_eq

theorem phaseProductReserveSupportCertificate_subsetReserveCylinder
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    (phaseProductReserveSupportCertificate parent h a m hh ha hm).supportSet ⊆
      ProductCylinder ({parent} : Set Parent)
        (PhaseLine (h := h) (M := m ^ a) (2 : ZMod h)) :=
  (phaseProductReserveSupportCertificate
    parent h a m hh ha hm).subsetReserveCylinder

theorem phaseProductReserveSupportCertificate_constantParentProjection
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    ProjectionConstantOn
      (fun x : Parent × PhaseSection h (m ^ a) => x.1)
      (phaseProductReserveSupportCertificate
        parent h a m hh ha hm).supportSet
      parent :=
  (phaseProductReserveSupportCertificate
    parent h a m hh ha hm).constantParentProjection

theorem phaseProductReserveSupportCertificate_constantPhaseProjection
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    ProjectionConstantOn
      (fun x : Parent × PhaseSection h (m ^ a) => phaseProjection x.2)
      (phaseProductReserveSupportCertificate
        parent h a m hh ha hm).supportSet
      (2 : ZMod h) :=
  (phaseProductReserveSupportCertificate
    parent h a m hh ha hm).constantPhaseProjection

theorem phaseProductReserveSupportCertificate_disjointProtected
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent) :
    SetsDisjoint
      (phaseProductReserveSupportCertificate
        parent h a m hh ha hm).supportSet
      (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :=
  (phaseProductReserveSupportCertificate
    parent h a m hh ha hm).disjointFromProtectedCylinder T

theorem phaseProductReserveSupportCertificate_existsUniqueSlot
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx :
      x ∈ (phaseProductReserveSupportCertificate
        parent h a m hh ha hm).supportSet) :
    ∃! i : Fin (2 * a + 3),
      (phaseProductReserveLineSlot parent h a m ha hm i).1 = x :=
  (phaseProductReserveSupportCertificate
    parent h a m hh ha hm).existsUniqueSlot hx

theorem phaseProductReserveSupportCertificate_pointInjective
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    Function.Injective
      (fun i : Fin (2 * a + 3) =>
        (phaseProductReserveLineSlot parent h a m ha hm i).1) :=
  (phaseProductReserveSupportCertificate
    parent h a m hh ha hm).pointInjective

theorem phaseProductReserveSupportCertificate_pairInjective
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m) :
    Function.Injective
      (fun i : Fin (2 * a + 3) =>
        (parent, (phaseProductReserveLineSlot parent h a m ha hm i).1.2)) :=
  (phaseProductReserveSupportCertificate
    parent h a m hh ha hm).pairInjective

theorem phaseProductReserveSupportCertificate_fixedByProtectedMap
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ C.supportSet) :
    f x = x :=
  supportedOn_apply_of_mem_disjoint hf
    (setsDisjoint_symm (C.disjointFromProtectedCylinder T)) hx

theorem phaseProductReserveSupportCertificate_fixedByProtectedIter
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    (n : Nat) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ C.supportSet) :
    (f^[n]) x = x :=
  supportedOn_iterate_apply_of_mem_disjoint hf
    (setsDisjoint_symm (C.disjointFromProtectedCylinder T)) n hx

theorem phaseProductReserveSupportCertificate_fixedByProtectedWordEval
    {ι Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ C.supportSet) :
    wordEval step word x = x :=
  supportedOn_wordEval_apply_of_mem_disjoint step hstep
    (setsDisjoint_symm (C.disjointFromProtectedCylinder T)) word hx

theorem phaseProductReserveSupportCertificate_fixedByProtectedWordIter
    {ι Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι) (n : Nat) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ C.supportSet) :
    ((wordEval step word)^[n]) x = x :=
  supportedOn_wordEval_iterate_apply_of_mem_disjoint step hstep
    (setsDisjoint_symm (C.disjointFromProtectedCylinder T)) word n hx

theorem phaseProductReserveSupportCertificate_mapsIntoProtectedMap
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f) :
    MapsInto C.supportSet f :=
  mapsInto_of_supportedOn_disjoint hf
    (setsDisjoint_symm (C.disjointFromProtectedCylinder T))

theorem phaseProductReserveSupportCertificate_mapsIntoProtectedIter
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    (n : Nat) :
    MapsInto C.supportSet (f^[n]) :=
  mapsInto_iterate_of_supportedOn_disjoint hf
    (setsDisjoint_symm (C.disjointFromProtectedCylinder T)) n

theorem phaseProductReserveSupportCertificate_mapsIntoProtectedWordEval
    {ι Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι) :
    MapsInto C.supportSet (wordEval step word) :=
  mapsInto_wordEval_of_supportedOn_disjoint step hstep
    (setsDisjoint_symm (C.disjointFromProtectedCylinder T)) word

theorem phaseProductReserveSupportCertificate_mapsIntoProtectedWordIter
    {ι Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι) (n : Nat) :
    MapsInto C.supportSet ((wordEval step word)^[n]) :=
  mapsInto_wordEval_iterate_of_supportedOn_disjoint step hstep
    (setsDisjoint_symm (C.disjointFromProtectedCylinder T)) word n

theorem phaseProductProtectedCylinder_fixedByReserveSupportCertificateMap
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn C.supportSet f)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :
    f x = x :=
  supportedOn_apply_of_mem_disjoint hf
    (C.disjointFromProtectedCylinder T) hx

theorem phaseProductProtectedCylinder_fixedByReserveSupportCertificateIter
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn C.supportSet f)
    (n : Nat) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :
    (f^[n]) x = x :=
  supportedOn_iterate_apply_of_mem_disjoint hf
    (C.disjointFromProtectedCylinder T) n hx

theorem phaseProductProtectedCylinder_fixedByReserveSupportCertificateWordEval
    {ι Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hstep : ∀ j : ι, SupportedOn C.supportSet (step j))
    (word : List ι) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :
    wordEval step word x = x :=
  supportedOn_wordEval_apply_of_mem_disjoint step hstep
    (C.disjointFromProtectedCylinder T) word hx

theorem phaseProductProtectedCylinder_fixedByReserveSupportCertificateWordIter
    {ι Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hstep : ∀ j : ι, SupportedOn C.supportSet (step j))
    (word : List ι) (n : Nat) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :
    ((wordEval step word)^[n]) x = x :=
  supportedOn_wordEval_iterate_apply_of_mem_disjoint step hstep
    (C.disjointFromProtectedCylinder T) word n hx

theorem phaseProductProtectedCylinder_mapsIntoReserveSupportCertificateMap
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn C.supportSet f) :
    MapsInto (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f :=
  mapsInto_of_supportedOn_disjoint hf
    (C.disjointFromProtectedCylinder T)

theorem phaseProductProtectedCylinder_mapsIntoReserveSupportCertificateIter
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn C.supportSet f)
    (n : Nat) :
    MapsInto (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (f^[n]) :=
  mapsInto_iterate_of_supportedOn_disjoint hf
    (C.disjointFromProtectedCylinder T) n

theorem phaseProductProtectedCylinder_mapsIntoReserveSupportCertificateWordEval
    {ι Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hstep : ∀ j : ι, SupportedOn C.supportSet (step j))
    (word : List ι) :
    MapsInto (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
      (wordEval step word) :=
  mapsInto_wordEval_of_supportedOn_disjoint step hstep
    (C.disjointFromProtectedCylinder T) word

theorem phaseProductProtectedCylinder_mapsIntoReserveSupportCertificateWordIter
    {ι Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hstep : ∀ j : ι, SupportedOn C.supportSet (step j))
    (word : List ι) (n : Nat) :
    MapsInto (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
      ((wordEval step word)^[n]) :=
  mapsInto_wordEval_iterate_of_supportedOn_disjoint step hstep
    (C.disjointFromProtectedCylinder T) word n

theorem phaseProductReserveSupportCertificateProtectedMapsCommute
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f g : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn C.supportSet f)
    (hg : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) g) :
    Function.Commute f g :=
  commuteOfDisjointSupportedOn hf hg
    (C.disjointFromProtectedCylinder T)

theorem phaseProductReserveSupportCertificateProtectedMapsCommute_symmSupports
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f g : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    (hg : SupportedOn C.supportSet g) :
    Function.Commute f g :=
  commuteOfDisjointSupportedOn_symmSupports hf hg
    (C.disjointFromProtectedCylinder T)

theorem phaseProductReserveSupportCertificateProtectedItersCommute
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f g : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn C.supportSet f)
    (hg : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  commuteOfDisjointSupportedOn_iterates hf hg
    (C.disjointFromProtectedCylinder T) n k

theorem phaseProductReserveSupportCertificateProtectedItersCommute_symmSupports
    {Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    {f g : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    (hg : SupportedOn C.supportSet g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  commuteOfDisjointSupportedOn_iterates_symmSupports hf hg
    (C.disjointFromProtectedCylinder T) n k

theorem phaseProductReserveSupportCertificateProtectedWordEvalsCommute
    {ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn C.supportSet (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  commuteOfDisjointSupportedWordEvals
    leftStep rightStep hleft hright
    (C.disjointFromProtectedCylinder T) leftWord rightWord

theorem phaseProductReserveSupportCertificateProtectedWordEvalsCommute_symmSupports
    {ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ i : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (leftStep i))
    (hright : ∀ j : κ, SupportedOn C.supportSet (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  commuteOfDisjointSupportedWordEvals_symmSupports
    leftStep rightStep hleft hright
    (C.disjointFromProtectedCylinder T) leftWord rightWord

theorem phaseProductReserveSupportCertificateProtectedWordItersCommute
    {ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft : ∀ i : ι, SupportedOn C.supportSet (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  commuteOfDisjointSupportedWordEvalIterates
    leftStep rightStep hleft hright
    (C.disjointFromProtectedCylinder T) leftWord rightWord n k

theorem phaseProductReserveSupportCertificateProtectedWordItersCommute_symmSupports
    {ι κ Parent : Type*} {parent : Parent}
    {h a m : Nat} [NeZero h] [NeZero m]
    {hh : 3 < h} {ha : 2 ≤ a} {hm : 4 ≤ m}
    (C : PhaseProductReserveSupportCertificate parent h a m hh ha hm)
    (T : Set Parent)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ i : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (leftStep i))
    (hright : ∀ j : κ, SupportedOn C.supportSet (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  commuteOfDisjointSupportedWordEvalIterates_symmSupports
    leftStep rightStep hleft hright
    (C.disjointFromProtectedCylinder T) leftWord rightWord n k

theorem phaseProductReserveLineSlotPointWordEvalsCommute
    {ι κ Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ symbol : ι, SupportedOn
        ({(phaseProductReserveLineSlot parent h a m ha hm i).1} :
          Set (Parent × PhaseSection h (m ^ a))) (leftStep symbol))
    (hright :
      ∀ symbol : κ, SupportedOn
        ({(phaseProductReserveLineSlot parent h a m ha hm j).1} :
          Set (Parent × PhaseSection h (m ^ a))) (rightStep symbol))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  indexedSingletonSupportedWordEvalsCommute_of_injective
    (phaseProductReserveLineSlotPoint_injective parent h a m ha hm)
    hij leftStep rightStep hleft hright leftWord rightWord

theorem phaseProductReserveLineSlotPointWordEvalsCommute_symm
    {ι κ Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ symbol : ι, SupportedOn
        ({(phaseProductReserveLineSlot parent h a m ha hm j).1} :
          Set (Parent × PhaseSection h (m ^ a))) (leftStep symbol))
    (hright :
      ∀ symbol : κ, SupportedOn
        ({(phaseProductReserveLineSlot parent h a m ha hm i).1} :
          Set (Parent × PhaseSection h (m ^ a))) (rightStep symbol))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  indexedSingletonSupportedWordEvalsCommute_symmSupports_of_injective
    (phaseProductReserveLineSlotPoint_injective parent h a m ha hm)
    hij leftStep rightStep hleft hright leftWord rightWord

theorem phaseProductReserveLineSlotPointWordEvalIteratesCommute
    {ι κ Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ symbol : ι, SupportedOn
        ({(phaseProductReserveLineSlot parent h a m ha hm i).1} :
          Set (Parent × PhaseSection h (m ^ a))) (leftStep symbol))
    (hright :
      ∀ symbol : κ, SupportedOn
        ({(phaseProductReserveLineSlot parent h a m ha hm j).1} :
          Set (Parent × PhaseSection h (m ^ a))) (rightStep symbol))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  indexedSingletonSupportedWordEvalIteratesCommute_of_injective
    (phaseProductReserveLineSlotPoint_injective parent h a m ha hm)
    hij leftStep rightStep hleft hright leftWord rightWord n k

theorem phaseProductReserveLineSlotPointWordEvalIteratesCommute_symm
    {ι κ Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ symbol : ι, SupportedOn
        ({(phaseProductReserveLineSlot parent h a m ha hm j).1} :
          Set (Parent × PhaseSection h (m ^ a))) (leftStep symbol))
    (hright :
      ∀ symbol : κ, SupportedOn
        ({(phaseProductReserveLineSlot parent h a m ha hm i).1} :
          Set (Parent × PhaseSection h (m ^ a))) (rightStep symbol))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  indexedSingletonSupportedWordEvalIteratesCommute_symmSupports_of_injective
    (phaseProductReserveLineSlotPoint_injective parent h a m ha hm)
    hij leftStep rightStep hleft hright leftWord rightWord n k

theorem phaseProductReserveLineSlotCylinderWordEvalsCommute
    {ι κ Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ symbol : ι, SupportedOn
        (ProductCylinder ({parent} : Set Parent)
          ({(phaseProductReserveLineSlot parent h a m ha hm i).1.2} :
            Set (PhaseSection h (m ^ a)))) (leftStep symbol))
    (hright :
      ∀ symbol : κ, SupportedOn
        (ProductCylinder ({parent} : Set Parent)
          ({(phaseProductReserveLineSlot parent h a m ha hm j).1.2} :
            Set (PhaseSection h (m ^ a)))) (rightStep symbol))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  indexedSingletonProductSupportedWordEvalsCommute_of_injective_pair
    (phaseProductReserveLineSlotPair_injective parent h a m ha hm)
    hij leftStep rightStep hleft hright leftWord rightWord

theorem phaseProductReserveLineSlotCylinderWordEvalsCommute_symm
    {ι κ Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ symbol : ι, SupportedOn
        (ProductCylinder ({parent} : Set Parent)
          ({(phaseProductReserveLineSlot parent h a m ha hm j).1.2} :
            Set (PhaseSection h (m ^ a)))) (leftStep symbol))
    (hright :
      ∀ symbol : κ, SupportedOn
        (ProductCylinder ({parent} : Set Parent)
          ({(phaseProductReserveLineSlot parent h a m ha hm i).1.2} :
            Set (PhaseSection h (m ^ a)))) (rightStep symbol))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  indexedSingletonProductSupportedWordEvalsCommute_symmSupports_of_injective_pair
    (phaseProductReserveLineSlotPair_injective parent h a m ha hm)
    hij leftStep rightStep hleft hright leftWord rightWord

theorem phaseProductReserveLineSlotCylinderWordEvalIteratesCommute
    {ι κ Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ symbol : ι, SupportedOn
        (ProductCylinder ({parent} : Set Parent)
          ({(phaseProductReserveLineSlot parent h a m ha hm i).1.2} :
            Set (PhaseSection h (m ^ a)))) (leftStep symbol))
    (hright :
      ∀ symbol : κ, SupportedOn
        (ProductCylinder ({parent} : Set Parent)
          ({(phaseProductReserveLineSlot parent h a m ha hm j).1.2} :
            Set (PhaseSection h (m ^ a)))) (rightStep symbol))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  indexedSingletonProductSupportedWordEvalIteratesCommute_of_injective_pair
    (phaseProductReserveLineSlotPair_injective parent h a m ha hm)
    hij leftStep rightStep hleft hright leftWord rightWord n k

theorem phaseProductReserveLineSlotCylinderWordEvalIteratesCommute_symm
    {ι κ Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero m] (ha : 2 ≤ a) (hm : 4 ≤ m)
    {i j : Fin (2 * a + 3)} (hij : i ≠ j)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ symbol : ι, SupportedOn
        (ProductCylinder ({parent} : Set Parent)
          ({(phaseProductReserveLineSlot parent h a m ha hm j).1.2} :
            Set (PhaseSection h (m ^ a)))) (leftStep symbol))
    (hright :
      ∀ symbol : κ, SupportedOn
        (ProductCylinder ({parent} : Set Parent)
          ({(phaseProductReserveLineSlot parent h a m ha hm i).1.2} :
            Set (PhaseSection h (m ^ a)))) (rightStep symbol))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  indexedSingletonProductSupportedWordEvalIteratesCommute_symm_of_injective_pair
    (phaseProductReserveLineSlotPair_injective parent h a m ha hm)
    hij leftStep rightStep hleft hright leftWord rightWord n k

theorem phaseProductReserveLineSlot_fixedByProtectedSupportedMap
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    (i : Fin (2 * a + 3)) :
    f (phaseProductReserveLineSlot parent h a m ha hm i).1 =
      (phaseProductReserveLineSlot parent h a m ha hm i).1 :=
  supportedOn_apply_of_not_mem hf
    (phaseProductReserveLineSlot_not_mem_protectedCylinder
      parent h a m hh ha hm T i)

theorem phaseProductReserveLineSlot_fixedByProtectedSupportedIterate
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    (n : Nat) (i : Fin (2 * a + 3)) :
    (f^[n]) (phaseProductReserveLineSlot parent h a m ha hm i).1 =
      (phaseProductReserveLineSlot parent h a m ha hm i).1 :=
  supportedOn_apply_of_not_mem (supportedOn_iterate hf n)
    (phaseProductReserveLineSlot_not_mem_protectedCylinder
      parent h a m hh ha hm T i)

theorem phaseProductReserveLineSlot_fixedByProtectedSupportedWordEval
    {ι Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι) (i : Fin (2 * a + 3)) :
    wordEval step word (phaseProductReserveLineSlot parent h a m ha hm i).1 =
      (phaseProductReserveLineSlot parent h a m ha hm i).1 :=
  supportedOn_apply_of_not_mem (supportedOn_wordEval step hstep word)
    (phaseProductReserveLineSlot_not_mem_protectedCylinder
      parent h a m hh ha hm T i)

theorem phaseProductReserveLineSlot_fixedByProtectedSupportedWordEvalIterate
    {ι Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι) (n : Nat) (i : Fin (2 * a + 3)) :
    ((wordEval step word)^[n])
        (phaseProductReserveLineSlot parent h a m ha hm i).1 =
      (phaseProductReserveLineSlot parent h a m ha hm i).1 :=
  supportedOn_apply_of_not_mem
    (supportedOn_iterate (supportedOn_wordEval step hstep word) n)
    (phaseProductReserveLineSlot_not_mem_protectedCylinder
      parent h a m hh ha hm T i)

theorem phaseProductReserveLineSlotList_fixedByProtectedSupportedMap
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    {x : {x : Parent × PhaseSection h (m ^ a) //
      x ∈ ProductCylinder ({parent} : Set Parent)
        (@PhaseLine h (m ^ a) (2 : ZMod h))}}
    (hx : x ∈ phaseProductReserveLineSlotList parent h a m ha hm) :
    f x.1 = x.1 :=
  supportedOn_apply_of_not_mem hf
    (phaseProductReserveLineSlotList_not_mem_protectedCylinder
      parent h a m hh ha hm T hx)

theorem phaseProductReserveLineSlotList_fixedByProtectedSupportedIterate
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    (n : Nat)
    {x : {x : Parent × PhaseSection h (m ^ a) //
      x ∈ ProductCylinder ({parent} : Set Parent)
        (@PhaseLine h (m ^ a) (2 : ZMod h))}}
    (hx : x ∈ phaseProductReserveLineSlotList parent h a m ha hm) :
    (f^[n]) x.1 = x.1 :=
  supportedOn_apply_of_not_mem (supportedOn_iterate hf n)
    (phaseProductReserveLineSlotList_not_mem_protectedCylinder
      parent h a m hh ha hm T hx)

theorem phaseProductReserveLineSlotList_fixedByProtectedSupportedWordEval
    {ι Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι)
    {x : {x : Parent × PhaseSection h (m ^ a) //
      x ∈ ProductCylinder ({parent} : Set Parent)
        (@PhaseLine h (m ^ a) (2 : ZMod h))}}
    (hx : x ∈ phaseProductReserveLineSlotList parent h a m ha hm) :
    wordEval step word x.1 = x.1 :=
  supportedOn_apply_of_not_mem (supportedOn_wordEval step hstep word)
    (phaseProductReserveLineSlotList_not_mem_protectedCylinder
      parent h a m hh ha hm T hx)

theorem phaseProductReserveLineSlotList_fixedByProtectedSupportedWordEvalIterate
    {ι Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι) (n : Nat)
    {x : {x : Parent × PhaseSection h (m ^ a) //
      x ∈ ProductCylinder ({parent} : Set Parent)
        (@PhaseLine h (m ^ a) (2 : ZMod h))}}
    (hx : x ∈ phaseProductReserveLineSlotList parent h a m ha hm) :
    ((wordEval step word)^[n]) x.1 = x.1 :=
  supportedOn_apply_of_not_mem
    (supportedOn_iterate (supportedOn_wordEval step hstep word) n)
    (phaseProductReserveLineSlotList_not_mem_protectedCylinder
      parent h a m hh ha hm T hx)

theorem phaseProductReserveLineSlotPointList_fixedByProtectedSupportedMap
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ phaseProductReserveLineSlotPointList parent h a m ha hm) :
    f x = x :=
  supportedOn_apply_of_not_mem hf
    (phaseProductReserveLineSlotPointList_not_mem_protectedCylinder
      parent h a m hh ha hm T hx)

theorem phaseProductReserveLineSlotPointList_fixedByProtectedSupportedIterate
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    (n : Nat) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ phaseProductReserveLineSlotPointList parent h a m ha hm) :
    (f^[n]) x = x :=
  supportedOn_apply_of_not_mem (supportedOn_iterate hf n)
    (phaseProductReserveLineSlotPointList_not_mem_protectedCylinder
      parent h a m hh ha hm T hx)

theorem phaseProductReserveLineSlotPointList_fixedByProtectedSupportedWordEval
    {ι Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ phaseProductReserveLineSlotPointList parent h a m ha hm) :
    wordEval step word x = x :=
  supportedOn_apply_of_not_mem (supportedOn_wordEval step hstep word)
    (phaseProductReserveLineSlotPointList_not_mem_protectedCylinder
      parent h a m hh ha hm T hx)

theorem phaseProductReserveLineSlotPointList_fixedByProtectedSupportedWordEvalIterate
    {ι Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι) (n : Nat) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ phaseProductReserveLineSlotPointList parent h a m ha hm) :
    ((wordEval step word)^[n]) x = x :=
  supportedOn_apply_of_not_mem
    (supportedOn_iterate (supportedOn_wordEval step hstep word) n)
    (phaseProductReserveLineSlotPointList_not_mem_protectedCylinder
      parent h a m hh ha hm T hx)

theorem phaseProductReserveLineSlotPointSet_fixedByProtectedSupportedMap
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ phaseProductReserveLineSlotPointSet parent h a m ha hm) :
    f x = x :=
  phaseProductReserveLineSlotPointList_fixedByProtectedSupportedMap
    parent h a m hh ha hm T hf hx

theorem phaseProductReserveLineSlotPointSet_fixedByProtectedSupportedIterate
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    (n : Nat) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ phaseProductReserveLineSlotPointSet parent h a m ha hm) :
    (f^[n]) x = x :=
  phaseProductReserveLineSlotPointList_fixedByProtectedSupportedIterate
    parent h a m hh ha hm T hf n hx

theorem phaseProductReserveLineSlotPointSet_fixedByProtectedSupportedWordEval
    {ι Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ phaseProductReserveLineSlotPointSet parent h a m ha hm) :
    wordEval step word x = x :=
  phaseProductReserveLineSlotPointList_fixedByProtectedSupportedWordEval
    parent h a m hh ha hm T step hstep word hx

theorem phaseProductReserveLineSlotPointSet_fixedByProtectedSupportedWordEvalIterate
    {ι Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι) (n : Nat) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ phaseProductReserveLineSlotPointSet parent h a m ha hm) :
    ((wordEval step word)^[n]) x = x :=
  phaseProductReserveLineSlotPointList_fixedByProtectedSupportedWordEvalIterate
    parent h a m hh ha hm T step hstep word n hx

theorem phaseProductReserveLineSlotPointSet_mapsIntoProtectedSupportedMap
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f) :
    MapsInto (phaseProductReserveLineSlotPointSet parent h a m ha hm) f := by
  intro x hx
  rw [phaseProductReserveLineSlotPointSet_fixedByProtectedSupportedMap
    parent h a m hh ha hm T hf hx]
  exact hx

theorem phaseProductReserveLineSlotPointSet_mapsIntoProtectedSupportedIterate
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    (n : Nat) :
    MapsInto (phaseProductReserveLineSlotPointSet parent h a m ha hm)
      (f^[n]) := by
  intro x hx
  rw [phaseProductReserveLineSlotPointSet_fixedByProtectedSupportedIterate
    parent h a m hh ha hm T hf n hx]
  exact hx

theorem phaseProductReserveLineSlotPointSet_mapsIntoProtectedSupportedWordEval
    {ι Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι) :
    MapsInto (phaseProductReserveLineSlotPointSet parent h a m ha hm)
      (wordEval step word) := by
  intro x hx
  rw [phaseProductReserveLineSlotPointSet_fixedByProtectedSupportedWordEval
    parent h a m hh ha hm T step hstep word hx]
  exact hx

theorem phaseProductReserveLineSlotPointSet_mapsIntoProtectedSupportedWordEvalIterate
    {ι Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) → Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (step j))
    (word : List ι) (n : Nat) :
    MapsInto (phaseProductReserveLineSlotPointSet parent h a m ha hm)
      ((wordEval step word)^[n]) := by
  intro x hx
  rw [phaseProductReserveLineSlotPointSet_fixedByProtectedSupportedWordEvalIterate
    parent h a m hh ha hm T step hstep word n hx]
  exact hx

theorem phaseProductReserveLineSlotPointSetProtectedSupportedMapsCommute
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f g : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (phaseProductReserveLineSlotPointSet
      parent h a m ha hm) f)
    (hg : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) g) :
    Function.Commute f g :=
  productCylinderRightProjectionSeparatedSupportedMapsCommute
    (@phaseProjection h (m ^ a))
    (supportedOn_mono
      (phaseProductReserveLineSlotPointSet_subsetReserveCylinder
        parent h a m ha hm) hf)
    hg
    (phaseReserveLineProjectionSeparatedFromProtectedStrips hh)

theorem phaseProductReserveLineSlotPointSetProtectedSupportedMapsCommute_symmSupports
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f g : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    (hg : SupportedOn (phaseProductReserveLineSlotPointSet
      parent h a m ha hm) g) :
    Function.Commute f g :=
  productCylinderRightProjectionSeparatedSupportedMapsCommute
    (@phaseProjection h (m ^ a))
    hf
    (supportedOn_mono
      (phaseProductReserveLineSlotPointSet_subsetReserveCylinder
        parent h a m ha hm) hg)
    (projectionImagesDisjoint_symm (@phaseProjection h (m ^ a))
      (phaseReserveLineProjectionSeparatedFromProtectedStrips hh))

theorem phaseProductReserveLineSlotPointSetProtectedSupportedIteratesCommute
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f g : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (phaseProductReserveLineSlotPointSet
      parent h a m ha hm) f)
    (hg : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  productCylinderRightProjectionSeparatedSupportedIteratesCommute
    (@phaseProjection h (m ^ a))
    (supportedOn_mono
      (phaseProductReserveLineSlotPointSet_subsetReserveCylinder
        parent h a m ha hm) hf)
    hg
    (phaseReserveLineProjectionSeparatedFromProtectedStrips hh) n k

theorem phaseProductReserveLineSlotPointSetProtectedSupportedIteratesCommute_symmSupports
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f g : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f)
    (hg : SupportedOn (phaseProductReserveLineSlotPointSet
      parent h a m ha hm) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  productCylinderRightProjectionSeparatedSupportedIteratesCommute
    (@phaseProjection h (m ^ a))
    hf
    (supportedOn_mono
      (phaseProductReserveLineSlotPointSet_subsetReserveCylinder
        parent h a m ha hm) hg)
    (projectionImagesDisjoint_symm (@phaseProjection h (m ^ a))
      (phaseReserveLineProjectionSeparatedFromProtectedStrips hh)) n k

theorem phaseReserveProtectedProductCylinderSupportedMapsCommute
    {Parent : Type*} {h M : Nat} [NeZero h] (hh : 3 < h)
    {S T : Set Parent}
    {f g : Parent × PhaseSection h M → Parent × PhaseSection h M}
    (hf : SupportedOn
      (ProductCylinder S (PhaseLine (h := h) (M := M) (2 : ZMod h))) f)
    (hg : SupportedOn (ProductCylinder T (PhaseProtectedStrips h M)) g) :
    Function.Commute f g :=
  productCylinderRightProjectionSeparatedSupportedMapsCommute
    (@phaseProjection h M) hf hg
    (phaseReserveLineProjectionSeparatedFromProtectedStrips hh)

theorem phaseReserveProtectedProductCylinderSupportedMapsCommute_symmSupports
    {Parent : Type*} {h M : Nat} [NeZero h] (hh : 3 < h)
    {S T : Set Parent}
    {f g : Parent × PhaseSection h M → Parent × PhaseSection h M}
    (hf : SupportedOn (ProductCylinder S (PhaseProtectedStrips h M)) f)
    (hg : SupportedOn
      (ProductCylinder T (PhaseLine (h := h) (M := M) (2 : ZMod h))) g) :
    Function.Commute f g :=
  productCylinderRightProjectionSeparatedSupportedMapsCommute
    (@phaseProjection h M) hf hg
    (projectionImagesDisjoint_symm (@phaseProjection h M)
      (phaseReserveLineProjectionSeparatedFromProtectedStrips hh))

theorem phaseReserveProtectedProductCylinderSupportedIteratesCommute
    {Parent : Type*} {h M : Nat} [NeZero h] (hh : 3 < h)
    {S T : Set Parent}
    {f g : Parent × PhaseSection h M → Parent × PhaseSection h M}
    (hf : SupportedOn
      (ProductCylinder S (PhaseLine (h := h) (M := M) (2 : ZMod h))) f)
    (hg : SupportedOn (ProductCylinder T (PhaseProtectedStrips h M)) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  productCylinderRightProjectionSeparatedSupportedIteratesCommute
    (@phaseProjection h M) hf hg
    (phaseReserveLineProjectionSeparatedFromProtectedStrips hh) n k

theorem phaseReserveProtectedProductCylinderSupportedIteratesCommute_symmSupports
    {Parent : Type*} {h M : Nat} [NeZero h] (hh : 3 < h)
    {S T : Set Parent}
    {f g : Parent × PhaseSection h M → Parent × PhaseSection h M}
    (hf : SupportedOn (ProductCylinder S (PhaseProtectedStrips h M)) f)
    (hg : SupportedOn
      (ProductCylinder T (PhaseLine (h := h) (M := M) (2 : ZMod h))) g)
    (n k : Nat) :
    Function.Commute (f^[n]) (g^[k]) :=
  productCylinderRightProjectionSeparatedSupportedIteratesCommute
    (@phaseProjection h M) hf hg
    (projectionImagesDisjoint_symm (@phaseProjection h M)
      (phaseReserveLineProjectionSeparatedFromProtectedStrips hh)) n k

theorem phaseReserveProtectedProductCylinderSupportedWordEvalsCommute
    {ι κ Parent : Type*} {h M : Nat} [NeZero h] (hh : 3 < h)
    {S T : Set Parent}
    (leftStep : ι → Parent × PhaseSection h M → Parent × PhaseSection h M)
    (rightStep : κ → Parent × PhaseSection h M → Parent × PhaseSection h M)
    (hleft :
      ∀ i : ι, SupportedOn
        (ProductCylinder S
          (PhaseLine (h := h) (M := M) (2 : ZMod h))) (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h M)) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  commuteOfDisjointSupportedWordEvals leftStep rightStep hleft hright
    (productCylinderDisjointOfRightProjectionImagesDisjoint
      (@phaseProjection h M) S T
      (PhaseLine (h := h) (M := M) (2 : ZMod h))
      (PhaseProtectedStrips h M)
      (phaseReserveLineProjectionSeparatedFromProtectedStrips hh))
    leftWord rightWord

theorem phaseReserveProtectedProductCylinderSupportedWordEvalsCommute_symmSupports
    {ι κ Parent : Type*} {h M : Nat} [NeZero h] (hh : 3 < h)
    {S T : Set Parent}
    (leftStep : ι → Parent × PhaseSection h M → Parent × PhaseSection h M)
    (rightStep : κ → Parent × PhaseSection h M → Parent × PhaseSection h M)
    (hleft :
      ∀ i : ι, SupportedOn
        (ProductCylinder S (PhaseProtectedStrips h M)) (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn
        (ProductCylinder T
          (PhaseLine (h := h) (M := M) (2 : ZMod h))) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  commuteOfDisjointSupportedWordEvals_symmSupports
    leftStep rightStep hleft hright
    (productCylinderDisjointOfRightProjectionImagesDisjoint
      (@phaseProjection h M) T S
      (PhaseLine (h := h) (M := M) (2 : ZMod h))
      (PhaseProtectedStrips h M)
      (phaseReserveLineProjectionSeparatedFromProtectedStrips hh))
    leftWord rightWord

theorem phaseReserveProtectedProductCylinderSupportedWordEvalIteratesCommute
    {ι κ Parent : Type*} {h M : Nat} [NeZero h] (hh : 3 < h)
    {S T : Set Parent}
    (leftStep : ι → Parent × PhaseSection h M → Parent × PhaseSection h M)
    (rightStep : κ → Parent × PhaseSection h M → Parent × PhaseSection h M)
    (hleft :
      ∀ i : ι, SupportedOn
        (ProductCylinder S
          (PhaseLine (h := h) (M := M) (2 : ZMod h))) (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h M)) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  commuteOfDisjointSupportedWordEvalIterates leftStep rightStep hleft hright
    (productCylinderDisjointOfRightProjectionImagesDisjoint
      (@phaseProjection h M) S T
      (PhaseLine (h := h) (M := M) (2 : ZMod h))
      (PhaseProtectedStrips h M)
      (phaseReserveLineProjectionSeparatedFromProtectedStrips hh))
    leftWord rightWord n k

theorem phaseReserveProtectedProductCylinderSupportedWordEvalIteratesCommute_symmSupports
    {ι κ Parent : Type*} {h M : Nat} [NeZero h] (hh : 3 < h)
    {S T : Set Parent}
    (leftStep : ι → Parent × PhaseSection h M → Parent × PhaseSection h M)
    (rightStep : κ → Parent × PhaseSection h M → Parent × PhaseSection h M)
    (hleft :
      ∀ i : ι, SupportedOn
        (ProductCylinder S (PhaseProtectedStrips h M)) (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn
        (ProductCylinder T
          (PhaseLine (h := h) (M := M) (2 : ZMod h))) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  commuteOfDisjointSupportedWordEvalIterates_symmSupports
    leftStep rightStep hleft hright
    (productCylinderDisjointOfRightProjectionImagesDisjoint
      (@phaseProjection h M) T S
      (PhaseLine (h := h) (M := M) (2 : ZMod h))
      (PhaseProtectedStrips h M)
      (phaseReserveLineProjectionSeparatedFromProtectedStrips hh))
    leftWord rightWord n k

theorem phaseProductReserveLineSlotPointSetProtectedWordEvalsCommute
    {ι κ Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ i : ι, SupportedOn
        (phaseProductReserveLineSlotPointSet parent h a m ha hm) (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  phaseReserveProtectedProductCylinderSupportedWordEvalsCommute hh
    leftStep rightStep
    (fun i => supportedOn_mono
      (phaseProductReserveLineSlotPointSet_subsetReserveCylinder
        parent h a m ha hm) (hleft i))
    hright leftWord rightWord

theorem phaseProductReserveLineSlotPointSetProtectedWordEvalsCommute_symmSupports
    {ι κ Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ i : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn
        (phaseProductReserveLineSlotPointSet parent h a m ha hm) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) :
    Function.Commute
      (wordEval leftStep leftWord) (wordEval rightStep rightWord) :=
  phaseReserveProtectedProductCylinderSupportedWordEvalsCommute_symmSupports hh
    leftStep rightStep hleft
    (fun j => supportedOn_mono
      (phaseProductReserveLineSlotPointSet_subsetReserveCylinder
        parent h a m ha hm) (hright j))
    leftWord rightWord

theorem phaseProductReserveLineSlotPointSetProtectedWordEvalIteratesCommute
    {ι κ Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ i : ι, SupportedOn
        (phaseProductReserveLineSlotPointSet parent h a m ha hm) (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  phaseReserveProtectedProductCylinderSupportedWordEvalIteratesCommute hh
    leftStep rightStep
    (fun i => supportedOn_mono
      (phaseProductReserveLineSlotPointSet_subsetReserveCylinder
        parent h a m ha hm) (hleft i))
    hright leftWord rightWord n k

theorem phaseProductReserveLineSlotPointSetProtectedWordEvalIteratesCommute_symmSupports
    {ι κ Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (leftStep : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (rightStep : κ → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hleft :
      ∀ i : ι, SupportedOn
        (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (leftStep i))
    (hright :
      ∀ j : κ, SupportedOn
        (phaseProductReserveLineSlotPointSet parent h a m ha hm) (rightStep j))
    (leftWord : List ι) (rightWord : List κ) (n k : Nat) :
    Function.Commute
      ((wordEval leftStep leftWord)^[n])
      ((wordEval rightStep rightWord)^[k]) :=
  phaseReserveProtectedProductCylinderSupportedWordEvalIteratesCommute_symmSupports
    hh leftStep rightStep hleft
    (fun j => supportedOn_mono
      (phaseProductReserveLineSlotPointSet_subsetReserveCylinder
        parent h a m ha hm) (hright j))
    leftWord rightWord n k

theorem phaseProductProtectedCylinder_fixedByReserveLineSlotPointSetSupportedMap
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn
      (phaseProductReserveLineSlotPointSet parent h a m ha hm) f)
    {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :
    f x = x :=
  supportedOn_apply_of_mem_disjoint hf
    (phaseProductReserveLineSlotPointSet_disjointFromProtectedCylinder
      parent h a m hh ha hm T) hx

theorem phaseProductProtectedCylinder_mapsIntoReserveLineSlotPointSetSupportedMap
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn
      (phaseProductReserveLineSlotPointSet parent h a m ha hm) f) :
    MapsInto (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) f :=
  mapsInto_of_supportedOn_disjoint hf
    (phaseProductReserveLineSlotPointSet_disjointFromProtectedCylinder
      parent h a m hh ha hm T)

theorem phaseProductProtectedCylinder_fixedByReserveLineSlotPointSetSupportedIterate
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn
      (phaseProductReserveLineSlotPointSet parent h a m ha hm) f)
    (n : Nat) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :
    (f^[n]) x = x :=
  supportedOn_iterate_apply_of_mem_disjoint hf
    (phaseProductReserveLineSlotPointSet_disjointFromProtectedCylinder
      parent h a m hh ha hm T) n hx

theorem phaseProductProtectedCylinder_mapsIntoReserveLineSlotPointSetSupportedIterate
    {Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    {f : Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a)}
    (hf : SupportedOn
      (phaseProductReserveLineSlotPointSet parent h a m ha hm) f)
    (n : Nat) :
    MapsInto (ProductCylinder T (PhaseProtectedStrips h (m ^ a))) (f^[n]) :=
  mapsInto_iterate_of_supportedOn_disjoint hf
    (phaseProductReserveLineSlotPointSet_disjointFromProtectedCylinder
      parent h a m hh ha hm T) n

theorem phaseProductProtectedCylinder_fixedByReserveLineSlotPointSetSupportedWordEval
    {ι Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (phaseProductReserveLineSlotPointSet parent h a m ha hm) (step j))
    (word : List ι) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :
    wordEval step word x = x :=
  supportedOn_wordEval_apply_of_mem_disjoint step hstep
    (phaseProductReserveLineSlotPointSet_disjointFromProtectedCylinder
      parent h a m hh ha hm T) word hx

theorem phaseProductProtectedCylinder_mapsIntoReserveLineSlotPointSetSupportedWordEval
    {ι Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (phaseProductReserveLineSlotPointSet parent h a m ha hm) (step j))
    (word : List ι) :
    MapsInto (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
      (wordEval step word) :=
  mapsInto_wordEval_of_supportedOn_disjoint step hstep
    (phaseProductReserveLineSlotPointSet_disjointFromProtectedCylinder
      parent h a m hh ha hm T) word

theorem phaseProductProtectedCylinder_fixedByReserveLineSlotPointSetSupportedWordEvalIterate
    {ι Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (phaseProductReserveLineSlotPointSet parent h a m ha hm) (step j))
    (word : List ι) (n : Nat) {x : Parent × PhaseSection h (m ^ a)}
    (hx : x ∈ ProductCylinder T (PhaseProtectedStrips h (m ^ a))) :
    ((wordEval step word)^[n]) x = x :=
  supportedOn_wordEval_iterate_apply_of_mem_disjoint step hstep
    (phaseProductReserveLineSlotPointSet_disjointFromProtectedCylinder
      parent h a m hh ha hm T) word n hx

theorem phaseProductProtectedCylinder_mapsIntoReserveLineSlotPointSetSupportedWordEvalIterate
    {ι Parent : Type*} (parent : Parent)
    (h a m : Nat) [NeZero h] [NeZero m]
    (hh : 3 < h) (ha : 2 ≤ a) (hm : 4 ≤ m)
    (T : Set Parent)
    (step : ι → Parent × PhaseSection h (m ^ a) →
      Parent × PhaseSection h (m ^ a))
    (hstep :
      ∀ j : ι, SupportedOn
        (phaseProductReserveLineSlotPointSet parent h a m ha hm) (step j))
    (word : List ι) (n : Nat) :
    MapsInto (ProductCylinder T (PhaseProtectedStrips h (m ^ a)))
      ((wordEval step word)^[n]) :=
  mapsInto_wordEval_iterate_of_supportedOn_disjoint step hstep
    (phaseProductReserveLineSlotPointSet_disjointFromProtectedCylinder
      parent h a m hh ha hm T) word n

end PhaseProductSupport

export PhaseProductSupport
  (phaseProductLineInitialSlot phaseProductLineInitialSlot_injective
   phaseProductLineInitialSlot_parent phaseProductLineInitialSlot_phase
   phaseProductReserveLineSlot phaseProductReserveLineSlot_injective
   phaseProductReserveLineSlot_parent phaseProductReserveLineSlot_phase
   phaseProductReserveLineSlot_not_mem_protectedCylinder
   phaseProductReserveLineSlotList phaseProductReserveLineSlotList_length
   phaseProductReserveLineSlotList_nodup
   phaseProductReserveLineSlotList_parent phaseProductReserveLineSlotList_phase
   phaseProductReserveLineSlotList_not_mem_protectedCylinder
   phaseProductReserveLineSlotPointList
   phaseProductReserveLineSlotPointList_length
   phaseProductReserveLineSlotPointList_nodup
   phaseProductReserveLineSlotPointList_parent
   phaseProductReserveLineSlotPointList_phase
   phaseProductReserveLineSlotPointList_not_mem_protectedCylinder
   phaseProductReserveLineSlotPointSet
   phaseProductReserveLineSlotPointSet_mem
   phaseProductReserveLineSlotPointSet_subsetReserveCylinder
   phaseProductReserveLineSlotPointSet_constantParentProjection
   phaseProductReserveLineSlotPointSet_constantPhaseProjection
   phaseProductReserveLineSlotPointSet_disjointFromProtectedCylinder
   phaseProductReserveLineSlotPointSet_mem_iff_exists_slot
   phaseProductReserveLineSlotPointSet_slot_unique
   phaseProductReserveLineSlotPointSet_exists_unique_slot
   phaseProductReserveLineSlotPoint_injective
   phaseProductReserveLineSlotPair_injective
   PhaseProductReserveSupportCertificate
   phaseProductReserveSupportCertificate
   phaseProductReserveSupportCertificate_supportSet
   phaseProductReserveSupportCertificate_subsetReserveCylinder
   phaseProductReserveSupportCertificate_constantParentProjection
   phaseProductReserveSupportCertificate_constantPhaseProjection
   phaseProductReserveSupportCertificate_disjointProtected
   phaseProductReserveSupportCertificate_existsUniqueSlot
   phaseProductReserveSupportCertificate_pointInjective
   phaseProductReserveSupportCertificate_pairInjective
   phaseProductReserveSupportCertificate_fixedByProtectedMap
   phaseProductReserveSupportCertificate_fixedByProtectedIter
   phaseProductReserveSupportCertificate_fixedByProtectedWordEval
   phaseProductReserveSupportCertificate_fixedByProtectedWordIter
   phaseProductReserveSupportCertificate_mapsIntoProtectedMap
   phaseProductReserveSupportCertificate_mapsIntoProtectedIter
   phaseProductReserveSupportCertificate_mapsIntoProtectedWordEval
   phaseProductReserveSupportCertificate_mapsIntoProtectedWordIter
   phaseProductProtectedCylinder_fixedByReserveSupportCertificateMap
   phaseProductProtectedCylinder_fixedByReserveSupportCertificateIter
   phaseProductProtectedCylinder_fixedByReserveSupportCertificateWordEval
   phaseProductProtectedCylinder_fixedByReserveSupportCertificateWordIter
   phaseProductProtectedCylinder_mapsIntoReserveSupportCertificateMap
   phaseProductProtectedCylinder_mapsIntoReserveSupportCertificateIter
   phaseProductProtectedCylinder_mapsIntoReserveSupportCertificateWordEval
   phaseProductProtectedCylinder_mapsIntoReserveSupportCertificateWordIter
   phaseProductReserveSupportCertificateProtectedMapsCommute
   phaseProductReserveSupportCertificateProtectedMapsCommute_symmSupports
   phaseProductReserveSupportCertificateProtectedItersCommute
   phaseProductReserveSupportCertificateProtectedItersCommute_symmSupports
   phaseProductReserveSupportCertificateProtectedWordEvalsCommute
   phaseProductReserveSupportCertificateProtectedWordEvalsCommute_symmSupports
   phaseProductReserveSupportCertificateProtectedWordItersCommute
   phaseProductReserveSupportCertificateProtectedWordItersCommute_symmSupports
   phaseProductReserveLineSlotPointWordEvalsCommute
   phaseProductReserveLineSlotPointWordEvalsCommute_symm
   phaseProductReserveLineSlotPointWordEvalIteratesCommute
   phaseProductReserveLineSlotPointWordEvalIteratesCommute_symm
   phaseProductReserveLineSlotCylinderWordEvalsCommute
   phaseProductReserveLineSlotCylinderWordEvalsCommute_symm
   phaseProductReserveLineSlotCylinderWordEvalIteratesCommute
   phaseProductReserveLineSlotCylinderWordEvalIteratesCommute_symm
   phaseProductReserveLineSlot_fixedByProtectedSupportedMap
   phaseProductReserveLineSlot_fixedByProtectedSupportedIterate
   phaseProductReserveLineSlot_fixedByProtectedSupportedWordEval
   phaseProductReserveLineSlot_fixedByProtectedSupportedWordEvalIterate
   phaseProductReserveLineSlotList_fixedByProtectedSupportedMap
   phaseProductReserveLineSlotList_fixedByProtectedSupportedIterate
   phaseProductReserveLineSlotList_fixedByProtectedSupportedWordEval
   phaseProductReserveLineSlotList_fixedByProtectedSupportedWordEvalIterate
   phaseProductReserveLineSlotPointList_fixedByProtectedSupportedMap
   phaseProductReserveLineSlotPointList_fixedByProtectedSupportedIterate
   phaseProductReserveLineSlotPointList_fixedByProtectedSupportedWordEval
   phaseProductReserveLineSlotPointList_fixedByProtectedSupportedWordEvalIterate
   phaseProductReserveLineSlotPointSet_fixedByProtectedSupportedMap
   phaseProductReserveLineSlotPointSet_fixedByProtectedSupportedIterate
   phaseProductReserveLineSlotPointSet_fixedByProtectedSupportedWordEval
   phaseProductReserveLineSlotPointSet_fixedByProtectedSupportedWordEvalIterate
   phaseProductReserveLineSlotPointSet_mapsIntoProtectedSupportedMap
   phaseProductReserveLineSlotPointSet_mapsIntoProtectedSupportedIterate
   phaseProductReserveLineSlotPointSet_mapsIntoProtectedSupportedWordEval
   phaseProductReserveLineSlotPointSet_mapsIntoProtectedSupportedWordEvalIterate
   phaseProductReserveLineSlotPointSetProtectedSupportedMapsCommute
   phaseProductReserveLineSlotPointSetProtectedSupportedMapsCommute_symmSupports
   phaseProductReserveLineSlotPointSetProtectedSupportedIteratesCommute
   phaseProductReserveLineSlotPointSetProtectedSupportedIteratesCommute_symmSupports
   phaseReserveProtectedProductCylinderSupportedMapsCommute
   phaseReserveProtectedProductCylinderSupportedMapsCommute_symmSupports
   phaseReserveProtectedProductCylinderSupportedIteratesCommute
   phaseReserveProtectedProductCylinderSupportedIteratesCommute_symmSupports
   phaseReserveProtectedProductCylinderSupportedWordEvalsCommute
   phaseReserveProtectedProductCylinderSupportedWordEvalsCommute_symmSupports
   phaseReserveProtectedProductCylinderSupportedWordEvalIteratesCommute
   phaseReserveProtectedProductCylinderSupportedWordEvalIteratesCommute_symmSupports
   phaseProductReserveLineSlotPointSetProtectedWordEvalsCommute
   phaseProductReserveLineSlotPointSetProtectedWordEvalsCommute_symmSupports
   phaseProductReserveLineSlotPointSetProtectedWordEvalIteratesCommute
   phaseProductReserveLineSlotPointSetProtectedWordEvalIteratesCommute_symmSupports
   phaseProductProtectedCylinder_fixedByReserveLineSlotPointSetSupportedMap
   phaseProductProtectedCylinder_mapsIntoReserveLineSlotPointSetSupportedMap
   phaseProductProtectedCylinder_fixedByReserveLineSlotPointSetSupportedIterate
   phaseProductProtectedCylinder_mapsIntoReserveLineSlotPointSetSupportedIterate
   phaseProductProtectedCylinder_fixedByReserveLineSlotPointSetSupportedWordEval
   phaseProductProtectedCylinder_mapsIntoReserveLineSlotPointSetSupportedWordEval
   phaseProductProtectedCylinder_fixedByReserveLineSlotPointSetSupportedWordEvalIterate
   phaseProductProtectedCylinder_mapsIntoReserveLineSlotPointSetSupportedWordEvalIterate)

end EvenV11
