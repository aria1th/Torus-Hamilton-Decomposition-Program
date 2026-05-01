import D7Odd.Handoff.Additive4Plus2D5Base
import D7Odd.Handoff.Additive4Plus2BridgeChart

namespace D7Odd
namespace Handoff
namespace Additive4Plus2

def bridgeFiberGlobal (i : Direction3) : Direction :=
  ⟨i.val + 4, by omega⟩

@[simp] theorem bridgeFiberGlobal_zero :
    bridgeFiberGlobal 0 = (4 : Direction) := rfl

@[simp] theorem bridgeFiberGlobal_one :
    bridgeFiberGlobal 1 = (5 : Direction) := rfl

@[simp] theorem bridgeFiberGlobal_two :
    bridgeFiberGlobal 2 = (6 : Direction) := rfl

def bridgeRawBaseSlot (slot : D5Odd.Color) : Direction :=
  ⟨slot.val, by omega⟩

def bridgeBaseOrFiberGlobal
    (phi : Direction3 → Direction3) (d : D5Odd.Direction) :
    Direction :=
  match d.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | _ => bridgeFiberGlobal (phi 0)

def bridgeConcreteKappa {m : Nat}
    (base : D5Odd.ARoot5 m) (phi : Direction3 → Direction3) :
    Direction → Direction :=
  fun raw =>
    if hraw : raw.val < 5 then
      bridgeBaseOrFiberGlobal phi
        (d5BaseZeroSetDirection base ⟨raw.val, hraw⟩)
    else if raw = 5 then
      bridgeFiberGlobal (phi 1)
    else
      bridgeFiberGlobal (phi 2)

theorem bridgeConcreteKappa_surjective {m : Nat}
    (base : D5Odd.ARoot5 m) (phi : Direction3 → Direction3)
    (hphi : Function.Bijective phi) :
    Function.Surjective (bridgeConcreteKappa base phi) := by
  intro y
  fin_cases y
  · rcases (d5BaseZeroSetDirection_rowLatin base).2
      (0 : D5Odd.Direction) with ⟨slot, hslot⟩
    refine ⟨bridgeRawBaseSlot slot, ?_⟩
    simp [bridgeConcreteKappa, bridgeRawBaseSlot, bridgeBaseOrFiberGlobal,
      hslot]
  · rcases (d5BaseZeroSetDirection_rowLatin base).2
      (1 : D5Odd.Direction) with ⟨slot, hslot⟩
    refine ⟨bridgeRawBaseSlot slot, ?_⟩
    simp [bridgeConcreteKappa, bridgeRawBaseSlot, bridgeBaseOrFiberGlobal,
      hslot]
  · rcases (d5BaseZeroSetDirection_rowLatin base).2
      (2 : D5Odd.Direction) with ⟨slot, hslot⟩
    refine ⟨bridgeRawBaseSlot slot, ?_⟩
    simp [bridgeConcreteKappa, bridgeRawBaseSlot, bridgeBaseOrFiberGlobal,
      hslot]
  · rcases (d5BaseZeroSetDirection_rowLatin base).2
      (3 : D5Odd.Direction) with ⟨slot, hslot⟩
    refine ⟨bridgeRawBaseSlot slot, ?_⟩
    simp [bridgeConcreteKappa, bridgeRawBaseSlot, bridgeBaseOrFiberGlobal,
      hslot]
  · rcases hphi.2 (0 : Direction3) with ⟨slot, hslot⟩
    fin_cases slot
    · rcases (d5BaseZeroSetDirection_rowLatin base).2
        (4 : D5Odd.Direction) with ⟨baseSlot, hbaseSlot⟩
      have hphi0 : phi 0 = (0 : Direction3) := by simpa using hslot
      refine ⟨bridgeRawBaseSlot baseSlot, ?_⟩
      simp [bridgeConcreteKappa, bridgeRawBaseSlot, bridgeBaseOrFiberGlobal,
        hbaseSlot, hphi0]
    · refine ⟨(5 : Direction), ?_⟩
      have hphi1 : phi 1 = (0 : Direction3) := by simpa using hslot
      simp [bridgeConcreteKappa, hphi1]
    · refine ⟨(6 : Direction), ?_⟩
      have hphi2 : phi 2 = (0 : Direction3) := by simpa using hslot
      simp [bridgeConcreteKappa, hphi2]
  · rcases hphi.2 (1 : Direction3) with ⟨slot, hslot⟩
    fin_cases slot
    · rcases (d5BaseZeroSetDirection_rowLatin base).2
        (4 : D5Odd.Direction) with ⟨baseSlot, hbaseSlot⟩
      have hphi0 : phi 0 = (1 : Direction3) := by simpa using hslot
      refine ⟨bridgeRawBaseSlot baseSlot, ?_⟩
      simp [bridgeConcreteKappa, bridgeRawBaseSlot, bridgeBaseOrFiberGlobal,
        hbaseSlot, hphi0]
    · refine ⟨(5 : Direction), ?_⟩
      have hphi1 : phi 1 = (1 : Direction3) := by simpa using hslot
      simp [bridgeConcreteKappa, hphi1]
    · refine ⟨(6 : Direction), ?_⟩
      have hphi2 : phi 2 = (1 : Direction3) := by simpa using hslot
      simp [bridgeConcreteKappa, hphi2]
  · rcases hphi.2 (2 : Direction3) with ⟨slot, hslot⟩
    fin_cases slot
    · rcases (d5BaseZeroSetDirection_rowLatin base).2
        (4 : D5Odd.Direction) with ⟨baseSlot, hbaseSlot⟩
      have hphi0 : phi 0 = (2 : Direction3) := by simpa using hslot
      refine ⟨bridgeRawBaseSlot baseSlot, ?_⟩
      simp [bridgeConcreteKappa, bridgeRawBaseSlot, bridgeBaseOrFiberGlobal,
        hbaseSlot, hphi0]
    · refine ⟨(5 : Direction), ?_⟩
      have hphi1 : phi 1 = (2 : Direction3) := by simpa using hslot
      simp [bridgeConcreteKappa, hphi1]
    · refine ⟨(6 : Direction), ?_⟩
      have hphi2 : phi 2 = (2 : Direction3) := by simpa using hslot
      simp [bridgeConcreteKappa, hphi2]

theorem bridgeConcreteKappa_bijective {m : Nat}
    (base : D5Odd.ARoot5 m) (phi : Direction3 → Direction3)
    (hphi : Function.Bijective phi) :
    Function.Bijective (bridgeConcreteKappa base phi) :=
  (Fintype.bijective_iff_surjective_and_card _).2
    ⟨bridgeConcreteKappa_surjective base phi hphi, rfl⟩

def bridgeConcreteStateKappa {m : Nat}
    (phi : ZMod m → ProductRoot m → Direction3 → Direction3) :
    ZMod m → ProductRoot m → Direction → Direction :=
  fun t bf => bridgeConcreteKappa bf.1 (phi t bf)

theorem bridgeConcreteStateKappa_bijective {m : Nat}
    (phi : ZMod m → ProductRoot m → Direction3 → Direction3)
    (hphi : ∀ t bf, Function.Bijective (phi t bf)) :
    ∀ t bf, Function.Bijective (bridgeConcreteStateKappa phi t bf) := by
  intro t bf
  exact bridgeConcreteKappa_bijective bf.1 (phi t bf) (hphi t bf)

def bridgeConcreteRawDir {m : Nat}
    (row : Color → ZMod m → Direction) :
    ZMod m → ProductRoot m → Color → Direction :=
  fun t _ c => row c t

def bridgeConcreteSchedule {m : Nat}
    (row : Color → ZMod m → Direction)
    (phi : ZMod m → ProductRoot m → Direction3 → Direction3) :
    BridgeProductRootSchedule m where
  dir := fun t bf c => bridgeConcreteStateKappa phi t bf (row c t)

theorem bridgeConcreteRawDir_bijective {m : Nat}
    (row : Color → ZMod m → Direction)
    (hrow : ∀ t, Function.Bijective fun c : Color => row c t) :
    ∀ t bf, Function.Bijective (bridgeConcreteRawDir row t bf) := by
  intro t bf
  simpa [bridgeConcreteRawDir] using hrow t

theorem bridgeConcreteSchedule_rowLatin {m : Nat}
    (row : Color → ZMod m → Direction)
    (phi : ZMod m → ProductRoot m → Direction3 → Direction3)
    (hrow : ∀ t, Function.Bijective fun c : Color => row c t)
    (hphi : ∀ t bf, Function.Bijective (phi t bf)) :
    (bridgeConcreteSchedule row phi).rowLatin := by
  refine (bridgeConcreteSchedule row phi).rowLatin_of_stateDirectionPermutation
    (bridgeConcreteRawDir row) (bridgeConcreteStateKappa phi) ?_ ?_ ?_
  · exact bridgeConcreteRawDir_bijective row hrow
  · exact bridgeConcreteStateKappa_bijective phi hphi
  · intro t bf c
    rfl

end Additive4Plus2
end Handoff
end D7Odd
