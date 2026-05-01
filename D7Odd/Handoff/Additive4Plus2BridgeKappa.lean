import D7Odd.Handoff.Additive4Plus2D5Base
import D7Odd.Handoff.Additive4Plus2D3Fiber
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

@[simp] theorem baseDirectionOfSlot_bridgeFiberGlobal
    (i : Direction3) :
    baseDirectionOfSlot (bridgeFiberGlobal i) = (4 : D5Odd.Direction) := by
  fin_cases i <;> rfl

@[simp] theorem bridgeFiberDirectionOfSlot_bridgeFiberGlobal
    (i : Direction3) :
    bridgeFiberDirectionOfSlot (bridgeFiberGlobal i) = i := by
  fin_cases i <;> rfl

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

set_option linter.flexible false in
@[simp] theorem baseDirectionOfSlot_bridgeBaseOrFiberGlobal
    (phi : Direction3 → Direction3) (d : D5Odd.Direction) :
    baseDirectionOfSlot (bridgeBaseOrFiberGlobal phi d) = d := by
  fin_cases d <;>
    simp [bridgeBaseOrFiberGlobal, baseDirectionOfSlot]
  generalize hphi0 : phi 0 = i
  fin_cases i <;> rfl

set_option linter.flexible false in
@[simp] theorem bridgeFiberDirectionOfSlot_bridgeBaseOrFiberGlobal
    (phi : Direction3 → Direction3) (d : D5Odd.Direction) :
    bridgeFiberDirectionOfSlot (bridgeBaseOrFiberGlobal phi d) =
      if d = (4 : D5Odd.Direction) then phi 0 else 0 := by
  fin_cases d <;>
    simp [bridgeBaseOrFiberGlobal, bridgeFiberDirectionOfSlot]
  generalize hphi0 : phi 0 = i
  fin_cases i <;> rfl

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

def bridgeConcreteBaseDirection {m : Nat}
    (base : D5Odd.ARoot5 m) (raw : Direction) :
    D5Odd.Direction :=
  if hraw : raw.val < 5 then
    d5BaseZeroSetDirection base ⟨raw.val, hraw⟩
  else
    4

def bridgeConcreteFiberDirection {m : Nat}
    (base : D5Odd.ARoot5 m) (phi : Direction3 → Direction3)
    (raw : Direction) : Direction3 :=
  if hraw : raw.val < 5 then
    if d5BaseZeroSetDirection base ⟨raw.val, hraw⟩ = (4 : D5Odd.Direction) then
      phi 0
    else
      0
  else if raw = 5 then
    phi 1
  else
    phi 2

set_option linter.flexible false in
theorem bridgeConcreteKappa_baseDirection {m : Nat}
    (base : D5Odd.ARoot5 m) (phi : Direction3 → Direction3)
    (raw : Direction) :
    baseDirectionOfSlot (bridgeConcreteKappa base phi raw) =
      bridgeConcreteBaseDirection base raw := by
  fin_cases raw <;>
    simp [bridgeConcreteKappa, bridgeConcreteBaseDirection]

set_option linter.flexible false in
theorem bridgeConcreteKappa_fiberDirection {m : Nat}
    (base : D5Odd.ARoot5 m) (phi : Direction3 → Direction3)
    (raw : Direction) :
    bridgeFiberDirectionOfSlot (bridgeConcreteKappa base phi raw) =
      bridgeConcreteFiberDirection base phi raw := by
  fin_cases raw <;>
    simp [bridgeConcreteKappa, bridgeConcreteFiberDirection]

def bridgeConcreteBaseStepOfRaw {m : Nat}
    (raw : Direction) : D5Odd.ARoot5 m → D5Odd.ARoot5 m :=
  fun base => baseAddQ (bridgeConcreteBaseDirection base raw) base

theorem bridgeConcreteBaseStepOfRaw_bijective {m : Nat} [NeZero m]
    (hm : 5 ≤ m) (raw : Direction) :
    Function.Bijective (bridgeConcreteBaseStepOfRaw (m := m) raw) := by
  fin_cases raw
  · simpa [bridgeConcreteBaseStepOfRaw, bridgeConcreteBaseDirection,
      d5BaseZeroSetStep] using
      d5BaseZeroSetStep_bijective (m := m) hm (0 : D5Odd.Color)
  · simpa [bridgeConcreteBaseStepOfRaw, bridgeConcreteBaseDirection,
      d5BaseZeroSetStep] using
      d5BaseZeroSetStep_bijective (m := m) hm (1 : D5Odd.Color)
  · simpa [bridgeConcreteBaseStepOfRaw, bridgeConcreteBaseDirection,
      d5BaseZeroSetStep] using
      d5BaseZeroSetStep_bijective (m := m) hm (2 : D5Odd.Color)
  · simpa [bridgeConcreteBaseStepOfRaw, bridgeConcreteBaseDirection,
      d5BaseZeroSetStep] using
      d5BaseZeroSetStep_bijective (m := m) hm (3 : D5Odd.Color)
  · simpa [bridgeConcreteBaseStepOfRaw, bridgeConcreteBaseDirection,
      d5BaseZeroSetStep] using
      d5BaseZeroSetStep_bijective (m := m) hm (4 : D5Odd.Color)
  · simp [bridgeConcreteBaseStepOfRaw, bridgeConcreteBaseDirection,
      baseAddQ]
  · simp [bridgeConcreteBaseStepOfRaw, bridgeConcreteBaseDirection,
      baseAddQ]

def bridgeConcreteBaseStep {m : Nat}
    (row : Color → ZMod m → Direction)
    (t : ZMod m) (c : Color) :
    D5Odd.ARoot5 m → D5Odd.ARoot5 m :=
  bridgeConcreteBaseStepOfRaw (row c t)

theorem bridgeConcreteBaseStep_bijective {m : Nat} [NeZero m]
    (hm : 5 ≤ m) (row : Color → ZMod m → Direction) :
    ∀ t c, Function.Bijective (bridgeConcreteBaseStep (m := m) row t c) := by
  intro t c
  exact bridgeConcreteBaseStepOfRaw_bijective hm (row c t)

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

def bridgeD3Phi {m : Nat}
    (fiberLayer : ZMod m → D5Odd.ARoot5 m → ZMod m)
    (perm : ZMod m → D5Odd.ARoot5 m → Direction3 → Direction3) :
    ZMod m → ProductRoot m → Direction3 → Direction3 :=
  fun t bf =>
    d3OddPermutedDirection (fiberLayer t bf.1) (perm t bf.1) bf.2

theorem bridgeD3Phi_bijective_of_two_le {m : Nat}
    (hm : 2 ≤ m)
    (fiberLayer : ZMod m → D5Odd.ARoot5 m → ZMod m)
    (perm : ZMod m → D5Odd.ARoot5 m → Direction3 → Direction3)
    (hperm : ∀ t base, Function.Bijective (perm t base)) :
    ∀ t bf, Function.Bijective (bridgeD3Phi fiberLayer perm t bf) := by
  intro t bf
  exact d3OddPermutedDirection_rowLatin_of_two_le hm
    (fiberLayer t bf.1) (perm t bf.1) (hperm t bf.1) bf.2

def bridgeD3FiberStep {m : Nat}
    (fiberLayer : ZMod m → D5Odd.ARoot5 m → ZMod m)
    (perm : ZMod m → D5Odd.ARoot5 m → Direction3 → Direction3)
    (t : ZMod m) (base : D5Odd.ARoot5 m) (slot : Direction3) :
    ARoot3 m → ARoot3 m :=
  d3OddPermutedStep (fiberLayer t base) (perm t base) slot

theorem bridgeD3FiberStep_bijective_of_two_le {m : Nat}
    (hm : 2 ≤ m)
    (fiberLayer : ZMod m → D5Odd.ARoot5 m → ZMod m)
    (perm : ZMod m → D5Odd.ARoot5 m → Direction3 → Direction3) :
    ∀ t base slot,
      Function.Bijective (bridgeD3FiberStep fiberLayer perm t base slot) := by
  intro t base slot
  exact d3OddPermutedStep_bijective_of_two_le hm
    (fiberLayer t base) (perm t base) slot

def bridgeConcreteFiberStepOfRaw {m : Nat}
    (fiberLayer : ZMod m → D5Odd.ARoot5 m → ZMod m)
    (perm : ZMod m → D5Odd.ARoot5 m → Direction3 → Direction3)
    (t : ZMod m) (base : D5Odd.ARoot5 m) (raw : Direction) :
    ARoot3 m → ARoot3 m :=
  fun fiber =>
    fiberAddQ
      (bridgeConcreteFiberDirection base
        (bridgeD3Phi fiberLayer perm t (base, fiber)) raw)
      fiber

theorem bridgeConcreteFiberStepOfRaw_bijective_of_two_le {m : Nat}
    (hm : 2 ≤ m)
    (fiberLayer : ZMod m → D5Odd.ARoot5 m → ZMod m)
    (perm : ZMod m → D5Odd.ARoot5 m → Direction3 → Direction3) :
    ∀ t base raw,
      Function.Bijective
        (bridgeConcreteFiberStepOfRaw fiberLayer perm t base raw) := by
  haveI : NeZero m := ⟨by omega⟩
  intro t base raw
  fin_cases raw
  · by_cases hroot :
      d5BaseZeroSetDirection base (0 : D5Odd.Color) =
        (4 : D5Odd.Direction)
    · simpa [bridgeConcreteFiberStepOfRaw, bridgeConcreteFiberDirection,
        bridgeD3Phi, d3OddPermutedStep, d3OddPermutedDirection,
        d3OddStep, hroot] using
        d3OddPermutedStep_bijective_of_two_le hm
          (fiberLayer t base) (perm t base) (0 : Direction3)
    · simpa [bridgeConcreteFiberStepOfRaw, bridgeConcreteFiberDirection,
        hroot] using fiberAddQ_bijective (m := m) (0 : Direction3)
  · by_cases hroot :
      d5BaseZeroSetDirection base (1 : D5Odd.Color) =
        (4 : D5Odd.Direction)
    · simpa [bridgeConcreteFiberStepOfRaw, bridgeConcreteFiberDirection,
        bridgeD3Phi, d3OddPermutedStep, d3OddPermutedDirection,
        d3OddStep, hroot] using
        d3OddPermutedStep_bijective_of_two_le hm
          (fiberLayer t base) (perm t base) (0 : Direction3)
    · simpa [bridgeConcreteFiberStepOfRaw, bridgeConcreteFiberDirection,
        hroot] using fiberAddQ_bijective (m := m) (0 : Direction3)
  · by_cases hroot :
      d5BaseZeroSetDirection base (2 : D5Odd.Color) =
        (4 : D5Odd.Direction)
    · simpa [bridgeConcreteFiberStepOfRaw, bridgeConcreteFiberDirection,
        bridgeD3Phi, d3OddPermutedStep, d3OddPermutedDirection,
        d3OddStep, hroot] using
        d3OddPermutedStep_bijective_of_two_le hm
          (fiberLayer t base) (perm t base) (0 : Direction3)
    · simpa [bridgeConcreteFiberStepOfRaw, bridgeConcreteFiberDirection,
        hroot] using fiberAddQ_bijective (m := m) (0 : Direction3)
  · by_cases hroot :
      d5BaseZeroSetDirection base (3 : D5Odd.Color) =
        (4 : D5Odd.Direction)
    · simpa [bridgeConcreteFiberStepOfRaw, bridgeConcreteFiberDirection,
        bridgeD3Phi, d3OddPermutedStep, d3OddPermutedDirection,
        d3OddStep, hroot] using
        d3OddPermutedStep_bijective_of_two_le hm
          (fiberLayer t base) (perm t base) (0 : Direction3)
    · simpa [bridgeConcreteFiberStepOfRaw, bridgeConcreteFiberDirection,
        hroot] using fiberAddQ_bijective (m := m) (0 : Direction3)
  · by_cases hroot :
      d5BaseZeroSetDirection base (4 : D5Odd.Color) =
        (4 : D5Odd.Direction)
    · simpa [bridgeConcreteFiberStepOfRaw, bridgeConcreteFiberDirection,
        bridgeD3Phi, d3OddPermutedStep, d3OddPermutedDirection,
        d3OddStep, hroot] using
        d3OddPermutedStep_bijective_of_two_le hm
          (fiberLayer t base) (perm t base) (0 : Direction3)
    · simpa [bridgeConcreteFiberStepOfRaw, bridgeConcreteFiberDirection,
        hroot] using fiberAddQ_bijective (m := m) (0 : Direction3)
  · simpa [bridgeConcreteFiberStepOfRaw, bridgeConcreteFiberDirection,
      bridgeD3Phi, d3OddPermutedStep, d3OddPermutedDirection,
      d3OddStep] using
      d3OddPermutedStep_bijective_of_two_le hm
        (fiberLayer t base) (perm t base) (1 : Direction3)
  · simpa [bridgeConcreteFiberStepOfRaw, bridgeConcreteFiberDirection,
      bridgeD3Phi, d3OddPermutedStep, d3OddPermutedDirection,
      d3OddStep] using
      d3OddPermutedStep_bijective_of_two_le hm
        (fiberLayer t base) (perm t base) (2 : Direction3)

def bridgeConcreteFiberStep {m : Nat}
    (row : Color → ZMod m → Direction)
    (fiberLayer : ZMod m → D5Odd.ARoot5 m → ZMod m)
    (perm : ZMod m → D5Odd.ARoot5 m → Direction3 → Direction3)
    (t : ZMod m) (c : Color) (base : D5Odd.ARoot5 m) :
    ARoot3 m → ARoot3 m :=
  bridgeConcreteFiberStepOfRaw fiberLayer perm t base (row c t)

theorem bridgeConcreteFiberStep_bijective_of_two_le {m : Nat}
    (hm : 2 ≤ m) (row : Color → ZMod m → Direction)
    (fiberLayer : ZMod m → D5Odd.ARoot5 m → ZMod m)
    (perm : ZMod m → D5Odd.ARoot5 m → Direction3 → Direction3) :
    ∀ t c base,
      Function.Bijective
        (bridgeConcreteFiberStep row fiberLayer perm t c base) := by
  intro t c base
  exact bridgeConcreteFiberStepOfRaw_bijective_of_two_le hm
    fiberLayer perm t base (row c t)

theorem bridgeConcreteSchedule_layerMap_eq_skewProductMap {m : Nat}
    (row : Color → ZMod m → Direction)
    (fiberLayer : ZMod m → D5Odd.ARoot5 m → ZMod m)
    (perm : ZMod m → D5Odd.ARoot5 m → Direction3 → Direction3)
    (t : ZMod m) (c : Color) :
    (bridgeConcreteSchedule row (bridgeD3Phi fiberLayer perm)).layerMap t c =
      Shared.skewProductMap
        (bridgeConcreteBaseStep row t c)
        (bridgeConcreteFiberStep row fiberLayer perm t c) := by
  exact (bridgeConcreteSchedule row (bridgeD3Phi fiberLayer perm))
    |>.layerMap_eq_skewProductMap_of_components
      (bridgeConcreteBaseStep row)
      (bridgeConcreteFiberStep row fiberLayer perm)
      (by
        intro t c base fiber
        simp [bridgeConcreteSchedule, bridgeConcreteStateKappa,
          bridgeConcreteBaseStep, bridgeConcreteBaseStepOfRaw,
          bridgeConcreteKappa_baseDirection])
      (by
        intro t c base fiber
        simp [bridgeConcreteSchedule, bridgeConcreteStateKappa,
          bridgeConcreteFiberStep, bridgeConcreteFiberStepOfRaw,
          bridgeConcreteKappa_fiberDirection])
      t c

theorem bridgeConcreteSchedule_layerBijective {m : Nat} [NeZero m]
    (hm : 5 ≤ m) (row : Color → ZMod m → Direction)
    (fiberLayer : ZMod m → D5Odd.ARoot5 m → ZMod m)
    (perm : ZMod m → D5Odd.ARoot5 m → Direction3 → Direction3) :
    (bridgeConcreteSchedule row (bridgeD3Phi fiberLayer perm)).layerBijective := by
  intro t c
  rw [bridgeConcreteSchedule_layerMap_eq_skewProductMap
    row fiberLayer perm t c]
  exact Shared.skewProductMap_bijective
    (bridgeConcreteBaseStep row t c)
    (bridgeConcreteFiberStep row fiberLayer perm t c)
    (bridgeConcreteBaseStep_bijective hm row t c)
    (bridgeConcreteFiberStep_bijective_of_two_le (by omega)
      row fiberLayer perm t c)

end Additive4Plus2
end Handoff
end D7Odd
