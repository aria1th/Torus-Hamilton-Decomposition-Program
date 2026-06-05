import EvenV11.UnitCarry

namespace EvenV11
namespace EndpointCompletion

def cyclicCompletionRow {n : Nat} (shift : ZMod n) :
    ZMod n → ZMod n :=
  fun k => k + shift

def cyclicCompletionTail {n : Nat} (target shift : ZMod n) : ZMod n :=
  target - shift

def rowIncidence {Coord : Type*} {m : Nat}
    (coordRead : Coord → ZMod m) (row : Coord → Coord) (tail : Coord) :
    ZMod m :=
  coordRead (row tail) - coordRead tail

def targetIndicatorCoordRead {n m : Nat} (target : ZMod n) :
    ZMod n → ZMod m :=
  fun coord => if coord = target then 1 else 0

def completionCarry {Base Coord : Type*} {m : Nat}
    (coordRead : Coord → ZMod m) (row : Coord → Coord)
    (tail : Base → Coord) : Base → ZMod m :=
  fun x => rowIncidence coordRead row (tail x)

structure CompletionCarryCertificate
    (Base Coord : Type*) (m : Nat) where
  row : Coord → Coord
  coordRead : Coord → ZMod m
  tail : Base → Coord
  crossing : Base
  epsilon : ZMod m
  crossingIncidence :
    rowIncidence coordRead row (tail crossing) = epsilon
  offIncidence :
    ∀ x : Base, x ≠ crossing →
      rowIncidence coordRead row (tail x) = 0

theorem rowIncidence_eq_zero_of_eq
    {Coord : Type*} {m : Nat}
    {coordRead : Coord → ZMod m} {row : Coord → Coord} {tail : Coord}
    (hread : coordRead (row tail) = coordRead tail) :
    rowIncidence coordRead row tail = 0 := by
  simp [rowIncidence, hread]

theorem targetIndicatorCoordRead_target {n m : Nat}
    (target : ZMod n) :
    targetIndicatorCoordRead (m := m) target target = 1 := by
  simp [targetIndicatorCoordRead]

theorem targetIndicatorCoordRead_of_ne {n m : Nat}
    (target coord : ZMod n) (hcoord : coord ≠ target) :
    targetIndicatorCoordRead (m := m) target coord = 0 := by
  simp [targetIndicatorCoordRead, hcoord]

theorem carry_eq_pointCarry_of_crossing_and_off
    {Base : Type*} [DecidableEq Base] {m : Nat}
    (carry : Base → ZMod m) (crossing : Base) (epsilon : ZMod m)
    (hcross : carry crossing = epsilon)
    (hoff : ∀ x : Base, x ≠ crossing → carry x = 0) :
    carry = pointCarry crossing epsilon := by
  funext x
  by_cases hx : x = crossing
  · subst x
    simp [pointCarry, hcross]
  · simp [pointCarry, hx, hoff x hx]

theorem completionCarryCertificate_eq_pointCarry
    {Base Coord : Type*} [DecidableEq Base] {m : Nat}
    (C : CompletionCarryCertificate Base Coord m) :
    completionCarry C.coordRead C.row C.tail =
      pointCarry C.crossing C.epsilon :=
  carry_eq_pointCarry_of_crossing_and_off
    (completionCarry C.coordRead C.row C.tail) C.crossing C.epsilon
    (by simpa [completionCarry] using C.crossingIncidence)
    (by
      intro x hx
      simpa [completionCarry] using C.offIncidence x hx)

theorem completionCarryCertificate_singleCycle
    {Base Coord : Type*} [Finite Base]
    {N m : Nat} [NeZero N] [NeZero m]
    (baseStep : Base → Base) (rank : Base ≃ ZMod N)
    (base : Base) (C : CompletionCarryCertificate Base Coord m)
    (hstep : ∀ x : Base, rank (baseStep x) = rank x + 1)
    (hepsilon : IsUnit C.epsilon) :
    Shared.IsSingleCycleMap
      (additiveSkewMap baseStep
        (completionCarry C.coordRead C.row C.tail)) := by
  letI : DecidableEq Base := Classical.decEq Base
  rw [completionCarryCertificate_eq_pointCarry C]
  exact pointCarrySingleCycle baseStep rank base C.crossing C.epsilon
    hstep hepsilon

theorem cyclicCompletionRow_bijective {n : Nat} (shift : ZMod n) :
    Function.Bijective (cyclicCompletionRow shift) := by
  constructor
  · intro x y hxy
    exact add_right_cancel hxy
  · intro y
    exact ⟨y - shift, by simp [cyclicCompletionRow]⟩

theorem cyclicCompletionRow_tail {n : Nat}
    (target shift : ZMod n) :
    cyclicCompletionRow shift (cyclicCompletionTail target shift) =
      target := by
  simp [cyclicCompletionRow, cyclicCompletionTail]

theorem cyclicCompletionTail_unique {n : Nat}
    {target shift k : ZMod n}
    (hk : cyclicCompletionRow shift k = target) :
    k = cyclicCompletionTail target shift := by
  calc
    k = cyclicCompletionRow shift k - shift := by
      simp [cyclicCompletionRow]
    _ = target - shift := by rw [hk]
    _ = cyclicCompletionTail target shift := rfl

theorem cyclicCompletionRow_tail_iff {n : Nat}
    {target shift k : ZMod n} :
    cyclicCompletionRow shift k = target ↔
      k = cyclicCompletionTail target shift := by
  constructor
  · exact cyclicCompletionTail_unique
  · intro hk
    rw [hk]
    exact cyclicCompletionRow_tail target shift

theorem cyclicCompletionRow_moved_of_shift_ne_zero {n : Nat}
    {shift k : ZMod n} (hshift : shift ≠ 0) :
    cyclicCompletionRow shift k ≠ k := by
  intro hfix
  have hcancel : k + shift = k + 0 := by
    simpa [cyclicCompletionRow] using hfix
  exact hshift (add_left_cancel hcancel)

theorem cyclicCompletionTail_ne_target_of_shift_ne_zero {n : Nat}
    {target shift : ZMod n} (hshift : shift ≠ 0) :
    cyclicCompletionTail target shift ≠ target := by
  intro htail
  have hrow := cyclicCompletionRow_tail target shift
  rw [htail] at hrow
  exact cyclicCompletionRow_moved_of_shift_ne_zero hshift hrow

theorem targetIndicatorCoordRead_cyclicCompletionTail {n m : Nat}
    {target shift : ZMod n} (hshift : shift ≠ 0) :
    targetIndicatorCoordRead (m := m) target
      (cyclicCompletionTail target shift) = 0 :=
  targetIndicatorCoordRead_of_ne target
    (cyclicCompletionTail target shift)
    (cyclicCompletionTail_ne_target_of_shift_ne_zero hshift)

theorem cyclicCompletionRowIncidence_tail
    {n m : Nat} (target shift : ZMod n)
    (coordRead : ZMod n → ZMod m) {epsilon : ZMod m}
    (htarget : coordRead target = epsilon)
    (htail :
      coordRead (cyclicCompletionTail target shift) = 0) :
    rowIncidence coordRead (cyclicCompletionRow shift)
      (cyclicCompletionTail target shift) = epsilon := by
  rw [rowIncidence, cyclicCompletionRow_tail target shift,
    htarget, htail]
  simp

theorem cyclicCompletionRowIncidence_eq_zero_of_read_eq
    {n m : Nat} (shift : ZMod n) (coordRead : ZMod n → ZMod m)
    {tail : ZMod n}
    (hread :
      coordRead (cyclicCompletionRow shift tail) = coordRead tail) :
    rowIncidence coordRead (cyclicCompletionRow shift) tail = 0 :=
  rowIncidence_eq_zero_of_eq hread

theorem cyclicCompletionRowIncidence_targetIndicator_tail
    {n m : Nat} {target shift : ZMod n}
    (hshift : shift ≠ 0) :
    rowIncidence (targetIndicatorCoordRead (m := m) target)
      (cyclicCompletionRow shift)
      (cyclicCompletionTail target shift) = 1 :=
  cyclicCompletionRowIncidence_tail target shift
    (targetIndicatorCoordRead target)
    (targetIndicatorCoordRead_target target)
    (targetIndicatorCoordRead_cyclicCompletionTail hshift)

theorem cyclicCompletionRowIncidence_targetIndicator_eq_zero_of_ne_target
    {n m : Nat} (target shift tail : ZMod n)
    (htail : tail ≠ target)
    (hrow : cyclicCompletionRow shift tail ≠ target) :
    rowIncidence (targetIndicatorCoordRead (m := m) target)
      (cyclicCompletionRow shift) tail = 0 :=
  rowIncidence_eq_zero_of_eq
    (by
      rw [targetIndicatorCoordRead_of_ne target
          (cyclicCompletionRow shift tail) hrow,
        targetIndicatorCoordRead_of_ne target tail htail])

def completionTargetAvoids {n : Nat}
    (target shift tail : ZMod n) : Prop :=
  tail ≠ target ∧ cyclicCompletionRow shift tail ≠ target

theorem completionTargetAvoids_tail_ne_target
    {n : Nat} {target shift tail : ZMod n}
    (havoid : completionTargetAvoids target shift tail) :
    tail ≠ target :=
  havoid.1

theorem completionTargetAvoids_row_ne_target
    {n : Nat} {target shift tail : ZMod n}
    (havoid : completionTargetAvoids target shift tail) :
    cyclicCompletionRow shift tail ≠ target :=
  havoid.2

theorem cyclicCompletionRowIncidence_targetIndicator_eq_zero_of_avoids
    {n m : Nat} {target shift tail : ZMod n}
    (havoid : completionTargetAvoids target shift tail) :
    rowIncidence (targetIndicatorCoordRead (m := m) target)
      (cyclicCompletionRow shift) tail = 0 :=
  cyclicCompletionRowIncidence_targetIndicator_eq_zero_of_ne_target
    target shift tail
    (completionTargetAvoids_tail_ne_target havoid)
    (completionTargetAvoids_row_ne_target havoid)

theorem cyclicCompletionCarry_eq_pointCarry
    {Base : Type*} [DecidableEq Base] {n m : Nat}
    (target shift : ZMod n) (coordRead : ZMod n → ZMod m)
    (tail : Base → ZMod n) (crossing : Base) (epsilon : ZMod m)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (htarget : coordRead target = epsilon)
    (htail :
      coordRead (cyclicCompletionTail target shift) = 0)
    (hoff : ∀ x : Base, x ≠ crossing →
      rowIncidence coordRead (cyclicCompletionRow shift) (tail x) = 0) :
    completionCarry coordRead (cyclicCompletionRow shift) tail =
      pointCarry crossing epsilon :=
  carry_eq_pointCarry_of_crossing_and_off
    (completionCarry coordRead (cyclicCompletionRow shift) tail)
    crossing epsilon
    (by
      simpa [completionCarry, hcrossTail] using
        cyclicCompletionRowIncidence_tail target shift coordRead
          htarget htail)
    (by
      intro x hx
      simpa [completionCarry] using hoff x hx)

theorem cyclicCompletionCarrySingleCycle
    {Base : Type*} [Finite Base]
    {n N m : Nat} [NeZero N] [NeZero m]
    (baseStep : Base → Base) (rank : Base ≃ ZMod N)
    (base crossing : Base)
    (target shift : ZMod n) (coordRead : ZMod n → ZMod m)
    (tail : Base → ZMod n) (epsilon : ZMod m)
    (hstep : ∀ x : Base, rank (baseStep x) = rank x + 1)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (htarget : coordRead target = epsilon)
    (htail :
      coordRead (cyclicCompletionTail target shift) = 0)
    (hoff : ∀ x : Base, x ≠ crossing →
      rowIncidence coordRead (cyclicCompletionRow shift) (tail x) = 0)
    (hepsilon : IsUnit epsilon) :
    Shared.IsSingleCycleMap
      (additiveSkewMap baseStep
        (completionCarry coordRead (cyclicCompletionRow shift) tail)) := by
  letI : DecidableEq Base := Classical.decEq Base
  rw [cyclicCompletionCarry_eq_pointCarry
    target shift coordRead tail crossing epsilon
    hcrossTail htarget htail hoff]
  exact pointCarrySingleCycle baseStep rank base crossing epsilon
    hstep hepsilon

def finCompletionBaseStep {N : Nat} [NeZero N] : Fin N → Fin N :=
  fun i => i + 1

theorem finCompletionBaseStep_rank {N : Nat} [NeZero N]
    (i : Fin N) :
    (ZMod.finEquiv N).toEquiv (finCompletionBaseStep i) =
      (ZMod.finEquiv N).toEquiv i + 1 := by
  simp [finCompletionBaseStep]

structure FinCompletionCarryCertificate
    (N n m : Nat) where
  target : ZMod n
  shift : ZMod n
  coordRead : ZMod n → ZMod m
  tail : Fin N → ZMod n
  crossing : Fin N
  epsilon : ZMod m
  crossingTail :
    tail crossing = cyclicCompletionTail target shift
  targetRead : coordRead target = epsilon
  tailRead : coordRead (cyclicCompletionTail target shift) = 0
  offIncidence :
    ∀ i : Fin N, i ≠ crossing →
      rowIncidence coordRead (cyclicCompletionRow shift) (tail i) = 0

def finCompletionCarryCertificateOfTargetIndicator
    {N n m : Nat} (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (hoffTail :
      ∀ i : Fin N, i ≠ crossing → tail i ≠ target)
    (hoffRow :
      ∀ i : Fin N, i ≠ crossing →
        cyclicCompletionRow shift (tail i) ≠ target) :
    FinCompletionCarryCertificate N n m where
  target := target
  shift := shift
  coordRead := targetIndicatorCoordRead target
  tail := tail
  crossing := crossing
  epsilon := 1
  crossingTail := hcrossTail
  targetRead := targetIndicatorCoordRead_target target
  tailRead := targetIndicatorCoordRead_cyclicCompletionTail hshift
  offIncidence := by
    intro i hi
    exact cyclicCompletionRowIncidence_targetIndicator_eq_zero_of_ne_target
      target shift (tail i) (hoffTail i hi) (hoffRow i hi)

def finCompletionTargetAvoids {N n : Nat}
    (target shift : ZMod n) (tail : Fin N → ZMod n)
    (crossing : Fin N) : Prop :=
  ∀ i : Fin N, i ≠ crossing →
    completionTargetAvoids target shift (tail i)

def finCompletionTailAvoidsTarget {N n : Nat}
    (target : ZMod n) (tail : Fin N → ZMod n) : Prop :=
  ∀ i : Fin N, tail i ≠ target

def finCompletionOffCrossingTailAvoidsTarget {N n : Nat}
    (target : ZMod n) (tail : Fin N → ZMod n)
    (crossing : Fin N) : Prop :=
  ∀ i : Fin N, i ≠ crossing → tail i ≠ target

theorem finCompletionTailAvoidsTarget_of_offCrossing
    {N n : Nat} {target shift : ZMod n}
    {tail : Fin N → ZMod n} {crossing : Fin N}
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (hoffTail :
      finCompletionOffCrossingTailAvoidsTarget target tail crossing) :
    finCompletionTailAvoidsTarget target tail := by
  intro i
  by_cases hi : i = crossing
  · rw [hi, hcrossTail]
    exact cyclicCompletionTail_ne_target_of_shift_ne_zero hshift
  · exact hoffTail i hi

def finCompletionRowTargetHitsOnlyAtCrossing {N n : Nat}
    (target shift : ZMod n) (tail : Fin N → ZMod n)
    (crossing : Fin N) : Prop :=
  ∀ i : Fin N, cyclicCompletionRow shift (tail i) = target →
    i = crossing

def finCompletionTargetProfile {N n : Nat}
    (target shift : ZMod n) (tail : Fin N → ZMod n)
    (crossing : Fin N) : Prop :=
  finCompletionTailAvoidsTarget target tail ∧
    finCompletionRowTargetHitsOnlyAtCrossing target shift tail crossing

theorem finCompletionRowTargetHitsOnlyAtCrossing_of_injective_tail
    {N n : Nat} {target shift : ZMod n}
    {tail : Fin N → ZMod n} {crossing : Fin N}
    (htailInj : Function.Injective tail)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift) :
    finCompletionRowTargetHitsOnlyAtCrossing
      target shift tail crossing := by
  intro i hrow
  apply htailInj
  exact (cyclicCompletionTail_unique hrow).trans hcrossTail.symm

theorem finCompletionTargetProfile_of_injective_tail
    {N n : Nat} {target shift : ZMod n}
    {tail : Fin N → ZMod n} {crossing : Fin N}
    (htailAvoids : finCompletionTailAvoidsTarget target tail)
    (htailInj : Function.Injective tail)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift) :
    finCompletionTargetProfile target shift tail crossing :=
  ⟨htailAvoids,
    finCompletionRowTargetHitsOnlyAtCrossing_of_injective_tail
      htailInj hcrossTail⟩

theorem finCompletionTargetAvoids_of_injective_tail
    {N n : Nat} {target shift : ZMod n}
    {tail : Fin N → ZMod n} {crossing : Fin N}
    (htailAvoids : finCompletionTailAvoidsTarget target tail)
    (htailInj : Function.Injective tail)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift) :
    finCompletionTargetAvoids target shift tail crossing := by
  intro i hi
  exact ⟨htailAvoids i, by
    intro hrow
    exact hi
      (finCompletionRowTargetHitsOnlyAtCrossing_of_injective_tail
        htailInj hcrossTail i hrow)⟩

theorem finCompletionTargetAvoids_of_targetProfile {N n : Nat}
    {target shift : ZMod n} {tail : Fin N → ZMod n}
    {crossing : Fin N}
    (hprofile :
      finCompletionTargetProfile target shift tail crossing) :
    finCompletionTargetAvoids target shift tail crossing := by
  intro i hi
  exact ⟨hprofile.1 i, by
    intro hrow
    exact hi (hprofile.2 i hrow)⟩

def finCompletionCarryCertificateOfTargetAvoidance
    {N n m : Nat} (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (havoid : finCompletionTargetAvoids target shift tail crossing) :
    FinCompletionCarryCertificate N n m :=
  finCompletionCarryCertificateOfTargetIndicator
    target shift tail crossing hshift hcrossTail
    (fun i hi => (havoid i hi).1)
    (fun i hi => (havoid i hi).2)

def finCompletionCarryCertificateOfTargetProfile
    {N n m : Nat} (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (hprofile :
      finCompletionTargetProfile target shift tail crossing) :
    FinCompletionCarryCertificate N n m :=
  finCompletionCarryCertificateOfTargetAvoidance
    target shift tail crossing hshift hcrossTail
    (finCompletionTargetAvoids_of_targetProfile hprofile)

def finCompletionCarryCertificateOfInjectiveTail
    {N n m : Nat} (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (htailAvoids : finCompletionTailAvoidsTarget target tail)
    (htailInj : Function.Injective tail) :
    FinCompletionCarryCertificate N n m :=
  finCompletionCarryCertificateOfTargetProfile
    target shift tail crossing hshift hcrossTail
    (finCompletionTargetProfile_of_injective_tail
      htailAvoids htailInj hcrossTail)

def FinCompletionCarryCertificate.toCompletionCarryCertificate
    {N n m : Nat} (C : FinCompletionCarryCertificate N n m) :
    CompletionCarryCertificate (Fin N) (ZMod n) m where
  row := cyclicCompletionRow C.shift
  coordRead := C.coordRead
  tail := C.tail
  crossing := C.crossing
  epsilon := C.epsilon
  crossingIncidence := by
    rw [C.crossingTail]
    exact cyclicCompletionRowIncidence_tail
      C.target C.shift C.coordRead C.targetRead C.tailRead
  offIncidence := C.offIncidence

theorem finCompletionCarryCertificate_eq_pointCarry
    {N n m : Nat} (C : FinCompletionCarryCertificate N n m) :
    completionCarry C.coordRead (cyclicCompletionRow C.shift) C.tail =
      pointCarry C.crossing C.epsilon :=
  completionCarryCertificate_eq_pointCarry
    C.toCompletionCarryCertificate

theorem finCompletionCarryCertificate_singleCycle
    {N n m : Nat} [NeZero N] [NeZero m]
    (C : FinCompletionCarryCertificate N n m)
    (hepsilon : IsUnit C.epsilon) :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry C.coordRead (cyclicCompletionRow C.shift)
          C.tail)) :=
  completionCarryCertificate_singleCycle finCompletionBaseStep
    (ZMod.finEquiv N).toEquiv (0 : Fin N)
    C.toCompletionCarryCertificate finCompletionBaseStep_rank hepsilon

theorem finCompletionCarryCertificateOfTargetAvoidance_eq_pointCarry
    {N n m : Nat} (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (havoid : finCompletionTargetAvoids target shift tail crossing) :
    completionCarry (targetIndicatorCoordRead (m := m) target)
      (cyclicCompletionRow shift) tail =
        pointCarry crossing (1 : ZMod m) :=
  finCompletionCarryCertificate_eq_pointCarry
    (finCompletionCarryCertificateOfTargetAvoidance
      target shift tail crossing hshift hcrossTail havoid)

theorem finCompletionCarryCertificateOfTargetAvoidance_singleCycle
    {N n m : Nat} [NeZero N] [NeZero m]
    (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (havoid : finCompletionTargetAvoids target shift tail crossing) :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry (targetIndicatorCoordRead (m := m) target)
          (cyclicCompletionRow shift) tail)) :=
  finCompletionCarryCertificate_singleCycle
    (finCompletionCarryCertificateOfTargetAvoidance
      target shift tail crossing hshift hcrossTail havoid) isUnit_one

theorem finCompletionCarryCertificateOfTargetProfile_eq_pointCarry
    {N n m : Nat} (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (hprofile :
      finCompletionTargetProfile target shift tail crossing) :
    completionCarry (targetIndicatorCoordRead (m := m) target)
      (cyclicCompletionRow shift) tail =
        pointCarry crossing (1 : ZMod m) :=
  finCompletionCarryCertificateOfTargetAvoidance_eq_pointCarry
    target shift tail crossing hshift hcrossTail
    (finCompletionTargetAvoids_of_targetProfile hprofile)

theorem finCompletionCarryCertificateOfTargetProfile_singleCycle
    {N n m : Nat} [NeZero N] [NeZero m]
    (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (hprofile :
      finCompletionTargetProfile target shift tail crossing) :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry (targetIndicatorCoordRead (m := m) target)
          (cyclicCompletionRow shift) tail)) :=
  finCompletionCarryCertificateOfTargetAvoidance_singleCycle
    target shift tail crossing hshift hcrossTail
    (finCompletionTargetAvoids_of_targetProfile hprofile)

theorem finCompletionCarryCertificateOfInjectiveTail_eq_pointCarry
    {N n m : Nat} (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (htailAvoids : finCompletionTailAvoidsTarget target tail)
    (htailInj : Function.Injective tail) :
    completionCarry (targetIndicatorCoordRead (m := m) target)
      (cyclicCompletionRow shift) tail =
        pointCarry crossing (1 : ZMod m) :=
  finCompletionCarryCertificateOfTargetProfile_eq_pointCarry
    target shift tail crossing hshift hcrossTail
    (finCompletionTargetProfile_of_injective_tail
      htailAvoids htailInj hcrossTail)

theorem finCompletionCarryCertificateOfInjectiveTail_singleCycle
    {N n m : Nat} [NeZero N] [NeZero m]
    (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (htailAvoids : finCompletionTailAvoidsTarget target tail)
    (htailInj : Function.Injective tail) :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry (targetIndicatorCoordRead (m := m) target)
          (cyclicCompletionRow shift) tail)) :=
  finCompletionCarryCertificateOfTargetProfile_singleCycle
    target shift tail crossing hshift hcrossTail
    (finCompletionTargetProfile_of_injective_tail
      htailAvoids htailInj hcrossTail)

structure FinCompletionInjectiveTailCertificate
    (N n : Nat) where
  target : ZMod n
  shift : ZMod n
  tail : Fin N → ZMod n
  crossing : Fin N
  shiftNeZero : shift ≠ 0
  crossingTail : tail crossing = cyclicCompletionTail target shift
  tailAvoidsTarget : finCompletionTailAvoidsTarget target tail
  tailInjective : Function.Injective tail

theorem finCompletionInjectiveTailCertificate_targetProfile
    {N n : Nat} (C : FinCompletionInjectiveTailCertificate N n) :
    finCompletionTargetProfile C.target C.shift C.tail C.crossing :=
  finCompletionTargetProfile_of_injective_tail
    C.tailAvoidsTarget C.tailInjective C.crossingTail

theorem finCompletionInjectiveTailCertificate_targetAvoids
    {N n : Nat} (C : FinCompletionInjectiveTailCertificate N n) :
    finCompletionTargetAvoids C.target C.shift C.tail C.crossing :=
  finCompletionTargetAvoids_of_injective_tail
    C.tailAvoidsTarget C.tailInjective C.crossingTail

def FinCompletionInjectiveTailCertificate.toCarryCertificate
    {N n : Nat} (C : FinCompletionInjectiveTailCertificate N n)
    (m : Nat) :
    FinCompletionCarryCertificate N n m :=
  finCompletionCarryCertificateOfInjectiveTail
    C.target C.shift C.tail C.crossing
    C.shiftNeZero C.crossingTail
    C.tailAvoidsTarget C.tailInjective

theorem finCompletionInjectiveTailCertificate_eq_pointCarry
    {N n m : Nat} (C : FinCompletionInjectiveTailCertificate N n) :
    completionCarry (targetIndicatorCoordRead (m := m) C.target)
      (cyclicCompletionRow C.shift) C.tail =
        pointCarry C.crossing (1 : ZMod m) :=
  finCompletionCarryCertificateOfInjectiveTail_eq_pointCarry
    C.target C.shift C.tail C.crossing
    C.shiftNeZero C.crossingTail
    C.tailAvoidsTarget C.tailInjective

theorem finCompletionInjectiveTailCertificate_singleCycle
    {N n m : Nat} [NeZero N] [NeZero m]
    (C : FinCompletionInjectiveTailCertificate N n) :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry (targetIndicatorCoordRead (m := m) C.target)
          (cyclicCompletionRow C.shift) C.tail)) :=
  finCompletionCarryCertificateOfInjectiveTail_singleCycle
    C.target C.shift C.tail C.crossing
    C.shiftNeZero C.crossingTail
    C.tailAvoidsTarget C.tailInjective

def finCompletionTailPairwiseSeparated {N n : Nat}
    (tail : Fin N → ZMod n) : Prop :=
  ∀ i j : Fin N, i ≠ j → tail i ≠ tail j

theorem finCompletionTailPairwiseSeparated_injective
    {N n : Nat} {tail : Fin N → ZMod n}
    (hsep : finCompletionTailPairwiseSeparated tail) :
    Function.Injective tail := by
  intro i j hij
  by_cases hidx : i = j
  · exact hidx
  · exact False.elim (hsep i j hidx hij)

def finCompletionTailList {N n : Nat}
    (tail : Fin N → ZMod n) : List (ZMod n) :=
  (List.finRange N).map tail

def finCompletionOffCrossingTailList {N n : Nat}
    (tail : Fin N → ZMod n) (crossing : Fin N) :
    List (ZMod n) :=
  ((List.finRange N).filter (fun i : Fin N => i ≠ crossing)).map tail

theorem mem_finCompletionTailList
    {N n : Nat} {tail : Fin N → ZMod n} {coord : ZMod n} :
    coord ∈ finCompletionTailList tail ↔
      ∃ i : Fin N, tail i = coord := by
  simp [finCompletionTailList]

theorem mem_finCompletionOffCrossingTailList
    {N n : Nat} {tail : Fin N → ZMod n}
    {crossing : Fin N} {coord : ZMod n} :
    coord ∈ finCompletionOffCrossingTailList tail crossing ↔
      ∃ i : Fin N, i ≠ crossing ∧ tail i = coord := by
  simp [finCompletionOffCrossingTailList]

theorem finCompletionTailAvoidsTarget_of_target_not_mem_tailList
    {N n : Nat} {target : ZMod n} {tail : Fin N → ZMod n}
    (hnot : target ∉ finCompletionTailList tail) :
    finCompletionTailAvoidsTarget target tail := by
  intro i htail
  exact hnot ((mem_finCompletionTailList).mpr ⟨i, htail⟩)

theorem finCompletionOffCrossingTailAvoidsTarget_of_target_not_mem_offCrossingTailList
    {N n : Nat} {target : ZMod n} {tail : Fin N → ZMod n}
    {crossing : Fin N}
    (hnot : target ∉ finCompletionOffCrossingTailList tail crossing) :
    finCompletionOffCrossingTailAvoidsTarget target tail crossing := by
  intro i hi htail
  exact hnot
    ((mem_finCompletionOffCrossingTailList).mpr ⟨i, hi, htail⟩)

theorem finCompletionTargetProfile_of_separated_tail
    {N n : Nat} {target shift : ZMod n}
    {tail : Fin N → ZMod n} {crossing : Fin N}
    (htailAvoids : finCompletionTailAvoidsTarget target tail)
    (htailSep : finCompletionTailPairwiseSeparated tail)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift) :
    finCompletionTargetProfile target shift tail crossing :=
  finCompletionTargetProfile_of_injective_tail
    htailAvoids
    (finCompletionTailPairwiseSeparated_injective htailSep)
    hcrossTail

theorem finCompletionTargetAvoids_of_separated_tail
    {N n : Nat} {target shift : ZMod n}
    {tail : Fin N → ZMod n} {crossing : Fin N}
    (htailAvoids : finCompletionTailAvoidsTarget target tail)
    (htailSep : finCompletionTailPairwiseSeparated tail)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift) :
    finCompletionTargetAvoids target shift tail crossing :=
  finCompletionTargetAvoids_of_injective_tail
    htailAvoids
    (finCompletionTailPairwiseSeparated_injective htailSep)
    hcrossTail

def finCompletionCarryCertificateOfSeparatedTail
    {N n m : Nat} (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (htailAvoids : finCompletionTailAvoidsTarget target tail)
    (htailSep : finCompletionTailPairwiseSeparated tail) :
    FinCompletionCarryCertificate N n m :=
  finCompletionCarryCertificateOfInjectiveTail
    target shift tail crossing hshift hcrossTail htailAvoids
    (finCompletionTailPairwiseSeparated_injective htailSep)

theorem finCompletionCarryCertificateOfSeparatedTail_eq_pointCarry
    {N n m : Nat} (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (htailAvoids : finCompletionTailAvoidsTarget target tail)
    (htailSep : finCompletionTailPairwiseSeparated tail) :
    completionCarry (targetIndicatorCoordRead (m := m) target)
      (cyclicCompletionRow shift) tail =
        pointCarry crossing (1 : ZMod m) :=
  finCompletionCarryCertificateOfInjectiveTail_eq_pointCarry
    target shift tail crossing hshift hcrossTail htailAvoids
    (finCompletionTailPairwiseSeparated_injective htailSep)

theorem finCompletionCarryCertificateOfSeparatedTail_singleCycle
    {N n m : Nat} [NeZero N] [NeZero m]
    (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (htailAvoids : finCompletionTailAvoidsTarget target tail)
    (htailSep : finCompletionTailPairwiseSeparated tail) :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry (targetIndicatorCoordRead (m := m) target)
          (cyclicCompletionRow shift) tail)) :=
  finCompletionCarryCertificateOfInjectiveTail_singleCycle
    target shift tail crossing hshift hcrossTail htailAvoids
    (finCompletionTailPairwiseSeparated_injective htailSep)

theorem finCompletionTargetProfile_of_offCrossing_separated_tail
    {N n : Nat} {target shift : ZMod n}
    {tail : Fin N → ZMod n} {crossing : Fin N}
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (hoffTail :
      finCompletionOffCrossingTailAvoidsTarget target tail crossing)
    (htailSep : finCompletionTailPairwiseSeparated tail) :
    finCompletionTargetProfile target shift tail crossing :=
  finCompletionTargetProfile_of_separated_tail
    (finCompletionTailAvoidsTarget_of_offCrossing
      hshift hcrossTail hoffTail)
    htailSep hcrossTail

theorem finCompletionTargetAvoids_of_offCrossing_separated_tail
    {N n : Nat} {target shift : ZMod n}
    {tail : Fin N → ZMod n} {crossing : Fin N}
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (hoffTail :
      finCompletionOffCrossingTailAvoidsTarget target tail crossing)
    (htailSep : finCompletionTailPairwiseSeparated tail) :
    finCompletionTargetAvoids target shift tail crossing :=
  finCompletionTargetAvoids_of_separated_tail
    (finCompletionTailAvoidsTarget_of_offCrossing
      hshift hcrossTail hoffTail)
    htailSep hcrossTail

def finCompletionCarryCertificateOfOffCrossingSeparatedTail
    {N n m : Nat} (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (hoffTail :
      finCompletionOffCrossingTailAvoidsTarget target tail crossing)
    (htailSep : finCompletionTailPairwiseSeparated tail) :
    FinCompletionCarryCertificate N n m :=
  finCompletionCarryCertificateOfSeparatedTail
    target shift tail crossing hshift hcrossTail
    (finCompletionTailAvoidsTarget_of_offCrossing
      hshift hcrossTail hoffTail)
    htailSep

theorem finCompletionCarryCertificateOfOffCrossingSeparatedTail_eq_pointCarry
    {N n m : Nat} (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (hoffTail :
      finCompletionOffCrossingTailAvoidsTarget target tail crossing)
    (htailSep : finCompletionTailPairwiseSeparated tail) :
    completionCarry (targetIndicatorCoordRead (m := m) target)
      (cyclicCompletionRow shift) tail =
        pointCarry crossing (1 : ZMod m) :=
  finCompletionCarryCertificateOfSeparatedTail_eq_pointCarry
    target shift tail crossing hshift hcrossTail
    (finCompletionTailAvoidsTarget_of_offCrossing
      hshift hcrossTail hoffTail)
    htailSep

theorem finCompletionCarryCertificateOfOffCrossingSeparatedTail_singleCycle
    {N n m : Nat} [NeZero N] [NeZero m]
    (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (hoffTail :
      finCompletionOffCrossingTailAvoidsTarget target tail crossing)
    (htailSep : finCompletionTailPairwiseSeparated tail) :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry (targetIndicatorCoordRead (m := m) target)
          (cyclicCompletionRow shift) tail)) :=
  finCompletionCarryCertificateOfSeparatedTail_singleCycle
    target shift tail crossing hshift hcrossTail
    (finCompletionTailAvoidsTarget_of_offCrossing
      hshift hcrossTail hoffTail)
    htailSep

theorem finCompletionTargetProfile_of_offCrossing_tailList_separated_tail
    {N n : Nat} {target shift : ZMod n}
    {tail : Fin N → ZMod n} {crossing : Fin N}
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (hnot :
      target ∉ finCompletionOffCrossingTailList tail crossing)
    (htailSep : finCompletionTailPairwiseSeparated tail) :
    finCompletionTargetProfile target shift tail crossing :=
  finCompletionTargetProfile_of_offCrossing_separated_tail
    hshift hcrossTail
    (finCompletionOffCrossingTailAvoidsTarget_of_target_not_mem_offCrossingTailList
      hnot)
    htailSep

theorem finCompletionTargetAvoids_of_offCrossing_tailList_separated_tail
    {N n : Nat} {target shift : ZMod n}
    {tail : Fin N → ZMod n} {crossing : Fin N}
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (hnot :
      target ∉ finCompletionOffCrossingTailList tail crossing)
    (htailSep : finCompletionTailPairwiseSeparated tail) :
    finCompletionTargetAvoids target shift tail crossing :=
  finCompletionTargetAvoids_of_offCrossing_separated_tail
    hshift hcrossTail
    (finCompletionOffCrossingTailAvoidsTarget_of_target_not_mem_offCrossingTailList
      hnot)
    htailSep

def finCompletionCarryCertificateOfOffCrossingTailListSeparatedTail
    {N n m : Nat} (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (hnot :
      target ∉ finCompletionOffCrossingTailList tail crossing)
    (htailSep : finCompletionTailPairwiseSeparated tail) :
    FinCompletionCarryCertificate N n m :=
  finCompletionCarryCertificateOfOffCrossingSeparatedTail
    target shift tail crossing hshift hcrossTail
    (finCompletionOffCrossingTailAvoidsTarget_of_target_not_mem_offCrossingTailList
      hnot)
    htailSep

theorem finCompletionCarryCertificateOfOffCrossingTailListSeparatedTail_eq_pointCarry
    {N n m : Nat} (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (hnot :
      target ∉ finCompletionOffCrossingTailList tail crossing)
    (htailSep : finCompletionTailPairwiseSeparated tail) :
    completionCarry (targetIndicatorCoordRead (m := m) target)
      (cyclicCompletionRow shift) tail =
        pointCarry crossing (1 : ZMod m) :=
  finCompletionCarryCertificateOfOffCrossingSeparatedTail_eq_pointCarry
    target shift tail crossing hshift hcrossTail
    (finCompletionOffCrossingTailAvoidsTarget_of_target_not_mem_offCrossingTailList
      hnot)
    htailSep

theorem finCompletionCarryCertificateOfOffCrossingTailListSeparatedTail_singleCycle
    {N n m : Nat} [NeZero N] [NeZero m]
    (target shift : ZMod n)
    (tail : Fin N → ZMod n) (crossing : Fin N)
    (hshift : shift ≠ 0)
    (hcrossTail : tail crossing = cyclicCompletionTail target shift)
    (hnot :
      target ∉ finCompletionOffCrossingTailList tail crossing)
    (htailSep : finCompletionTailPairwiseSeparated tail) :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry (targetIndicatorCoordRead (m := m) target)
          (cyclicCompletionRow shift) tail)) :=
  finCompletionCarryCertificateOfOffCrossingSeparatedTail_singleCycle
    target shift tail crossing hshift hcrossTail
    (finCompletionOffCrossingTailAvoidsTarget_of_target_not_mem_offCrossingTailList
      hnot)
    htailSep

structure FinCompletionSeparatedTailCertificate
    (N n : Nat) where
  target : ZMod n
  shift : ZMod n
  tail : Fin N → ZMod n
  crossing : Fin N
  shiftNeZero : shift ≠ 0
  crossingTail : tail crossing = cyclicCompletionTail target shift
  tailAvoidsTarget : finCompletionTailAvoidsTarget target tail
  tailPairwiseSeparated : finCompletionTailPairwiseSeparated tail

theorem finCompletionSeparatedTailCertificate_tailInjective
    {N n : Nat} (C : FinCompletionSeparatedTailCertificate N n) :
    Function.Injective C.tail :=
  finCompletionTailPairwiseSeparated_injective
    C.tailPairwiseSeparated

def FinCompletionSeparatedTailCertificate.toInjectiveTailCertificate
    {N n : Nat} (C : FinCompletionSeparatedTailCertificate N n) :
    FinCompletionInjectiveTailCertificate N n where
  target := C.target
  shift := C.shift
  tail := C.tail
  crossing := C.crossing
  shiftNeZero := C.shiftNeZero
  crossingTail := C.crossingTail
  tailAvoidsTarget := C.tailAvoidsTarget
  tailInjective :=
    finCompletionSeparatedTailCertificate_tailInjective C

def FinCompletionSeparatedTailCertificate.toCarryCertificate
    {N n : Nat} (C : FinCompletionSeparatedTailCertificate N n)
    (m : Nat) :
    FinCompletionCarryCertificate N n m :=
  C.toInjectiveTailCertificate.toCarryCertificate m

theorem finCompletionSeparatedTailCertificate_targetProfile
    {N n : Nat} (C : FinCompletionSeparatedTailCertificate N n) :
    finCompletionTargetProfile C.target C.shift C.tail C.crossing :=
  finCompletionInjectiveTailCertificate_targetProfile
    C.toInjectiveTailCertificate

theorem finCompletionSeparatedTailCertificate_targetAvoids
    {N n : Nat} (C : FinCompletionSeparatedTailCertificate N n) :
    finCompletionTargetAvoids C.target C.shift C.tail C.crossing :=
  finCompletionInjectiveTailCertificate_targetAvoids
    C.toInjectiveTailCertificate

theorem finCompletionSeparatedTailCertificate_eq_pointCarry
    {N n m : Nat} (C : FinCompletionSeparatedTailCertificate N n) :
    completionCarry (targetIndicatorCoordRead (m := m) C.target)
      (cyclicCompletionRow C.shift) C.tail =
        pointCarry C.crossing (1 : ZMod m) :=
  finCompletionInjectiveTailCertificate_eq_pointCarry
    C.toInjectiveTailCertificate

theorem finCompletionSeparatedTailCertificate_singleCycle
    {N n m : Nat} [NeZero N] [NeZero m]
    (C : FinCompletionSeparatedTailCertificate N n) :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry (targetIndicatorCoordRead (m := m) C.target)
          (cyclicCompletionRow C.shift) C.tail)) :=
  finCompletionInjectiveTailCertificate_singleCycle
    C.toInjectiveTailCertificate

structure FinCompletionOffCrossingSeparatedTailCertificate
    (N n : Nat) where
  target : ZMod n
  shift : ZMod n
  tail : Fin N → ZMod n
  crossing : Fin N
  shiftNeZero : shift ≠ 0
  crossingTail : tail crossing = cyclicCompletionTail target shift
  offCrossingTailAvoidsTarget :
    finCompletionOffCrossingTailAvoidsTarget target tail crossing
  tailPairwiseSeparated : finCompletionTailPairwiseSeparated tail

theorem finCompletionOffCrossingSeparatedTailCertificate_tailAvoidsTarget
    {N n : Nat}
    (C : FinCompletionOffCrossingSeparatedTailCertificate N n) :
    finCompletionTailAvoidsTarget C.target C.tail :=
  finCompletionTailAvoidsTarget_of_offCrossing
    C.shiftNeZero C.crossingTail C.offCrossingTailAvoidsTarget

def FinCompletionOffCrossingSeparatedTailCertificate.toSeparatedTailCertificate
    {N n : Nat}
    (C : FinCompletionOffCrossingSeparatedTailCertificate N n) :
    FinCompletionSeparatedTailCertificate N n where
  target := C.target
  shift := C.shift
  tail := C.tail
  crossing := C.crossing
  shiftNeZero := C.shiftNeZero
  crossingTail := C.crossingTail
  tailAvoidsTarget :=
    finCompletionOffCrossingSeparatedTailCertificate_tailAvoidsTarget C
  tailPairwiseSeparated := C.tailPairwiseSeparated

def FinCompletionOffCrossingSeparatedTailCertificate.toCarryCertificate
    {N n : Nat}
    (C : FinCompletionOffCrossingSeparatedTailCertificate N n)
    (m : Nat) :
    FinCompletionCarryCertificate N n m :=
  C.toSeparatedTailCertificate.toCarryCertificate m

theorem finCompletionOffCrossingSeparatedTailCertificate_targetProfile
    {N n : Nat}
    (C : FinCompletionOffCrossingSeparatedTailCertificate N n) :
    finCompletionTargetProfile C.target C.shift C.tail C.crossing :=
  finCompletionSeparatedTailCertificate_targetProfile
    C.toSeparatedTailCertificate

theorem finCompletionOffCrossingSeparatedTailCertificate_targetAvoids
    {N n : Nat}
    (C : FinCompletionOffCrossingSeparatedTailCertificate N n) :
    finCompletionTargetAvoids C.target C.shift C.tail C.crossing :=
  finCompletionSeparatedTailCertificate_targetAvoids
    C.toSeparatedTailCertificate

theorem finCompletionOffCrossingSeparatedTailCertificate_eq_pointCarry
    {N n m : Nat}
    (C : FinCompletionOffCrossingSeparatedTailCertificate N n) :
    completionCarry (targetIndicatorCoordRead (m := m) C.target)
      (cyclicCompletionRow C.shift) C.tail =
        pointCarry C.crossing (1 : ZMod m) :=
  finCompletionSeparatedTailCertificate_eq_pointCarry
    C.toSeparatedTailCertificate

theorem finCompletionOffCrossingSeparatedTailCertificate_singleCycle
    {N n m : Nat} [NeZero N] [NeZero m]
    (C : FinCompletionOffCrossingSeparatedTailCertificate N n) :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry (targetIndicatorCoordRead (m := m) C.target)
          (cyclicCompletionRow C.shift) C.tail)) :=
  finCompletionSeparatedTailCertificate_singleCycle
    C.toSeparatedTailCertificate

structure FinCompletionOffCrossingTailListSeparatedTailCertificate
    (N n : Nat) where
  target : ZMod n
  shift : ZMod n
  tail : Fin N → ZMod n
  crossing : Fin N
  shiftNeZero : shift ≠ 0
  crossingTail : tail crossing = cyclicCompletionTail target shift
  offCrossingTargetNotMemTailList :
    target ∉ finCompletionOffCrossingTailList tail crossing
  tailPairwiseSeparated : finCompletionTailPairwiseSeparated tail

theorem finCompletionOffCrossingTailListSeparatedTailCertificate_offCrossingTailAvoidsTarget
    {N n : Nat}
    (C : FinCompletionOffCrossingTailListSeparatedTailCertificate N n) :
    finCompletionOffCrossingTailAvoidsTarget
      C.target C.tail C.crossing :=
  finCompletionOffCrossingTailAvoidsTarget_of_target_not_mem_offCrossingTailList
    C.offCrossingTargetNotMemTailList

def FinCompletionOffCrossingTailListSeparatedTailCertificate.toOffCrossingSeparatedTailCertificate
    {N n : Nat}
    (C : FinCompletionOffCrossingTailListSeparatedTailCertificate N n) :
    FinCompletionOffCrossingSeparatedTailCertificate N n where
  target := C.target
  shift := C.shift
  tail := C.tail
  crossing := C.crossing
  shiftNeZero := C.shiftNeZero
  crossingTail := C.crossingTail
  offCrossingTailAvoidsTarget :=
    finCompletionOffCrossingTailListSeparatedTailCertificate_offCrossingTailAvoidsTarget
      C
  tailPairwiseSeparated := C.tailPairwiseSeparated

def FinCompletionOffCrossingTailListSeparatedTailCertificate.toCarryCertificate
    {N n : Nat}
    (C : FinCompletionOffCrossingTailListSeparatedTailCertificate N n)
    (m : Nat) :
    FinCompletionCarryCertificate N n m :=
  C.toOffCrossingSeparatedTailCertificate.toCarryCertificate m

theorem finCompletionOffCrossingTailListSeparatedTailCertificate_targetProfile
    {N n : Nat}
    (C : FinCompletionOffCrossingTailListSeparatedTailCertificate N n) :
    finCompletionTargetProfile C.target C.shift C.tail C.crossing :=
  finCompletionOffCrossingSeparatedTailCertificate_targetProfile
    C.toOffCrossingSeparatedTailCertificate

theorem finCompletionOffCrossingTailListSeparatedTailCertificate_targetAvoids
    {N n : Nat}
    (C : FinCompletionOffCrossingTailListSeparatedTailCertificate N n) :
    finCompletionTargetAvoids C.target C.shift C.tail C.crossing :=
  finCompletionOffCrossingSeparatedTailCertificate_targetAvoids
    C.toOffCrossingSeparatedTailCertificate

theorem finCompletionOffCrossingTailListSeparatedTailCertificate_eq_pointCarry
    {N n m : Nat}
    (C : FinCompletionOffCrossingTailListSeparatedTailCertificate N n) :
    completionCarry (targetIndicatorCoordRead (m := m) C.target)
      (cyclicCompletionRow C.shift) C.tail =
        pointCarry C.crossing (1 : ZMod m) :=
  finCompletionOffCrossingSeparatedTailCertificate_eq_pointCarry
    C.toOffCrossingSeparatedTailCertificate

theorem finCompletionOffCrossingTailListSeparatedTailCertificate_singleCycle
    {N n m : Nat} [NeZero N] [NeZero m]
    (C : FinCompletionOffCrossingTailListSeparatedTailCertificate N n) :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry (targetIndicatorCoordRead (m := m) C.target)
          (cyclicCompletionRow C.shift) C.tail)) :=
  finCompletionOffCrossingSeparatedTailCertificate_singleCycle
    C.toOffCrossingSeparatedTailCertificate

def endpointB4FirstCompletionTarget : ZMod 9 := 8

def endpointB4FirstCompletionShift : ZMod 9 := 1

def endpointB4FirstCompletionTail : ZMod 9 := 7

def endpointB4FirstCompletionCoordRead {m : Nat} :
    ZMod 9 → ZMod m :=
  targetIndicatorCoordRead endpointB4FirstCompletionTarget

theorem endpointB4FirstCompletion_tail :
    cyclicCompletionTail endpointB4FirstCompletionTarget
      endpointB4FirstCompletionShift =
        endpointB4FirstCompletionTail := by
  norm_num [endpointB4FirstCompletionTarget,
    endpointB4FirstCompletionShift, endpointB4FirstCompletionTail,
    cyclicCompletionTail]

theorem endpointB4FirstCompletion_row :
    cyclicCompletionRow endpointB4FirstCompletionShift
      endpointB4FirstCompletionTail =
        endpointB4FirstCompletionTarget := by
  rw [← endpointB4FirstCompletion_tail]
  exact cyclicCompletionRow_tail
    endpointB4FirstCompletionTarget endpointB4FirstCompletionShift

theorem endpointB4FirstCompletion_shift_ne_zero :
    endpointB4FirstCompletionShift ≠ (0 : ZMod 9) := by
  change (1 : ZMod 9) ≠ 0
  intro h
  have hmod : 1 ≡ 0 [MOD 9] :=
    (ZMod.natCast_eq_natCast_iff 1 0 9).mp h
  norm_num at hmod

theorem endpointB4FirstCompletionCoordRead_target {m : Nat} :
    endpointB4FirstCompletionCoordRead (m := m)
      endpointB4FirstCompletionTarget = 1 :=
  targetIndicatorCoordRead_target endpointB4FirstCompletionTarget

theorem endpointB4FirstCompletionCoordRead_tail {m : Nat} :
    endpointB4FirstCompletionCoordRead (m := m)
      endpointB4FirstCompletionTail = 0 := by
  rw [← endpointB4FirstCompletion_tail]
  exact targetIndicatorCoordRead_cyclicCompletionTail
    endpointB4FirstCompletion_shift_ne_zero

theorem endpointB4FirstCompletion_tail_ne_target :
    endpointB4FirstCompletionTail ≠ endpointB4FirstCompletionTarget := by
  rw [← endpointB4FirstCompletion_tail]
  exact cyclicCompletionTail_ne_target_of_shift_ne_zero
    endpointB4FirstCompletion_shift_ne_zero

theorem endpointB4FirstCompletionTailAvoidsTarget :
    finCompletionTailAvoidsTarget
      endpointB4FirstCompletionTarget
      (fun _ : Fin 1 => endpointB4FirstCompletionTail) := by
  intro _
  exact endpointB4FirstCompletion_tail_ne_target

theorem endpointB4FirstCompletionRowTargetHitsOnlyAtCrossing :
    finCompletionRowTargetHitsOnlyAtCrossing
      endpointB4FirstCompletionTarget
      endpointB4FirstCompletionShift
      (fun _ : Fin 1 => endpointB4FirstCompletionTail) 0 := by
  intro i _
  exact Subsingleton.elim i 0

theorem endpointB4FirstCompletionTail_pairwiseSeparated :
    finCompletionTailPairwiseSeparated
      (fun _ : Fin 1 => endpointB4FirstCompletionTail) := by
  intro i j hidx hij
  exact hidx (Subsingleton.elim i j)

theorem endpointB4FirstCompletionOffCrossingTailAvoidsTarget :
    finCompletionOffCrossingTailAvoidsTarget
      endpointB4FirstCompletionTarget
      (fun _ : Fin 1 => endpointB4FirstCompletionTail) 0 := by
  intro i hi
  exact False.elim (hi (Subsingleton.elim i 0))

theorem endpointB4FirstCompletionTailAvoidsTarget_fromOffCrossing :
    finCompletionTailAvoidsTarget
      endpointB4FirstCompletionTarget
      (fun _ : Fin 1 => endpointB4FirstCompletionTail) :=
  finCompletionTailAvoidsTarget_of_offCrossing
    endpointB4FirstCompletion_shift_ne_zero
    endpointB4FirstCompletion_tail
    endpointB4FirstCompletionOffCrossingTailAvoidsTarget

theorem endpointB4FirstCompletionTail_injective :
    Function.Injective
      (fun _ : Fin 1 => endpointB4FirstCompletionTail) :=
  finCompletionTailPairwiseSeparated_injective
    endpointB4FirstCompletionTail_pairwiseSeparated

theorem endpointB4FirstCompletionTargetProfile :
    finCompletionTargetProfile
      endpointB4FirstCompletionTarget
      endpointB4FirstCompletionShift
      (fun _ : Fin 1 => endpointB4FirstCompletionTail) 0 :=
  ⟨endpointB4FirstCompletionTailAvoidsTarget,
    endpointB4FirstCompletionRowTargetHitsOnlyAtCrossing⟩

def endpointB4FirstCompletionSeparatedTailCertificate :
    FinCompletionSeparatedTailCertificate 1 9 where
  target := endpointB4FirstCompletionTarget
  shift := endpointB4FirstCompletionShift
  tail := fun _ : Fin 1 => endpointB4FirstCompletionTail
  crossing := 0
  shiftNeZero := endpointB4FirstCompletion_shift_ne_zero
  crossingTail := endpointB4FirstCompletion_tail
  tailAvoidsTarget := endpointB4FirstCompletionTailAvoidsTarget
  tailPairwiseSeparated :=
    endpointB4FirstCompletionTail_pairwiseSeparated

def endpointB4FirstCompletionInjectiveTailCertificate :
    FinCompletionInjectiveTailCertificate 1 9 :=
  FinCompletionSeparatedTailCertificate.toInjectiveTailCertificate
    endpointB4FirstCompletionSeparatedTailCertificate

theorem endpointB4FirstCompletionTargetAvoids :
    finCompletionTargetAvoids
      endpointB4FirstCompletionTarget
      endpointB4FirstCompletionShift
      (fun _ : Fin 1 => endpointB4FirstCompletionTail) 0 :=
  finCompletionTargetAvoids_of_targetProfile
    endpointB4FirstCompletionTargetProfile

def endpointB4FirstCompletionOffCrossingSeparatedTailCertificate :
    FinCompletionOffCrossingSeparatedTailCertificate 1 9 where
  target := endpointB4FirstCompletionTarget
  shift := endpointB4FirstCompletionShift
  tail := fun _ : Fin 1 => endpointB4FirstCompletionTail
  crossing := 0
  shiftNeZero := endpointB4FirstCompletion_shift_ne_zero
  crossingTail := endpointB4FirstCompletion_tail
  offCrossingTailAvoidsTarget :=
    endpointB4FirstCompletionOffCrossingTailAvoidsTarget
  tailPairwiseSeparated :=
    endpointB4FirstCompletionTail_pairwiseSeparated

theorem endpointB4FirstCompletionOffCrossingTarget_not_mem_tailList :
    endpointB4FirstCompletionTarget ∉
      finCompletionOffCrossingTailList
        (fun _ : Fin 1 => endpointB4FirstCompletionTail) 0 := by
  intro hmem
  rw [mem_finCompletionOffCrossingTailList] at hmem
  rcases hmem with ⟨i, hi, _⟩
  exact hi (Subsingleton.elim i 0)

theorem endpointB4FirstCompletionOffCrossingTailListAvoidsTarget :
    finCompletionOffCrossingTailAvoidsTarget
      endpointB4FirstCompletionTarget
      (fun _ : Fin 1 => endpointB4FirstCompletionTail) 0 :=
  finCompletionOffCrossingTailAvoidsTarget_of_target_not_mem_offCrossingTailList
    endpointB4FirstCompletionOffCrossingTarget_not_mem_tailList

def endpointB4FirstCompletionOffCrossingTailListSeparatedTailCertificate :
    FinCompletionOffCrossingTailListSeparatedTailCertificate 1 9 where
  target := endpointB4FirstCompletionTarget
  shift := endpointB4FirstCompletionShift
  tail := fun _ : Fin 1 => endpointB4FirstCompletionTail
  crossing := 0
  shiftNeZero := endpointB4FirstCompletion_shift_ne_zero
  crossingTail := endpointB4FirstCompletion_tail
  offCrossingTargetNotMemTailList :=
    endpointB4FirstCompletionOffCrossingTarget_not_mem_tailList
  tailPairwiseSeparated :=
    endpointB4FirstCompletionTail_pairwiseSeparated

theorem endpointB4FirstCompletionOffCrossingTailListTargetProfile :
    finCompletionTargetProfile
      endpointB4FirstCompletionTarget
      endpointB4FirstCompletionShift
      (fun _ : Fin 1 => endpointB4FirstCompletionTail) 0 :=
  finCompletionOffCrossingTailListSeparatedTailCertificate_targetProfile
    endpointB4FirstCompletionOffCrossingTailListSeparatedTailCertificate

theorem endpointB4FirstCompletionOffCrossingTailListTargetAvoids :
    finCompletionTargetAvoids
      endpointB4FirstCompletionTarget
      endpointB4FirstCompletionShift
      (fun _ : Fin 1 => endpointB4FirstCompletionTail) 0 :=
  finCompletionOffCrossingTailListSeparatedTailCertificate_targetAvoids
    endpointB4FirstCompletionOffCrossingTailListSeparatedTailCertificate

def endpointB4FirstCompletionOffCrossingOnePointCertificate
    (m : Nat) :
    FinCompletionCarryCertificate 1 9 m :=
  FinCompletionOffCrossingSeparatedTailCertificate.toCarryCertificate
    endpointB4FirstCompletionOffCrossingSeparatedTailCertificate m

def endpointB4FirstCompletionOffCrossingTailListOnePointCertificate
    (m : Nat) :
    FinCompletionCarryCertificate 1 9 m :=
  FinCompletionOffCrossingTailListSeparatedTailCertificate.toCarryCertificate
    endpointB4FirstCompletionOffCrossingTailListSeparatedTailCertificate m

theorem endpointB4FirstCompletionOffCrossingTailListOnePointCertificate_fromTailList
    (m : Nat) :
    endpointB4FirstCompletionOffCrossingTailListOnePointCertificate m =
      FinCompletionOffCrossingTailListSeparatedTailCertificate.toCarryCertificate
        endpointB4FirstCompletionOffCrossingTailListSeparatedTailCertificate m :=
  rfl

theorem endpointB4FirstCompletionTailListOnePointCertificate_eq_pointCarry
    {m : Nat} :
    completionCarry
        (endpointB4FirstCompletionOffCrossingTailListOnePointCertificate
          m).coordRead
        (cyclicCompletionRow
          (endpointB4FirstCompletionOffCrossingTailListOnePointCertificate
            m).shift)
        (endpointB4FirstCompletionOffCrossingTailListOnePointCertificate
          m).tail =
      pointCarry
        (endpointB4FirstCompletionOffCrossingTailListOnePointCertificate
          m).crossing
        (endpointB4FirstCompletionOffCrossingTailListOnePointCertificate
          m).epsilon :=
  finCompletionCarryCertificate_eq_pointCarry
    (endpointB4FirstCompletionOffCrossingTailListOnePointCertificate m)

theorem endpointB4FirstCompletionTailListOnePointCertificate_singleCycle
    {m : Nat} [NeZero m] :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry
          (endpointB4FirstCompletionOffCrossingTailListOnePointCertificate
            m).coordRead
          (cyclicCompletionRow
            (endpointB4FirstCompletionOffCrossingTailListOnePointCertificate
              m).shift)
          (endpointB4FirstCompletionOffCrossingTailListOnePointCertificate
            m).tail)) :=
  finCompletionCarryCertificate_singleCycle
    (endpointB4FirstCompletionOffCrossingTailListOnePointCertificate m)
    isUnit_one

theorem endpointB4FirstCompletionOffCrossingOnePointCertificate_fromTail
    (m : Nat) :
    endpointB4FirstCompletionOffCrossingOnePointCertificate m =
      FinCompletionOffCrossingSeparatedTailCertificate.toCarryCertificate
        endpointB4FirstCompletionOffCrossingSeparatedTailCertificate m :=
  rfl

theorem endpointB4FirstCompletionOffCrossingSeparatedTail_eq_pointCarry
    {m : Nat} :
    completionCarry
        (targetIndicatorCoordRead (m := m)
          endpointB4FirstCompletionTarget)
        (cyclicCompletionRow endpointB4FirstCompletionShift)
        (fun _ : Fin 1 => endpointB4FirstCompletionTail) =
      pointCarry (0 : Fin 1) (1 : ZMod m) :=
  finCompletionOffCrossingSeparatedTailCertificate_eq_pointCarry
    endpointB4FirstCompletionOffCrossingSeparatedTailCertificate

theorem endpointB4FirstCompletionOffCrossingSeparatedTail_singleCycle
    {m : Nat} [NeZero m] :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry
          (targetIndicatorCoordRead (m := m)
            endpointB4FirstCompletionTarget)
          (cyclicCompletionRow endpointB4FirstCompletionShift)
          (fun _ : Fin 1 => endpointB4FirstCompletionTail))) :=
  finCompletionOffCrossingSeparatedTailCertificate_singleCycle
    endpointB4FirstCompletionOffCrossingSeparatedTailCertificate

theorem endpointB4FirstCompletionOffCrossingTailListSeparatedTail_eq_pointCarry
    {m : Nat} :
    completionCarry
        (targetIndicatorCoordRead (m := m)
          endpointB4FirstCompletionTarget)
        (cyclicCompletionRow endpointB4FirstCompletionShift)
        (fun _ : Fin 1 => endpointB4FirstCompletionTail) =
      pointCarry (0 : Fin 1) (1 : ZMod m) :=
  finCompletionOffCrossingTailListSeparatedTailCertificate_eq_pointCarry
    endpointB4FirstCompletionOffCrossingTailListSeparatedTailCertificate

theorem endpointB4FirstCompletionOffCrossingTailListSeparatedTail_singleCycle
    {m : Nat} [NeZero m] :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry
          (targetIndicatorCoordRead (m := m)
            endpointB4FirstCompletionTarget)
          (cyclicCompletionRow endpointB4FirstCompletionShift)
          (fun _ : Fin 1 => endpointB4FirstCompletionTail))) :=
  finCompletionOffCrossingTailListSeparatedTailCertificate_singleCycle
    endpointB4FirstCompletionOffCrossingTailListSeparatedTailCertificate

def endpointB4FirstCompletionOnePointCertificate (m : Nat) :
    FinCompletionCarryCertificate 1 9 m :=
  endpointB4FirstCompletionSeparatedTailCertificate.toCarryCertificate m

theorem endpointB4FirstCompletionOnePointCertificate_fromSeparatedTail
    (m : Nat) :
    endpointB4FirstCompletionOnePointCertificate m =
      FinCompletionSeparatedTailCertificate.toCarryCertificate
        endpointB4FirstCompletionSeparatedTailCertificate m :=
  rfl

theorem endpointB4FirstCompletionInjectiveTailCertificate_eq_pointCarry
    {m : Nat} :
    completionCarry
        (targetIndicatorCoordRead (m := m)
          endpointB4FirstCompletionTarget)
        (cyclicCompletionRow endpointB4FirstCompletionShift)
        (fun _ : Fin 1 => endpointB4FirstCompletionTail) =
      pointCarry (0 : Fin 1) (1 : ZMod m) :=
  finCompletionSeparatedTailCertificate_eq_pointCarry
    endpointB4FirstCompletionSeparatedTailCertificate

theorem endpointB4FirstCompletionInjectiveTailCertificate_singleCycle
    {m : Nat} [NeZero m] :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry
          (targetIndicatorCoordRead (m := m)
            endpointB4FirstCompletionTarget)
          (cyclicCompletionRow endpointB4FirstCompletionShift)
          (fun _ : Fin 1 => endpointB4FirstCompletionTail))) :=
  finCompletionSeparatedTailCertificate_singleCycle
    endpointB4FirstCompletionSeparatedTailCertificate

theorem endpointB4FirstCompletionSeparatedTailCertificate_eq_pointCarry
    {m : Nat} :
    completionCarry
        (targetIndicatorCoordRead (m := m)
          endpointB4FirstCompletionTarget)
        (cyclicCompletionRow endpointB4FirstCompletionShift)
        (fun _ : Fin 1 => endpointB4FirstCompletionTail) =
      pointCarry (0 : Fin 1) (1 : ZMod m) :=
  finCompletionSeparatedTailCertificate_eq_pointCarry
    endpointB4FirstCompletionSeparatedTailCertificate

theorem endpointB4FirstCompletionSeparatedTailCertificate_singleCycle
    {m : Nat} [NeZero m] :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry
          (targetIndicatorCoordRead (m := m)
            endpointB4FirstCompletionTarget)
          (cyclicCompletionRow endpointB4FirstCompletionShift)
          (fun _ : Fin 1 => endpointB4FirstCompletionTail))) :=
  finCompletionSeparatedTailCertificate_singleCycle
    endpointB4FirstCompletionSeparatedTailCertificate

theorem endpointB4FirstCompletionOnePointCertificate_eq_pointCarry
    {m : Nat} :
    completionCarry
        (endpointB4FirstCompletionOnePointCertificate m).coordRead
        (cyclicCompletionRow
          (endpointB4FirstCompletionOnePointCertificate m).shift)
        (endpointB4FirstCompletionOnePointCertificate m).tail =
      pointCarry
        (endpointB4FirstCompletionOnePointCertificate m).crossing
        (endpointB4FirstCompletionOnePointCertificate m).epsilon :=
  finCompletionCarryCertificate_eq_pointCarry
    (endpointB4FirstCompletionOnePointCertificate m)

theorem endpointB4FirstCompletionOnePointCertificate_singleCycle
    {m : Nat} [NeZero m] :
    Shared.IsSingleCycleMap
      (additiveSkewMap finCompletionBaseStep
        (completionCarry
          (endpointB4FirstCompletionOnePointCertificate m).coordRead
          (cyclicCompletionRow
            (endpointB4FirstCompletionOnePointCertificate m).shift)
          (endpointB4FirstCompletionOnePointCertificate m).tail)) :=
  finCompletionCarryCertificate_singleCycle
    (endpointB4FirstCompletionOnePointCertificate m) isUnit_one

end EndpointCompletion

export EndpointCompletion
  (cyclicCompletionRow
   cyclicCompletionTail
   rowIncidence
   targetIndicatorCoordRead
   completionCarry
   CompletionCarryCertificate
   rowIncidence_eq_zero_of_eq
   targetIndicatorCoordRead_target
   targetIndicatorCoordRead_of_ne
   carry_eq_pointCarry_of_crossing_and_off
   completionCarryCertificate_eq_pointCarry
   completionCarryCertificate_singleCycle
   cyclicCompletionRow_bijective
   cyclicCompletionRow_tail
   cyclicCompletionTail_unique
   cyclicCompletionRow_tail_iff
   cyclicCompletionRow_moved_of_shift_ne_zero
   cyclicCompletionTail_ne_target_of_shift_ne_zero
   targetIndicatorCoordRead_cyclicCompletionTail
   cyclicCompletionRowIncidence_tail
   cyclicCompletionRowIncidence_eq_zero_of_read_eq
   cyclicCompletionRowIncidence_targetIndicator_tail
   cyclicCompletionRowIncidence_targetIndicator_eq_zero_of_ne_target
   completionTargetAvoids
   completionTargetAvoids_tail_ne_target
   completionTargetAvoids_row_ne_target
   cyclicCompletionRowIncidence_targetIndicator_eq_zero_of_avoids
   cyclicCompletionCarry_eq_pointCarry
   cyclicCompletionCarrySingleCycle
   finCompletionBaseStep
   finCompletionBaseStep_rank
   FinCompletionCarryCertificate
   finCompletionCarryCertificateOfTargetIndicator
   finCompletionTargetAvoids
   finCompletionTailAvoidsTarget
   finCompletionOffCrossingTailAvoidsTarget
   finCompletionTailAvoidsTarget_of_offCrossing
   finCompletionRowTargetHitsOnlyAtCrossing
   finCompletionTargetProfile
   finCompletionRowTargetHitsOnlyAtCrossing_of_injective_tail
   finCompletionTargetProfile_of_injective_tail
   finCompletionTargetAvoids_of_injective_tail
   finCompletionTargetAvoids_of_targetProfile
   finCompletionCarryCertificateOfTargetAvoidance
   finCompletionCarryCertificateOfTargetProfile
   finCompletionCarryCertificateOfInjectiveTail
   FinCompletionInjectiveTailCertificate
   finCompletionInjectiveTailCertificate_targetProfile
   finCompletionInjectiveTailCertificate_targetAvoids
   FinCompletionInjectiveTailCertificate.toCarryCertificate
   finCompletionInjectiveTailCertificate_eq_pointCarry
   finCompletionInjectiveTailCertificate_singleCycle
   finCompletionTailPairwiseSeparated
   finCompletionTailPairwiseSeparated_injective
   finCompletionTailList
   finCompletionOffCrossingTailList
   mem_finCompletionTailList
   mem_finCompletionOffCrossingTailList
   finCompletionTailAvoidsTarget_of_target_not_mem_tailList
   finCompletionOffCrossingTailAvoidsTarget_of_target_not_mem_offCrossingTailList
   finCompletionTargetProfile_of_separated_tail
   finCompletionTargetAvoids_of_separated_tail
   finCompletionCarryCertificateOfSeparatedTail
   finCompletionCarryCertificateOfSeparatedTail_eq_pointCarry
   finCompletionCarryCertificateOfSeparatedTail_singleCycle
   finCompletionTargetProfile_of_offCrossing_separated_tail
   finCompletionTargetAvoids_of_offCrossing_separated_tail
   finCompletionCarryCertificateOfOffCrossingSeparatedTail
   finCompletionCarryCertificateOfOffCrossingSeparatedTail_eq_pointCarry
   finCompletionCarryCertificateOfOffCrossingSeparatedTail_singleCycle
   finCompletionTargetProfile_of_offCrossing_tailList_separated_tail
   finCompletionTargetAvoids_of_offCrossing_tailList_separated_tail
   finCompletionCarryCertificateOfOffCrossingTailListSeparatedTail
   finCompletionCarryCertificateOfOffCrossingTailListSeparatedTail_eq_pointCarry
   finCompletionCarryCertificateOfOffCrossingTailListSeparatedTail_singleCycle
   FinCompletionSeparatedTailCertificate
   finCompletionSeparatedTailCertificate_tailInjective
   FinCompletionSeparatedTailCertificate.toInjectiveTailCertificate
   FinCompletionSeparatedTailCertificate.toCarryCertificate
   finCompletionSeparatedTailCertificate_targetProfile
   finCompletionSeparatedTailCertificate_targetAvoids
   finCompletionSeparatedTailCertificate_eq_pointCarry
   finCompletionSeparatedTailCertificate_singleCycle
   FinCompletionOffCrossingSeparatedTailCertificate
   finCompletionOffCrossingSeparatedTailCertificate_tailAvoidsTarget
   FinCompletionOffCrossingSeparatedTailCertificate.toSeparatedTailCertificate
   FinCompletionOffCrossingSeparatedTailCertificate.toCarryCertificate
   finCompletionOffCrossingSeparatedTailCertificate_targetProfile
   finCompletionOffCrossingSeparatedTailCertificate_targetAvoids
   finCompletionOffCrossingSeparatedTailCertificate_eq_pointCarry
   finCompletionOffCrossingSeparatedTailCertificate_singleCycle
   FinCompletionOffCrossingTailListSeparatedTailCertificate
   finCompletionOffCrossingTailListSeparatedTailCertificate_offCrossingTailAvoidsTarget
   FinCompletionOffCrossingTailListSeparatedTailCertificate.toOffCrossingSeparatedTailCertificate
   FinCompletionOffCrossingTailListSeparatedTailCertificate.toCarryCertificate
   finCompletionOffCrossingTailListSeparatedTailCertificate_targetProfile
   finCompletionOffCrossingTailListSeparatedTailCertificate_targetAvoids
   finCompletionOffCrossingTailListSeparatedTailCertificate_eq_pointCarry
   finCompletionOffCrossingTailListSeparatedTailCertificate_singleCycle
   finCompletionCarryCertificateOfTargetAvoidance_eq_pointCarry
   finCompletionCarryCertificateOfTargetAvoidance_singleCycle
   finCompletionCarryCertificateOfTargetProfile_eq_pointCarry
   finCompletionCarryCertificateOfTargetProfile_singleCycle
   finCompletionCarryCertificateOfInjectiveTail_eq_pointCarry
   finCompletionCarryCertificateOfInjectiveTail_singleCycle
   FinCompletionCarryCertificate.toCompletionCarryCertificate
   finCompletionCarryCertificate_eq_pointCarry
   finCompletionCarryCertificate_singleCycle
   endpointB4FirstCompletionTarget
   endpointB4FirstCompletionShift
   endpointB4FirstCompletionTail
   endpointB4FirstCompletionCoordRead
   endpointB4FirstCompletion_tail
   endpointB4FirstCompletion_row
   endpointB4FirstCompletion_shift_ne_zero
   endpointB4FirstCompletionCoordRead_target
   endpointB4FirstCompletionCoordRead_tail
   endpointB4FirstCompletion_tail_ne_target
   endpointB4FirstCompletionTailAvoidsTarget
   endpointB4FirstCompletionRowTargetHitsOnlyAtCrossing
   endpointB4FirstCompletionTail_pairwiseSeparated
   endpointB4FirstCompletionOffCrossingTailAvoidsTarget
   endpointB4FirstCompletionTailAvoidsTarget_fromOffCrossing
   endpointB4FirstCompletionTail_injective
   endpointB4FirstCompletionTargetProfile
   endpointB4FirstCompletionSeparatedTailCertificate
   endpointB4FirstCompletionInjectiveTailCertificate
   endpointB4FirstCompletionTargetAvoids
   endpointB4FirstCompletionOffCrossingSeparatedTailCertificate
   endpointB4FirstCompletionOffCrossingTarget_not_mem_tailList
   endpointB4FirstCompletionOffCrossingTailListAvoidsTarget
   endpointB4FirstCompletionOffCrossingTailListSeparatedTailCertificate
   endpointB4FirstCompletionOffCrossingTailListTargetProfile
   endpointB4FirstCompletionOffCrossingTailListTargetAvoids
   endpointB4FirstCompletionOffCrossingOnePointCertificate
   endpointB4FirstCompletionOffCrossingTailListOnePointCertificate
   endpointB4FirstCompletionOffCrossingTailListOnePointCertificate_fromTailList
   endpointB4FirstCompletionTailListOnePointCertificate_eq_pointCarry
   endpointB4FirstCompletionTailListOnePointCertificate_singleCycle
   endpointB4FirstCompletionOffCrossingOnePointCertificate_fromTail
   endpointB4FirstCompletionOffCrossingSeparatedTail_eq_pointCarry
   endpointB4FirstCompletionOffCrossingSeparatedTail_singleCycle
   endpointB4FirstCompletionOffCrossingTailListSeparatedTail_eq_pointCarry
   endpointB4FirstCompletionOffCrossingTailListSeparatedTail_singleCycle
   endpointB4FirstCompletionOnePointCertificate
   endpointB4FirstCompletionOnePointCertificate_fromSeparatedTail
   endpointB4FirstCompletionInjectiveTailCertificate_eq_pointCarry
   endpointB4FirstCompletionInjectiveTailCertificate_singleCycle
   endpointB4FirstCompletionSeparatedTailCertificate_eq_pointCarry
   endpointB4FirstCompletionSeparatedTailCertificate_singleCycle
   endpointB4FirstCompletionOnePointCertificate_eq_pointCarry
   endpointB4FirstCompletionOnePointCertificate_singleCycle)

end EvenV11
