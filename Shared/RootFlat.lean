import Shared.ReturnLift

namespace Shared

structure RootFlatSchedule (Color Direction RootState : Type*) (m : Nat) where
  dir : ZMod m → RootState → Color → Direction
  step : Direction → RootState → RootState

namespace RootFlatSchedule

def rowLatin {Color Direction RootState : Type*} {m : Nat}
    (S : RootFlatSchedule Color Direction RootState m) : Prop :=
  ∀ t w, Function.Bijective fun c : Color => S.dir t w c

def layerMap {Color Direction RootState : Type*} {m : Nat}
    (S : RootFlatSchedule Color Direction RootState m) (t : ZMod m)
    (c : Color) : RootState → RootState :=
  fun w => S.step (S.dir t w c) w

def layerBijective {Color Direction RootState : Type*} {m : Nat}
    (S : RootFlatSchedule Color Direction RootState m) : Prop :=
  ∀ t c, Function.Bijective (S.layerMap t c)

def returnMap {Color Direction RootState : Type*} {m : Nat} [NeZero m]
    (S : RootFlatSchedule Color Direction RootState m) (c : Color) :
    RootState → RootState :=
  fun w => ((List.range m).foldl
    (fun x (t : Nat) => S.layerMap (t : ZMod m) c x) w)

def returnsSingleCycle {Color Direction RootState : Type*}
    {m : Nat} [NeZero m]
    (S : RootFlatSchedule Color Direction RootState m) : Prop :=
  ∀ c : Color, IsSingleCycleMap (S.returnMap c)

def edgePartition {Color Direction RootState : Type*} {m : Nat}
    (S : RootFlatSchedule Color Direction RootState m) : Prop :=
  ∀ t w i, ∃! c : Color, S.dir t w c = i

def fullStep {Color Direction RootState : Type*} {m : Nat}
    (S : RootFlatSchedule Color Direction RootState m) (c : Color) :
    ZMod m × RootState → ZMod m × RootState :=
  fun x => (x.1 + 1, S.layerMap x.1 c x.2)

def prefixMap {Color Direction RootState : Type*} {m : Nat}
    (S : RootFlatSchedule Color Direction RootState m) (c : Color) :
    Nat → RootState → RootState
  | 0 => fun w => w
  | k + 1 => fun w => S.layerMap (k : ZMod m) c (S.prefixMap c k w)

def fullStepsHamiltonian {Color Direction RootState : Type*}
    {m : Nat} [NeZero m]
    (S : RootFlatSchedule Color Direction RootState m) : Prop :=
  ∀ c : Color, IsSingleCycleMap (S.fullStep c)

theorem edgePartition_of_rowLatin
    {Color Direction RootState : Type*} {m : Nat}
    {S : RootFlatSchedule Color Direction RootState m}
    (hRow : S.rowLatin) :
    S.edgePartition := by
  intro t w i
  rcases (hRow t w).2 i with ⟨c, hc⟩
  refine ⟨c, hc, ?_⟩
  intro c' hc'
  exact (hRow t w).1 (by
    calc
      S.dir t w c' = i := hc'
      _ = S.dir t w c := hc.symm)

theorem prefixMap_eq_range_foldl
    {Color Direction RootState : Type*} {m : Nat}
    (S : RootFlatSchedule Color Direction RootState m)
    (c : Color) :
    ∀ k : Nat, ∀ w : RootState,
      S.prefixMap c k w =
        (List.range k).foldl
          (fun x (t : Nat) => S.layerMap (t : ZMod m) c x) w
  | 0, w => by
      simp [prefixMap]
  | k + 1, w => by
      simp [prefixMap, List.range_succ, List.foldl_append,
        prefixMap_eq_range_foldl S c k w]

theorem returnMap_eq_prefixMap
    {Color Direction RootState : Type*} {m : Nat} [NeZero m]
    (S : RootFlatSchedule Color Direction RootState m)
    (c : Color) :
    S.returnMap c = S.prefixMap c m := by
  funext w
  rw [prefixMap_eq_range_foldl]
  rfl

theorem prefixMap_bijective
    {Color Direction RootState : Type*} {m : Nat}
    (S : RootFlatSchedule Color Direction RootState m)
    (hLayer : S.layerBijective) (c : Color) :
    ∀ k : Nat, Function.Bijective (S.prefixMap c k)
  | 0 => by
      constructor
      · intro x y hxy
        simpa [prefixMap] using hxy
      · intro y
        exact ⟨y, by simp [prefixMap]⟩
  | k + 1 => by
      exact (hLayer (k : ZMod m) c).comp
        (prefixMap_bijective S hLayer c k)

theorem fullStep_bijective
    {Color Direction RootState : Type*} {m : Nat}
    (S : RootFlatSchedule Color Direction RootState m)
    (hLayer : S.layerBijective) (c : Color) :
    Function.Bijective (S.fullStep c) := by
  constructor
  · intro x y hxy
    rcases x with ⟨tx, wx⟩
    rcases y with ⟨ty, wy⟩
    have ht : tx = ty := by
      have hfst : tx + 1 = ty + 1 := congrArg Prod.fst hxy
      have hsub := congrArg (fun z : ZMod m => z - 1) hfst
      simpa using hsub
    subst ty
    have hw :
        S.layerMap tx c wx = S.layerMap tx c wy :=
      congrArg Prod.snd hxy
    exact Prod.ext rfl ((hLayer tx c).1 hw)
  · intro y
    rcases y with ⟨t', w'⟩
    let t : ZMod m := t' - 1
    rcases (hLayer t c).2 w' with ⟨w, hw⟩
    refine ⟨(t, w), ?_⟩
    simp [fullStep, t, hw]

theorem fullStep_iterate_zero_prefixMap
    {Color Direction RootState : Type*} {m : Nat}
    (S : RootFlatSchedule Color Direction RootState m)
    (c : Color) :
    ∀ k : Nat, ∀ w : RootState,
      (S.fullStep c)^[k] (0, w) =
        ((k : ZMod m), S.prefixMap c k w)
  | 0, w => by
      simp [prefixMap]
  | k + 1, w => by
      rw [Function.iterate_succ_apply']
      simp [fullStep, prefixMap, fullStep_iterate_zero_prefixMap S c k w,
        Nat.cast_add]

theorem fullStep_iterate_period_base
    {Color Direction RootState : Type*} {m : Nat} [NeZero m]
    (S : RootFlatSchedule Color Direction RootState m)
    (c : Color) (w : RootState) :
    (S.fullStep c)^[m] (0, w) = (0, S.returnMap c w) := by
  rw [fullStep_iterate_zero_prefixMap]
  rw [returnMap_eq_prefixMap]
  simp

theorem fullStep_cover_from_base
    {Color Direction RootState : Type*} {m : Nat} [NeZero m]
    (S : RootFlatSchedule Color Direction RootState m)
    (hLayer : S.layerBijective) (c : Color) :
    ∀ x : ZMod m × RootState, ∃ w : RootState, ∃ k : Nat,
      k < m ∧ (S.fullStep c)^[k] (0, w) = x := by
  intro x
  rcases x with ⟨t, w⟩
  let k : Nat := t.val
  rcases (prefixMap_bijective S hLayer c k).2 w with ⟨w0, hw0⟩
  refine ⟨w0, k, ZMod.val_lt t, ?_⟩
  rw [fullStep_iterate_zero_prefixMap, hw0]
  have hk : (k : ZMod m) = t := by
    exact ZMod.natCast_zmod_val t
  exact Prod.ext hk rfl

theorem fullStep_singleCycle_of_return
    {Color Direction RootState : Type*} {m : Nat} [NeZero m]
    (S : RootFlatSchedule Color Direction RootState m)
    (hLayer : S.layerBijective) {c : Color}
    (hReturn : IsSingleCycleMap (S.returnMap c)) :
    IsSingleCycleMap (S.fullStep c) := by
  exact single_cycle_of_periodic_return_cover
    (S := S.fullStep c) (base := fun w : RootState => (0, w))
    (R := S.returnMap c) (period := m)
    (fullStep_bijective S hLayer c)
    (fullStep_iterate_period_base S c)
    hReturn
    (fullStep_cover_from_base S hLayer c)

theorem fullStepsHamiltonian_of_return
    {Color Direction RootState : Type*} {m : Nat} [NeZero m]
    {S : RootFlatSchedule Color Direction RootState m}
    (hLayer : S.layerBijective)
    (hReturn : S.returnsSingleCycle) :
    S.fullStepsHamiltonian := by
  intro c
  exact fullStep_singleCycle_of_return S hLayer (hReturn c)

end RootFlatSchedule

structure RootFlatLayeredDecomposition
    (Color Direction RootState : Type*) (m : Nat) [NeZero m] where
  schedule : RootFlatSchedule Color Direction RootState m
  edgePartition : schedule.edgePartition
  colorHamiltonian : schedule.fullStepsHamiltonian

def RootFlatLayeredHamiltonDecomposition
    (Color Direction RootState : Type*) (m : Nat) [NeZero m] : Prop :=
  Nonempty (RootFlatLayeredDecomposition Color Direction RootState m)

structure RootFlatCertificate
    (Color Direction RootState : Type*) (m : Nat) [NeZero m] where
  schedule : RootFlatSchedule Color Direction RootState m
  rowLatin : schedule.rowLatin
  layerBijective : schedule.layerBijective
  returnsSingleCycle : schedule.returnsSingleCycle

def RootFlatReturnCriterion
    (Color Direction RootState : Type*) (m : Nat) [NeZero m] : Prop :=
  Nonempty (RootFlatCertificate Color Direction RootState m)

theorem rootFlatReturnCriterion_of_certificate
    {Color Direction RootState : Type*} {m : Nat} [NeZero m]
    (cert : RootFlatCertificate Color Direction RootState m) :
    RootFlatReturnCriterion Color Direction RootState m := by
  exact ⟨cert⟩

theorem rootFlatReturnCriterion_of_schedule
    {Color Direction RootState : Type*} {m : Nat} [NeZero m]
    {S : RootFlatSchedule Color Direction RootState m}
    (hRow : S.rowLatin) (hLayer : S.layerBijective)
    (hReturn : S.returnsSingleCycle) :
    RootFlatReturnCriterion Color Direction RootState m := by
  exact ⟨{
    schedule := S
    rowLatin := hRow
    layerBijective := hLayer
    returnsSingleCycle := hReturn
  }⟩

theorem rootFlatLayeredDecomposition_of_schedule
    {Color Direction RootState : Type*} {m : Nat} [NeZero m]
    {S : RootFlatSchedule Color Direction RootState m}
    (hRow : S.rowLatin) (hLayer : S.layerBijective)
    (hReturn : S.returnsSingleCycle) :
    RootFlatLayeredHamiltonDecomposition Color Direction RootState m := by
  exact ⟨{
    schedule := S
    edgePartition := S.edgePartition_of_rowLatin hRow
    colorHamiltonian := S.fullStepsHamiltonian_of_return hLayer hReturn
  }⟩

theorem rootFlatLayeredDecomposition_of_certificate
    {Color Direction RootState : Type*} {m : Nat} [NeZero m]
    (cert : RootFlatCertificate Color Direction RootState m) :
    RootFlatLayeredHamiltonDecomposition Color Direction RootState m :=
  rootFlatLayeredDecomposition_of_schedule
    cert.rowLatin cert.layerBijective cert.returnsSingleCycle

end Shared
