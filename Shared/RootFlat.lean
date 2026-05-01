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

end RootFlatSchedule

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

end Shared
