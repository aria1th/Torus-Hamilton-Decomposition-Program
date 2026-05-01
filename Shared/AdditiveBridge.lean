import Shared.RootFlat
import Shared.Monodromy

namespace Shared

def composeRowDirection {Color Direction : Type*}
    (dir : Color → Direction) (kappa : Direction → Direction) :
    Color → Direction :=
  fun c => kappa (dir c)

theorem composeRowDirection_bijective {Color Direction : Type*}
    (dir : Color → Direction) (kappa : Direction → Direction)
    (hdir : Function.Bijective dir)
    (hkappa : Function.Bijective kappa) :
    Function.Bijective (composeRowDirection dir kappa) := by
  exact hkappa.comp hdir

theorem rowLatin_of_stateDirectionPermutation
    {State Color Direction : Type*}
    (dir : State → Color → Direction)
    (kappa : State → Direction → Direction)
    (hdir : ∀ s : State, Function.Bijective (dir s))
    (hkappa : ∀ s : State, Function.Bijective (kappa s)) :
    ∀ s : State, Function.Bijective fun c : Color => kappa s (dir s c) := by
  intro s
  exact composeRowDirection_bijective (dir s) (kappa s) (hdir s) (hkappa s)

def reindexRootFlatDirections
    {Color Direction RootState : Type*} {m : Nat}
    (S : RootFlatSchedule Color Direction RootState m)
    (kappa : ZMod m → RootState → Direction → Direction) :
    RootFlatSchedule Color Direction RootState m where
  dir := fun t w c => kappa t w (S.dir t w c)
  step := S.step

theorem reindexRootFlatDirections_rowLatin
    {Color Direction RootState : Type*} {m : Nat}
    (S : RootFlatSchedule Color Direction RootState m)
    (kappa : ZMod m → RootState → Direction → Direction)
    (hrow : S.rowLatin)
    (hkappa : ∀ t w, Function.Bijective (kappa t w)) :
    (reindexRootFlatDirections S kappa).rowLatin := by
  intro t w
  exact composeRowDirection_bijective
    (fun c : Color => S.dir t w c)
    (kappa t w)
    (hrow t w)
    (hkappa t w)

end Shared
