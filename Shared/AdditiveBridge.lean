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

def skewProductLayerMap {Base Fiber : Type*}
    (baseStep : Base → Base) (fiberStep : Base → Fiber → Fiber) :
    Base × Fiber → Base × Fiber :=
  skewProductMap baseStep fiberStep

theorem skewProductLayerMap_bijective {Base Fiber : Type*}
    (baseStep : Base → Base) (fiberStep : Base → Fiber → Fiber)
    (hbase : Function.Bijective baseStep)
    (hfiber : ∀ u : Base, Function.Bijective (fiberStep u)) :
    Function.Bijective (skewProductLayerMap baseStep fiberStep) := by
  exact skewProductMap_bijective baseStep fiberStep hbase hfiber

theorem localBridge_rowLatin_and_layerBijective
    {Base Fiber Color Direction : Type*}
    (dir : Base × Fiber → Color → Direction)
    (kappa : Base × Fiber → Direction → Direction)
    (baseStep : Color → Base → Base)
    (fiberStep : Color → Base → Fiber → Fiber)
    (hdir : ∀ s : Base × Fiber, Function.Bijective (dir s))
    (hkappa : ∀ s : Base × Fiber, Function.Bijective (kappa s))
    (hbase : ∀ c : Color, Function.Bijective (baseStep c))
    (hfiber : ∀ c : Color, ∀ u : Base, Function.Bijective (fiberStep c u)) :
    (∀ s : Base × Fiber,
        Function.Bijective fun c : Color => kappa s (dir s c)) ∧
      (∀ c : Color,
        Function.Bijective (skewProductLayerMap (baseStep c) (fiberStep c))) := by
  constructor
  · exact rowLatin_of_stateDirectionPermutation dir kappa hdir hkappa
  · intro c
    exact skewProductLayerMap_bijective
      (baseStep c) (fiberStep c) (hbase c) (hfiber c)

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
