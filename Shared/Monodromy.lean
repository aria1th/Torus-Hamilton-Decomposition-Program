import Shared.ReturnLift

namespace Shared

def skewProductMap {Base Fiber : Type*}
    (baseStep : Base → Base) (fiberStep : Base → Fiber → Fiber) :
    Base × Fiber → Base × Fiber :=
  fun x => (baseStep x.1, fiberStep x.1 x.2)

theorem skewProductMap_bijective {Base Fiber : Type*}
    (baseStep : Base → Base) (fiberStep : Base → Fiber → Fiber)
    (hbase : Function.Bijective baseStep)
    (hfiber : ∀ u : Base, Function.Bijective (fiberStep u)) :
    Function.Bijective (skewProductMap baseStep fiberStep) := by
  constructor
  · intro x y hxy
    rcases x with ⟨ux, vx⟩
    rcases y with ⟨uy, vy⟩
    have hu : ux = uy := hbase.1 (congrArg Prod.fst hxy)
    subst uy
    have hv : vx = vy := (hfiber ux).1 (congrArg Prod.snd hxy)
    exact Prod.ext rfl hv
  · intro y
    rcases y with ⟨u', v'⟩
    rcases hbase.2 u' with ⟨u, hu⟩
    rcases (hfiber u).2 v' with ⟨v, hv⟩
    exact ⟨(u, v), Prod.ext hu hv⟩

def sectionReturn {Base Fiber : Type*}
    (S : Base × Fiber → Base × Fiber) (base : Base) (period : Nat) :
    Fiber → Fiber :=
  fun v => (S^[period] (base, v)).2

theorem single_cycle_of_skewProduct_monodromy
    {Base Fiber : Type*} (S : Base × Fiber → Base × Fiber)
    (base : Base) (period : Nat)
    (hS : Function.Bijective S)
    (hreturnBase : ∀ v : Fiber, (S^[period] (base, v)).1 = base)
    (hmonodromy : IsSingleCycleMap (sectionReturn S base period))
    (hcover : ∀ x : Base × Fiber, ∃ v : Fiber, ∃ k : Nat,
      k < period ∧ S^[k] (base, v) = x) :
    IsSingleCycleMap S := by
  have hreturn :
      ∀ v : Fiber,
        S^[period] (base, v) =
          (base, sectionReturn S base period v) := by
    intro v
    exact Prod.ext (hreturnBase v) rfl
  exact single_cycle_of_periodic_return_cover
    (S := S) (base := fun v : Fiber => (base, v))
    (R := sectionReturn S base period) (period := period)
    hS hreturn hmonodromy hcover

end Shared
