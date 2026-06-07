import EvenV11.RootFlatCycleData
import EvenV11.LowD7M4Finite
import EvenV11.LowD7M6Finite
import Shared.Monodromy

/-!
# Hard slots H3/H4: transporting generated D7 checks to `RootFlatCycleData`

This module is a deliberately transitional bridge.  It still reuses the trusted
finite audit blobs for `D₇(4)` and `D₇(6)`, but it does **not** expose their final
certificate theorems directly.  Instead it transports the generated schedules
through `rootIndexEquiv` and packages the result in the paper-facing
`RootFlatCycle.RootFlatCycleData 6 m` interface.

Why this matters: the main proof spine now asks for the structural RF1/RF2/RF3
handoff.  The code below gives a precise, type-level target for replacing the
finite blob by the paper two-rail relay proof one lemma at a time.

Written without a local `lake build`; minor namespace/simp repairs may be needed.
-/

namespace EvenV11
namespace V28Hard
namespace D7FiniteToCycleData

open Shared
open StandardRootFlatLift

namespace Transport

/-- Transport bijectivity across a conjugacy by an equivalence. -/
theorem bijective_of_equiv_conj {α β : Type*}
    (e : α ≃ β) (f : α → α) (g : β → β)
    (hf : Function.Bijective f)
    (hconj : ∀ x : α, e (f x) = g (e x)) :
    Function.Bijective g := by
  constructor
  · intro y₁ y₂ hy
    rcases e.surjective y₁ with ⟨x₁, rfl⟩
    rcases e.surjective y₂ with ⟨x₂, rfl⟩
    have hx : f x₁ = f x₂ := by
      apply e.injective
      simpa [hconj] using hy
    exact congrArg e (hf.1 hx)
  · intro y
    rcases e.surjective y with ⟨x, rfl⟩
    rcases hf.2 x with ⟨x₀, hx₀⟩
    refine ⟨e x₀, ?_⟩
    simpa [hconj] using congrArg e hx₀

/-- Transport a folded first-return map across pointwise layer conjugacies. -/
theorem returnMap_conj_of_layerMap_conj
    {Color Direction α β : Type*} {m : Nat} [NeZero m]
    (e : α ≃ β)
    (Sα : RootFlatSchedule Color Direction α m)
    (Sβ : RootFlatSchedule Color Direction β m)
    (hLayer : ∀ t c x,
      e (Sα.layerMap t c x) = Sβ.layerMap t c (e x)) :
    ∀ c x, e (Sα.returnMap c x) = Sβ.returnMap c (e x) := by
  intro c x
  simp [RootFlatSchedule.returnMap]
  generalize hts : List.range m = ts
  revert x
  induction ts with
  | nil =>
      intro x
      simp
  | cons t ts ih =>
      intro x
      simp [List.foldl]
      calc
        e (ts.foldl (fun x t => Sα.layerMap (t : ZMod m) c x)
            (Sα.layerMap (t : ZMod m) c x))
            = ts.foldl (fun y t => Sβ.layerMap (t : ZMod m) c y)
                (e (Sα.layerMap (t : ZMod m) c x)) := by
                simpa using ih (Sα.layerMap (t : ZMod m) c x)
        _ = ts.foldl (fun y t => Sβ.layerMap (t : ZMod m) c y)
                (Sβ.layerMap (t : ZMod m) c (e x)) := by
                rw [hLayer]

/-- The orientation expected by `Shared.single_cycle_of_equiv_conj`. -/
theorem returnMap_symm_conj_of_layerMap_conj
    {Color Direction α β : Type*} {m : Nat} [NeZero m]
    (e : α ≃ β)
    (Sα : RootFlatSchedule Color Direction α m)
    (Sβ : RootFlatSchedule Color Direction β m)
    (hLayer : ∀ t c x,
      e (Sα.layerMap t c x) = Sβ.layerMap t c (e x)) :
    ∀ c x, e.symm (Sβ.returnMap c (e x)) = Sα.returnMap c x := by
  intro c x
  apply e.injective
  simpa using
    (returnMap_conj_of_layerMap_conj e Sα Sβ hLayer c x).symm

end Transport

/-! ## `D₇(4)` finite schedule transported to standard root-flat cycle data -/

namespace M4

abbrev StdState := StandardRootFlatLift.RootState 6 4

/-- Pull the generated direction table back to the standard root section. -/
def dir (t : ZMod 4) (w : StdState) (c : TorusColor 7) : TorusDirection 7 :=
  LowD7M4Finite.dir t (LowD7M4Finite.rootIndexEquiv.symm w) c

/-- The generated and standard schedules have conjugate layer maps. -/
theorem layerMap_conj (t : ZMod 4) (c : TorusColor 7)
    (x : LowD7M4Finite.RootState) :
    LowD7M4Finite.rootIndexEquiv
      (LowD7M4Finite.schedule.layerMap t c x) =
    (RootFlatCycle.schedule dir).layerMap t c
      (LowD7M4Finite.rootIndexEquiv x) := by
  simpa [RootFlatSchedule.layerMap, LowD7M4Finite.schedule,
    RootFlatCycle.schedule, dir]
    using LowD7M4Finite.step_rootStep
      (LowD7M4Finite.dir t x c) x

/-- RF1 transported from the generated row table. -/
theorem rowLatin : (RootFlatCycle.schedule dir).rowLatin := by
  intro t w
  have h := LowD7M4Finite.schedule_rowLatin t
    (LowD7M4Finite.rootIndexEquiv.symm w)
  simpa [RootFlatSchedule.rowLatin, RootFlatCycle.schedule, dir]
    using h

/-- RF2 transported across `rootIndexEquiv`. -/
theorem layerBijective : (RootFlatCycle.schedule dir).layerBijective := by
  intro t c
  refine Transport.bijective_of_equiv_conj
    LowD7M4Finite.rootIndexEquiv
    (LowD7M4Finite.schedule.layerMap t c)
    ((RootFlatCycle.schedule dir).layerMap t c)
    (LowD7M4Finite.schedule_layerBijective t c)
    ?_
  intro x
  exact layerMap_conj t c x

/-- First-return conjugacy for the generated and standard D7(4) schedules. -/
theorem returnMap_symm_conj (c : TorusColor 7)
    (x : LowD7M4Finite.RootState) :
    LowD7M4Finite.rootIndexEquiv.symm
      ((RootFlatCycle.schedule dir).returnMap c
        (LowD7M4Finite.rootIndexEquiv x)) =
    LowD7M4Finite.schedule.returnMap c x :=
  Transport.returnMap_symm_conj_of_layerMap_conj
    LowD7M4Finite.rootIndexEquiv
    LowD7M4Finite.schedule
    (RootFlatCycle.schedule dir)
    (fun t c x => layerMap_conj t c x)
    c x

/-- RF3 transported from the generated single-cycle checks. -/
theorem returnsSingleCycle : (RootFlatCycle.schedule dir).returnsSingleCycle := by
  intro c
  refine Shared.single_cycle_of_equiv_conj
    LowD7M4Finite.rootIndexEquiv
    ((RootFlatCycle.schedule dir).returnMap c)
    (LowD7M4Finite.schedule.returnMap c)
    (LowD7M4Finite.schedule_returnsSingleCycle c)
    ?_
  intro x
  exact returnMap_symm_conj c x

/-- The generated D7(4) audit, but exposed as structural RF1/RF2/RF3 data. -/
def cycleData : RootFlatCycle.RootFlatCycleData 6 4 where
  dir := dir
  rowLatin := rowLatin
  layerBijective := layerBijective
  returnsSingleCycle := returnsSingleCycle

theorem nonempty_cycleData : Nonempty (RootFlatCycle.RootFlatCycleData 6 4) :=
  ⟨cycleData⟩

theorem finalLowD7M4RootFlatCertificateFamily :
    FinalLowD7M4RootFlatCertificateFamily :=
  RootFlatCycle.finalLowD7M4RootFlatCertificateFamily_of_cycleData cycleData

end M4

/-! ## `D₇(6)` finite schedule transported to standard root-flat cycle data -/

namespace M6

abbrev StdState := StandardRootFlatLift.RootState 6 6

def dir (t : ZMod 6) (w : StdState) (c : TorusColor 7) : TorusDirection 7 :=
  LowD7M6Finite.dir t (LowD7M6Finite.rootIndexEquiv.symm w) c

theorem layerMap_conj (t : ZMod 6) (c : TorusColor 7)
    (x : LowD7M6Finite.RootState) :
    LowD7M6Finite.rootIndexEquiv
      (LowD7M6Finite.schedule.layerMap t c x) =
    (RootFlatCycle.schedule dir).layerMap t c
      (LowD7M6Finite.rootIndexEquiv x) := by
  simpa [RootFlatSchedule.layerMap, LowD7M6Finite.schedule,
    RootFlatCycle.schedule, dir]
    using LowD7M6Finite.step_rootStep
      (LowD7M6Finite.dir t x c) x

theorem rowLatin : (RootFlatCycle.schedule dir).rowLatin := by
  intro t w
  have h := LowD7M6Finite.schedule_rowLatin t
    (LowD7M6Finite.rootIndexEquiv.symm w)
  simpa [RootFlatSchedule.rowLatin, RootFlatCycle.schedule, dir]
    using h

theorem layerBijective : (RootFlatCycle.schedule dir).layerBijective := by
  intro t c
  refine Transport.bijective_of_equiv_conj
    LowD7M6Finite.rootIndexEquiv
    (LowD7M6Finite.schedule.layerMap t c)
    ((RootFlatCycle.schedule dir).layerMap t c)
    (LowD7M6Finite.schedule_layerBijective t c)
    ?_
  intro x
  exact layerMap_conj t c x

theorem returnMap_symm_conj (c : TorusColor 7)
    (x : LowD7M6Finite.RootState) :
    LowD7M6Finite.rootIndexEquiv.symm
      ((RootFlatCycle.schedule dir).returnMap c
        (LowD7M6Finite.rootIndexEquiv x)) =
    LowD7M6Finite.schedule.returnMap c x :=
  Transport.returnMap_symm_conj_of_layerMap_conj
    LowD7M6Finite.rootIndexEquiv
    LowD7M6Finite.schedule
    (RootFlatCycle.schedule dir)
    (fun t c x => layerMap_conj t c x)
    c x

theorem returnsSingleCycle : (RootFlatCycle.schedule dir).returnsSingleCycle := by
  intro c
  refine Shared.single_cycle_of_equiv_conj
    LowD7M6Finite.rootIndexEquiv
    ((RootFlatCycle.schedule dir).returnMap c)
    (LowD7M6Finite.schedule.returnMap c)
    (LowD7M6Finite.schedule_returnsSingleCycle c)
    ?_
  intro x
  exact returnMap_symm_conj c x

def cycleData : RootFlatCycle.RootFlatCycleData 6 6 where
  dir := dir
  rowLatin := rowLatin
  layerBijective := layerBijective
  returnsSingleCycle := returnsSingleCycle

theorem nonempty_cycleData : Nonempty (RootFlatCycle.RootFlatCycleData 6 6) :=
  ⟨cycleData⟩

theorem finalLowD7M6RootFlatCertificateFamily :
    FinalLowD7M6RootFlatCertificateFamily :=
  RootFlatCycle.finalLowD7M6RootFlatCertificateFamily_of_cycleData cycleData

end M6

end D7FiniteToCycleData
end V28Hard
end EvenV11
