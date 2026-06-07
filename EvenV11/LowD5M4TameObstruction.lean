import EvenV11.LowD5M4RibbonInterface

/-!
# D5(4) tame-coordinate obstruction

This records why the H2 realization cannot be closed by the coordinate chart
`((Q4 x Y) x Z) ~= (ZMod 4)^4`.  In that chart, color `0` has a return at one
source whose displacement needs five positive root steps, but a D5(4) first
return has only four layers.  Thus the active H2 target must use the wild
return-section reindexing `e` from the ribbon realization.
-/

namespace EvenV11
namespace LowD5M4TameObstruction

open Shared
open LowD5M4Structural
open LowD5M4RibbonInterface

/-- The tame coordinate chart, kept here only as a negative control. -/
def tameSeedRootEquiv : Seed ≃ RootState where
  toFun x := fun i =>
    match i with
    | 0 => x.1.1.1
    | 1 => x.1.1.2
    | 2 => x.1.2
    | 3 => x.2
  invFun w := (((w 0, w 1), w 2), w 3)
  left_inv := by
    intro x
    rcases x with ⟨⟨⟨q0, q1⟩, y⟩, z⟩
    rfl
  right_inv := by
    intro w
    funext i
    fin_cases i <;> rfl

def tamePaperReturn (c : TorusColor 5) : RootState → RootState :=
  fun w => tameSeedRootEquiv (LowD5M4.fullReturn c (tameSeedRootEquiv.symm w))

def obstructionSource : RootState :=
  tameSeedRootEquiv
    ((((0 : ZMod 4), (3 : ZMod 4)), (0 : ZMod 4)), (0 : ZMod 4))

theorem no_four_rootSteps_to_tamePaperReturn_color0 :
    ∀ d0 d1 d2 d3 : TorusDirection 5,
      LowD5M4Schedule.rootStep d3
          (LowD5M4Schedule.rootStep d2
            (LowD5M4Schedule.rootStep d1
              (LowD5M4Schedule.rootStep d0 obstructionSource))) ≠
        tamePaperReturn (0 : TorusColor 5) obstructionSource := by
  decide

theorem returnMap_tamePaperReturn_color0_source_ne
    (dir : ZMod 4 → RootState → TorusColor 5 → TorusDirection 5) :
    (LowD5M4Schedule.schedule dir).returnMap (0 : TorusColor 5)
        obstructionSource ≠
      tamePaperReturn (0 : TorusColor 5) obstructionSource := by
  intro hReturn
  let x1 :=
    LowD5M4Schedule.rootStep
      (dir (0 : ZMod 4) obstructionSource (0 : TorusColor 5))
      obstructionSource
  let x2 :=
    LowD5M4Schedule.rootStep
      (dir (1 : ZMod 4) x1 (0 : TorusColor 5)) x1
  let x3 :=
    LowD5M4Schedule.rootStep
      (dir (2 : ZMod 4) x2 (0 : TorusColor 5)) x2
  have hSteps :
      LowD5M4Schedule.rootStep
          (dir (3 : ZMod 4) x3 (0 : TorusColor 5)) x3 =
        tamePaperReturn (0 : TorusColor 5) obstructionSource := by
    simpa [Shared.RootFlatSchedule.returnMap,
      Shared.RootFlatSchedule.layerMap, LowD5M4Schedule.schedule,
      List.range, x1, x2, x3] using hReturn
  exact no_four_rootSteps_to_tamePaperReturn_color0
    (dir (0 : ZMod 4) obstructionSource (0 : TorusColor 5))
    (dir (1 : ZMod 4) x1 (0 : TorusColor 5))
    (dir (2 : ZMod 4) x2 (0 : TorusColor 5))
    (dir (3 : ZMod 4) x3 (0 : TorusColor 5))
    hSteps

theorem returnMap_ne_tamePaperReturn_color0
    (dir : ZMod 4 → RootState → TorusColor 5 → TorusDirection 5) :
    (LowD5M4Schedule.schedule dir).returnMap (0 : TorusColor 5) ≠
      tamePaperReturn (0 : TorusColor 5) := by
  intro h
  exact returnMap_tamePaperReturn_color0_source_ne dir
    (congrFun h obstructionSource)

theorem not_returnMapConj_tameSeedRootEquiv
    (rows : PhysicalLayerRows) :
    ¬ PhysicalRowsReturnMapConjGoal rows tameSeedRootEquiv := by
  intro hConj
  exact returnMap_tamePaperReturn_color0_source_ne
    (dirOfRowEquiv rows.row) (by
      simpa [PhysicalRowsReturnMapConjGoal, schedule, tamePaperReturn]
        using hConj (0 : TorusColor 5) obstructionSource)

end LowD5M4TameObstruction
end EvenV11
