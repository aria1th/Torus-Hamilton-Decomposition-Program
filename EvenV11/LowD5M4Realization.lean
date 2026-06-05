import EvenV11.D54ResetData
import EvenV11.LowD5M4Structural
import EvenV11.Switching

/-!
# D5(4) paper realization interface

This file fixes the paper-coordinate identification used for the D5(4) parity
reset seed and restates the remaining layer-row realization as a direct return
map equality.
-/

namespace EvenV11
namespace LowD5M4Realization

open Shared
open LowD5M4Structural

abbrev RootState := LowD5M4Structural.RootState
abbrev Seed := LowD5M4Structural.Seed
abbrev ResetPortBaseRow :=
  ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5

/-- The paper coordinate identification
`((q0,q1),y),z : (ZMod 4)^4` as a root-flat state `Fin 4 -> ZMod 4`. -/
def seedRootEquiv : Seed ≃ RootState where
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

/-- The return map prescribed by the paper's D5(4) parity-reset seed, transported
to the root-flat coordinates used by `LowD5M4Schedule`. -/
def paperReturn (c : TorusColor 5) : RootState → RootState :=
  fun w => seedRootEquiv (LowD5M4.fullReturn c (seedRootEquiv.symm w))

/-- Terminal `Q4` coordinates inside the standard root-flat coordinates. -/
def qCoord (w : RootState) : LowD5M4.Q4 := (w 0, w 1)

/-- The first unit-carry coordinate from the paper. -/
def yCoord (w : RootState) : LowD5M4.Y := w 2

/-- The final unit-carry coordinate from the paper. -/
def zCoord (w : RootState) : LowD5M4.Z := w 3

/-- Repack paper coordinates as a standard root-flat state. -/
def rootOfCoords (q : LowD5M4.Q4) (y : LowD5M4.Y) (z : LowD5M4.Z) :
    RootState :=
  seedRootEquiv ((q, y), z)

@[simp] theorem seedRootEquiv_symm_eq_coords (w : RootState) :
    seedRootEquiv.symm w = ((qCoord w, yCoord w), zCoord w) :=
  rfl

@[simp] theorem qCoord_rootOfCoords
    (q : LowD5M4.Q4) (y : LowD5M4.Y) (z : LowD5M4.Z) :
    qCoord (rootOfCoords q y z) = q :=
  rfl

@[simp] theorem yCoord_rootOfCoords
    (q : LowD5M4.Q4) (y : LowD5M4.Y) (z : LowD5M4.Z) :
    yCoord (rootOfCoords q y z) = y :=
  rfl

@[simp] theorem zCoord_rootOfCoords
    (q : LowD5M4.Q4) (y : LowD5M4.Y) (z : LowD5M4.Z) :
    zCoord (rootOfCoords q y z) = z :=
  rfl

/-- Paper return in root-flat coordinates: first apply the paper base return on
`Q4 x Y`, then add the final point carry in `Z`. -/
theorem paperReturn_apply (c : TorusColor 5) (w : RootState) :
    paperReturn c w =
      rootOfCoords
        (LowD5M4.baseReturn c (qCoord w, yCoord w)).1
        (LowD5M4.baseReturn c (qCoord w, yCoord w)).2
        (zCoord w +
          EvenV11.UnitCarry.pointCarry
            (LowD5M4.liftSite c) (1 : ZMod 4) (qCoord w, yCoord w)) :=
  rfl

theorem paperReturn_apply_zero (w : RootState) :
    paperReturn 0 w =
      rootOfCoords
        (LowD5M4.F TerminalSymbol.F0 (qCoord w))
        (yCoord w +
          EvenV11.UnitCarry.pointCarry LowD5M4.p0 (1 : ZMod 4) (qCoord w))
        (zCoord w +
          EvenV11.UnitCarry.pointCarry LowD5M4.a0 (1 : ZMod 4)
            (qCoord w, yCoord w)) := by
  simp [paperReturn_apply, LowD5M4.baseReturn, LowD5M4.T,
    LowD5M4.liftSite, EvenV11.UnitCarry.additiveSkewMap,
    Shared.skewProductMap]

theorem paperReturn_apply_one (w : RootState) :
    paperReturn 1 w =
      rootOfCoords
        (LowD5M4.F TerminalSymbol.F1 (qCoord w))
        (yCoord w +
          EvenV11.UnitCarry.pointCarry LowD5M4.p1 (1 : ZMod 4) (qCoord w))
        (zCoord w +
          EvenV11.UnitCarry.pointCarry LowD5M4.a1 (1 : ZMod 4)
            (qCoord w, yCoord w)) := by
  simp [paperReturn_apply, LowD5M4.baseReturn, LowD5M4.T,
    LowD5M4.liftSite, EvenV11.UnitCarry.additiveSkewMap,
    Shared.skewProductMap]

theorem paperReturn_apply_two (w : RootState) :
    paperReturn 2 w =
      rootOfCoords
        (LowD5M4.F TerminalSymbol.F2 (qCoord w))
        (yCoord w +
          EvenV11.UnitCarry.pointCarry LowD5M4.p2 (1 : ZMod 4) (qCoord w))
        (zCoord w +
          EvenV11.UnitCarry.pointCarry LowD5M4.a2 (1 : ZMod 4)
            (qCoord w, yCoord w)) := by
  simp [paperReturn_apply, LowD5M4.baseReturn, LowD5M4.T,
    LowD5M4.liftSite, EvenV11.UnitCarry.additiveSkewMap,
    Shared.skewProductMap]

theorem paperReturn_apply_three (w : RootState) :
    paperReturn 3 w =
      rootOfCoords
        (if yCoord w = 0 then LowD5M4.F TerminalSymbol.F0 (qCoord w)
          else qCoord w)
        (yCoord w + 1)
        (zCoord w +
          EvenV11.UnitCarry.pointCarry LowD5M4.a3 (1 : ZMod 4)
            (qCoord w, yCoord w)) := by
  simp [paperReturn_apply, LowD5M4.baseReturn, LowD5M4.P0,
    LowD5M4.liftSite]

theorem paperReturn_apply_four (w : RootState) :
    paperReturn 4 w =
      rootOfCoords
        (if yCoord w = 1 then LowD5M4.F TerminalSymbol.F0 (qCoord w)
          else if yCoord w = 2 then LowD5M4.F TerminalSymbol.F2 (qCoord w)
          else if yCoord w = 3 then LowD5M4.F TerminalSymbol.F1 (qCoord w)
          else qCoord w)
        (yCoord w + 1)
        (zCoord w +
          EvenV11.UnitCarry.pointCarry LowD5M4.a4 (1 : ZMod 4)
            (qCoord w, yCoord w)) := by
  simp [paperReturn_apply, LowD5M4.baseReturn, LowD5M4.P1,
    LowD5M4.liftSite]

theorem paperReturn_singleCycle (c : TorusColor 5) :
    Shared.IsSingleCycleMap (paperReturn c) := by
  refine Shared.single_cycle_of_equiv_conj seedRootEquiv
    (paperReturn c)
    (LowD5M4.fullReturn c)
    (LowD5M4.fullReturn_singleCycle c) ?_
  intro x
  simp [paperReturn]

/-- The remaining paper-faithful realization obligation: the layer-row schedule
has exactly the transported D5(4) paper return maps. -/
def ReturnMapRealizationGoal
    (dir : ZMod 4 → RootState → TorusColor 5 → TorusDirection 5) : Prop :=
  ∀ c : TorusColor 5, ∀ w : RootState,
    (LowD5M4Schedule.schedule dir).returnMap c w = paperReturn c w

/-- The explicit four-layer return for `m = 4`, avoiding later proof scripts
having to unfold `List.range 4`. -/
def fourLayerReturn
    (dir : ZMod 4 → RootState → TorusColor 5 → TorusDirection 5)
    (c : TorusColor 5) : RootState → RootState :=
  fun w =>
    let S := LowD5M4Schedule.schedule dir
    S.layerMap (3 : ZMod 4) c
      (S.layerMap (2 : ZMod 4) c
        (S.layerMap (1 : ZMod 4) c
          (S.layerMap (0 : ZMod 4) c w)))

theorem returnMap_eq_fourLayerReturn
    (dir : ZMod 4 → RootState → TorusColor 5 → TorusDirection 5)
    (c : TorusColor 5) :
    (LowD5M4Schedule.schedule dir).returnMap c = fourLayerReturn dir c := by
  funext w
  rfl

/-- A calculation-friendly version of the paper realization goal. -/
def FourLayerRealizationGoal
    (dir : ZMod 4 → RootState → TorusColor 5 → TorusDirection 5) : Prop :=
  ∀ c : TorusColor 5, ∀ w : RootState,
    fourLayerReturn dir c w = paperReturn c w

theorem fourLayerReturn_eq_of_layerMap_steps
    (dir : ZMod 4 → RootState → TorusColor 5 → TorusDirection 5)
    (c : TorusColor 5) (w x1 x2 x3 x4 : RootState)
    (h0 :
      (LowD5M4Schedule.schedule dir).layerMap (0 : ZMod 4) c w = x1)
    (h1 :
      (LowD5M4Schedule.schedule dir).layerMap (1 : ZMod 4) c x1 = x2)
    (h2 :
      (LowD5M4Schedule.schedule dir).layerMap (2 : ZMod 4) c x2 = x3)
    (h3 :
      (LowD5M4Schedule.schedule dir).layerMap (3 : ZMod 4) c x3 = x4) :
    fourLayerReturn dir c w = x4 := by
  simp [fourLayerReturn, h0, h1, h2, h3]

/-- A layer-by-layer proof shape for the four-layer return calculation. The
intermediate states are functions of the starting root state, matching how the
paper computes the terminal word and the two unit-carry substitutions. -/
def FourLayerPathGoal
    (dir : ZMod 4 → RootState → TorusColor 5 → TorusDirection 5)
    (c : TorusColor 5) (target : RootState → RootState) : Prop :=
  ∃ x1 x2 x3 : RootState → RootState,
    ∀ w : RootState,
      (LowD5M4Schedule.schedule dir).layerMap (0 : ZMod 4) c w = x1 w ∧
      (LowD5M4Schedule.schedule dir).layerMap (1 : ZMod 4) c (x1 w) = x2 w ∧
      (LowD5M4Schedule.schedule dir).layerMap (2 : ZMod 4) c (x2 w) = x3 w ∧
      (LowD5M4Schedule.schedule dir).layerMap (3 : ZMod 4) c (x3 w) =
        target w

theorem fourLayerRealizationGoal_of_pathGoals
    (dir : ZMod 4 → RootState → TorusColor 5 → TorusDirection 5)
    (hPath : ∀ c : TorusColor 5, FourLayerPathGoal dir c (paperReturn c)) :
    FourLayerRealizationGoal dir := by
  intro c w
  rcases hPath c with ⟨x1, x2, x3, hsteps⟩
  rcases hsteps w with ⟨h0, h1, h2, h3⟩
  exact fourLayerReturn_eq_of_layerMap_steps
    dir c w (x1 w) (x2 w) (x3 w) (paperReturn c w) h0 h1 h2 h3

theorem returnMapRealizationGoal_of_fourLayer
    (dir : ZMod 4 → RootState → TorusColor 5 → TorusDirection 5)
    (h : FourLayerRealizationGoal dir) :
    ReturnMapRealizationGoal dir := by
  intro c w
  rw [returnMap_eq_fourLayerReturn]
  exact h c w

/-- Embed the terminal A2 color indices into the first three D5 colors. -/
def fin3ToFin5 (i : Fin 3) : Fin 5 :=
  ⟨i.val, Nat.lt_trans i.isLt (by decide : 3 < 5)⟩

/-- The standard root-flat direction realizing the terminal `a_i` move in the
stored `Q4` coordinates. The third terminal vertex is `a₂ = 0`, hence it is
represented by the inert fifth direction of the standard D5 lift. -/
def terminalStdDirection5 : Fin 3 → TorusDirection 5
  | 0 => 0
  | 1 => 1
  | 2 => 4

/-- The standard root-flat direction that increments the paper `Y` coordinate. -/
def liftYDirection5 : TorusDirection 5 := 2

/-- The standard root-flat direction that increments the paper `Z` coordinate. -/
def liftZDirection5 : TorusDirection 5 := 3

theorem rootStep_terminalStdDirection5_eq_rootOfCoords
    (i : Fin 3) (w : RootState) :
    LowD5M4Schedule.rootStep (terminalStdDirection5 i) w =
      rootOfCoords (qCoord w + terminalVertex (m := 4) i) (yCoord w) (zCoord w) := by
  ext j
  fin_cases j <;>
    fin_cases i <;>
    simp [qCoord, yCoord, zCoord, rootOfCoords, seedRootEquiv,
      terminalStdDirection5, terminalVertex, LowD5M4Schedule.rootStep,
      TerminalA2LowMod.a0, TerminalA2LowMod.a1, TerminalA2LowMod.a2,
      TerminalA2LowMod.q]

theorem qCoord_rootStep_terminalStdDirection5
    (i : Fin 3) (w : RootState) :
    qCoord (LowD5M4Schedule.rootStep (terminalStdDirection5 i) w) =
      qCoord w + terminalVertex (m := 4) i := by
  rw [rootStep_terminalStdDirection5_eq_rootOfCoords]
  rfl

theorem yCoord_rootStep_terminalStdDirection5
    (i : Fin 3) (w : RootState) :
    yCoord (LowD5M4Schedule.rootStep (terminalStdDirection5 i) w) =
      yCoord w := by
  rw [rootStep_terminalStdDirection5_eq_rootOfCoords]
  rfl

theorem zCoord_rootStep_terminalStdDirection5
    (i : Fin 3) (w : RootState) :
    zCoord (LowD5M4Schedule.rootStep (terminalStdDirection5 i) w) =
      zCoord w := by
  rw [rootStep_terminalStdDirection5_eq_rootOfCoords]
  rfl

theorem rootStep_liftYDirection5_eq_rootOfCoords (w : RootState) :
    LowD5M4Schedule.rootStep liftYDirection5 w =
      rootOfCoords (qCoord w) (yCoord w + 1) (zCoord w) := by
  ext j
  fin_cases j <;>
    simp [qCoord, yCoord, zCoord, rootOfCoords, seedRootEquiv,
      liftYDirection5, LowD5M4Schedule.rootStep]

theorem qCoord_rootStep_liftYDirection5 (w : RootState) :
    qCoord (LowD5M4Schedule.rootStep liftYDirection5 w) =
      qCoord w := by
  rw [rootStep_liftYDirection5_eq_rootOfCoords]
  rfl

theorem yCoord_rootStep_liftYDirection5 (w : RootState) :
    yCoord (LowD5M4Schedule.rootStep liftYDirection5 w) =
      yCoord w + 1 := by
  rw [rootStep_liftYDirection5_eq_rootOfCoords]
  rfl

theorem zCoord_rootStep_liftYDirection5 (w : RootState) :
    zCoord (LowD5M4Schedule.rootStep liftYDirection5 w) =
      zCoord w := by
  rw [rootStep_liftYDirection5_eq_rootOfCoords]
  rfl

theorem rootStep_liftZDirection5_eq_rootOfCoords (w : RootState) :
    LowD5M4Schedule.rootStep liftZDirection5 w =
      rootOfCoords (qCoord w) (yCoord w) (zCoord w + 1) := by
  ext j
  fin_cases j <;>
    simp [qCoord, yCoord, zCoord, rootOfCoords, seedRootEquiv,
      liftZDirection5, LowD5M4Schedule.rootStep]

theorem qCoord_rootStep_liftZDirection5 (w : RootState) :
    qCoord (LowD5M4Schedule.rootStep liftZDirection5 w) =
      qCoord w := by
  rw [rootStep_liftZDirection5_eq_rootOfCoords]
  rfl

theorem yCoord_rootStep_liftZDirection5 (w : RootState) :
    yCoord (LowD5M4Schedule.rootStep liftZDirection5 w) =
      yCoord w := by
  rw [rootStep_liftZDirection5_eq_rootOfCoords]
  rfl

theorem zCoord_rootStep_liftZDirection5 (w : RootState) :
    zCoord (LowD5M4Schedule.rootStep liftZDirection5 w) =
      zCoord w + 1 := by
  rw [rootStep_liftZDirection5_eq_rootOfCoords]
  rfl

/-- The terminal paper row word transported through the standard root-flat
direction chart. Colors `0,1,2` use the terminal `Q4` directions `0,1,4`;
colors `3,4` are the `Y` and `Z` lift directions. -/
def terminalStdRowTargetIndex5 (row : TerminalRow) :
    TorusColor 5 → TorusDirection 5
  | 0 => terminalStdDirection5 (terminalRowEquiv row 0)
  | 1 => terminalStdDirection5 (terminalRowEquiv row 1)
  | 2 => terminalStdDirection5 (terminalRowEquiv row 2)
  | 3 => liftYDirection5
  | 4 => liftZDirection5

/-- Inverse of `terminalStdRowTargetIndex5`. -/
def terminalStdRowSourceIndex5 (row : TerminalRow) :
    TorusDirection 5 → TorusColor 5
  | 0 => fin3ToFin5 ((terminalRowEquiv row).symm 0)
  | 1 => fin3ToFin5 ((terminalRowEquiv row).symm 1)
  | 2 => 3
  | 3 => 4
  | 4 => fin3ToFin5 ((terminalRowEquiv row).symm 2)

/-- The standard-lift row equivalence induced by the terminal A2 row word. This
is the row to use when composing with `LowD5M4Schedule.rootStep`; the older
`terminalRowEquiv5` below only records the paper's raw row-word indices. -/
def terminalStdRowEquiv5 (row : TerminalRow) :
    TorusColor 5 ≃ TorusDirection 5 where
  toFun := terminalStdRowTargetIndex5 row
  invFun := terminalStdRowSourceIndex5 row
  left_inv := by
    intro c
    cases row <;> fin_cases c <;> rfl
  right_inv := by
    intro d
    cases row <;> fin_cases d <;> rfl

@[simp] theorem terminalStdRowEquiv5_fin3
    (row : TerminalRow) (i : Fin 3) :
    terminalStdRowEquiv5 row (fin3ToFin5 i) =
      terminalStdDirection5 (terminalRowEquiv row i) := by
  fin_cases i <;> rfl

@[simp] theorem terminalStdRowEquiv5_three (row : TerminalRow) :
    terminalStdRowEquiv5 row 3 = liftYDirection5 :=
  rfl

@[simp] theorem terminalStdRowEquiv5_four (row : TerminalRow) :
    terminalStdRowEquiv5 row 4 = liftZDirection5 :=
  rfl

theorem rootStep_terminalStdRowEquiv5_fin3_eq_rootOfCoords
    (row : TerminalRow) (i : Fin 3) (w : RootState) :
    LowD5M4Schedule.rootStep
        (terminalStdRowEquiv5 row (fin3ToFin5 i)) w =
      rootOfCoords
        (qCoord w + terminalVertex (m := 4) (terminalRowEquiv row i))
        (yCoord w)
        (zCoord w) := by
  rw [terminalStdRowEquiv5_fin3]
  exact rootStep_terminalStdDirection5_eq_rootOfCoords
    (terminalRowEquiv row i) w

theorem qCoord_rootStep_terminalStdRowEquiv5_fin3
    (row : TerminalRow) (i : Fin 3) (w : RootState) :
    qCoord
        (LowD5M4Schedule.rootStep
          (terminalStdRowEquiv5 row (fin3ToFin5 i)) w) =
      qCoord w + terminalVertex (m := 4) (terminalRowEquiv row i) := by
  rw [rootStep_terminalStdRowEquiv5_fin3_eq_rootOfCoords]
  rfl

theorem yCoord_rootStep_terminalStdRowEquiv5_fin3
    (row : TerminalRow) (i : Fin 3) (w : RootState) :
    yCoord
        (LowD5M4Schedule.rootStep
          (terminalStdRowEquiv5 row (fin3ToFin5 i)) w) =
      yCoord w := by
  rw [rootStep_terminalStdRowEquiv5_fin3_eq_rootOfCoords]
  rfl

theorem zCoord_rootStep_terminalStdRowEquiv5_fin3
    (row : TerminalRow) (i : Fin 3) (w : RootState) :
    zCoord
        (LowD5M4Schedule.rootStep
          (terminalStdRowEquiv5 row (fin3ToFin5 i)) w) =
      zCoord w := by
  rw [rootStep_terminalStdRowEquiv5_fin3_eq_rootOfCoords]
  rfl

theorem rootStep_terminalStdRowEquiv5_three_eq_rootOfCoords
    (row : TerminalRow) (w : RootState) :
    LowD5M4Schedule.rootStep (terminalStdRowEquiv5 row 3) w =
      rootOfCoords (qCoord w) (yCoord w + 1) (zCoord w) := by
  rw [terminalStdRowEquiv5_three]
  exact rootStep_liftYDirection5_eq_rootOfCoords w

theorem rootStep_terminalStdRowEquiv5_four_eq_rootOfCoords
    (row : TerminalRow) (w : RootState) :
    LowD5M4Schedule.rootStep (terminalStdRowEquiv5 row 4) w =
      rootOfCoords (qCoord w) (yCoord w) (zCoord w + 1) := by
  rw [terminalStdRowEquiv5_four]
  exact rootStep_liftZDirection5_eq_rootOfCoords w

/-- Lift a terminal A2 row word to a five-color D5 row, leaving the two lift
directions fixed. This records the paper row-word indexing; the physical
standard-lift chart is supplied separately by `terminalStdDirection5`,
`liftYDirection5`, and `liftZDirection5`. -/
def terminalRowTargetIndex5 (row : TerminalRow) :
    TorusColor 5 → TorusDirection 5
  | 0 => fin3ToFin5 (terminalRowEquiv row 0)
  | 1 => fin3ToFin5 (terminalRowEquiv row 1)
  | 2 => fin3ToFin5 (terminalRowEquiv row 2)
  | 3 => 3
  | 4 => 4

/-- Inverse of `terminalRowTargetIndex5`. -/
def terminalRowSourceIndex5 (row : TerminalRow) :
    TorusDirection 5 → TorusColor 5
  | 0 => fin3ToFin5 ((terminalRowEquiv row).symm 0)
  | 1 => fin3ToFin5 ((terminalRowEquiv row).symm 1)
  | 2 => fin3ToFin5 ((terminalRowEquiv row).symm 2)
  | 3 => 3
  | 4 => 4

/-- The terminal A2 row word, lifted to a D5 row equivalence. -/
def terminalRowEquiv5 (row : TerminalRow) :
    TorusColor 5 ≃ TorusDirection 5 where
  toFun := terminalRowTargetIndex5 row
  invFun := terminalRowSourceIndex5 row
  left_inv := by
    intro c
    cases row <;> fin_cases c <;> rfl
  right_inv := by
    intro d
    cases row <;> fin_cases d <;> rfl

@[simp] theorem terminalRowEquiv5_zero (row : TerminalRow) :
    terminalRowEquiv5 row 0 = fin3ToFin5 (terminalRowEquiv row 0) :=
  rfl

@[simp] theorem terminalRowEquiv5_one (row : TerminalRow) :
    terminalRowEquiv5 row 1 = fin3ToFin5 (terminalRowEquiv row 1) :=
  rfl

@[simp] theorem terminalRowEquiv5_two (row : TerminalRow) :
    terminalRowEquiv5 row 2 = fin3ToFin5 (terminalRowEquiv row 2) :=
  rfl

@[simp] theorem terminalRowEquiv5_three (row : TerminalRow) :
    terminalRowEquiv5 row 3 = 3 :=
  rfl

@[simp] theorem terminalRowEquiv5_four (row : TerminalRow) :
    terminalRowEquiv5 row 4 = 4 :=
  rfl

/-- The paper's terminal row word, read at a triangle base point in `Q4` and
lifted to a five-entry row permutation. This is the terminal `A2` component
before the `Y` and `Z` reset switches are applied. -/
def terminalBaseRowEquiv5 (q : LowD5M4.Q4) :
    TorusColor 5 ≃ TorusDirection 5 :=
  terminalRowEquiv5 (terminalOmega q)

/-- The terminal row word read from the stored paper `Q4` coordinates. The final
physical layer-row construction may compose this with a layer-dependent chart;
this definition only records the paper row word itself. -/
def terminalBaseRowAtState (w : RootState) :
    TorusColor 5 ≃ TorusDirection 5 :=
  terminalBaseRowEquiv5 (qCoord w)

/-- The paper's terminal row word transported through the standard D5 root-step
direction chart. This is a row-level component, not yet the full physical
layer-row schedule with reset-port substitutions. -/
def terminalStdBaseRowEquiv5 (q : LowD5M4.Q4) :
    TorusColor 5 ≃ TorusDirection 5 :=
  terminalStdRowEquiv5 (terminalOmega q)

/-- The charted terminal row word read from the stored paper `Q4` coordinates. -/
def terminalStdBaseRowAtState (w : RootState) :
    TorusColor 5 ≃ TorusDirection 5 :=
  terminalStdBaseRowEquiv5 (qCoord w)

/-- The triangle base `z - a_i` from the paper's local terminal jump
`eta_i(z) = (z-a_i) + a_{omega(z-a_i)_i}`. -/
def terminalTailBase (i : Fin 3) (z : LowD5M4.Q4) : LowD5M4.Q4 :=
  z - terminalVertex (m := 4) i

/-- The triangle base used by the run-collapsed terminal return
`F_i(z) = eta_i(z + Delta_i)`. -/
def terminalReturnTailBase (i : Fin 3) (z : LowD5M4.Q4) :
    LowD5M4.Q4 :=
  z + terminalDelta i - terminalVertex (m := 4) i

/-- The charted terminal row word realizes the paper's local jump `eta_i` as
one standard D5 root step from the triangle base `z-a_i`. -/
theorem rootStep_terminalTailBase_eq_terminalEta
    (i : Fin 3) (q : LowD5M4.Q4) (y : LowD5M4.Y) (z : LowD5M4.Z) :
    LowD5M4Schedule.rootStep
        (terminalStdBaseRowEquiv5 (terminalTailBase i q) (fin3ToFin5 i))
        (rootOfCoords (terminalTailBase i q) y z) =
      rootOfCoords (terminalEta (m := 4) i q) y z := by
  simpa [terminalStdBaseRowEquiv5, terminalTailBase, terminalEta]
    using rootStep_terminalStdRowEquiv5_fin3_eq_rootOfCoords
      (terminalOmega (terminalTailBase i q)) i
      (rootOfCoords (terminalTailBase i q) y z)

/-- The same local-step statement at the run-collapsed return base
`z + Delta_i - a_i`, yielding the indexed terminal return `F_i`. -/
theorem rootStep_terminalReturnTailBase_eq_terminalReturn
    (i : Fin 3) (q : LowD5M4.Q4) (y : LowD5M4.Y) (z : LowD5M4.Z) :
    LowD5M4Schedule.rootStep
        (terminalStdBaseRowEquiv5
          (terminalReturnTailBase i q) (fin3ToFin5 i))
        (rootOfCoords (terminalReturnTailBase i q) y z) =
      rootOfCoords (terminalReturn (m := 4) i q) y z := by
  simpa [terminalStdBaseRowEquiv5, terminalReturnTailBase, terminalReturn,
    terminalEta]
    using rootStep_terminalStdRowEquiv5_fin3_eq_rootOfCoords
      (terminalOmega (terminalReturnTailBase i q)) i
      (rootOfCoords (terminalReturnTailBase i q) y z)

/-- Read a terminal symbol as the corresponding terminal color index. -/
def terminalIndexOfSymbol : TerminalSymbol → Fin 3
  | TerminalSymbol.F0 => 0
  | TerminalSymbol.F1 => 1
  | TerminalSymbol.F2 => 2

@[simp] theorem terminalSymbolOfIndex_terminalIndexOfSymbol
    (s : TerminalSymbol) :
    terminalSymbolOfIndex (terminalIndexOfSymbol s) = s := by
  cases s <;> rfl

/-- The run-collapsed terminal return base indexed by terminal symbol. -/
def terminalReturnTailBaseOfSymbol
    (s : TerminalSymbol) (q : LowD5M4.Q4) : LowD5M4.Q4 :=
  terminalReturnTailBase (terminalIndexOfSymbol s) q

theorem rootStep_terminalReturnTailBaseOfSymbol_eq_F
    (s : TerminalSymbol) (q : LowD5M4.Q4) (y : LowD5M4.Y)
    (z : LowD5M4.Z) :
    LowD5M4Schedule.rootStep
        (terminalStdBaseRowEquiv5
          (terminalReturnTailBaseOfSymbol s q)
          (fin3ToFin5 (terminalIndexOfSymbol s)))
        (rootOfCoords (terminalReturnTailBaseOfSymbol s q) y z) =
      rootOfCoords (LowD5M4.F s q) y z := by
  have hF :
      terminalReturn (m := 4) (terminalIndexOfSymbol s) q =
        LowD5M4.F s q := by
    calc
      terminalReturn (m := 4) (terminalIndexOfSymbol s) q =
          terminalSymbolStep 4
            (terminalSymbolOfIndex (terminalIndexOfSymbol s)) q := by
            rw [terminalSymbolStep_of_index (m := 4)
              (terminalIndexOfSymbol s)]
      _ = terminalSymbolStep 4 s q := by
            rw [terminalSymbolOfIndex_terminalIndexOfSymbol]
      _ = LowD5M4.F s q := rfl
  simpa [terminalReturnTailBaseOfSymbol, hF]
    using rootStep_terminalReturnTailBase_eq_terminalReturn
      (terminalIndexOfSymbol s) q y z

/-- Post-compose a Latin row with the transposition of two output directions.
This is the row-level form of the two-entry exchanges used by the reset ports. -/
def postSwapRow (row : TorusColor 5 ≃ TorusDirection 5)
    (a b : TorusDirection 5) :
    TorusColor 5 ≃ TorusDirection 5 :=
  row.trans (Equiv.swap a b)

@[simp] theorem postSwapRow_apply
    (row : TorusColor 5 ≃ TorusDirection 5)
    (a b : TorusDirection 5) (c : TorusColor 5) :
    postSwapRow row a b c = Equiv.swap a b (row c) :=
  rfl

/-- Swap the output direction used by a chosen color with a specified lift
direction. This is the canonical row-level two-entry substitution used by the
unit-carry ports. -/
def postSwapColorWithDirection
    (row : TorusColor 5 ≃ TorusDirection 5)
    (c : TorusColor 5) (d : TorusDirection 5) :
    TorusColor 5 ≃ TorusDirection 5 :=
  postSwapRow row (row c) d

@[simp] theorem postSwapColorWithDirection_apply_color
    (row : TorusColor 5 ≃ TorusDirection 5)
    (c : TorusColor 5) (d : TorusDirection 5) :
    postSwapColorWithDirection row c d c = d := by
  simp [postSwapColorWithDirection]

@[simp] theorem postSwapColorWithDirection_apply_directionSource
    (row : TorusColor 5 ≃ TorusDirection 5)
    (c : TorusColor 5) (d : TorusDirection 5) :
    postSwapColorWithDirection row c d (row.symm d) = row c := by
  simp [postSwapColorWithDirection]

/-- Conditionally apply one row-level output transposition. -/
def postSwapRowIf (p : Prop) [Decidable p]
    (row : TorusColor 5 ≃ TorusDirection 5)
    (a b : TorusDirection 5) :
    TorusColor 5 ≃ TorusDirection 5 :=
  if p then postSwapRow row a b else row

@[simp] theorem postSwapRowIf_true
    (row : TorusColor 5 ≃ TorusDirection 5)
    (a b : TorusDirection 5) :
    postSwapRowIf True row a b = postSwapRow row a b := by
  simp [postSwapRowIf]

@[simp] theorem postSwapRowIf_false
    (row : TorusColor 5 ≃ TorusDirection 5)
    (a b : TorusDirection 5) :
    postSwapRowIf False row a b = row := by
  simp [postSwapRowIf]

/-- The first `Y`-carry reset sites from Table D54-reset-ports. Only colors
`0,1,2` have this first lift. -/
def firstLiftCarrySite (c : TorusColor 5) (w : RootState) : Prop :=
  match c with
  | 0 => qCoord w = LowD5M4.p0
  | 1 => qCoord w = LowD5M4.p1
  | 2 => qCoord w = LowD5M4.p2
  | 3 => False
  | 4 => False

instance firstLiftCarrySite_decidable
    (c : TorusColor 5) (w : RootState) :
    Decidable (firstLiftCarrySite c w) :=
  match c with
  | 0 => by
      unfold firstLiftCarrySite
      infer_instance
  | 1 => by
      unfold firstLiftCarrySite
      infer_instance
  | 2 => by
      unfold firstLiftCarrySite
      infer_instance
  | 3 => by
      unfold firstLiftCarrySite
      infer_instance
  | 4 => by
      unfold firstLiftCarrySite
      infer_instance

/-- The final `Z`-carry reset sites from Table D54-reset-ports. -/
def finalLiftCarrySite (c : TorusColor 5) (w : RootState) : Prop :=
  (qCoord w, yCoord w) = LowD5M4.liftSite c

instance finalLiftCarrySite_decidable
    (c : TorusColor 5) (w : RootState) :
    Decidable (finalLiftCarrySite c w) := by
  unfold finalLiftCarrySite
  infer_instance

/-- The first `Y`-carry sites for the terminal colors `0,1,2`, indexed in the
same order as `F0,F1,F2`. -/
def firstLiftSiteOfIndex : Fin 3 → LowD5M4.Q4
  | 0 => LowD5M4.p0
  | 1 => LowD5M4.p1
  | 2 => LowD5M4.p2

/-- The first-lift reset-site table in the order used by Table
D54-reset-ports. -/
def firstLiftSites : List LowD5M4.Q4 :=
  [ firstLiftSiteOfIndex (0 : Fin 3),
    firstLiftSiteOfIndex (1 : Fin 3),
    firstLiftSiteOfIndex (2 : Fin 3) ]

theorem firstLiftSiteOfIndex_mem_firstLiftSites
    (i : Fin 3) :
    firstLiftSiteOfIndex i ∈ firstLiftSites := by
  fin_cases i <;> simp [firstLiftSites]

/-- The terminal selector points \(C_4\), indexed in the order used in the
D54 audit table. -/
def d54TerminalSelectorSite : Fin 3 → TerminalQ 4
  | 0 => D54ResetData.d54q4 0 3
  | 1 => D54ResetData.d54q4 3 0
  | 2 => D54ResetData.d54q4 3 3

theorem d54TerminalSelector_eq_selectorSites :
    d54TerminalSelector =
      [ d54TerminalSelectorSite (0 : Fin 3),
        d54TerminalSelectorSite (1 : Fin 3),
        d54TerminalSelectorSite (2 : Fin 3) ] := by
  rfl

theorem d54TerminalSelectorSite_mem_d54TerminalSelector
    (i : Fin 3) :
    d54TerminalSelectorSite i ∈ d54TerminalSelector := by
  rw [d54TerminalSelector_eq_selectorSites]
  fin_cases i <;> simp

/-- The lifted selector points used by Table D54-reset-ports. -/
def d54LiftedSelectorPointOfIndex (i : Fin 3) : D54Point where
  q := d54TerminalSelectorSite i
  y := (0 : Y4)
  z := (0 : Z4)

theorem d54LiftedSelector_eq_liftedSelectorPoints :
    d54LiftedSelector =
      [ d54LiftedSelectorPointOfIndex (0 : Fin 3),
        d54LiftedSelectorPointOfIndex (1 : Fin 3),
        d54LiftedSelectorPointOfIndex (2 : Fin 3) ] := by
  rfl

theorem d54LiftedSelectorPointOfIndex_mem_d54LiftedSelector
    (i : Fin 3) :
    d54LiftedSelectorPointOfIndex i ∈ d54LiftedSelector := by
  rw [d54LiftedSelector_eq_liftedSelectorPoints]
  fin_cases i <;> simp

theorem d54ReserveD54PointOfRole_mem_reservePoints
    (role : D54ReserveRole) :
    d54ReserveD54PointOfRole role ∈ reservePoints := by
  rw [reservePoints_eq_map_reserveD54PointOfRole]
  cases role <;> simp [d54ReserveRoles]

/-- The indexed reset-site table in `D54ResetData` is the same first-lift site
table used by the reset-port row construction. -/
theorem d54TerminalResetSite_eq_firstLiftSiteOfIndex
    (i : Fin 3) :
    d54TerminalResetSite i = firstLiftSiteOfIndex i := by
  fin_cases i <;> rfl

theorem d54TerminalResetSites_eq_firstLiftSites :
    d54TerminalResetSites = firstLiftSites := by
  simpa [firstLiftSites, firstLiftSiteOfIndex] using
    d54TerminalResetSites_eq_lowD5M4

theorem firstLiftCarrySite_fin3 (i : Fin 3) (w : RootState) :
    firstLiftCarrySite (fin3ToFin5 i) w ↔
      qCoord w = firstLiftSiteOfIndex i := by
  fin_cases i <;> simp [firstLiftCarrySite, firstLiftSiteOfIndex, fin3ToFin5]

theorem firstLiftCarrySite_iff_d54TerminalResetSite
    (i : Fin 3) (w : RootState) :
    firstLiftCarrySite (fin3ToFin5 i) w ↔
      qCoord w = d54TerminalResetSite i := by
  rw [d54TerminalResetSite_eq_firstLiftSiteOfIndex i]
  exact firstLiftCarrySite_fin3 i w

theorem firstLiftSiteOfIndex_ne_d54TerminalSelectorSite
    (i j : Fin 3) :
    firstLiftSiteOfIndex i ≠ d54TerminalSelectorSite j := by
  fin_cases i <;> fin_cases j <;> decide

theorem firstLiftSiteOfIndex_ne_d54ReservePointOfRole_q
    (i : Fin 3) (role : D54ReserveRole) :
    firstLiftSiteOfIndex i ≠ (d54ReserveD54PointOfRole role).q := by
  fin_cases i <;> cases role <;> decide

/-- The three first-stage reset sites in Table D54-reset-ports are distinct. -/
theorem firstLiftSiteOfIndex_injective :
    Function.Injective firstLiftSiteOfIndex := by
  decide

/-- At a fixed root state, at most one terminal color can be at its first-stage
reset site. -/
theorem firstLiftCarrySite_fin3_injective
    {i j : Fin 3} {w : RootState}
    (hi : firstLiftCarrySite (fin3ToFin5 i) w)
    (hj : firstLiftCarrySite (fin3ToFin5 j) w) :
    i = j := by
  apply firstLiftSiteOfIndex_injective
  exact ((firstLiftCarrySite_fin3 i w).1 hi).symm.trans
    ((firstLiftCarrySite_fin3 j w).1 hj)

theorem not_firstLiftCarrySite_fin3_of_ne
    {i j : Fin 3} {w : RootState} (hij : i ≠ j)
    (hi : firstLiftCarrySite (fin3ToFin5 i) w) :
    ¬ firstLiftCarrySite (fin3ToFin5 j) w := by
  intro hj
  exact hij (firstLiftCarrySite_fin3_injective hi hj)

/-- The five final-stage reset sites in Table D54-reset-ports are distinct. -/
theorem finalLiftSite_injective :
    Function.Injective LowD5M4.liftSite := by
  decide

/-- At a fixed root state, at most one color can be at its final-stage reset
site. -/
theorem finalLiftCarrySite_injective
    {c d : TorusColor 5} {w : RootState}
    (hc : finalLiftCarrySite c w)
    (hd : finalLiftCarrySite d w) :
    c = d := by
  exact finalLiftSite_injective (hc.symm.trans hd)

theorem not_finalLiftCarrySite_of_ne
    {c d : TorusColor 5} {w : RootState} (hcd : c ≠ d)
    (hc : finalLiftCarrySite c w) :
    ¬ finalLiftCarrySite d w := by
  intro hd
  exact hcd (finalLiftCarrySite_injective hc hd)

/-- The final switching-site table as `D54ResetData` cylinders. -/
def finalLiftCylinderOfColor (c : TorusColor 5) : D54Cylinder where
  q := (LowD5M4.liftSite c).1
  y := (LowD5M4.liftSite c).2

/-- The final-lift switching cylinders in the order used by Table
D54-reset-ports. -/
def finalLiftCylinders : List D54Cylinder :=
  [ finalLiftCylinderOfColor (0 : TorusColor 5),
    finalLiftCylinderOfColor (1 : TorusColor 5),
    finalLiftCylinderOfColor (2 : TorusColor 5),
    finalLiftCylinderOfColor (3 : TorusColor 5),
    finalLiftCylinderOfColor (4 : TorusColor 5) ]

theorem finalLiftCylinderOfColor_mem_finalLiftCylinders
    (c : TorusColor 5) :
    finalLiftCylinderOfColor c ∈ finalLiftCylinders := by
  fin_cases c <;> simp [finalLiftCylinders]

/-- The `(q,y)` cylinder occupied by a root state, in the D54 table language. -/
def rootStateD54Cylinder (w : RootState) : D54Cylinder where
  q := qCoord w
  y := yCoord w

/-- The D54 table point occupied by a root state. -/
def rootStateD54Point (w : RootState) : D54Point where
  q := qCoord w
  y := yCoord w
  z := zCoord w

theorem d54FinalCylinderOfColor_eq_finalLiftCylinderOfColor
    (c : TorusColor 5) :
    d54FinalCylinderOfColor c = finalLiftCylinderOfColor c := by
  simpa [finalLiftCylinderOfColor] using
    d54FinalCylinderOfColor_eq_lowD5M4_liftSite c

theorem d54FinalCylinders_eq_finalLiftCylinders :
    d54FinalCylinders = finalLiftCylinders := by
  simpa [finalLiftCylinders, finalLiftCylinderOfColor] using
    d54FinalCylinders_eq_lowD5M4_liftSites

theorem finalLiftCarrySite_iff_d54FinalCylinderOfColor
    (c : TorusColor 5) (w : RootState) :
    finalLiftCarrySite c w ↔
      rootStateD54Cylinder w = d54FinalCylinderOfColor c := by
  fin_cases c <;>
    simp [finalLiftCarrySite, rootStateD54Cylinder,
      d54FinalCylinderOfColor,
      D54ResetData.d54q4, TerminalA2LowMod.q4, TerminalA2LowMod.q,
      LowD5M4.liftSite, LowD5M4.a0, LowD5M4.a1, LowD5M4.a2,
      LowD5M4.a3, LowD5M4.a4]

theorem finalLiftCarrySite_iff_finalLiftCylinderOfColor
    (c : TorusColor 5) (w : RootState) :
    finalLiftCarrySite c w ↔
      rootStateD54Cylinder w = finalLiftCylinderOfColor c := by
  rw [← d54FinalCylinderOfColor_eq_finalLiftCylinderOfColor c]
  exact finalLiftCarrySite_iff_d54FinalCylinderOfColor c w

theorem d54TerminalSelectorSite_ne_d54FinalCylinderOfColor_q
    (i : Fin 3) (c : TorusColor 5) :
    d54TerminalSelectorSite i ≠ (d54FinalCylinderOfColor c).q := by
  fin_cases i <;> fin_cases c <;> decide

theorem d54ReservePointOfRole_q_ne_d54FinalCylinderOfColor_q
    (role : D54ReserveRole) (c : TorusColor 5) :
    (d54ReserveD54PointOfRole role).q ≠
      (d54FinalCylinderOfColor c).q := by
  cases role <;> fin_cases c <;> decide

theorem finalLiftCylinderOfColor_avoids_d54LiftedSelectorPoint
    (c : TorusColor 5) (i : Fin 3) :
    D54ResetData.cylinderAvoidsPoint
      (finalLiftCylinderOfColor c) (d54LiftedSelectorPointOfIndex i) =
        true := by
  fin_cases c <;> fin_cases i <;> rfl

theorem finalLiftCylinderOfColor_avoids_d54ReservePointOfRole
    (c : TorusColor 5) (role : D54ReserveRole) :
    D54ResetData.cylinderAvoidsPoint
      (finalLiftCylinderOfColor c) (d54ReserveD54PointOfRole role) =
        true := by
  fin_cases c <;> cases role <;> rfl

theorem pointCarry_firstLiftSiteOfIndex_eq_ite
    (i : Fin 3) (w : RootState) :
    EvenV11.UnitCarry.pointCarry
        (firstLiftSiteOfIndex i) (1 : ZMod 4) (qCoord w) =
      if firstLiftCarrySite (fin3ToFin5 i) w then 1 else 0 := by
  fin_cases i <;>
    simp [firstLiftCarrySite, firstLiftSiteOfIndex, fin3ToFin5,
      EvenV11.UnitCarry.pointCarry]

theorem pointCarry_liftSite_eq_ite
    (c : TorusColor 5) (w : RootState) :
    EvenV11.UnitCarry.pointCarry
        (LowD5M4.liftSite c) (1 : ZMod 4) (qCoord w, yCoord w) =
      if finalLiftCarrySite c w then 1 else 0 := by
  rfl

theorem add_pointCarry_firstLiftSiteOfIndex_eq_ite
    (i : Fin 3) (w : RootState) :
    yCoord w +
        EvenV11.UnitCarry.pointCarry
          (firstLiftSiteOfIndex i) (1 : ZMod 4) (qCoord w) =
      if firstLiftCarrySite (fin3ToFin5 i) w then
        yCoord w + 1
      else
        yCoord w := by
  rw [pointCarry_firstLiftSiteOfIndex_eq_ite i w]
  by_cases h : firstLiftCarrySite (fin3ToFin5 i) w <;> simp [h]

theorem add_pointCarry_liftSite_eq_ite
    (c : TorusColor 5) (w : RootState) :
    zCoord w +
        EvenV11.UnitCarry.pointCarry
          (LowD5M4.liftSite c) (1 : ZMod 4) (qCoord w, yCoord w) =
      if finalLiftCarrySite c w then
        zCoord w + 1
      else
        zCoord w := by
  rw [pointCarry_liftSite_eq_ite c w]
  by_cases h : finalLiftCarrySite c w <;> simp [h]

/-- Table D54-reset-ports first lift: swap terminal color `i` with the standard
`Y` lift direction. -/
def firstLiftSwapRow (i : Fin 3)
    (row : TorusColor 5 ≃ TorusDirection 5) :
    TorusColor 5 ≃ TorusDirection 5 :=
  postSwapColorWithDirection row (fin3ToFin5 i) liftYDirection5

@[simp] theorem firstLiftSwapRow_apply_color
    (i : Fin 3) (row : TorusColor 5 ≃ TorusDirection 5) :
    firstLiftSwapRow i row (fin3ToFin5 i) = liftYDirection5 := by
  simp [firstLiftSwapRow]

/-- Conditionally apply the first `Y`-carry substitution at the indexed site. -/
def firstLiftSwapRowIf (i : Fin 3) (w : RootState)
    (row : TorusColor 5 ≃ TorusDirection 5) :
    TorusColor 5 ≃ TorusDirection 5 :=
  postSwapRowIf (qCoord w = firstLiftSiteOfIndex i)
    row (row (fin3ToFin5 i)) liftYDirection5

theorem firstLiftSwapRowIf_of_site
    (i : Fin 3) (w : RootState)
    (row : TorusColor 5 ≃ TorusDirection 5)
    (h : qCoord w = firstLiftSiteOfIndex i) :
    firstLiftSwapRowIf i w row = firstLiftSwapRow i row := by
  simp [firstLiftSwapRowIf, firstLiftSwapRow, postSwapColorWithDirection, h]

theorem firstLiftSwapRowIf_of_not_site
    (i : Fin 3) (w : RootState)
    (row : TorusColor 5 ≃ TorusDirection 5)
    (h : qCoord w ≠ firstLiftSiteOfIndex i) :
    firstLiftSwapRowIf i w row = row := by
  simp [firstLiftSwapRowIf, h]

@[simp] theorem firstLiftSwapRowIf_apply_color_of_site
    (i : Fin 3) (w : RootState)
    (row : TorusColor 5 ≃ TorusDirection 5)
    (h : qCoord w = firstLiftSiteOfIndex i) :
    firstLiftSwapRowIf i w row (fin3ToFin5 i) = liftYDirection5 := by
  rw [firstLiftSwapRowIf_of_site i w row h]
  simp

@[simp] theorem firstLiftSwapRowIf_apply_color_of_not_site
    (i : Fin 3) (w : RootState)
    (row : TorusColor 5 ≃ TorusDirection 5)
    (h : qCoord w ≠ firstLiftSiteOfIndex i) :
    firstLiftSwapRowIf i w row (fin3ToFin5 i) =
      row (fin3ToFin5 i) := by
  rw [firstLiftSwapRowIf_of_not_site i w row h]

theorem rootStep_firstLiftSwapRowIf_color_of_site
    (i : Fin 3) (w : RootState)
    (row : TorusColor 5 ≃ TorusDirection 5)
    (h : qCoord w = firstLiftSiteOfIndex i) :
    LowD5M4Schedule.rootStep
        (firstLiftSwapRowIf i w row (fin3ToFin5 i)) w =
      rootOfCoords (qCoord w) (yCoord w + 1) (zCoord w) := by
  rw [firstLiftSwapRowIf_apply_color_of_site i w row h]
  exact rootStep_liftYDirection5_eq_rootOfCoords w

theorem rootStep_firstLiftSwapRowIf_color_of_not_site
    (i : Fin 3) (w : RootState)
    (row : TorusColor 5 ≃ TorusDirection 5)
    (h : qCoord w ≠ firstLiftSiteOfIndex i) :
    LowD5M4Schedule.rootStep
        (firstLiftSwapRowIf i w row (fin3ToFin5 i)) w =
      LowD5M4Schedule.rootStep (row (fin3ToFin5 i)) w := by
  rw [firstLiftSwapRowIf_apply_color_of_not_site i w row h]

theorem rootStep_firstLiftSwapRowIf_color
    (i : Fin 3) (w : RootState)
    (row : TorusColor 5 ≃ TorusDirection 5) :
    LowD5M4Schedule.rootStep
        (firstLiftSwapRowIf i w row (fin3ToFin5 i)) w =
      if qCoord w = firstLiftSiteOfIndex i then
        rootOfCoords (qCoord w) (yCoord w + 1) (zCoord w)
      else
        LowD5M4Schedule.rootStep (row (fin3ToFin5 i)) w := by
  by_cases h : qCoord w = firstLiftSiteOfIndex i
  · rw [if_pos h]
    exact rootStep_firstLiftSwapRowIf_color_of_site i w row h
  · rw [if_neg h]
    exact rootStep_firstLiftSwapRowIf_color_of_not_site i w row h

/-- Apply the three possible first-lift substitutions from Table
D54-reset-ports. Their sites are distinct; this nested form keeps the result an
explicit row equivalence at every stage. -/
def firstLiftSwappedRow (w : RootState)
    (row : TorusColor 5 ≃ TorusDirection 5) :
    TorusColor 5 ≃ TorusDirection 5 :=
  firstLiftSwapRowIf 2 w
    (firstLiftSwapRowIf 1 w
      (firstLiftSwapRowIf 0 w row))

theorem firstLiftSwappedRow_apply_fin3_of_site
    (i : Fin 3) (w : RootState)
    (row : TorusColor 5 ≃ TorusDirection 5)
    (h : firstLiftCarrySite (fin3ToFin5 i) w) :
    firstLiftSwappedRow w row (fin3ToFin5 i) = liftYDirection5 := by
  have hi : qCoord w = firstLiftSiteOfIndex i :=
    (firstLiftCarrySite_fin3 i w).1 h
  fin_cases i
  · have h01 :
        firstLiftSiteOfIndex (0 : Fin 3) ≠ firstLiftSiteOfIndex (1 : Fin 3) := by
      decide
    have h02 :
        firstLiftSiteOfIndex (0 : Fin 3) ≠ firstLiftSiteOfIndex (2 : Fin 3) := by
      decide
    simp [firstLiftSwappedRow, firstLiftSwapRowIf, hi, h01, h02]
  · have h10 :
        firstLiftSiteOfIndex (1 : Fin 3) ≠ firstLiftSiteOfIndex (0 : Fin 3) := by
      decide
    have h12 :
        firstLiftSiteOfIndex (1 : Fin 3) ≠ firstLiftSiteOfIndex (2 : Fin 3) := by
      decide
    simp [firstLiftSwappedRow, firstLiftSwapRowIf, hi, h10, h12]
  · have h20 :
        firstLiftSiteOfIndex (2 : Fin 3) ≠ firstLiftSiteOfIndex (0 : Fin 3) := by
      decide
    have h21 :
        firstLiftSiteOfIndex (2 : Fin 3) ≠ firstLiftSiteOfIndex (1 : Fin 3) := by
      decide
    simp [firstLiftSwappedRow, firstLiftSwapRowIf, hi, h20, h21]

theorem rootStep_firstLiftSwappedRow_fin3_of_site
    (i : Fin 3) (w : RootState)
    (row : TorusColor 5 ≃ TorusDirection 5)
    (h : firstLiftCarrySite (fin3ToFin5 i) w) :
    LowD5M4Schedule.rootStep
        (firstLiftSwappedRow w row (fin3ToFin5 i)) w =
      rootOfCoords (qCoord w) (yCoord w + 1) (zCoord w) := by
  rw [firstLiftSwappedRow_apply_fin3_of_site i w row h]
  exact rootStep_liftYDirection5_eq_rootOfCoords w

/-- If none of the first-stage reset sites is active at a source, the
first-stage substitution layer leaves every row unchanged. -/
theorem firstLiftSwappedRow_of_no_site
    (w : RootState) (row : TorusColor 5 ≃ TorusDirection 5)
    (h : ∀ i : Fin 3, ¬ firstLiftCarrySite (fin3ToFin5 i) w) :
    firstLiftSwappedRow w row = row := by
  have h0 : qCoord w ≠ firstLiftSiteOfIndex (0 : Fin 3) := by
    intro hq
    exact h 0 ((firstLiftCarrySite_fin3 0 w).2 hq)
  have h1 : qCoord w ≠ firstLiftSiteOfIndex (1 : Fin 3) := by
    intro hq
    exact h 1 ((firstLiftCarrySite_fin3 1 w).2 hq)
  have h2 : qCoord w ≠ firstLiftSiteOfIndex (2 : Fin 3) := by
    intro hq
    exact h 2 ((firstLiftCarrySite_fin3 2 w).2 hq)
  ext c
  simp [firstLiftSwappedRow, firstLiftSwapRowIf, h0, h1, h2]

/-- Table D54-reset-ports final lift: swap color `c` with the standard `Z` lift
direction. -/
def finalLiftSwapRow (c : TorusColor 5)
    (row : TorusColor 5 ≃ TorusDirection 5) :
    TorusColor 5 ≃ TorusDirection 5 :=
  postSwapColorWithDirection row c liftZDirection5

@[simp] theorem finalLiftSwapRow_apply_color
    (c : TorusColor 5) (row : TorusColor 5 ≃ TorusDirection 5) :
    finalLiftSwapRow c row c = liftZDirection5 := by
  simp [finalLiftSwapRow]

/-- Conditionally apply the final `Z`-carry substitution at the paper's final
switching site for color `c`. -/
def finalLiftSwapRowIf (c : TorusColor 5) (w : RootState)
    (row : TorusColor 5 ≃ TorusDirection 5) :
    TorusColor 5 ≃ TorusDirection 5 :=
  postSwapRowIf (finalLiftCarrySite c w) row (row c) liftZDirection5

theorem finalLiftSwapRowIf_of_site
    (c : TorusColor 5) (w : RootState)
    (row : TorusColor 5 ≃ TorusDirection 5)
    (h : finalLiftCarrySite c w) :
    finalLiftSwapRowIf c w row = finalLiftSwapRow c row := by
  simp [finalLiftSwapRowIf, finalLiftSwapRow, postSwapColorWithDirection, h]

theorem finalLiftSwapRowIf_of_not_site
    (c : TorusColor 5) (w : RootState)
    (row : TorusColor 5 ≃ TorusDirection 5)
    (h : ¬ finalLiftCarrySite c w) :
    finalLiftSwapRowIf c w row = row := by
  simp [finalLiftSwapRowIf, h]

@[simp] theorem finalLiftSwapRowIf_apply_color_of_site
    (c : TorusColor 5) (w : RootState)
    (row : TorusColor 5 ≃ TorusDirection 5)
    (h : finalLiftCarrySite c w) :
    finalLiftSwapRowIf c w row c = liftZDirection5 := by
  rw [finalLiftSwapRowIf_of_site c w row h]
  simp

@[simp] theorem finalLiftSwapRowIf_apply_color_of_not_site
    (c : TorusColor 5) (w : RootState)
    (row : TorusColor 5 ≃ TorusDirection 5)
    (h : ¬ finalLiftCarrySite c w) :
    finalLiftSwapRowIf c w row c = row c := by
  rw [finalLiftSwapRowIf_of_not_site c w row h]

theorem rootStep_finalLiftSwapRowIf_color_of_site
    (c : TorusColor 5) (w : RootState)
    (row : TorusColor 5 ≃ TorusDirection 5)
    (h : finalLiftCarrySite c w) :
    LowD5M4Schedule.rootStep (finalLiftSwapRowIf c w row c) w =
      rootOfCoords (qCoord w) (yCoord w) (zCoord w + 1) := by
  rw [finalLiftSwapRowIf_apply_color_of_site c w row h]
  exact rootStep_liftZDirection5_eq_rootOfCoords w

theorem rootStep_finalLiftSwapRowIf_color_of_not_site
    (c : TorusColor 5) (w : RootState)
    (row : TorusColor 5 ≃ TorusDirection 5)
    (h : ¬ finalLiftCarrySite c w) :
    LowD5M4Schedule.rootStep (finalLiftSwapRowIf c w row c) w =
      LowD5M4Schedule.rootStep (row c) w := by
  rw [finalLiftSwapRowIf_apply_color_of_not_site c w row h]

theorem rootStep_finalLiftSwapRowIf_color
    (c : TorusColor 5) (w : RootState)
    (row : TorusColor 5 ≃ TorusDirection 5) :
    LowD5M4Schedule.rootStep (finalLiftSwapRowIf c w row c) w =
      if finalLiftCarrySite c w then
        rootOfCoords (qCoord w) (yCoord w) (zCoord w + 1)
      else
        LowD5M4Schedule.rootStep (row c) w := by
  by_cases h : finalLiftCarrySite c w
  · rw [if_pos h]
    exact rootStep_finalLiftSwapRowIf_color_of_site c w row h
  · rw [if_neg h]
    exact rootStep_finalLiftSwapRowIf_color_of_not_site c w row h

/-- Apply the five possible final-lift substitutions from Table
D54-reset-ports. -/
def finalLiftSwappedRow (w : RootState)
    (row : TorusColor 5 ≃ TorusDirection 5) :
    TorusColor 5 ≃ TorusDirection 5 :=
  finalLiftSwapRowIf 4 w
    (finalLiftSwapRowIf 3 w
      (finalLiftSwapRowIf 2 w
        (finalLiftSwapRowIf 1 w
          (finalLiftSwapRowIf 0 w row))))

theorem finalLiftSwappedRow_apply_color_of_site
    (c : TorusColor 5) (w : RootState)
    (row : TorusColor 5 ≃ TorusDirection 5)
    (h : finalLiftCarrySite c w) :
    finalLiftSwappedRow w row c = liftZDirection5 := by
  fin_cases c
  · have h0 : finalLiftCarrySite (0 : TorusColor 5) w := by simpa using h
    have h1 : ¬ finalLiftCarrySite (1 : TorusColor 5) w :=
      not_finalLiftCarrySite_of_ne (by decide : (0 : TorusColor 5) ≠ 1) h0
    have h2 : ¬ finalLiftCarrySite (2 : TorusColor 5) w :=
      not_finalLiftCarrySite_of_ne (by decide : (0 : TorusColor 5) ≠ 2) h0
    have h3 : ¬ finalLiftCarrySite (3 : TorusColor 5) w :=
      not_finalLiftCarrySite_of_ne (by decide : (0 : TorusColor 5) ≠ 3) h0
    have h4 : ¬ finalLiftCarrySite (4 : TorusColor 5) w :=
      not_finalLiftCarrySite_of_ne (by decide : (0 : TorusColor 5) ≠ 4) h0
    simp [finalLiftSwappedRow, finalLiftSwapRowIf, h0, h1, h2, h3, h4]
  · have h1 : finalLiftCarrySite (1 : TorusColor 5) w := by simpa using h
    have h0 : ¬ finalLiftCarrySite (0 : TorusColor 5) w :=
      not_finalLiftCarrySite_of_ne (by decide : (1 : TorusColor 5) ≠ 0) h1
    have h2 : ¬ finalLiftCarrySite (2 : TorusColor 5) w :=
      not_finalLiftCarrySite_of_ne (by decide : (1 : TorusColor 5) ≠ 2) h1
    have h3 : ¬ finalLiftCarrySite (3 : TorusColor 5) w :=
      not_finalLiftCarrySite_of_ne (by decide : (1 : TorusColor 5) ≠ 3) h1
    have h4 : ¬ finalLiftCarrySite (4 : TorusColor 5) w :=
      not_finalLiftCarrySite_of_ne (by decide : (1 : TorusColor 5) ≠ 4) h1
    simp [finalLiftSwappedRow, finalLiftSwapRowIf, h0, h1, h2, h3, h4]
  · have h2 : finalLiftCarrySite (2 : TorusColor 5) w := by simpa using h
    have h0 : ¬ finalLiftCarrySite (0 : TorusColor 5) w :=
      not_finalLiftCarrySite_of_ne (by decide : (2 : TorusColor 5) ≠ 0) h2
    have h1 : ¬ finalLiftCarrySite (1 : TorusColor 5) w :=
      not_finalLiftCarrySite_of_ne (by decide : (2 : TorusColor 5) ≠ 1) h2
    have h3 : ¬ finalLiftCarrySite (3 : TorusColor 5) w :=
      not_finalLiftCarrySite_of_ne (by decide : (2 : TorusColor 5) ≠ 3) h2
    have h4 : ¬ finalLiftCarrySite (4 : TorusColor 5) w :=
      not_finalLiftCarrySite_of_ne (by decide : (2 : TorusColor 5) ≠ 4) h2
    simp [finalLiftSwappedRow, finalLiftSwapRowIf, h0, h1, h2, h3, h4]
  · have h3 : finalLiftCarrySite (3 : TorusColor 5) w := by simpa using h
    have h0 : ¬ finalLiftCarrySite (0 : TorusColor 5) w :=
      not_finalLiftCarrySite_of_ne (by decide : (3 : TorusColor 5) ≠ 0) h3
    have h1 : ¬ finalLiftCarrySite (1 : TorusColor 5) w :=
      not_finalLiftCarrySite_of_ne (by decide : (3 : TorusColor 5) ≠ 1) h3
    have h2 : ¬ finalLiftCarrySite (2 : TorusColor 5) w :=
      not_finalLiftCarrySite_of_ne (by decide : (3 : TorusColor 5) ≠ 2) h3
    have h4 : ¬ finalLiftCarrySite (4 : TorusColor 5) w :=
      not_finalLiftCarrySite_of_ne (by decide : (3 : TorusColor 5) ≠ 4) h3
    simp [finalLiftSwappedRow, finalLiftSwapRowIf, h0, h1, h2, h3, h4]
  · have h4 : finalLiftCarrySite (4 : TorusColor 5) w := by simpa using h
    have h0 : ¬ finalLiftCarrySite (0 : TorusColor 5) w :=
      not_finalLiftCarrySite_of_ne (by decide : (4 : TorusColor 5) ≠ 0) h4
    have h1 : ¬ finalLiftCarrySite (1 : TorusColor 5) w :=
      not_finalLiftCarrySite_of_ne (by decide : (4 : TorusColor 5) ≠ 1) h4
    have h2 : ¬ finalLiftCarrySite (2 : TorusColor 5) w :=
      not_finalLiftCarrySite_of_ne (by decide : (4 : TorusColor 5) ≠ 2) h4
    have h3 : ¬ finalLiftCarrySite (3 : TorusColor 5) w :=
      not_finalLiftCarrySite_of_ne (by decide : (4 : TorusColor 5) ≠ 3) h4
    simp [finalLiftSwappedRow, finalLiftSwapRowIf, h0, h1, h2, h3, h4]

theorem rootStep_finalLiftSwappedRow_color_of_site
    (c : TorusColor 5) (w : RootState)
    (row : TorusColor 5 ≃ TorusDirection 5)
    (h : finalLiftCarrySite c w) :
    LowD5M4Schedule.rootStep (finalLiftSwappedRow w row c) w =
      rootOfCoords (qCoord w) (yCoord w) (zCoord w + 1) := by
  rw [finalLiftSwappedRow_apply_color_of_site c w row h]
  exact rootStep_liftZDirection5_eq_rootOfCoords w

/-- If no final-stage reset site is active at a source, the final-stage
substitution layer leaves every row unchanged. -/
theorem finalLiftSwappedRow_of_no_site
    (w : RootState) (row : TorusColor 5 ≃ TorusDirection 5)
    (h : ∀ c : TorusColor 5, ¬ finalLiftCarrySite c w) :
    finalLiftSwappedRow w row = row := by
  ext c
  simp [finalLiftSwappedRow, finalLiftSwapRowIf, h]

/-- Apply all Table D54-reset-ports substitutions to an already chosen base row.
The base row still comes from the terminal/layer chart; this transformer only
encodes the two unit-carry layers. -/
def resetPortSwappedRow (w : RootState)
    (row : TorusColor 5 ≃ TorusDirection 5) :
    TorusColor 5 ≃ TorusDirection 5 :=
  finalLiftSwappedRow w (firstLiftSwappedRow w row)

theorem resetPortSwappedRow_of_no_final_site
    (w : RootState) (row : TorusColor 5 ≃ TorusDirection 5)
    (hFinal : ∀ c : TorusColor 5, ¬ finalLiftCarrySite c w) :
    resetPortSwappedRow w row = firstLiftSwappedRow w row := by
  rw [resetPortSwappedRow,
    finalLiftSwappedRow_of_no_site w (firstLiftSwappedRow w row) hFinal]

theorem resetPortSwappedRow_of_no_site
    (w : RootState) (row : TorusColor 5 ≃ TorusDirection 5)
    (hFirst : ∀ i : Fin 3, ¬ firstLiftCarrySite (fin3ToFin5 i) w)
    (hFinal : ∀ c : TorusColor 5, ¬ finalLiftCarrySite c w) :
    resetPortSwappedRow w row = row := by
  rw [resetPortSwappedRow_of_no_final_site w row hFinal,
    firstLiftSwappedRow_of_no_site w row hFirst]

theorem resetPortSwappedRow_apply_color_of_final_site
    (c : TorusColor 5) (w : RootState)
    (row : TorusColor 5 ≃ TorusDirection 5)
    (h : finalLiftCarrySite c w) :
    resetPortSwappedRow w row c = liftZDirection5 := by
  simpa [resetPortSwappedRow] using
    finalLiftSwappedRow_apply_color_of_site c w (firstLiftSwappedRow w row) h

theorem rootStep_resetPortSwappedRow_color_of_final_site
    (c : TorusColor 5) (w : RootState)
    (row : TorusColor 5 ≃ TorusDirection 5)
    (h : finalLiftCarrySite c w) :
    LowD5M4Schedule.rootStep (resetPortSwappedRow w row c) w =
      rootOfCoords (qCoord w) (yCoord w) (zCoord w + 1) := by
  rw [resetPortSwappedRow_apply_color_of_final_site c w row h]
  exact rootStep_liftZDirection5_eq_rootOfCoords w

theorem resetPortSwappedRow_apply_fin3_of_first_site_of_no_final_site
    (i : Fin 3) (w : RootState)
    (row : TorusColor 5 ≃ TorusDirection 5)
    (hFirst : firstLiftCarrySite (fin3ToFin5 i) w)
    (hFinal : ∀ c : TorusColor 5, ¬ finalLiftCarrySite c w) :
    resetPortSwappedRow w row (fin3ToFin5 i) = liftYDirection5 := by
  rw [resetPortSwappedRow,
    finalLiftSwappedRow_of_no_site w (firstLiftSwappedRow w row) hFinal]
  exact firstLiftSwappedRow_apply_fin3_of_site i w row hFirst

theorem rootStep_resetPortSwappedRow_fin3_of_first_site_of_no_final_site
    (i : Fin 3) (w : RootState)
    (row : TorusColor 5 ≃ TorusDirection 5)
    (hFirst : firstLiftCarrySite (fin3ToFin5 i) w)
    (hFinal : ∀ c : TorusColor 5, ¬ finalLiftCarrySite c w) :
    LowD5M4Schedule.rootStep
        (resetPortSwappedRow w row (fin3ToFin5 i)) w =
      rootOfCoords (qCoord w) (yCoord w + 1) (zCoord w) := by
  rw [resetPortSwappedRow_apply_fin3_of_first_site_of_no_final_site
    i w row hFirst hFinal]
  exact rootStep_liftYDirection5_eq_rootOfCoords w

theorem rootStep_resetPortSwappedRow_color_of_no_final_site
    (c : TorusColor 5) (w : RootState)
    (row : TorusColor 5 ≃ TorusDirection 5)
    (hFinal : ∀ d : TorusColor 5, ¬ finalLiftCarrySite d w) :
    LowD5M4Schedule.rootStep (resetPortSwappedRow w row c) w =
      LowD5M4Schedule.rootStep (firstLiftSwappedRow w row c) w := by
  rw [resetPortSwappedRow_of_no_final_site w row hFinal]

theorem rootStep_resetPortSwappedRow_color_of_no_site
    (c : TorusColor 5) (w : RootState)
    (row : TorusColor 5 ≃ TorusDirection 5)
    (hFirst : ∀ i : Fin 3, ¬ firstLiftCarrySite (fin3ToFin5 i) w)
    (hFinal : ∀ d : TorusColor 5, ¬ finalLiftCarrySite d w) :
    LowD5M4Schedule.rootStep (resetPortSwappedRow w row c) w =
      LowD5M4Schedule.rootStep (row c) w := by
  rw [resetPortSwappedRow_of_no_site w row hFirst hFinal]

/-- The D5 seed's terminal carrier for indexed colors is exactly the indexed
terminal return from `TerminalA2LowMod`. -/
theorem F_terminalSymbolOfIndex (i : Fin 3) :
    LowD5M4.F (terminalSymbolOfIndex i) =
      terminalReturn (m := 4) i := by
  simpa [LowD5M4.F] using terminalSymbolStep_of_index (m := 4) i

/-- The local terminal-return root step, restated in the paper seed's `F_i`
notation. -/
theorem rootStep_terminalReturnTailBase_eq_F_terminalSymbolOfIndex
    (i : Fin 3) (q : LowD5M4.Q4) (y : LowD5M4.Y) (z : LowD5M4.Z) :
    LowD5M4Schedule.rootStep
        (terminalStdBaseRowEquiv5
          (terminalReturnTailBase i q) (fin3ToFin5 i))
        (rootOfCoords (terminalReturnTailBase i q) y z) =
      rootOfCoords (LowD5M4.F (terminalSymbolOfIndex i) q) y z := by
  rw [F_terminalSymbolOfIndex i]
  exact rootStep_terminalReturnTailBase_eq_terminalReturn i q y z

/-- The first three D5 paper returns, stated uniformly over the terminal color
index. This is Table D54-reset-ports for colors `0,1,2` in root coordinates. -/
theorem paperReturn_apply_terminal (i : Fin 3) (w : RootState) :
    paperReturn (fin3ToFin5 i) w =
      rootOfCoords
        (LowD5M4.F (terminalSymbolOfIndex i) (qCoord w))
        (yCoord w +
          EvenV11.UnitCarry.pointCarry
            (firstLiftSiteOfIndex i) (1 : ZMod 4) (qCoord w))
        (zCoord w +
          EvenV11.UnitCarry.pointCarry
            (LowD5M4.liftSite (fin3ToFin5 i)) (1 : ZMod 4)
            (qCoord w, yCoord w)) := by
  fin_cases i
  · simpa [fin3ToFin5, firstLiftSiteOfIndex, terminalSymbolOfIndex]
      using paperReturn_apply_zero w
  · simpa [fin3ToFin5, firstLiftSiteOfIndex, terminalSymbolOfIndex]
      using paperReturn_apply_one w
  · simpa [fin3ToFin5, firstLiftSiteOfIndex, terminalSymbolOfIndex]
      using paperReturn_apply_two w

theorem paperReturn_apply_finalSite (c : TorusColor 5) (w : RootState) :
    paperReturn c w =
      rootOfCoords
        (LowD5M4.baseReturn c (qCoord w, yCoord w)).1
        (LowD5M4.baseReturn c (qCoord w, yCoord w)).2
        (if finalLiftCarrySite c w then zCoord w + 1 else zCoord w) := by
  rw [paperReturn_apply, add_pointCarry_liftSite_eq_ite c w]

/-- The paper return before the final `Z` unit-carry lift: this is the
`R_i`-stage on `Q4 x Y`, transported to root coordinates and leaving `Z`
fixed. -/
def preFinalReturn (c : TorusColor 5) : RootState → RootState :=
  fun w =>
    rootOfCoords
      (LowD5M4.baseReturn c (qCoord w, yCoord w)).1
      (LowD5M4.baseReturn c (qCoord w, yCoord w)).2
      (zCoord w)

@[simp] theorem preFinalReturn_apply (c : TorusColor 5) (w : RootState) :
    preFinalReturn c w =
      rootOfCoords
        (LowD5M4.baseReturn c (qCoord w, yCoord w)).1
        (LowD5M4.baseReturn c (qCoord w, yCoord w)).2
        (zCoord w) := rfl

/-- The paper target at an active final `Z` carry site. -/
def finalCarryReturn (c : TorusColor 5) : RootState → RootState :=
  fun w =>
    rootOfCoords
      (LowD5M4.baseReturn c (qCoord w, yCoord w)).1
      (LowD5M4.baseReturn c (qCoord w, yCoord w)).2
      (zCoord w + 1)

@[simp] theorem finalCarryReturn_apply (c : TorusColor 5) (w : RootState) :
    finalCarryReturn c w =
      rootOfCoords
        (LowD5M4.baseReturn c (qCoord w, yCoord w)).1
        (LowD5M4.baseReturn c (qCoord w, yCoord w)).2
        (zCoord w + 1) := rfl

theorem paperReturn_eq_preFinalReturn_of_not_finalLiftCarrySite
    (c : TorusColor 5) (w : RootState)
    (hFinal : ¬ finalLiftCarrySite c w) :
    paperReturn c w = preFinalReturn c w := by
  simp [paperReturn_apply_finalSite, hFinal]

theorem paperReturn_eq_finalCarryReturn_of_finalLiftCarrySite
    (c : TorusColor 5) (w : RootState)
    (hFinal : finalLiftCarrySite c w) :
    paperReturn c w = finalCarryReturn c w := by
  simp [paperReturn_apply_finalSite, hFinal]

/-- The pre-final `R_i` target for terminal colors `0,1,2`: terminal carrier
plus the first `Y` unit-carry, with the final `Z` coordinate untouched. -/
theorem preFinalReturn_terminal_sites (i : Fin 3) (w : RootState) :
    preFinalReturn (fin3ToFin5 i) w =
      rootOfCoords
        (LowD5M4.F (terminalSymbolOfIndex i) (qCoord w))
        (if firstLiftCarrySite (fin3ToFin5 i) w then
          yCoord w + 1
        else
          yCoord w)
        (zCoord w) := by
  fin_cases i
  · by_cases h : qCoord w = LowD5M4.p0 <;>
      simp [preFinalReturn, LowD5M4.baseReturn, LowD5M4.T,
        firstLiftCarrySite, fin3ToFin5, terminalSymbolOfIndex,
        EvenV11.UnitCarry.additiveSkewMap, Shared.skewProductMap,
        EvenV11.UnitCarry.pointCarry, h]
  · by_cases h : qCoord w = LowD5M4.p1 <;>
      simp [preFinalReturn, LowD5M4.baseReturn, LowD5M4.T,
        firstLiftCarrySite, fin3ToFin5, terminalSymbolOfIndex,
        EvenV11.UnitCarry.additiveSkewMap, Shared.skewProductMap,
        EvenV11.UnitCarry.pointCarry, h]
  · by_cases h : qCoord w = LowD5M4.p2 <;>
      simp [preFinalReturn, LowD5M4.baseReturn, LowD5M4.T,
        firstLiftCarrySite, fin3ToFin5, terminalSymbolOfIndex,
        EvenV11.UnitCarry.additiveSkewMap, Shared.skewProductMap,
        EvenV11.UnitCarry.pointCarry, h]

/-- The pre-final `R_3=P0` target from paper §11, equation (63). -/
theorem preFinalReturn_three (w : RootState) :
    preFinalReturn 3 w =
      rootOfCoords
        (if yCoord w = 0 then
          LowD5M4.F TerminalSymbol.F0 (qCoord w)
        else
          qCoord w)
        (yCoord w + 1)
        (zCoord w) := by
  simp [preFinalReturn, LowD5M4.baseReturn, LowD5M4.P0]

/-- The pre-final `R_4=P1` target from paper §11, equation (66). -/
theorem preFinalReturn_four (w : RootState) :
    preFinalReturn 4 w =
      rootOfCoords
        (if yCoord w = 1 then
          LowD5M4.F TerminalSymbol.F0 (qCoord w)
        else if yCoord w = 2 then
          LowD5M4.F TerminalSymbol.F2 (qCoord w)
        else if yCoord w = 3 then
          LowD5M4.F TerminalSymbol.F1 (qCoord w)
        else
          qCoord w)
        (yCoord w + 1)
        (zCoord w) := by
  simp [preFinalReturn, LowD5M4.baseReturn, LowD5M4.P1]

/-- The final-carry target for terminal colors `0,1,2`, after the final
`Z` unit-carry site has fired. -/
theorem finalCarryReturn_terminal_sites (i : Fin 3) (w : RootState) :
    finalCarryReturn (fin3ToFin5 i) w =
      rootOfCoords
        (LowD5M4.F (terminalSymbolOfIndex i) (qCoord w))
        (if firstLiftCarrySite (fin3ToFin5 i) w then
          yCoord w + 1
        else
          yCoord w)
        (zCoord w + 1) := by
  fin_cases i
  · by_cases h : qCoord w = LowD5M4.p0 <;>
      simp [finalCarryReturn, LowD5M4.baseReturn, LowD5M4.T,
        firstLiftCarrySite, fin3ToFin5, terminalSymbolOfIndex,
        EvenV11.UnitCarry.additiveSkewMap, Shared.skewProductMap,
        EvenV11.UnitCarry.pointCarry, h]
  · by_cases h : qCoord w = LowD5M4.p1 <;>
      simp [finalCarryReturn, LowD5M4.baseReturn, LowD5M4.T,
        firstLiftCarrySite, fin3ToFin5, terminalSymbolOfIndex,
        EvenV11.UnitCarry.additiveSkewMap, Shared.skewProductMap,
        EvenV11.UnitCarry.pointCarry, h]
  · by_cases h : qCoord w = LowD5M4.p2 <;>
      simp [finalCarryReturn, LowD5M4.baseReturn, LowD5M4.T,
        firstLiftCarrySite, fin3ToFin5, terminalSymbolOfIndex,
        EvenV11.UnitCarry.additiveSkewMap, Shared.skewProductMap,
        EvenV11.UnitCarry.pointCarry, h]

/-- The final-carry target for `R_3=P0`. -/
theorem finalCarryReturn_three (w : RootState) :
    finalCarryReturn 3 w =
      rootOfCoords
        (if yCoord w = 0 then
          LowD5M4.F TerminalSymbol.F0 (qCoord w)
        else
          qCoord w)
        (yCoord w + 1)
        (zCoord w + 1) := by
  simp [finalCarryReturn, LowD5M4.baseReturn, LowD5M4.P0]

/-- The final-carry target for `R_4=P1`. -/
theorem finalCarryReturn_four (w : RootState) :
    finalCarryReturn 4 w =
      rootOfCoords
        (if yCoord w = 1 then
          LowD5M4.F TerminalSymbol.F0 (qCoord w)
        else if yCoord w = 2 then
          LowD5M4.F TerminalSymbol.F2 (qCoord w)
        else if yCoord w = 3 then
          LowD5M4.F TerminalSymbol.F1 (qCoord w)
        else
          qCoord w)
        (yCoord w + 1)
        (zCoord w + 1) := by
  simp [finalCarryReturn, LowD5M4.baseReturn, LowD5M4.P1]

/-- Table D54-reset-ports for terminal colors in the same site/if form as the
local row-switch lemmas. -/
theorem paperReturn_apply_terminal_sites (i : Fin 3) (w : RootState) :
    paperReturn (fin3ToFin5 i) w =
      rootOfCoords
        (LowD5M4.F (terminalSymbolOfIndex i) (qCoord w))
        (if firstLiftCarrySite (fin3ToFin5 i) w then
          yCoord w + 1
        else
          yCoord w)
        (if finalLiftCarrySite (fin3ToFin5 i) w then
          zCoord w + 1
        else
          zCoord w) := by
  rw [paperReturn_apply_terminal,
    add_pointCarry_firstLiftSiteOfIndex_eq_ite,
    add_pointCarry_liftSite_eq_ite]

/-- The terminal factor inserted by the `Y`-row word for colors `3` and `4`.
Colors `0,1,2` use the terminal row continuously and have no separate `Y`
reset factor. -/
def yResetTerminalFactor (c : TorusColor 5) (y : LowD5M4.Y) :
    Option TerminalSymbol :=
  match c with
  | 0 => none
  | 1 => none
  | 2 => none
  | 3 => if y = 0 then some TerminalSymbol.F0 else none
  | 4 =>
      if y = 1 then some TerminalSymbol.F0
      else if y = 2 then some TerminalSymbol.F2
      else if y = 3 then some TerminalSymbol.F1
      else none

/-- Apply the D54 reset-port substitutions pointwise to an arbitrary base
layer-row family. This isolates the paper's Table D54-reset-ports from the
remaining choice of terminal/layer chart. -/
def resetPortRowOfBase
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5 :=
  fun t w => resetPortSwappedRow w (baseRow t w)

@[simp] theorem resetPortRowOfBase_apply
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (t : ZMod 4) (w : RootState) :
    resetPortRowOfBase baseRow t w = resetPortSwappedRow w (baseRow t w) :=
  rfl

/-- Build a direction table from explicit Latin rows. This is the intended
interface for the paper construction: the terminal row word and each two-entry
switch should produce an equivalence `Color ~= Direction` at every source. -/
def dirOfRowEquiv
    (row : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    ZMod 4 → RootState → TorusColor 5 → TorusDirection 5 :=
  fun t w c => row t w c

@[simp] theorem dirOfRowEquiv_apply
    (row : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (t : ZMod 4) (w : RootState) (c : TorusColor 5) :
    dirOfRowEquiv row t w c = row t w c :=
  rfl

theorem layerMap_dirOfRowEquiv_apply
    (row : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (t : ZMod 4) (c : TorusColor 5) (w : RootState) :
    (LowD5M4Schedule.schedule (dirOfRowEquiv row)).layerMap t c w =
      LowD5M4Schedule.rootStep (row t w c) w :=
  rfl

theorem layerMap_resetPortRowOfBase_apply
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (t : ZMod 4) (c : TorusColor 5) (w : RootState) :
    (LowD5M4Schedule.schedule
      (dirOfRowEquiv (resetPortRowOfBase baseRow))).layerMap t c w =
      LowD5M4Schedule.rootStep
        (resetPortSwappedRow w (baseRow t w) c) w :=
  rfl

theorem rowLatin_of_rowEquiv
    (row : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    (LowD5M4Schedule.schedule (dirOfRowEquiv row)).rowLatin := by
  intro t w
  exact (row t w).bijective

/-- RF1 for the reset-port transformer: once the base row is represented as an
equivalence at each source, all Table D54-reset-ports substitutions preserve
Latin rows by construction. -/
theorem rowLatin_of_resetPortRowOfBase
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    (LowD5M4Schedule.schedule
      (dirOfRowEquiv (resetPortRowOfBase baseRow))).rowLatin :=
  rowLatin_of_rowEquiv (resetPortRowOfBase baseRow)

/-- RF2 obligation for a base row after applying the paper reset-port
substitutions. -/
def ResetPortLayerBijectiveGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  (LowD5M4Schedule.schedule
    (dirOfRowEquiv (resetPortRowOfBase baseRow))).layerBijective

/-- RF2 data in the direct form used by paper RF2 class (ii): for every
layer/color row, identify the realized layer map with an explicit equivalence
of the root-flat section.  This keeps skew-product lift proofs separate from
the local partial-exchange interface below. -/
structure ResetPortLayerEquivData
    (baseRow : ResetPortBaseRow) where
  layerEquiv : ZMod 4 → TorusColor 5 → RootState ≃ RootState
  layerMap_eq :
    ∀ t c w,
      (LowD5M4Schedule.schedule
        (dirOfRowEquiv (resetPortRowOfBase baseRow))).layerMap t c w =
        layerEquiv t c w

theorem resetPortLayerBijective_of_layerEquivData
    (baseRow : ResetPortBaseRow)
    (data : ResetPortLayerEquivData baseRow) :
    ResetPortLayerBijectiveGoal baseRow :=
  Shared.RootFlatSchedule.layerBijective_of_layerMap_apply_eq
    (S := LowD5M4Schedule.schedule
      (dirOfRowEquiv (resetPortRowOfBase baseRow)))
    (fun t c => data.layerEquiv t c)
    (fun t c => (data.layerEquiv t c).bijective)
    data.layerMap_eq

/-- Transport a bijection of the paper seed coordinates
`(Q4 × Y) × Z` to the standard root-flat section. -/
def rootEquivOfSeedEquiv (e : Seed ≃ Seed) : RootState ≃ RootState :=
  (seedRootEquiv.symm.trans e).trans seedRootEquiv

@[simp] theorem rootEquivOfSeedEquiv_apply
    (e : Seed ≃ Seed) (w : RootState) :
    rootEquivOfSeedEquiv e w = seedRootEquiv (e (seedRootEquiv.symm w)) :=
  rfl

/-- RF2 class (ii) data from the paper: in the paper coordinates
`(Q4 × Y) × Z`, every layer/color map is a skew-product lift over a bijective
base map, with a bijective fiber map depending on the base point. -/
structure ResetPortLayerSkewProductData
    (baseRow : ResetPortBaseRow) where
  baseStep : ZMod 4 → TorusColor 5 → LowD5M4.Q4 × LowD5M4.Y ≃
    LowD5M4.Q4 × LowD5M4.Y
  fiberStep : ZMod 4 → TorusColor 5 → LowD5M4.Q4 × LowD5M4.Y →
    LowD5M4.Z ≃ LowD5M4.Z
  layerMap_eq :
    ∀ t c w,
      seedRootEquiv.symm
          ((LowD5M4Schedule.schedule
            (dirOfRowEquiv (resetPortRowOfBase baseRow))).layerMap t c w) =
        Shared.skewProductMap (baseStep t c)
          (fun x z => fiberStep t c x z) (seedRootEquiv.symm w)

/-- The explicit seed-coordinate skew-product equivalence associated to
`ResetPortLayerSkewProductData`. -/
noncomputable def seedSkewProductLayerEquiv
    {baseRow : ResetPortBaseRow}
    (data : ResetPortLayerSkewProductData baseRow)
    (t : ZMod 4) (c : TorusColor 5) : Seed ≃ Seed :=
  Equiv.ofBijective
    (Shared.skewProductMap (data.baseStep t c)
      (fun x z => data.fiberStep t c x z))
    (Shared.skewProductMap_bijective
      (data.baseStep t c) (fun x z => data.fiberStep t c x z)
      (data.baseStep t c).bijective
      (fun x => (data.fiberStep t c x).bijective))

theorem seedSkewProductLayerEquiv_apply
    {baseRow : ResetPortBaseRow}
    (data : ResetPortLayerSkewProductData baseRow)
    (t : ZMod 4) (c : TorusColor 5) (x : Seed) :
    seedSkewProductLayerEquiv data t c x =
      Shared.skewProductMap (data.baseStep t c)
        (fun y z => data.fiberStep t c y z) x :=
  rfl

/-- Convert the paper's RF2 class (ii) skew-product lift data into the direct
layer-equivalence RF2 interface used by the H2 handoff. -/
noncomputable def resetPortLayerEquivData_of_layerSkewProductData
    (baseRow : ResetPortBaseRow)
    (data : ResetPortLayerSkewProductData baseRow) :
    ResetPortLayerEquivData baseRow where
  layerEquiv := fun t c =>
    rootEquivOfSeedEquiv (seedSkewProductLayerEquiv data t c)
  layerMap_eq := by
    intro t c w
    apply seedRootEquiv.symm.injective
    rw [data.layerMap_eq]
    simp [rootEquivOfSeedEquiv, seedSkewProductLayerEquiv_apply]

theorem resetPortLayerBijective_of_layerSkewProductData
    (baseRow : ResetPortBaseRow)
    (data : ResetPortLayerSkewProductData baseRow) :
    ResetPortLayerBijectiveGoal baseRow :=
  resetPortLayerBijective_of_layerEquivData baseRow
    (resetPortLayerEquivData_of_layerSkewProductData baseRow data)

/-- RF2 interface for reset-port rows when each layer map is identified with
the left half of a paper switching-ribbon partial exchange. -/
theorem resetPortLayerBijective_of_partialExchangeLeft_eq
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (T R : ZMod 4 → TorusColor 5 → RootState ≃ RootState)
    (U : ZMod 4 → TorusColor 5 → Set RootState)
    [∀ t c w, Decidable (w ∈ U t c)]
    (hU : ∀ t c, ComparisonSetInvariant (T t c) (R t c) (U t c))
    (hLayer :
      ∀ t c w,
        (LowD5M4Schedule.schedule
          (dirOfRowEquiv (resetPortRowOfBase baseRow))).layerMap t c w =
          partialExchangeLeft (T t c) (R t c) (U t c) w) :
    ResetPortLayerBijectiveGoal baseRow :=
  rootFlatLayerBijective_of_partialExchangeLeft_eq
    (LowD5M4Schedule.schedule
      (dirOfRowEquiv (resetPortRowOfBase baseRow)))
    T R U hU hLayer

/-- RF2 interface for reset-port rows when each layer map is identified with
the right half of a paper switching-ribbon partial exchange. -/
theorem resetPortLayerBijective_of_partialExchangeRight_eq
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (T R : ZMod 4 → TorusColor 5 → RootState ≃ RootState)
    (U : ZMod 4 → TorusColor 5 → Set RootState)
    [∀ t c w, Decidable (w ∈ U t c)]
    (hU : ∀ t c, ComparisonSetInvariant (T t c) (R t c) (U t c))
    (hLayer :
      ∀ t c w,
        (LowD5M4Schedule.schedule
          (dirOfRowEquiv (resetPortRowOfBase baseRow))).layerMap t c w =
          partialExchangeRight (T t c) (R t c) (U t c) w) :
    ResetPortLayerBijectiveGoal baseRow :=
  rootFlatLayerBijective_of_partialExchangeRight_eq
    (LowD5M4Schedule.schedule
      (dirOfRowEquiv (resetPortRowOfBase baseRow)))
    T R U hU hLayer

/-- RF2 interface for reset-port rows when each layer chooses one side of a
paper switching-ribbon partial exchange. -/
theorem resetPortLayerBijective_of_partialExchangeChoice_eq
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (T R : ZMod 4 → TorusColor 5 → RootState ≃ RootState)
    (U : ZMod 4 → TorusColor 5 → Set RootState)
    (chooseLeft : ZMod 4 → TorusColor 5 → Bool)
    [∀ t c w, Decidable (w ∈ U t c)]
    (hU : ∀ t c, ComparisonSetInvariant (T t c) (R t c) (U t c))
    (hLayer :
      ∀ t c w,
        (LowD5M4Schedule.schedule
          (dirOfRowEquiv (resetPortRowOfBase baseRow))).layerMap t c w =
          (if chooseLeft t c then
            partialExchangeLeft (T t c) (R t c) (U t c)
          else
            partialExchangeRight (T t c) (R t c) (U t c)) w) :
    ResetPortLayerBijectiveGoal baseRow :=
  rootFlatLayerBijective_of_partialExchangeChoice_eq
    (LowD5M4Schedule.schedule
      (dirOfRowEquiv (resetPortRowOfBase baseRow)))
    T R U chooseLeft hU hLayer

/-- Paper §11 RF2 data for reset-port rows. It packages the comparison maps
`T`, `R`, the comparison set `U`, the side choice, the invariant
`T^{-1} R(U) = U`, and the pointwise identification of each layer map with the
corresponding partial exchange. -/
structure ResetPortPartialExchangeLayerData
    (baseRow : ResetPortBaseRow) where
  T : ZMod 4 → TorusColor 5 → RootState ≃ RootState
  R : ZMod 4 → TorusColor 5 → RootState ≃ RootState
  U : ZMod 4 → TorusColor 5 → Set RootState
  chooseLeft : ZMod 4 → TorusColor 5 → Bool
  [decidableMem : ∀ t c w, Decidable (w ∈ U t c)]
  invariant : ∀ t c, ComparisonSetInvariant (T t c) (R t c) (U t c)
  layerMap_eq :
    ∀ t c w,
      (LowD5M4Schedule.schedule
        (dirOfRowEquiv (resetPortRowOfBase baseRow))).layerMap t c w =
        (if chooseLeft t c then
          partialExchangeLeft (T t c) (R t c) (U t c)
        else
          partialExchangeRight (T t c) (R t c) (U t c)) w

theorem resetPortLayerBijective_of_partialExchangeLayerData
    (baseRow : ResetPortBaseRow)
    (data : ResetPortPartialExchangeLayerData baseRow) :
    ResetPortLayerBijectiveGoal baseRow := by
  letI := data.decidableMem
  exact resetPortLayerBijective_of_partialExchangeChoice_eq
    baseRow data.T data.R data.U data.chooseLeft data.invariant data.layerMap_eq

/-- Paper §11 RF2 data specialized to a single switching site in each
layer/color row.  This is the common case for the reset-port substitutions:
two Latin rows are compared at one common-image site, and the chosen side of the
partial exchange is the realized layer map. -/
structure ResetPortSingletonSwitchLayerData
    (baseRow : ResetPortBaseRow) where
  T : ZMod 4 → TorusColor 5 → RootState ≃ RootState
  R : ZMod 4 → TorusColor 5 → RootState ≃ RootState
  site : ZMod 4 → TorusColor 5 → RootState
  chooseLeft : ZMod 4 → TorusColor 5 → Bool
  commonImage : ∀ t c, T t c (site t c) = R t c (site t c)
  layerMap_eq :
    ∀ t c w,
      (LowD5M4Schedule.schedule
        (dirOfRowEquiv (resetPortRowOfBase baseRow))).layerMap t c w =
        (if chooseLeft t c then
          partialExchangeLeft (T t c) (R t c) ({site t c} : Set RootState)
        else
          partialExchangeRight (T t c) (R t c) ({site t c} : Set RootState)) w

def resetPortPartialExchangeLayerData_of_singletonSwitchLayerData
    (baseRow : ResetPortBaseRow)
    (data : ResetPortSingletonSwitchLayerData baseRow) :
    ResetPortPartialExchangeLayerData baseRow where
  T := data.T
  R := data.R
  U := fun t c => ({data.site t c} : Set RootState)
  chooseLeft := data.chooseLeft
  decidableMem := fun _ _ _ => inferInstance
  invariant := fun t c =>
    comparisonSetInvariant_singleton_of_common_image
      (data.commonImage t c)
  layerMap_eq := data.layerMap_eq

theorem resetPortLayerBijective_of_singletonSwitchLayerData
    (baseRow : ResetPortBaseRow)
    (data : ResetPortSingletonSwitchLayerData baseRow) :
    ResetPortLayerBijectiveGoal baseRow :=
  resetPortLayerBijective_of_partialExchangeLayerData baseRow
    (resetPortPartialExchangeLayerData_of_singletonSwitchLayerData
      baseRow data)

noncomputable def resetPortLayerEquivData_of_singletonSwitchLayerData
    (baseRow : ResetPortBaseRow)
    (data : ResetPortSingletonSwitchLayerData baseRow) :
    ResetPortLayerEquivData baseRow where
  layerEquiv := fun t c =>
    if h : data.chooseLeft t c then
      partialExchangeLeftEquiv (data.T t c) (data.R t c)
        ({data.site t c} : Set RootState)
        (comparisonSetInvariant_singleton_of_common_image
          (data.commonImage t c))
    else
      partialExchangeRightEquiv (data.T t c) (data.R t c)
        ({data.site t c} : Set RootState)
        (comparisonSetInvariant_singleton_of_common_image
          (data.commonImage t c))
  layerMap_eq := by
    intro t c w
    by_cases h : data.chooseLeft t c
    · rw [data.layerMap_eq, if_pos h]
      simp [h, partialExchangeLeftEquiv_apply]
    · rw [data.layerMap_eq, if_neg h]
      simp [h, partialExchangeRightEquiv_apply]

/-- Four-layer return-map obligation for a base row after applying the paper
reset-port substitutions. -/
def ResetPortFourLayerRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  FourLayerRealizationGoal
    (dirOfRowEquiv (resetPortRowOfBase baseRow))

/-- The reset-port direction table induced by a base row family. -/
def resetPortDirOfBase
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    ZMod 4 → RootState → TorusColor 5 → TorusDirection 5 :=
  dirOfRowEquiv (resetPortRowOfBase baseRow)

theorem resetPortDirOfBase_eq
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    resetPortDirOfBase baseRow =
      dirOfRowEquiv (resetPortRowOfBase baseRow) :=
  rfl

@[simp] theorem resetPortDirOfBase_apply
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (t : ZMod 4) (w : RootState) (c : TorusColor 5) :
    resetPortDirOfBase baseRow t w c =
      resetPortSwappedRow w (baseRow t w) c :=
  rfl

theorem layerMap_resetPortDirOfBase_apply
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (t : ZMod 4) (c : TorusColor 5) (w : RootState) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t c w =
      LowD5M4Schedule.rootStep
        (resetPortSwappedRow w (baseRow t w) c) w :=
  rfl

theorem layerMap_resetPortDirOfBase_color_of_final_site
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (t : ZMod 4) (c : TorusColor 5) (w : RootState)
    (h : finalLiftCarrySite c w) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t c w =
      rootOfCoords (qCoord w) (yCoord w) (zCoord w + 1) := by
  rw [layerMap_resetPortDirOfBase_apply]
  exact rootStep_resetPortSwappedRow_color_of_final_site
    c w (baseRow t w) h

theorem layerMap_resetPortDirOfBase_fin3_of_first_site_of_no_final_site
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (t : ZMod 4) (i : Fin 3) (w : RootState)
    (hFirst : firstLiftCarrySite (fin3ToFin5 i) w)
    (hFinal : ∀ c : TorusColor 5, ¬ finalLiftCarrySite c w) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t (fin3ToFin5 i) w =
      rootOfCoords (qCoord w) (yCoord w + 1) (zCoord w) := by
  rw [layerMap_resetPortDirOfBase_apply]
  exact rootStep_resetPortSwappedRow_fin3_of_first_site_of_no_final_site
    i w (baseRow t w) hFirst hFinal

theorem layerMap_resetPortDirOfBase_color_of_no_site
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (t : ZMod 4) (c : TorusColor 5) (w : RootState)
    (hFirst : ∀ i : Fin 3, ¬ firstLiftCarrySite (fin3ToFin5 i) w)
    (hFinal : ∀ d : TorusColor 5, ¬ finalLiftCarrySite d w) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t c w =
      LowD5M4Schedule.rootStep (baseRow t w c) w := by
  rw [layerMap_resetPortDirOfBase_apply]
  exact rootStep_resetPortSwappedRow_color_of_no_site
    c w (baseRow t w) hFirst hFinal

/-- If no reset-port site is active, a layer step is just the base-row
direction chosen for that color. This is the main inactive-source adapter for
path calculations. -/
theorem layerMap_resetPortDirOfBase_of_baseColor_of_no_site
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (t : ZMod 4) (c : TorusColor 5) (w : RootState)
    (d : TorusDirection 5)
    (hBase : baseRow t w c = d)
    (hFirst : ∀ i : Fin 3, ¬ firstLiftCarrySite (fin3ToFin5 i) w)
    (hFinal : ∀ e : TorusColor 5, ¬ finalLiftCarrySite e w) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t c w =
      LowD5M4Schedule.rootStep d w := by
  rw [layerMap_resetPortDirOfBase_color_of_no_site
    baseRow t c w hFirst hFinal, hBase]

/-- In an inactive source, if the base row is the charted terminal row word,
then a terminal color performs the corresponding A2 row jump. -/
theorem layerMap_resetPortDirOfBase_terminalStdBaseRow_fin3_of_no_site
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (t : ZMod 4) (i : Fin 3) (w : RootState)
    (hBase :
      baseRow t w (fin3ToFin5 i) =
        terminalStdBaseRowEquiv5 (qCoord w) (fin3ToFin5 i))
    (hFirst : ∀ j : Fin 3, ¬ firstLiftCarrySite (fin3ToFin5 j) w)
    (hFinal : ∀ c : TorusColor 5, ¬ finalLiftCarrySite c w) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t (fin3ToFin5 i) w =
      rootOfCoords
        (qCoord w +
          terminalVertex (m := 4)
            (terminalRowEquiv (terminalOmega (qCoord w)) i))
        (yCoord w) (zCoord w) := by
  rw [layerMap_resetPortDirOfBase_of_baseColor_of_no_site
    baseRow t (fin3ToFin5 i) w
      (terminalStdBaseRowEquiv5 (qCoord w) (fin3ToFin5 i))
      hBase hFirst hFinal]
  exact rootStep_terminalStdRowEquiv5_fin3_eq_rootOfCoords
    (terminalOmega (qCoord w)) i w

/-- In an inactive source at the paper's terminal tail base, the charted
terminal row realizes the local jump `eta_i`. -/
theorem layerMap_resetPortDirOfBase_terminalTailBase_of_no_site
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (t : ZMod 4) (i : Fin 3)
    (q : LowD5M4.Q4) (y : LowD5M4.Y) (z : LowD5M4.Z)
    (hBase :
      baseRow t (rootOfCoords (terminalTailBase i q) y z)
          (fin3ToFin5 i) =
        terminalStdBaseRowEquiv5 (terminalTailBase i q) (fin3ToFin5 i))
    (hFirst :
      ∀ j : Fin 3,
        ¬ firstLiftCarrySite (fin3ToFin5 j)
          (rootOfCoords (terminalTailBase i q) y z))
    (hFinal :
      ∀ c : TorusColor 5,
        ¬ finalLiftCarrySite c
          (rootOfCoords (terminalTailBase i q) y z)) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t (fin3ToFin5 i)
        (rootOfCoords (terminalTailBase i q) y z) =
      rootOfCoords (terminalEta (m := 4) i q) y z := by
  rw [layerMap_resetPortDirOfBase_of_baseColor_of_no_site
    baseRow t (fin3ToFin5 i)
      (rootOfCoords (terminalTailBase i q) y z)
      (terminalStdBaseRowEquiv5 (terminalTailBase i q) (fin3ToFin5 i))
      hBase hFirst hFinal]
  exact rootStep_terminalTailBase_eq_terminalEta i q y z

/-- In an inactive source at the paper's run-collapsed terminal tail base, the
charted terminal row realizes the seed carrier `F_i`. -/
theorem layerMap_resetPortDirOfBase_terminalReturnTailBase_of_no_site
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (t : ZMod 4) (i : Fin 3)
    (q : LowD5M4.Q4) (y : LowD5M4.Y) (z : LowD5M4.Z)
    (hBase :
      baseRow t (rootOfCoords (terminalReturnTailBase i q) y z)
          (fin3ToFin5 i) =
        terminalStdBaseRowEquiv5
          (terminalReturnTailBase i q) (fin3ToFin5 i))
    (hFirst :
      ∀ j : Fin 3,
        ¬ firstLiftCarrySite (fin3ToFin5 j)
          (rootOfCoords (terminalReturnTailBase i q) y z))
    (hFinal :
      ∀ c : TorusColor 5,
        ¬ finalLiftCarrySite c
          (rootOfCoords (terminalReturnTailBase i q) y z)) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t (fin3ToFin5 i)
        (rootOfCoords (terminalReturnTailBase i q) y z) =
      rootOfCoords (LowD5M4.F (terminalSymbolOfIndex i) q) y z := by
  rw [layerMap_resetPortDirOfBase_of_baseColor_of_no_site
    baseRow t (fin3ToFin5 i)
      (rootOfCoords (terminalReturnTailBase i q) y z)
      (terminalStdBaseRowEquiv5
        (terminalReturnTailBase i q) (fin3ToFin5 i))
      hBase hFirst hFinal]
  exact rootStep_terminalReturnTailBase_eq_F_terminalSymbolOfIndex i q y z

/-- In an inactive source at the paper's run-collapsed terminal tail base, any
active D5 color can read the row direction belonging to a terminal symbol. This
is the adapter used for the `P₀`/`P₁` row-word terminal factors. -/
theorem layerMap_resetPortDirOfBase_terminalReturnTailBaseOfSymbol_of_no_site
    (baseRow : ResetPortBaseRow)
    (t : ZMod 4) (c : TorusColor 5) (s : TerminalSymbol)
    (q : LowD5M4.Q4) (y : LowD5M4.Y) (z : LowD5M4.Z)
    (hBase :
      baseRow t (rootOfCoords (terminalReturnTailBaseOfSymbol s q) y z) c =
        terminalStdBaseRowEquiv5
          (terminalReturnTailBaseOfSymbol s q)
          (fin3ToFin5 (terminalIndexOfSymbol s)))
    (hFirst :
      ∀ j : Fin 3,
        ¬ firstLiftCarrySite (fin3ToFin5 j)
          (rootOfCoords (terminalReturnTailBaseOfSymbol s q) y z))
    (hFinal :
      ∀ d : TorusColor 5,
        ¬ finalLiftCarrySite d
          (rootOfCoords (terminalReturnTailBaseOfSymbol s q) y z)) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t c
        (rootOfCoords (terminalReturnTailBaseOfSymbol s q) y z) =
      rootOfCoords (LowD5M4.F s q) y z := by
  rw [layerMap_resetPortDirOfBase_of_baseColor_of_no_site
    baseRow t c
      (rootOfCoords (terminalReturnTailBaseOfSymbol s q) y z)
      (terminalStdBaseRowEquiv5
        (terminalReturnTailBaseOfSymbol s q)
        (fin3ToFin5 (terminalIndexOfSymbol s)))
        hBase hFirst hFinal]
  exact rootStep_terminalReturnTailBaseOfSymbol_eq_F s q y z

/-- The last-layer row-word read required at a collapsed terminal tail for the
terminal color indexed by `i`. This isolates the paper row-word obligation from
the three preceding path layers. -/
def BaseRowReadsTerminalTailIndex
    (baseRow : ResetPortBaseRow) (t : ZMod 4) (i : Fin 3)
    (q : LowD5M4.Q4) (y : LowD5M4.Y) (z : LowD5M4.Z) : Prop :=
  baseRow t (rootOfCoords (terminalReturnTailBase i q) y z) (fin3ToFin5 i) =
    terminalStdBaseRowEquiv5 (terminalReturnTailBase i q) (fin3ToFin5 i)

/-- The last-layer row-word read required at a collapsed terminal tail when an
arbitrary active D5 color must realize terminal symbol `s`. This is the paper
`P₀`/`P₁` terminal-factor interface. -/
def BaseRowReadsTerminalTailSymbol
    (baseRow : ResetPortBaseRow) (t : ZMod 4) (c : TorusColor 5)
    (s : TerminalSymbol) (q : LowD5M4.Q4)
    (y : LowD5M4.Y) (z : LowD5M4.Z) : Prop :=
  baseRow t (rootOfCoords (terminalReturnTailBaseOfSymbol s q) y z) c =
    terminalStdBaseRowEquiv5
      (terminalReturnTailBaseOfSymbol s q)
      (fin3ToFin5 (terminalIndexOfSymbol s))

/-- The last-layer row-word read required for the pure `Y`-shift factor of the
paper `P₀`/`P₁` words. -/
def BaseRowReadsYShift
    (baseRow : ResetPortBaseRow) (t : ZMod 4) (c : TorusColor 5)
    (q : LowD5M4.Q4) (y : LowD5M4.Y) (z : LowD5M4.Z) : Prop :=
  baseRow t (rootOfCoords q y z) c = liftYDirection5

theorem layerMap_resetPortDirOfBase_of_terminalTailIndexRead_no_site
    (baseRow : ResetPortBaseRow) (t : ZMod 4) (i : Fin 3)
    (q : LowD5M4.Q4) (y : LowD5M4.Y) (z : LowD5M4.Z)
    (hBase : BaseRowReadsTerminalTailIndex baseRow t i q y z)
    (hFirst :
      ∀ j : Fin 3,
        ¬ firstLiftCarrySite (fin3ToFin5 j)
          (rootOfCoords (terminalReturnTailBase i q) y z))
    (hFinal :
      ∀ c : TorusColor 5,
        ¬ finalLiftCarrySite c
          (rootOfCoords (terminalReturnTailBase i q) y z)) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t (fin3ToFin5 i)
        (rootOfCoords (terminalReturnTailBase i q) y z) =
      rootOfCoords (LowD5M4.F (terminalSymbolOfIndex i) q) y z :=
  layerMap_resetPortDirOfBase_terminalReturnTailBase_of_no_site
    baseRow t i q y z hBase hFirst hFinal

theorem layerMap_resetPortDirOfBase_of_terminalTailSymbolRead_no_site
    (baseRow : ResetPortBaseRow) (t : ZMod 4) (c : TorusColor 5)
    (s : TerminalSymbol) (q : LowD5M4.Q4)
    (y : LowD5M4.Y) (z : LowD5M4.Z)
    (hBase : BaseRowReadsTerminalTailSymbol baseRow t c s q y z)
    (hFirst :
      ∀ j : Fin 3,
        ¬ firstLiftCarrySite (fin3ToFin5 j)
          (rootOfCoords (terminalReturnTailBaseOfSymbol s q) y z))
    (hFinal :
      ∀ d : TorusColor 5,
        ¬ finalLiftCarrySite d
          (rootOfCoords (terminalReturnTailBaseOfSymbol s q) y z)) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t c
        (rootOfCoords (terminalReturnTailBaseOfSymbol s q) y z) =
      rootOfCoords (LowD5M4.F s q) y z :=
  layerMap_resetPortDirOfBase_terminalReturnTailBaseOfSymbol_of_no_site
    baseRow t c s q y z hBase hFirst hFinal

theorem layerMap_resetPortDirOfBase_of_yShiftRead_no_site
    (baseRow : ResetPortBaseRow) (t : ZMod 4) (c : TorusColor 5)
    (q : LowD5M4.Q4) (y : LowD5M4.Y) (z : LowD5M4.Z)
    (hBase : BaseRowReadsYShift baseRow t c q y z)
    (hFirst :
      ∀ j : Fin 3,
        ¬ firstLiftCarrySite (fin3ToFin5 j)
          (rootOfCoords q y z))
    (hFinal :
      ∀ d : TorusColor 5,
        ¬ finalLiftCarrySite d
          (rootOfCoords q y z)) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t c
        (rootOfCoords q y z) =
      rootOfCoords q (y + 1) z := by
  rw [layerMap_resetPortDirOfBase_of_baseColor_of_no_site
    baseRow t c (rootOfCoords q y z) liftYDirection5
    hBase hFirst hFinal]
  exact rootStep_liftYDirection5_eq_rootOfCoords (rootOfCoords q y z)

/-- No first-stage reset-port site is active at this source. -/
def NoFirstLiftSites (w : RootState) : Prop :=
  ∀ i : Fin 3, ¬ firstLiftCarrySite (fin3ToFin5 i) w

/-- No final-stage reset-port site is active at this source. -/
def NoFinalLiftSites (w : RootState) : Prop :=
  ∀ c : TorusColor 5, ¬ finalLiftCarrySite c w

/-- No reset-port substitution is active at this source. -/
def NoResetPortSites (w : RootState) : Prop :=
  NoFirstLiftSites w ∧ NoFinalLiftSites w

theorem noFirstLiftSites_iff_d54TerminalResetSites
    (w : RootState) :
    NoFirstLiftSites w ↔
      ∀ i : Fin 3, qCoord w ≠ d54TerminalResetSite i := by
  constructor
  · intro h i hq
    exact h i ((firstLiftCarrySite_iff_d54TerminalResetSite i w).2 hq)
  · intro h i hi
    exact h i ((firstLiftCarrySite_iff_d54TerminalResetSite i w).1 hi)

theorem noFirstLiftSites_iff_not_mem_firstLiftSites
    (w : RootState) :
    NoFirstLiftSites w ↔ qCoord w ∉ firstLiftSites := by
  constructor
  · intro h hMem
    simp only [firstLiftSites, List.mem_cons, List.not_mem_nil,
      or_false] at hMem
    rcases hMem with hMem | hMem | hMem
    · exact h (0 : Fin 3)
        ((firstLiftCarrySite_fin3 (0 : Fin 3) w).2 hMem)
    · exact h (1 : Fin 3)
        ((firstLiftCarrySite_fin3 (1 : Fin 3) w).2 hMem)
    · exact h (2 : Fin 3)
        ((firstLiftCarrySite_fin3 (2 : Fin 3) w).2 hMem)
  · intro h i hi
    have hq := (firstLiftCarrySite_fin3 i w).1 hi
    apply h
    rw [hq]
    exact firstLiftSiteOfIndex_mem_firstLiftSites i

theorem noFirstLiftSites_iff_not_mem_d54TerminalResetSites
    (w : RootState) :
    NoFirstLiftSites w ↔ qCoord w ∉ d54TerminalResetSites := by
  rw [d54TerminalResetSites_eq_firstLiftSites]
  exact noFirstLiftSites_iff_not_mem_firstLiftSites w

theorem noFirstLiftSites_of_not_mem_d54TerminalResetSites
    (w : RootState)
    (hFirst : qCoord w ∉ d54TerminalResetSites) :
    NoFirstLiftSites w :=
  (noFirstLiftSites_iff_not_mem_d54TerminalResetSites w).2 hFirst

theorem noFinalLiftSites_iff_d54FinalCylinders
    (w : RootState) :
    NoFinalLiftSites w ↔
      ∀ c : TorusColor 5,
        rootStateD54Cylinder w ≠ d54FinalCylinderOfColor c := by
  constructor
  · intro h c hc
    exact h c ((finalLiftCarrySite_iff_d54FinalCylinderOfColor c w).2 hc)
  · intro h c hc
    exact h c ((finalLiftCarrySite_iff_d54FinalCylinderOfColor c w).1 hc)

theorem noFinalLiftSites_iff_not_mem_finalLiftCylinders
    (w : RootState) :
    NoFinalLiftSites w ↔
      rootStateD54Cylinder w ∉ finalLiftCylinders := by
  constructor
  · intro h hMem
    simp only [finalLiftCylinders, List.mem_cons, List.not_mem_nil,
      or_false] at hMem
    rcases hMem with hMem | hMem | hMem | hMem | hMem
    · exact h (0 : TorusColor 5)
        ((finalLiftCarrySite_iff_finalLiftCylinderOfColor 0 w).2 hMem)
    · exact h (1 : TorusColor 5)
        ((finalLiftCarrySite_iff_finalLiftCylinderOfColor 1 w).2 hMem)
    · exact h (2 : TorusColor 5)
        ((finalLiftCarrySite_iff_finalLiftCylinderOfColor 2 w).2 hMem)
    · exact h (3 : TorusColor 5)
        ((finalLiftCarrySite_iff_finalLiftCylinderOfColor 3 w).2 hMem)
    · exact h (4 : TorusColor 5)
        ((finalLiftCarrySite_iff_finalLiftCylinderOfColor 4 w).2 hMem)
  · intro h c hc
    have hCylinder :=
      (finalLiftCarrySite_iff_finalLiftCylinderOfColor c w).1 hc
    apply h
    rw [hCylinder]
    exact finalLiftCylinderOfColor_mem_finalLiftCylinders c

theorem noFinalLiftSites_iff_not_mem_d54FinalCylinders
    (w : RootState) :
    NoFinalLiftSites w ↔
      rootStateD54Cylinder w ∉ d54FinalCylinders := by
  rw [d54FinalCylinders_eq_finalLiftCylinders]
  exact noFinalLiftSites_iff_not_mem_finalLiftCylinders w

theorem noFinalLiftSites_of_not_mem_d54FinalCylinders
    (w : RootState)
    (hFinal : rootStateD54Cylinder w ∉ d54FinalCylinders) :
    NoFinalLiftSites w :=
  (noFinalLiftSites_iff_not_mem_d54FinalCylinders w).2 hFinal

theorem noResetPortSites_iff_d54TableSites
    (w : RootState) :
    NoResetPortSites w ↔
      (∀ i : Fin 3, qCoord w ≠ d54TerminalResetSite i) ∧
      (∀ c : TorusColor 5,
        rootStateD54Cylinder w ≠ d54FinalCylinderOfColor c) := by
  constructor
  · intro h
    exact ⟨
      (noFirstLiftSites_iff_d54TerminalResetSites w).1 h.1,
      (noFinalLiftSites_iff_d54FinalCylinders w).1 h.2⟩
  · intro h
    exact ⟨
      (noFirstLiftSites_iff_d54TerminalResetSites w).2 h.1,
      (noFinalLiftSites_iff_d54FinalCylinders w).2 h.2⟩

theorem noResetPortSites_iff_not_mem_tableLists
    (w : RootState) :
    NoResetPortSites w ↔
      qCoord w ∉ firstLiftSites ∧
      rootStateD54Cylinder w ∉ finalLiftCylinders := by
  constructor
  · intro h
    exact ⟨
      (noFirstLiftSites_iff_not_mem_firstLiftSites w).1 h.1,
      (noFinalLiftSites_iff_not_mem_finalLiftCylinders w).1 h.2⟩
  · intro h
    exact ⟨
      (noFirstLiftSites_iff_not_mem_firstLiftSites w).2 h.1,
      (noFinalLiftSites_iff_not_mem_finalLiftCylinders w).2 h.2⟩

theorem noResetPortSites_of_not_mem_tableLists
    (w : RootState)
    (hFirst : qCoord w ∉ firstLiftSites)
    (hFinal : rootStateD54Cylinder w ∉ finalLiftCylinders) :
    NoResetPortSites w :=
  (noResetPortSites_iff_not_mem_tableLists w).2 ⟨hFirst, hFinal⟩

theorem noResetPortSites_iff_not_mem_d54TableLists
    (w : RootState) :
    NoResetPortSites w ↔
      qCoord w ∉ d54TerminalResetSites ∧
      rootStateD54Cylinder w ∉ d54FinalCylinders := by
  rw [d54TerminalResetSites_eq_firstLiftSites,
    d54FinalCylinders_eq_finalLiftCylinders]
  exact noResetPortSites_iff_not_mem_tableLists w

theorem noResetPortSites_of_not_mem_d54TableLists
    (w : RootState)
    (hFirst : qCoord w ∉ d54TerminalResetSites)
    (hFinal : rootStateD54Cylinder w ∉ d54FinalCylinders) :
    NoResetPortSites w :=
  (noResetPortSites_iff_not_mem_d54TableLists w).2 ⟨hFirst, hFinal⟩

theorem layerMap_resetPortDirOfBase_fin3_of_first_site_of_no_finalLiftSites
    (baseRow : ResetPortBaseRow) (t : ZMod 4) (i : Fin 3)
    (w : RootState)
    (hFirst : firstLiftCarrySite (fin3ToFin5 i) w)
    (hFinal : NoFinalLiftSites w) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t (fin3ToFin5 i) w =
      rootOfCoords (qCoord w) (yCoord w + 1) (zCoord w) :=
  layerMap_resetPortDirOfBase_fin3_of_first_site_of_no_final_site
    baseRow t i w hFirst hFinal

theorem layerMap_resetPortDirOfBase_fin3_of_first_site_not_mem_final
    (baseRow : ResetPortBaseRow) (t : ZMod 4) (i : Fin 3)
    (w : RootState)
    (hFirst : firstLiftCarrySite (fin3ToFin5 i) w)
    (hFinal : rootStateD54Cylinder w ∉ finalLiftCylinders) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t (fin3ToFin5 i) w =
      rootOfCoords (qCoord w) (yCoord w + 1) (zCoord w) :=
  layerMap_resetPortDirOfBase_fin3_of_first_site_of_no_finalLiftSites
    baseRow t i w hFirst
    ((noFinalLiftSites_iff_not_mem_finalLiftCylinders w).2 hFinal)

theorem layerMap_resetPortDirOfBase_fin3_of_first_site_d54_not_mem_final
    (baseRow : ResetPortBaseRow) (t : ZMod 4) (i : Fin 3)
    (w : RootState)
    (hFirst : firstLiftCarrySite (fin3ToFin5 i) w)
    (hFinal : rootStateD54Cylinder w ∉ d54FinalCylinders) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t (fin3ToFin5 i) w =
      rootOfCoords (qCoord w) (yCoord w + 1) (zCoord w) :=
  layerMap_resetPortDirOfBase_fin3_of_first_site_of_no_finalLiftSites
    baseRow t i w hFirst
    (noFinalLiftSites_of_not_mem_d54FinalCylinders w hFinal)

theorem layerMap_resetPortDirOfBase_of_baseColor_of_no_resetPortSites
    (baseRow : ResetPortBaseRow) (t : ZMod 4)
    (c : TorusColor 5) (w : RootState) (d : TorusDirection 5)
    (hBase : baseRow t w c = d)
    (hNo : NoResetPortSites w) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t c w =
      LowD5M4Schedule.rootStep d w :=
  layerMap_resetPortDirOfBase_of_baseColor_of_no_site
    baseRow t c w d hBase hNo.1 hNo.2

theorem layerMap_resetPortDirOfBase_terminalStdBaseRow_fin3_of_no_resetPortSites
    (baseRow : ResetPortBaseRow) (t : ZMod 4) (i : Fin 3)
    (w : RootState)
    (hBase :
      baseRow t w (fin3ToFin5 i) =
        terminalStdBaseRowEquiv5 (qCoord w) (fin3ToFin5 i))
    (hNo : NoResetPortSites w) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t (fin3ToFin5 i) w =
      rootOfCoords
        (qCoord w +
          terminalVertex (m := 4)
            (terminalRowEquiv (terminalOmega (qCoord w)) i))
        (yCoord w) (zCoord w) :=
  layerMap_resetPortDirOfBase_terminalStdBaseRow_fin3_of_no_site
    baseRow t i w hBase hNo.1 hNo.2

theorem layerMap_resetPortDirOfBase_terminalTailBase_of_no_resetPortSites
    (baseRow : ResetPortBaseRow) (t : ZMod 4) (i : Fin 3)
    (q : LowD5M4.Q4) (y : LowD5M4.Y) (z : LowD5M4.Z)
    (hBase :
      baseRow t (rootOfCoords (terminalTailBase i q) y z)
          (fin3ToFin5 i) =
        terminalStdBaseRowEquiv5 (terminalTailBase i q) (fin3ToFin5 i))
    (hNo :
      NoResetPortSites
        (rootOfCoords (terminalTailBase i q) y z)) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t (fin3ToFin5 i)
        (rootOfCoords (terminalTailBase i q) y z) =
      rootOfCoords (terminalEta (m := 4) i q) y z :=
  layerMap_resetPortDirOfBase_terminalTailBase_of_no_site
    baseRow t i q y z hBase hNo.1 hNo.2

theorem layerMap_resetPortDirOfBase_terminalReturnTailBase_of_no_resetPortSites
    (baseRow : ResetPortBaseRow) (t : ZMod 4) (i : Fin 3)
    (q : LowD5M4.Q4) (y : LowD5M4.Y) (z : LowD5M4.Z)
    (hBase :
      baseRow t (rootOfCoords (terminalReturnTailBase i q) y z)
          (fin3ToFin5 i) =
        terminalStdBaseRowEquiv5
          (terminalReturnTailBase i q) (fin3ToFin5 i))
    (hNo :
      NoResetPortSites
        (rootOfCoords (terminalReturnTailBase i q) y z)) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t (fin3ToFin5 i)
        (rootOfCoords (terminalReturnTailBase i q) y z) =
      rootOfCoords (LowD5M4.F (terminalSymbolOfIndex i) q) y z :=
  layerMap_resetPortDirOfBase_terminalReturnTailBase_of_no_site
    baseRow t i q y z hBase hNo.1 hNo.2

theorem
    layerMap_resetPortDirOfBase_terminalReturnTailBaseOfSymbol_of_no_resetPortSites
    (baseRow : ResetPortBaseRow)
    (t : ZMod 4) (c : TorusColor 5) (s : TerminalSymbol)
    (q : LowD5M4.Q4) (y : LowD5M4.Y) (z : LowD5M4.Z)
    (hBase :
      baseRow t (rootOfCoords (terminalReturnTailBaseOfSymbol s q) y z) c =
        terminalStdBaseRowEquiv5
          (terminalReturnTailBaseOfSymbol s q)
          (fin3ToFin5 (terminalIndexOfSymbol s)))
    (hNo :
      NoResetPortSites
        (rootOfCoords (terminalReturnTailBaseOfSymbol s q) y z)) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t c
        (rootOfCoords (terminalReturnTailBaseOfSymbol s q) y z) =
      rootOfCoords (LowD5M4.F s q) y z :=
  layerMap_resetPortDirOfBase_terminalReturnTailBaseOfSymbol_of_no_site
    baseRow t c s q y z hBase hNo.1 hNo.2

theorem layerMap_resetPortDirOfBase_of_baseColor_not_mem
    (baseRow : ResetPortBaseRow) (t : ZMod 4)
    (c : TorusColor 5) (w : RootState) (d : TorusDirection 5)
    (hBase : baseRow t w c = d)
    (hFirst : qCoord w ∉ firstLiftSites)
    (hFinal : rootStateD54Cylinder w ∉ finalLiftCylinders) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t c w =
      LowD5M4Schedule.rootStep d w :=
  layerMap_resetPortDirOfBase_of_baseColor_of_no_resetPortSites
    baseRow t c w d hBase
    (noResetPortSites_of_not_mem_tableLists w hFirst hFinal)

theorem layerMap_resetPortDirOfBase_terminalStdBaseRow_fin3_not_mem
    (baseRow : ResetPortBaseRow) (t : ZMod 4) (i : Fin 3)
    (w : RootState)
    (hBase :
      baseRow t w (fin3ToFin5 i) =
        terminalStdBaseRowEquiv5 (qCoord w) (fin3ToFin5 i))
    (hFirst : qCoord w ∉ firstLiftSites)
    (hFinal : rootStateD54Cylinder w ∉ finalLiftCylinders) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t (fin3ToFin5 i) w =
      rootOfCoords
        (qCoord w +
          terminalVertex (m := 4)
            (terminalRowEquiv (terminalOmega (qCoord w)) i))
        (yCoord w) (zCoord w) :=
  layerMap_resetPortDirOfBase_terminalStdBaseRow_fin3_of_no_resetPortSites
    baseRow t i w hBase
    (noResetPortSites_of_not_mem_tableLists w hFirst hFinal)

theorem layerMap_resetPortDirOfBase_terminalTailBase_not_mem
    (baseRow : ResetPortBaseRow) (t : ZMod 4) (i : Fin 3)
    (q : LowD5M4.Q4) (y : LowD5M4.Y) (z : LowD5M4.Z)
    (hBase :
      baseRow t (rootOfCoords (terminalTailBase i q) y z)
          (fin3ToFin5 i) =
        terminalStdBaseRowEquiv5 (terminalTailBase i q) (fin3ToFin5 i))
    (hFirst :
      qCoord (rootOfCoords (terminalTailBase i q) y z) ∉
        firstLiftSites)
    (hFinal :
      rootStateD54Cylinder
        (rootOfCoords (terminalTailBase i q) y z) ∉
          finalLiftCylinders) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t (fin3ToFin5 i)
        (rootOfCoords (terminalTailBase i q) y z) =
      rootOfCoords (terminalEta (m := 4) i q) y z :=
  layerMap_resetPortDirOfBase_terminalTailBase_of_no_resetPortSites
    baseRow t i q y z hBase
    (noResetPortSites_of_not_mem_tableLists
      (rootOfCoords (terminalTailBase i q) y z) hFirst hFinal)

theorem layerMap_resetPortDirOfBase_terminalReturnTailBase_not_mem
    (baseRow : ResetPortBaseRow) (t : ZMod 4) (i : Fin 3)
    (q : LowD5M4.Q4) (y : LowD5M4.Y) (z : LowD5M4.Z)
    (hBase :
      baseRow t (rootOfCoords (terminalReturnTailBase i q) y z)
          (fin3ToFin5 i) =
        terminalStdBaseRowEquiv5
          (terminalReturnTailBase i q) (fin3ToFin5 i))
    (hFirst :
      qCoord (rootOfCoords (terminalReturnTailBase i q) y z) ∉
        firstLiftSites)
    (hFinal :
      rootStateD54Cylinder
        (rootOfCoords (terminalReturnTailBase i q) y z) ∉
          finalLiftCylinders) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t (fin3ToFin5 i)
        (rootOfCoords (terminalReturnTailBase i q) y z) =
      rootOfCoords (LowD5M4.F (terminalSymbolOfIndex i) q) y z :=
  layerMap_resetPortDirOfBase_terminalReturnTailBase_of_no_resetPortSites
    baseRow t i q y z hBase
    (noResetPortSites_of_not_mem_tableLists
      (rootOfCoords (terminalReturnTailBase i q) y z) hFirst hFinal)

theorem layerMap_resetPortDirOfBase_terminalReturnTailBaseOfSymbol_not_mem
    (baseRow : ResetPortBaseRow)
    (t : ZMod 4) (c : TorusColor 5) (s : TerminalSymbol)
    (q : LowD5M4.Q4) (y : LowD5M4.Y) (z : LowD5M4.Z)
    (hBase :
      baseRow t (rootOfCoords (terminalReturnTailBaseOfSymbol s q) y z) c =
        terminalStdBaseRowEquiv5
          (terminalReturnTailBaseOfSymbol s q)
          (fin3ToFin5 (terminalIndexOfSymbol s)))
    (hFirst :
      qCoord (rootOfCoords (terminalReturnTailBaseOfSymbol s q) y z) ∉
        firstLiftSites)
    (hFinal :
      rootStateD54Cylinder
        (rootOfCoords (terminalReturnTailBaseOfSymbol s q) y z) ∉
          finalLiftCylinders) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t c
        (rootOfCoords (terminalReturnTailBaseOfSymbol s q) y z) =
      rootOfCoords (LowD5M4.F s q) y z :=
  layerMap_resetPortDirOfBase_terminalReturnTailBaseOfSymbol_of_no_resetPortSites
    baseRow t c s q y z hBase
    (noResetPortSites_of_not_mem_tableLists
      (rootOfCoords (terminalReturnTailBaseOfSymbol s q) y z)
      hFirst hFinal)

theorem layerMap_resetPortDirOfBase_of_baseColor_d54_not_mem
    (baseRow : ResetPortBaseRow) (t : ZMod 4)
    (c : TorusColor 5) (w : RootState) (d : TorusDirection 5)
    (hBase : baseRow t w c = d)
    (hFirst : qCoord w ∉ d54TerminalResetSites)
    (hFinal : rootStateD54Cylinder w ∉ d54FinalCylinders) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t c w =
      LowD5M4Schedule.rootStep d w :=
  layerMap_resetPortDirOfBase_of_baseColor_of_no_resetPortSites
    baseRow t c w d hBase
    (noResetPortSites_of_not_mem_d54TableLists w hFirst hFinal)

theorem layerMap_resetPortDirOfBase_terminalStdBaseRow_fin3_d54_not_mem
    (baseRow : ResetPortBaseRow) (t : ZMod 4) (i : Fin 3)
    (w : RootState)
    (hBase :
      baseRow t w (fin3ToFin5 i) =
        terminalStdBaseRowEquiv5 (qCoord w) (fin3ToFin5 i))
    (hFirst : qCoord w ∉ d54TerminalResetSites)
    (hFinal : rootStateD54Cylinder w ∉ d54FinalCylinders) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t (fin3ToFin5 i) w =
      rootOfCoords
        (qCoord w +
          terminalVertex (m := 4)
            (terminalRowEquiv (terminalOmega (qCoord w)) i))
        (yCoord w) (zCoord w) :=
  layerMap_resetPortDirOfBase_terminalStdBaseRow_fin3_of_no_resetPortSites
    baseRow t i w hBase
    (noResetPortSites_of_not_mem_d54TableLists w hFirst hFinal)

theorem layerMap_resetPortDirOfBase_terminalTailBase_d54_not_mem
    (baseRow : ResetPortBaseRow) (t : ZMod 4) (i : Fin 3)
    (q : LowD5M4.Q4) (y : LowD5M4.Y) (z : LowD5M4.Z)
    (hBase :
      baseRow t (rootOfCoords (terminalTailBase i q) y z)
          (fin3ToFin5 i) =
        terminalStdBaseRowEquiv5 (terminalTailBase i q) (fin3ToFin5 i))
    (hFirst :
      qCoord (rootOfCoords (terminalTailBase i q) y z) ∉
        d54TerminalResetSites)
    (hFinal :
      rootStateD54Cylinder
        (rootOfCoords (terminalTailBase i q) y z) ∉
          d54FinalCylinders) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t (fin3ToFin5 i)
        (rootOfCoords (terminalTailBase i q) y z) =
      rootOfCoords (terminalEta (m := 4) i q) y z :=
  layerMap_resetPortDirOfBase_terminalTailBase_of_no_resetPortSites
    baseRow t i q y z hBase
    (noResetPortSites_of_not_mem_d54TableLists
      (rootOfCoords (terminalTailBase i q) y z) hFirst hFinal)

theorem layerMap_resetPortDirOfBase_terminalReturnTailBase_d54_not_mem
    (baseRow : ResetPortBaseRow) (t : ZMod 4) (i : Fin 3)
    (q : LowD5M4.Q4) (y : LowD5M4.Y) (z : LowD5M4.Z)
    (hBase :
      baseRow t (rootOfCoords (terminalReturnTailBase i q) y z)
          (fin3ToFin5 i) =
        terminalStdBaseRowEquiv5
          (terminalReturnTailBase i q) (fin3ToFin5 i))
    (hFirst :
      qCoord (rootOfCoords (terminalReturnTailBase i q) y z) ∉
        d54TerminalResetSites)
    (hFinal :
      rootStateD54Cylinder
        (rootOfCoords (terminalReturnTailBase i q) y z) ∉
          d54FinalCylinders) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t (fin3ToFin5 i)
        (rootOfCoords (terminalReturnTailBase i q) y z) =
      rootOfCoords (LowD5M4.F (terminalSymbolOfIndex i) q) y z :=
  layerMap_resetPortDirOfBase_terminalReturnTailBase_of_no_resetPortSites
    baseRow t i q y z hBase
    (noResetPortSites_of_not_mem_d54TableLists
      (rootOfCoords (terminalReturnTailBase i q) y z) hFirst hFinal)

theorem layerMap_resetPortDirOfBase_terminalReturnTailBaseOfSymbol_d54_not_mem
    (baseRow : ResetPortBaseRow)
    (t : ZMod 4) (c : TorusColor 5) (s : TerminalSymbol)
    (q : LowD5M4.Q4) (y : LowD5M4.Y) (z : LowD5M4.Z)
    (hBase :
      baseRow t (rootOfCoords (terminalReturnTailBaseOfSymbol s q) y z) c =
        terminalStdBaseRowEquiv5
          (terminalReturnTailBaseOfSymbol s q)
          (fin3ToFin5 (terminalIndexOfSymbol s)))
    (hFirst :
      qCoord (rootOfCoords (terminalReturnTailBaseOfSymbol s q) y z) ∉
        d54TerminalResetSites)
    (hFinal :
      rootStateD54Cylinder
        (rootOfCoords (terminalReturnTailBaseOfSymbol s q) y z) ∉
          d54FinalCylinders) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t c
        (rootOfCoords (terminalReturnTailBaseOfSymbol s q) y z) =
      rootOfCoords (LowD5M4.F s q) y z :=
  layerMap_resetPortDirOfBase_terminalReturnTailBaseOfSymbol_of_no_resetPortSites
    baseRow t c s q y z hBase
    (noResetPortSites_of_not_mem_d54TableLists
      (rootOfCoords (terminalReturnTailBaseOfSymbol s q) y z)
      hFirst hFinal)

theorem layerMap_resetPortDirOfBase_of_terminalTailIndexRead_no_resetPortSites
    (baseRow : ResetPortBaseRow) (t : ZMod 4) (i : Fin 3)
    (q : LowD5M4.Q4) (y : LowD5M4.Y) (z : LowD5M4.Z)
    (hBase : BaseRowReadsTerminalTailIndex baseRow t i q y z)
    (hNo :
      NoResetPortSites
        (rootOfCoords (terminalReturnTailBase i q) y z)) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t (fin3ToFin5 i)
        (rootOfCoords (terminalReturnTailBase i q) y z) =
      rootOfCoords (LowD5M4.F (terminalSymbolOfIndex i) q) y z :=
  layerMap_resetPortDirOfBase_of_terminalTailIndexRead_no_site
    baseRow t i q y z hBase hNo.1 hNo.2

theorem layerMap_resetPortDirOfBase_of_terminalTailSymbolRead_no_resetPortSites
    (baseRow : ResetPortBaseRow) (t : ZMod 4) (c : TorusColor 5)
    (s : TerminalSymbol) (q : LowD5M4.Q4)
    (y : LowD5M4.Y) (z : LowD5M4.Z)
    (hBase : BaseRowReadsTerminalTailSymbol baseRow t c s q y z)
    (hNo :
      NoResetPortSites
        (rootOfCoords (terminalReturnTailBaseOfSymbol s q) y z)) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t c
        (rootOfCoords (terminalReturnTailBaseOfSymbol s q) y z) =
      rootOfCoords (LowD5M4.F s q) y z :=
  layerMap_resetPortDirOfBase_of_terminalTailSymbolRead_no_site
    baseRow t c s q y z hBase hNo.1 hNo.2

theorem layerMap_resetPortDirOfBase_of_yShiftRead_no_resetPortSites
    (baseRow : ResetPortBaseRow) (t : ZMod 4) (c : TorusColor 5)
    (q : LowD5M4.Q4) (y : LowD5M4.Y) (z : LowD5M4.Z)
    (hBase : BaseRowReadsYShift baseRow t c q y z)
    (hNo : NoResetPortSites (rootOfCoords q y z)) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t c
        (rootOfCoords q y z) =
      rootOfCoords q (y + 1) z :=
  layerMap_resetPortDirOfBase_of_yShiftRead_no_site
    baseRow t c q y z hBase hNo.1 hNo.2

theorem layerMap_resetPortDirOfBase_of_terminalTailIndexRead_not_mem
    (baseRow : ResetPortBaseRow) (t : ZMod 4) (i : Fin 3)
    (q : LowD5M4.Q4) (y : LowD5M4.Y) (z : LowD5M4.Z)
    (hBase : BaseRowReadsTerminalTailIndex baseRow t i q y z)
    (hFirst :
      qCoord (rootOfCoords (terminalReturnTailBase i q) y z) ∉
        firstLiftSites)
    (hFinal :
      rootStateD54Cylinder
        (rootOfCoords (terminalReturnTailBase i q) y z) ∉
          finalLiftCylinders) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t (fin3ToFin5 i)
        (rootOfCoords (terminalReturnTailBase i q) y z) =
      rootOfCoords (LowD5M4.F (terminalSymbolOfIndex i) q) y z :=
  layerMap_resetPortDirOfBase_of_terminalTailIndexRead_no_resetPortSites
    baseRow t i q y z hBase
    (noResetPortSites_of_not_mem_tableLists
      (rootOfCoords (terminalReturnTailBase i q) y z) hFirst hFinal)

theorem layerMap_resetPortDirOfBase_of_terminalTailSymbolRead_not_mem
    (baseRow : ResetPortBaseRow) (t : ZMod 4) (c : TorusColor 5)
    (s : TerminalSymbol) (q : LowD5M4.Q4)
    (y : LowD5M4.Y) (z : LowD5M4.Z)
    (hBase : BaseRowReadsTerminalTailSymbol baseRow t c s q y z)
    (hFirst :
      qCoord (rootOfCoords (terminalReturnTailBaseOfSymbol s q) y z) ∉
        firstLiftSites)
    (hFinal :
      rootStateD54Cylinder
        (rootOfCoords (terminalReturnTailBaseOfSymbol s q) y z) ∉
          finalLiftCylinders) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t c
        (rootOfCoords (terminalReturnTailBaseOfSymbol s q) y z) =
      rootOfCoords (LowD5M4.F s q) y z :=
  layerMap_resetPortDirOfBase_of_terminalTailSymbolRead_no_resetPortSites
    baseRow t c s q y z hBase
    (noResetPortSites_of_not_mem_tableLists
      (rootOfCoords (terminalReturnTailBaseOfSymbol s q) y z)
      hFirst hFinal)

theorem layerMap_resetPortDirOfBase_of_yShiftRead_not_mem
    (baseRow : ResetPortBaseRow) (t : ZMod 4) (c : TorusColor 5)
    (q : LowD5M4.Q4) (y : LowD5M4.Y) (z : LowD5M4.Z)
    (hBase : BaseRowReadsYShift baseRow t c q y z)
    (hFirst : qCoord (rootOfCoords q y z) ∉ firstLiftSites)
    (hFinal :
      rootStateD54Cylinder (rootOfCoords q y z) ∉
        finalLiftCylinders) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t c
        (rootOfCoords q y z) =
      rootOfCoords q (y + 1) z :=
  layerMap_resetPortDirOfBase_of_yShiftRead_no_resetPortSites
    baseRow t c q y z hBase
    (noResetPortSites_of_not_mem_tableLists
      (rootOfCoords q y z) hFirst hFinal)

theorem layerMap_resetPortDirOfBase_of_terminalTailIndexRead_d54_not_mem
    (baseRow : ResetPortBaseRow) (t : ZMod 4) (i : Fin 3)
    (q : LowD5M4.Q4) (y : LowD5M4.Y) (z : LowD5M4.Z)
    (hBase : BaseRowReadsTerminalTailIndex baseRow t i q y z)
    (hFirst :
      qCoord (rootOfCoords (terminalReturnTailBase i q) y z) ∉
        d54TerminalResetSites)
    (hFinal :
      rootStateD54Cylinder
        (rootOfCoords (terminalReturnTailBase i q) y z) ∉
          d54FinalCylinders) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t (fin3ToFin5 i)
        (rootOfCoords (terminalReturnTailBase i q) y z) =
      rootOfCoords (LowD5M4.F (terminalSymbolOfIndex i) q) y z :=
  layerMap_resetPortDirOfBase_of_terminalTailIndexRead_no_resetPortSites
    baseRow t i q y z hBase
    (noResetPortSites_of_not_mem_d54TableLists
      (rootOfCoords (terminalReturnTailBase i q) y z) hFirst hFinal)

theorem layerMap_resetPortDirOfBase_of_terminalTailSymbolRead_d54_not_mem
    (baseRow : ResetPortBaseRow) (t : ZMod 4) (c : TorusColor 5)
    (s : TerminalSymbol) (q : LowD5M4.Q4)
    (y : LowD5M4.Y) (z : LowD5M4.Z)
    (hBase : BaseRowReadsTerminalTailSymbol baseRow t c s q y z)
    (hFirst :
      qCoord (rootOfCoords (terminalReturnTailBaseOfSymbol s q) y z) ∉
        d54TerminalResetSites)
    (hFinal :
      rootStateD54Cylinder
        (rootOfCoords (terminalReturnTailBaseOfSymbol s q) y z) ∉
          d54FinalCylinders) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t c
        (rootOfCoords (terminalReturnTailBaseOfSymbol s q) y z) =
      rootOfCoords (LowD5M4.F s q) y z :=
  layerMap_resetPortDirOfBase_of_terminalTailSymbolRead_no_resetPortSites
    baseRow t c s q y z hBase
    (noResetPortSites_of_not_mem_d54TableLists
      (rootOfCoords (terminalReturnTailBaseOfSymbol s q) y z)
      hFirst hFinal)

theorem layerMap_resetPortDirOfBase_of_yShiftRead_d54_not_mem
    (baseRow : ResetPortBaseRow) (t : ZMod 4) (c : TorusColor 5)
    (q : LowD5M4.Q4) (y : LowD5M4.Y) (z : LowD5M4.Z)
    (hBase : BaseRowReadsYShift baseRow t c q y z)
    (hFirst : qCoord (rootOfCoords q y z) ∉ d54TerminalResetSites)
    (hFinal :
      rootStateD54Cylinder (rootOfCoords q y z) ∉
        d54FinalCylinders) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t c
        (rootOfCoords q y z) =
      rootOfCoords q (y + 1) z :=
  layerMap_resetPortDirOfBase_of_yShiftRead_no_resetPortSites
    baseRow t c q y z hBase
    (noResetPortSites_of_not_mem_d54TableLists
      (rootOfCoords q y z) hFirst hFinal)

theorem noFirstLiftSites_of_d54TerminalSelectorSite
    (i : Fin 3) (w : RootState)
    (hq : qCoord w = d54TerminalSelectorSite i) :
    NoFirstLiftSites w := by
  intro j hj
  exact firstLiftSiteOfIndex_ne_d54TerminalSelectorSite j i
    (((firstLiftCarrySite_fin3 j w).1 hj).symm.trans hq)

theorem noResetPortSites_of_d54TerminalSelectorSite
    (i : Fin 3) (w : RootState)
    (hq : qCoord w = d54TerminalSelectorSite i) :
    NoResetPortSites w := by
  have hFinal : NoFinalLiftSites w := by
    intro c hc
    have hCylinder :=
      (finalLiftCarrySite_iff_d54FinalCylinderOfColor c w).1 hc
    have hqFinal :
        qCoord w = (d54FinalCylinderOfColor c).q := by
      simpa [rootStateD54Cylinder] using
        congrArg (fun cylinder : D54Cylinder => cylinder.q) hCylinder
    exact d54TerminalSelectorSite_ne_d54FinalCylinderOfColor_q i c
      (hq.symm.trans hqFinal)
  exact ⟨
    noFirstLiftSites_of_d54TerminalSelectorSite i w hq,
    hFinal⟩

theorem noFinalLiftSites_of_d54LiftedSelectorPoint
    (i : Fin 3) (w : RootState)
    (hq : qCoord w = (d54LiftedSelectorPointOfIndex i).q) :
    NoFinalLiftSites w := by
  intro c hc
  have hCylinder :=
    (finalLiftCarrySite_iff_d54FinalCylinderOfColor c w).1 hc
  have hqFinal :
      qCoord w = (d54FinalCylinderOfColor c).q := by
    simpa [rootStateD54Cylinder] using
      congrArg (fun cylinder : D54Cylinder => cylinder.q) hCylinder
  have hqSelector : qCoord w = d54TerminalSelectorSite i := by
    simpa [d54LiftedSelectorPointOfIndex] using hq
  exact d54TerminalSelectorSite_ne_d54FinalCylinderOfColor_q i c
    (hqSelector.symm.trans hqFinal)

theorem noResetPortSites_of_d54LiftedSelectorPoint
    (i : Fin 3) (w : RootState)
    (hq : qCoord w = (d54LiftedSelectorPointOfIndex i).q) :
    NoResetPortSites w := by
  exact noResetPortSites_of_d54TerminalSelectorSite i w
    (by simpa [d54LiftedSelectorPointOfIndex] using hq)

theorem noFirstLiftSites_of_d54ReservePointOfRole
    (role : D54ReserveRole) (w : RootState)
    (hq : qCoord w = (d54ReserveD54PointOfRole role).q) :
    NoFirstLiftSites w := by
  intro i hi
  exact firstLiftSiteOfIndex_ne_d54ReservePointOfRole_q i role
    (((firstLiftCarrySite_fin3 i w).1 hi).symm.trans hq)

theorem noFinalLiftSites_of_d54ReservePointOfRole
    (role : D54ReserveRole) (w : RootState)
    (hq : qCoord w = (d54ReserveD54PointOfRole role).q) :
    NoFinalLiftSites w := by
  intro c hc
  have hCylinder :=
    (finalLiftCarrySite_iff_d54FinalCylinderOfColor c w).1 hc
  have hqFinal :
      qCoord w = (d54FinalCylinderOfColor c).q := by
    simpa [rootStateD54Cylinder] using
      congrArg (fun cylinder : D54Cylinder => cylinder.q) hCylinder
  exact d54ReservePointOfRole_q_ne_d54FinalCylinderOfColor_q role c
    (hq.symm.trans hqFinal)

theorem noResetPortSites_of_d54ReservePointOfRole
    (role : D54ReserveRole) (w : RootState)
    (hq : qCoord w = (d54ReserveD54PointOfRole role).q) :
    NoResetPortSites w :=
  ⟨noFirstLiftSites_of_d54ReservePointOfRole role w hq,
    noFinalLiftSites_of_d54ReservePointOfRole role w hq⟩

theorem noResetPortSites_of_rootStateD54Point_eq_liftedSelectorPoint
    (i : Fin 3) (w : RootState)
    (hPoint :
      rootStateD54Point w = d54LiftedSelectorPointOfIndex i) :
    NoResetPortSites w :=
  noResetPortSites_of_d54LiftedSelectorPoint i w
    (by
      simpa [rootStateD54Point] using
        congrArg (fun point : D54Point => point.q) hPoint)

theorem noResetPortSites_of_qCoord_mem_d54TerminalSelector
    (w : RootState) (hMem : qCoord w ∈ d54TerminalSelector) :
    NoResetPortSites w := by
  rw [d54TerminalSelector_eq_selectorSites] at hMem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
  rcases hMem with hMem | hMem | hMem
  · exact noResetPortSites_of_d54TerminalSelectorSite (0 : Fin 3) w hMem
  · exact noResetPortSites_of_d54TerminalSelectorSite (1 : Fin 3) w hMem
  · exact noResetPortSites_of_d54TerminalSelectorSite (2 : Fin 3) w hMem

theorem noResetPortSites_of_rootStateD54Point_mem_liftedSelector
    (w : RootState) (hMem : rootStateD54Point w ∈ d54LiftedSelector) :
    NoResetPortSites w := by
  rw [d54LiftedSelector_eq_liftedSelectorPoints] at hMem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
  rcases hMem with hMem | hMem | hMem
  · exact
      noResetPortSites_of_rootStateD54Point_eq_liftedSelectorPoint
        (0 : Fin 3) w hMem
  · exact
      noResetPortSites_of_rootStateD54Point_eq_liftedSelectorPoint
        (1 : Fin 3) w hMem
  · exact
      noResetPortSites_of_rootStateD54Point_eq_liftedSelectorPoint
        (2 : Fin 3) w hMem

theorem noResetPortSites_of_rootStateD54Point_eq_reservePointOfRole
    (role : D54ReserveRole) (w : RootState)
    (hPoint :
      rootStateD54Point w = d54ReserveD54PointOfRole role) :
    NoResetPortSites w :=
  noResetPortSites_of_d54ReservePointOfRole role w
    (by
      simpa [rootStateD54Point] using
        congrArg (fun point : D54Point => point.q) hPoint)

theorem noResetPortSites_of_rootStateD54Point_mem_reservePoints
    (w : RootState) (hMem : rootStateD54Point w ∈ reservePoints) :
    NoResetPortSites w := by
  rw [reservePoints_eq_map_reserveD54PointOfRole] at hMem
  simp only [d54ReserveRoles, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hMem
  rcases hMem with hMem | hMem | hMem | hMem | hMem | hMem | hMem | hMem
  · exact
      noResetPortSites_of_rootStateD54Point_eq_reservePointOfRole
        EvenV11.D54ResetData.D54ReserveRole.U0 w hMem
  · exact
      noResetPortSites_of_rootStateD54Point_eq_reservePointOfRole
        EvenV11.D54ResetData.D54ReserveRole.U1 w hMem
  · exact
      noResetPortSites_of_rootStateD54Point_eq_reservePointOfRole
        EvenV11.D54ResetData.D54ReserveRole.U2 w hMem
  · exact
      noResetPortSites_of_rootStateD54Point_eq_reservePointOfRole
        EvenV11.D54ResetData.D54ReserveRole.U1c w hMem
  · exact
      noResetPortSites_of_rootStateD54Point_eq_reservePointOfRole
        EvenV11.D54ResetData.D54ReserveRole.U2c w hMem
  · exact
      noResetPortSites_of_rootStateD54Point_eq_reservePointOfRole
        EvenV11.D54ResetData.D54ReserveRole.U3c w hMem
  · exact
      noResetPortSites_of_rootStateD54Point_eq_reservePointOfRole
        EvenV11.D54ResetData.D54ReserveRole.U4c w hMem
  · exact
      noResetPortSites_of_rootStateD54Point_eq_reservePointOfRole
        EvenV11.D54ResetData.D54ReserveRole.Ustar w hMem

theorem layerMap_resetPortDirOfBase_color_of_no_resetPortSites
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (t : ZMod 4) (c : TorusColor 5) (w : RootState)
    (hNo : NoResetPortSites w) :
    (LowD5M4Schedule.schedule
      (resetPortDirOfBase baseRow)).layerMap t c w =
      LowD5M4Schedule.rootStep (baseRow t w c) w :=
  layerMap_resetPortDirOfBase_color_of_no_site
    baseRow t c w hNo.1 hNo.2

/-- A four-layer path goal for the base row before the paper reset-port
substitutions are applied. -/
def BaseRowFourLayerPathGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (c : TorusColor 5) (target : RootState → RootState) : Prop :=
  ∃ x1 x2 x3 : RootState → RootState,
    ∀ w : RootState,
      LowD5M4Schedule.rootStep (baseRow (0 : ZMod 4) w c) w = x1 w ∧
      LowD5M4Schedule.rootStep (baseRow (1 : ZMod 4) (x1 w) c)
          (x1 w) = x2 w ∧
      LowD5M4Schedule.rootStep (baseRow (2 : ZMod 4) (x2 w) c)
          (x2 w) = x3 w ∧
      LowD5M4Schedule.rootStep (baseRow (3 : ZMod 4) (x3 w) c)
          (x3 w) = target w

/-- A base-row four-layer path whose intermediate sources avoid every
reset-port substitution. This is the paper separation between the terminal A2
carrier and the reset-port switches. -/
def BaseRowNoResetFourLayerPathGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (c : TorusColor 5) (target : RootState → RootState) : Prop :=
  ∃ x1 x2 x3 : RootState → RootState,
    ∀ w : RootState,
      LowD5M4Schedule.rootStep (baseRow (0 : ZMod 4) w c) w = x1 w ∧
      LowD5M4Schedule.rootStep (baseRow (1 : ZMod 4) (x1 w) c)
          (x1 w) = x2 w ∧
      LowD5M4Schedule.rootStep (baseRow (2 : ZMod 4) (x2 w) c)
          (x2 w) = x3 w ∧
      LowD5M4Schedule.rootStep (baseRow (3 : ZMod 4) (x3 w) c)
          (x3 w) = target w ∧
      NoResetPortSites w ∧
      NoResetPortSites (x1 w) ∧
      NoResetPortSites (x2 w) ∧
      NoResetPortSites (x3 w)

theorem resetPortPathGoal_of_baseRowNoResetPathGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (c : TorusColor 5) (target : RootState → RootState)
    (hPath : BaseRowNoResetFourLayerPathGoal baseRow c target) :
    FourLayerPathGoal (resetPortDirOfBase baseRow) c target := by
  rcases hPath with ⟨x1, x2, x3, hsteps⟩
  refine ⟨x1, x2, x3, ?_⟩
  intro w
  rcases hsteps w with ⟨h0, h1, h2, h3, hNo0, hNo1, hNo2, hNo3⟩
  constructor
  · rw [layerMap_resetPortDirOfBase_color_of_no_resetPortSites
      baseRow (0 : ZMod 4) c w hNo0]
    exact h0
  constructor
  · rw [layerMap_resetPortDirOfBase_color_of_no_resetPortSites
      baseRow (1 : ZMod 4) c (x1 w) hNo1]
    exact h1
  constructor
  · rw [layerMap_resetPortDirOfBase_color_of_no_resetPortSites
      baseRow (2 : ZMod 4) c (x2 w) hNo2]
    exact h2
  · rw [layerMap_resetPortDirOfBase_color_of_no_resetPortSites
      baseRow (3 : ZMod 4) c (x3 w) hNo3]
    exact h3

/-- A four-layer realization goal restricted to sources satisfying `sourceOk`.
This is the right shape for the paper's support-separated switching-ribbon
arguments, where a formula is first proved off the reset sites and the local
substitutions are handled separately. -/
def FourLayerRealizationOnGoal
    (dir : ZMod 4 → RootState → TorusColor 5 → TorusDirection 5)
    (c : TorusColor 5) (sourceOk : RootState → Prop)
    (target : RootState → RootState) : Prop :=
  ∀ w : RootState, sourceOk w → fourLayerReturn dir c w = target w

/-- A layer-by-layer path goal restricted to sources satisfying `sourceOk`. This
is the conditional version of `FourLayerPathGoal`, suited to support-separated
cut-splice arguments. -/
def FourLayerPathOnGoal
    (dir : ZMod 4 → RootState → TorusColor 5 → TorusDirection 5)
    (c : TorusColor 5) (sourceOk : RootState → Prop)
    (target : RootState → RootState) : Prop :=
  ∃ x1 x2 x3 : RootState → RootState,
    ∀ w : RootState, sourceOk w →
      (LowD5M4Schedule.schedule dir).layerMap (0 : ZMod 4) c w = x1 w ∧
      (LowD5M4Schedule.schedule dir).layerMap (1 : ZMod 4) c (x1 w) =
        x2 w ∧
      (LowD5M4Schedule.schedule dir).layerMap (2 : ZMod 4) c (x2 w) =
        x3 w ∧
      (LowD5M4Schedule.schedule dir).layerMap (3 : ZMod 4) c (x3 w) =
        target w

theorem fourLayerRealizationOnGoal_of_pathOnGoal
    (dir : ZMod 4 → RootState → TorusColor 5 → TorusDirection 5)
    (c : TorusColor 5) (sourceOk : RootState → Prop)
    (target : RootState → RootState)
    (hPath : FourLayerPathOnGoal dir c sourceOk target) :
    FourLayerRealizationOnGoal dir c sourceOk target := by
  rcases hPath with ⟨x1, x2, x3, hsteps⟩
  intro w hOk
  rcases hsteps w hOk with ⟨h0, h1, h2, h3⟩
  exact fourLayerReturn_eq_of_layerMap_steps
    dir c w (x1 w) (x2 w) (x3 w) (target w) h0 h1 h2 h3

/-- A base-row four-layer path restricted to a source predicate, with the
source and intermediate states all avoiding reset-port substitutions. -/
def BaseRowNoResetFourLayerPathOnGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (c : TorusColor 5) (sourceOk : RootState → Prop)
    (target : RootState → RootState) : Prop :=
  ∃ x1 x2 x3 : RootState → RootState,
    ∀ w : RootState, sourceOk w →
      LowD5M4Schedule.rootStep (baseRow (0 : ZMod 4) w c) w = x1 w ∧
      LowD5M4Schedule.rootStep (baseRow (1 : ZMod 4) (x1 w) c)
          (x1 w) = x2 w ∧
      LowD5M4Schedule.rootStep (baseRow (2 : ZMod 4) (x2 w) c)
          (x2 w) = x3 w ∧
      LowD5M4Schedule.rootStep (baseRow (3 : ZMod 4) (x3 w) c)
          (x3 w) = target w ∧
      NoResetPortSites w ∧
      NoResetPortSites (x1 w) ∧
      NoResetPortSites (x2 w) ∧
      NoResetPortSites (x3 w)

theorem resetPortRealizationOnGoal_of_baseRowNoResetPathOnGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (c : TorusColor 5) (sourceOk : RootState → Prop)
    (target : RootState → RootState)
    (hPath : BaseRowNoResetFourLayerPathOnGoal baseRow c sourceOk target) :
    FourLayerRealizationOnGoal
      (resetPortDirOfBase baseRow) c sourceOk target := by
  rcases hPath with ⟨x1, x2, x3, hsteps⟩
  intro w hOk
  rcases hsteps w hOk with ⟨h0, h1, h2, h3, hNo0, hNo1, hNo2, hNo3⟩
  exact fourLayerReturn_eq_of_layerMap_steps
    (resetPortDirOfBase baseRow) c w
    (x1 w) (x2 w) (x3 w) (target w)
    (by
      rw [layerMap_resetPortDirOfBase_color_of_no_resetPortSites
        baseRow (0 : ZMod 4) c w hNo0]
      exact h0)
    (by
      rw [layerMap_resetPortDirOfBase_color_of_no_resetPortSites
        baseRow (1 : ZMod 4) c (x1 w) hNo1]
      exact h1)
    (by
      rw [layerMap_resetPortDirOfBase_color_of_no_resetPortSites
        baseRow (2 : ZMod 4) c (x2 w) hNo2]
      exact h2)
    (by
      rw [layerMap_resetPortDirOfBase_color_of_no_resetPortSites
        baseRow (3 : ZMod 4) c (x3 w) hNo3]
      exact h3)

/-- The reset-port realization obligation away from the final `Z` carry site,
using the pre-final paper target `R_i`. -/
def ResetPortPreFinalRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  ∀ c : TorusColor 5,
    FourLayerRealizationOnGoal
      (resetPortDirOfBase baseRow) c
      (fun w => ¬ finalLiftCarrySite c w) (preFinalReturn c)

/-- The pre-final `R_i` obligations for terminal colors `0,1,2`. -/
def ResetPortPreFinalTerminalRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  ∀ i : Fin 3,
    FourLayerRealizationOnGoal
      (resetPortDirOfBase baseRow) (fin3ToFin5 i)
      (fun w => ¬ finalLiftCarrySite (fin3ToFin5 i) w)
      (preFinalReturn (fin3ToFin5 i))

/-- The pre-final `R_3=P0` obligation. -/
def ResetPortPreFinalP0RealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  FourLayerRealizationOnGoal
    (resetPortDirOfBase baseRow) 3
    (fun w => ¬ finalLiftCarrySite 3 w) (preFinalReturn 3)

/-- The pre-final `R_4=P1` obligation. -/
def ResetPortPreFinalP1RealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  FourLayerRealizationOnGoal
    (resetPortDirOfBase baseRow) 4
    (fun w => ¬ finalLiftCarrySite 4 w) (preFinalReturn 4)

/-- Layer-by-layer pre-final `R_i` obligations for terminal colors `0,1,2`. -/
def ResetPortPreFinalTerminalPathRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  ∀ i : Fin 3,
    FourLayerPathOnGoal
      (resetPortDirOfBase baseRow) (fin3ToFin5 i)
      (fun w => ¬ finalLiftCarrySite (fin3ToFin5 i) w)
      (preFinalReturn (fin3ToFin5 i))

/-- Layer-by-layer pre-final `R_3=P0` obligation. -/
def ResetPortPreFinalP0PathRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  FourLayerPathOnGoal
    (resetPortDirOfBase baseRow) 3
    (fun w => ¬ finalLiftCarrySite 3 w) (preFinalReturn 3)

/-- Layer-by-layer pre-final `R_4=P1` obligation. -/
def ResetPortPreFinalP1PathRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  FourLayerPathOnGoal
    (resetPortDirOfBase baseRow) 4
    (fun w => ¬ finalLiftCarrySite 4 w) (preFinalReturn 4)

theorem resetPortPreFinalTerminalRealizationGoal_of_pathGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hPath : ResetPortPreFinalTerminalPathRealizationGoal baseRow) :
    ResetPortPreFinalTerminalRealizationGoal baseRow := by
  intro i
  exact fourLayerRealizationOnGoal_of_pathOnGoal
    (resetPortDirOfBase baseRow) (fin3ToFin5 i)
    (fun w => ¬ finalLiftCarrySite (fin3ToFin5 i) w)
    (preFinalReturn (fin3ToFin5 i)) (hPath i)

theorem resetPortPreFinalP0RealizationGoal_of_pathGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hPath : ResetPortPreFinalP0PathRealizationGoal baseRow) :
    ResetPortPreFinalP0RealizationGoal baseRow :=
  fourLayerRealizationOnGoal_of_pathOnGoal
    (resetPortDirOfBase baseRow) 3
    (fun w => ¬ finalLiftCarrySite 3 w) (preFinalReturn 3) hPath

theorem resetPortPreFinalP1RealizationGoal_of_pathGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hPath : ResetPortPreFinalP1PathRealizationGoal baseRow) :
    ResetPortPreFinalP1RealizationGoal baseRow :=
  fourLayerRealizationOnGoal_of_pathOnGoal
    (resetPortDirOfBase baseRow) 4
    (fun w => ¬ finalLiftCarrySite 4 w) (preFinalReturn 4) hPath

theorem resetPortPreFinalRealizationGoal_of_colorGoals
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hTerminal : ResetPortPreFinalTerminalRealizationGoal baseRow)
    (hP0 : ResetPortPreFinalP0RealizationGoal baseRow)
    (hP1 : ResetPortPreFinalP1RealizationGoal baseRow) :
    ResetPortPreFinalRealizationGoal baseRow := by
  intro c
  fin_cases c
  · simpa [ResetPortPreFinalTerminalRealizationGoal, fin3ToFin5]
      using hTerminal 0
  · simpa [ResetPortPreFinalTerminalRealizationGoal, fin3ToFin5]
      using hTerminal 1
  · simpa [ResetPortPreFinalTerminalRealizationGoal, fin3ToFin5]
      using hTerminal 2
  · simpa [ResetPortPreFinalP0RealizationGoal] using hP0
  · simpa [ResetPortPreFinalP1RealizationGoal] using hP1

theorem resetPortPreFinalRealizationGoal_of_pathGoals
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hTerminalPath : ResetPortPreFinalTerminalPathRealizationGoal baseRow)
    (hP0Path : ResetPortPreFinalP0PathRealizationGoal baseRow)
    (hP1Path : ResetPortPreFinalP1PathRealizationGoal baseRow) :
    ResetPortPreFinalRealizationGoal baseRow :=
  resetPortPreFinalRealizationGoal_of_colorGoals baseRow
    (resetPortPreFinalTerminalRealizationGoal_of_pathGoal
      baseRow hTerminalPath)
    (resetPortPreFinalP0RealizationGoal_of_pathGoal baseRow hP0Path)
    (resetPortPreFinalP1RealizationGoal_of_pathGoal baseRow hP1Path)

/-- The reset-port realization obligation away from the final `Z` carry site,
stated directly against the transported paper return. -/
def ResetPortNoFinalSiteRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  ∀ c : TorusColor 5,
    FourLayerRealizationOnGoal
      (resetPortDirOfBase baseRow) c
      (fun w => ¬ finalLiftCarrySite c w) (paperReturn c)

theorem resetPortNoFinalSiteRealizationGoal_of_preFinalRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hPreFinal : ResetPortPreFinalRealizationGoal baseRow) :
    ResetPortNoFinalSiteRealizationGoal baseRow := by
  intro c w hNoFinal
  calc
    fourLayerReturn (resetPortDirOfBase baseRow) c w =
        preFinalReturn c w := hPreFinal c w hNoFinal
    _ = paperReturn c w :=
        (paperReturn_eq_preFinalReturn_of_not_finalLiftCarrySite
          c w hNoFinal).symm

/-- The reset-port realization obligation on an active final `Z` carry site,
using the explicit `z += 1` target. -/
def ResetPortFinalCarryRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  ∀ c : TorusColor 5,
    FourLayerRealizationOnGoal
      (resetPortDirOfBase baseRow) c
      (finalLiftCarrySite c) (finalCarryReturn c)

/-- The final-carry obligations for terminal colors `0,1,2`. -/
def ResetPortFinalCarryTerminalRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  ∀ i : Fin 3,
    FourLayerRealizationOnGoal
      (resetPortDirOfBase baseRow) (fin3ToFin5 i)
      (finalLiftCarrySite (fin3ToFin5 i))
      (finalCarryReturn (fin3ToFin5 i))

/-- The final-carry obligation for `R_3=P0`. -/
def ResetPortFinalCarryP0RealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  FourLayerRealizationOnGoal
    (resetPortDirOfBase baseRow) 3
    (finalLiftCarrySite 3) (finalCarryReturn 3)

/-- The final-carry obligation for `R_4=P1`. -/
def ResetPortFinalCarryP1RealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  FourLayerRealizationOnGoal
    (resetPortDirOfBase baseRow) 4
    (finalLiftCarrySite 4) (finalCarryReturn 4)

/-- Layer-by-layer final-carry obligations for terminal colors `0,1,2`. -/
def ResetPortFinalCarryTerminalPathRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  ∀ i : Fin 3,
    FourLayerPathOnGoal
      (resetPortDirOfBase baseRow) (fin3ToFin5 i)
      (finalLiftCarrySite (fin3ToFin5 i))
      (finalCarryReturn (fin3ToFin5 i))

/-- Layer-by-layer final-carry obligation for `R_3=P0`. -/
def ResetPortFinalCarryP0PathRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  FourLayerPathOnGoal
    (resetPortDirOfBase baseRow) 3
    (finalLiftCarrySite 3) (finalCarryReturn 3)

/-- Layer-by-layer final-carry obligation for `R_4=P1`. -/
def ResetPortFinalCarryP1PathRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  FourLayerPathOnGoal
    (resetPortDirOfBase baseRow) 4
    (finalLiftCarrySite 4) (finalCarryReturn 4)

theorem resetPortFinalCarryTerminalRealizationGoal_of_pathGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hPath : ResetPortFinalCarryTerminalPathRealizationGoal baseRow) :
    ResetPortFinalCarryTerminalRealizationGoal baseRow := by
  intro i
  exact fourLayerRealizationOnGoal_of_pathOnGoal
    (resetPortDirOfBase baseRow) (fin3ToFin5 i)
    (finalLiftCarrySite (fin3ToFin5 i))
    (finalCarryReturn (fin3ToFin5 i)) (hPath i)

theorem resetPortFinalCarryP0RealizationGoal_of_pathGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hPath : ResetPortFinalCarryP0PathRealizationGoal baseRow) :
    ResetPortFinalCarryP0RealizationGoal baseRow :=
  fourLayerRealizationOnGoal_of_pathOnGoal
    (resetPortDirOfBase baseRow) 3
    (finalLiftCarrySite 3) (finalCarryReturn 3) hPath

theorem resetPortFinalCarryP1RealizationGoal_of_pathGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hPath : ResetPortFinalCarryP1PathRealizationGoal baseRow) :
    ResetPortFinalCarryP1RealizationGoal baseRow :=
  fourLayerRealizationOnGoal_of_pathOnGoal
    (resetPortDirOfBase baseRow) 4
    (finalLiftCarrySite 4) (finalCarryReturn 4) hPath

theorem resetPortFinalCarryRealizationGoal_of_colorGoals
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hTerminal : ResetPortFinalCarryTerminalRealizationGoal baseRow)
    (hP0 : ResetPortFinalCarryP0RealizationGoal baseRow)
    (hP1 : ResetPortFinalCarryP1RealizationGoal baseRow) :
    ResetPortFinalCarryRealizationGoal baseRow := by
  intro c
  fin_cases c
  · simpa [ResetPortFinalCarryTerminalRealizationGoal, fin3ToFin5]
      using hTerminal 0
  · simpa [ResetPortFinalCarryTerminalRealizationGoal, fin3ToFin5]
      using hTerminal 1
  · simpa [ResetPortFinalCarryTerminalRealizationGoal, fin3ToFin5]
      using hTerminal 2
  · simpa [ResetPortFinalCarryP0RealizationGoal] using hP0
  · simpa [ResetPortFinalCarryP1RealizationGoal] using hP1

theorem resetPortFinalCarryRealizationGoal_of_pathGoals
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hTerminalPath : ResetPortFinalCarryTerminalPathRealizationGoal baseRow)
    (hP0Path : ResetPortFinalCarryP0PathRealizationGoal baseRow)
    (hP1Path : ResetPortFinalCarryP1PathRealizationGoal baseRow) :
    ResetPortFinalCarryRealizationGoal baseRow :=
  resetPortFinalCarryRealizationGoal_of_colorGoals baseRow
    (resetPortFinalCarryTerminalRealizationGoal_of_pathGoal
      baseRow hTerminalPath)
    (resetPortFinalCarryP0RealizationGoal_of_pathGoal baseRow hP0Path)
    (resetPortFinalCarryP1RealizationGoal_of_pathGoal baseRow hP1Path)

/-- The reset-port realization obligation on an active final `Z` carry site,
stated directly against the transported paper return. -/
def ResetPortFinalSiteRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  ∀ c : TorusColor 5,
    FourLayerRealizationOnGoal
      (resetPortDirOfBase baseRow) c
      (finalLiftCarrySite c) (paperReturn c)

theorem resetPortFinalSiteRealizationGoal_of_finalCarryRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hFinalCarry : ResetPortFinalCarryRealizationGoal baseRow) :
    ResetPortFinalSiteRealizationGoal baseRow := by
  intro c w hFinal
  calc
    fourLayerReturn (resetPortDirOfBase baseRow) c w =
        finalCarryReturn c w := hFinalCarry c w hFinal
    _ = paperReturn c w :=
        (paperReturn_eq_finalCarryReturn_of_finalLiftCarrySite
          c w hFinal).symm

theorem resetPortFourLayerRealizationGoal_of_finalSiteSplit
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hNoFinal : ResetPortNoFinalSiteRealizationGoal baseRow)
    (hFinal : ResetPortFinalSiteRealizationGoal baseRow) :
    ResetPortFourLayerRealizationGoal baseRow := by
  change ∀ c : TorusColor 5, ∀ w : RootState,
    fourLayerReturn (resetPortDirOfBase baseRow) c w = paperReturn c w
  intro c w
  by_cases h : finalLiftCarrySite c w
  · exact hFinal c w h
  · exact hNoFinal c w h

theorem resetPortFourLayerRealizationGoal_of_preFinalFinalCarryGoals
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hPreFinal : ResetPortPreFinalRealizationGoal baseRow)
    (hFinalCarry : ResetPortFinalCarryRealizationGoal baseRow) :
    ResetPortFourLayerRealizationGoal baseRow :=
  resetPortFourLayerRealizationGoal_of_finalSiteSplit baseRow
    (resetPortNoFinalSiteRealizationGoal_of_preFinalRealizationGoal
      baseRow hPreFinal)
    (resetPortFinalSiteRealizationGoal_of_finalCarryRealizationGoal
      baseRow hFinalCarry)

/-- The terminal A2 carrier target before the two unit-carry reset lifts are
inserted. -/
def terminalCoreReturn (i : Fin 3) : RootState → RootState :=
  fun w =>
    rootOfCoords
      (LowD5M4.F (terminalSymbolOfIndex i) (qCoord w))
      (yCoord w) (zCoord w)

@[simp] theorem terminalCoreReturn_apply (i : Fin 3) (w : RootState) :
    terminalCoreReturn i w =
      rootOfCoords
        (LowD5M4.F (terminalSymbolOfIndex i) (qCoord w))
        (yCoord w) (zCoord w) := rfl

theorem paperReturn_terminal_eq_terminalCoreReturn_of_no_resetPortSites
    (i : Fin 3) (w : RootState)
    (hNo : NoResetPortSites w) :
    paperReturn (fin3ToFin5 i) w = terminalCoreReturn i w := by
  simp [paperReturn_apply_terminal_sites, hNo.1 i,
    hNo.2 (fin3ToFin5 i)]

theorem terminalCoreReturn_eq_paperReturn_terminal_of_no_resetPortSites
    (i : Fin 3) (w : RootState)
    (hNo : NoResetPortSites w) :
    terminalCoreReturn i w = paperReturn (fin3ToFin5 i) w :=
  (paperReturn_terminal_eq_terminalCoreReturn_of_no_resetPortSites
    i w hNo).symm

/-- The terminal target after an active first `Y` carry and before any final
`Z` carry. This is the active-site half of the paper formula
`T_i(q,y)=(F_i q,y+1_{q=p_i})`. -/
def terminalFirstCarryReturn (i : Fin 3) : RootState → RootState :=
  fun w =>
    rootOfCoords
      (LowD5M4.F (terminalSymbolOfIndex i) (qCoord w))
      (yCoord w + 1) (zCoord w)

@[simp] theorem terminalFirstCarryReturn_apply (i : Fin 3) (w : RootState) :
    terminalFirstCarryReturn i w =
      rootOfCoords
        (LowD5M4.F (terminalSymbolOfIndex i) (qCoord w))
        (yCoord w + 1) (zCoord w) := rfl

theorem preFinalReturn_terminal_eq_terminalCoreReturn_of_not_firstLiftCarrySite
    (i : Fin 3) (w : RootState)
    (hFirst : ¬ firstLiftCarrySite (fin3ToFin5 i) w) :
    preFinalReturn (fin3ToFin5 i) w = terminalCoreReturn i w := by
  rw [preFinalReturn_terminal_sites i w]
  simp [hFirst]

theorem preFinalReturn_terminal_eq_terminalFirstCarryReturn_of_firstLiftCarrySite
    (i : Fin 3) (w : RootState)
    (hFirst : firstLiftCarrySite (fin3ToFin5 i) w) :
    preFinalReturn (fin3ToFin5 i) w = terminalFirstCarryReturn i w := by
  rw [preFinalReturn_terminal_sites i w]
  simp [hFirst]

def ResetPortPreFinalTerminalNoFirstRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  ∀ i : Fin 3,
    FourLayerRealizationOnGoal
      (resetPortDirOfBase baseRow) (fin3ToFin5 i)
      (fun w =>
        ¬ finalLiftCarrySite (fin3ToFin5 i) w ∧
        ¬ firstLiftCarrySite (fin3ToFin5 i) w)
      (terminalCoreReturn i)

def ResetPortPreFinalTerminalFirstCarryRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  ∀ i : Fin 3,
    FourLayerRealizationOnGoal
      (resetPortDirOfBase baseRow) (fin3ToFin5 i)
      (fun w =>
        ¬ finalLiftCarrySite (fin3ToFin5 i) w ∧
        firstLiftCarrySite (fin3ToFin5 i) w)
      (terminalFirstCarryReturn i)

def ResetPortPreFinalTerminalNoFirstPathRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  ∀ i : Fin 3,
    FourLayerPathOnGoal
      (resetPortDirOfBase baseRow) (fin3ToFin5 i)
      (fun w =>
        ¬ finalLiftCarrySite (fin3ToFin5 i) w ∧
        ¬ firstLiftCarrySite (fin3ToFin5 i) w)
      (terminalCoreReturn i)

def ResetPortPreFinalTerminalFirstCarryPathRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  ∀ i : Fin 3,
    FourLayerPathOnGoal
      (resetPortDirOfBase baseRow) (fin3ToFin5 i)
      (fun w =>
        ¬ finalLiftCarrySite (fin3ToFin5 i) w ∧
        firstLiftCarrySite (fin3ToFin5 i) w)
      (terminalFirstCarryReturn i)

theorem resetPortPreFinalTerminalNoFirstRealizationGoal_of_pathGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hPath : ResetPortPreFinalTerminalNoFirstPathRealizationGoal baseRow) :
    ResetPortPreFinalTerminalNoFirstRealizationGoal baseRow := by
  intro i
  exact fourLayerRealizationOnGoal_of_pathOnGoal
    (resetPortDirOfBase baseRow) (fin3ToFin5 i)
    (fun w =>
      ¬ finalLiftCarrySite (fin3ToFin5 i) w ∧
      ¬ firstLiftCarrySite (fin3ToFin5 i) w)
    (terminalCoreReturn i) (hPath i)

theorem resetPortPreFinalTerminalFirstCarryRealizationGoal_of_pathGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hPath : ResetPortPreFinalTerminalFirstCarryPathRealizationGoal baseRow) :
    ResetPortPreFinalTerminalFirstCarryRealizationGoal baseRow := by
  intro i
  exact fourLayerRealizationOnGoal_of_pathOnGoal
    (resetPortDirOfBase baseRow) (fin3ToFin5 i)
    (fun w =>
      ¬ finalLiftCarrySite (fin3ToFin5 i) w ∧
      firstLiftCarrySite (fin3ToFin5 i) w)
    (terminalFirstCarryReturn i) (hPath i)

theorem resetPortPreFinalTerminalRealizationGoal_of_firstCarrySplit
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hNoFirst : ResetPortPreFinalTerminalNoFirstRealizationGoal baseRow)
    (hFirst : ResetPortPreFinalTerminalFirstCarryRealizationGoal baseRow) :
    ResetPortPreFinalTerminalRealizationGoal baseRow := by
  intro i w hNoFinal
  by_cases hFirstSite : firstLiftCarrySite (fin3ToFin5 i) w
  · calc
      fourLayerReturn (resetPortDirOfBase baseRow) (fin3ToFin5 i) w =
          terminalFirstCarryReturn i w :=
            hFirst i w ⟨hNoFinal, hFirstSite⟩
      _ = preFinalReturn (fin3ToFin5 i) w :=
          (preFinalReturn_terminal_eq_terminalFirstCarryReturn_of_firstLiftCarrySite
            i w hFirstSite).symm
  · calc
      fourLayerReturn (resetPortDirOfBase baseRow) (fin3ToFin5 i) w =
          terminalCoreReturn i w :=
            hNoFirst i w ⟨hNoFinal, hFirstSite⟩
      _ = preFinalReturn (fin3ToFin5 i) w :=
          (preFinalReturn_terminal_eq_terminalCoreReturn_of_not_firstLiftCarrySite
            i w hFirstSite).symm

theorem resetPortPreFinalTerminalRealizationGoal_of_firstCarryPathGoals
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hNoFirstPath :
      ResetPortPreFinalTerminalNoFirstPathRealizationGoal baseRow)
    (hFirstPath :
      ResetPortPreFinalTerminalFirstCarryPathRealizationGoal baseRow) :
    ResetPortPreFinalTerminalRealizationGoal baseRow :=
  resetPortPreFinalTerminalRealizationGoal_of_firstCarrySplit baseRow
    (resetPortPreFinalTerminalNoFirstRealizationGoal_of_pathGoal
      baseRow hNoFirstPath)
    (resetPortPreFinalTerminalFirstCarryRealizationGoal_of_pathGoal
      baseRow hFirstPath)

/-- The state reached by the forced first layer at an active terminal
first-`Y` carry site, before the residual terminal-A2 row word is read. -/
def firstCarryYFirstState : RootState → RootState :=
  fun w => rootOfCoords (qCoord w) (yCoord w + 1) (zCoord w)

@[simp] theorem firstCarryYFirstState_apply (w : RootState) :
    firstCarryYFirstState w =
      rootOfCoords (qCoord w) (yCoord w + 1) (zCoord w) :=
  rfl

/-- Residual path input after the pre-final terminal substitution has supplied
the first `y += 1` step. The remaining obligation is only layers `1,2,3`. -/
def ResetPortPreFinalTerminalFirstYResidualPathOnGoal
    (baseRow : ResetPortBaseRow) (i : Fin 3)
    (sourceOk : RootState → Prop) (target : RootState → RootState) :
    Prop :=
  ∃ x2 x3 : RootState → RootState,
    ∀ w : RootState, sourceOk w →
      (LowD5M4Schedule.schedule
        (resetPortDirOfBase baseRow)).layerMap (1 : ZMod 4)
          (fin3ToFin5 i) (firstCarryYFirstState w) =
        x2 w ∧
      (LowD5M4Schedule.schedule
        (resetPortDirOfBase baseRow)).layerMap (2 : ZMod 4)
          (fin3ToFin5 i) (x2 w) =
        x3 w ∧
      (LowD5M4Schedule.schedule
        (resetPortDirOfBase baseRow)).layerMap (3 : ZMod 4)
          (fin3ToFin5 i) (x3 w) =
        target w

theorem resetPortPreFinalTerminalFirstPathOnGoal_of_firstYResidualPathOnGoal
    (baseRow : ResetPortBaseRow) (i : Fin 3)
    (sourceOk : RootState → Prop) (target : RootState → RootState)
    (hFirst :
      ∀ w : RootState, sourceOk w →
        firstLiftCarrySite (fin3ToFin5 i) w)
    (hNoFinal :
      ∀ w : RootState, sourceOk w → NoFinalLiftSites w)
    (hResidual :
      ResetPortPreFinalTerminalFirstYResidualPathOnGoal
        baseRow i sourceOk target) :
    FourLayerPathOnGoal (resetPortDirOfBase baseRow) (fin3ToFin5 i)
      sourceOk target := by
  rcases hResidual with ⟨x2, x3, hsteps⟩
  refine ⟨firstCarryYFirstState, x2, x3, ?_⟩
  intro w hOk
  rcases hsteps w hOk with ⟨h1, h2, h3⟩
  refine ⟨?_, h1, h2, h3⟩
  simpa [firstCarryYFirstState] using
      layerMap_resetPortDirOfBase_fin3_of_first_site_of_no_finalLiftSites
        baseRow (0 : ZMod 4) i w (hFirst w hOk) (hNoFinal w hOk)

/-- Prefix-only form of the residual terminal-A2 input after an active first
`Y` carry has supplied layer `0`. It records the layers that reach the
collapsed terminal tail and the inactive-site proof at that tail; the final
row-word read is supplied separately. -/
def ResetPortPreFinalTerminalFirstYTailPrefixPathOnGoal
    (baseRow : ResetPortBaseRow) (i : Fin 3)
    (sourceOk : RootState → Prop) :
    Prop :=
  ∃ x2 : RootState → RootState,
    ∀ w : RootState, sourceOk w →
      (LowD5M4Schedule.schedule
        (resetPortDirOfBase baseRow)).layerMap (1 : ZMod 4)
          (fin3ToFin5 i) (firstCarryYFirstState w) =
        x2 w ∧
      (LowD5M4Schedule.schedule
        (resetPortDirOfBase baseRow)).layerMap (2 : ZMod 4)
          (fin3ToFin5 i) (x2 w) =
        rootOfCoords
          (terminalReturnTailBase i (qCoord w))
          (yCoord w + 1) (zCoord w) ∧
      NoResetPortSites
        (rootOfCoords
          (terminalReturnTailBase i (qCoord w))
          (yCoord w + 1) (zCoord w))

/-- Last-layer row-word read paired with
`ResetPortPreFinalTerminalFirstYTailPrefixPathOnGoal`. -/
def ResetPortPreFinalTerminalFirstYTailReadOnGoal
    (baseRow : ResetPortBaseRow) (i : Fin 3)
    (sourceOk : RootState → Prop) :
    Prop :=
  ∀ w : RootState, sourceOk w →
    BaseRowReadsTerminalTailIndex
      baseRow (3 : ZMod 4) i (qCoord w) (yCoord w + 1) (zCoord w)

/-- Split form of the active-first-`Y` terminal tail goal: path prefix plus
last-layer row-word read. -/
structure ResetPortPreFinalTerminalFirstYTailSplitPathOnGoal
    (baseRow : ResetPortBaseRow) (i : Fin 3)
    (sourceOk : RootState → Prop) :
    Prop where
  pathPrefix :
    ResetPortPreFinalTerminalFirstYTailPrefixPathOnGoal
      baseRow i sourceOk
  read :
    ResetPortPreFinalTerminalFirstYTailReadOnGoal
      baseRow i sourceOk

/-- Tail form of the residual terminal-A2 input after an active first `Y`
carry has supplied layer `0`. Layers `1,2` only need to reach the
run-collapsed terminal tail, and layer `3` reads the terminal row word. -/
def ResetPortPreFinalTerminalFirstYTailPathOnGoal
    (baseRow : ResetPortBaseRow) (i : Fin 3)
    (sourceOk : RootState → Prop) :
    Prop :=
  ∃ x2 : RootState → RootState,
    ∀ w : RootState, sourceOk w →
        (LowD5M4Schedule.schedule
          (resetPortDirOfBase baseRow)).layerMap (1 : ZMod 4)
            (fin3ToFin5 i) (firstCarryYFirstState w) =
          x2 w ∧
        (LowD5M4Schedule.schedule
          (resetPortDirOfBase baseRow)).layerMap (2 : ZMod 4)
            (fin3ToFin5 i) (x2 w) =
          rootOfCoords
            (terminalReturnTailBase i (qCoord w))
            (yCoord w + 1) (zCoord w) ∧
        BaseRowReadsTerminalTailIndex
          baseRow (3 : ZMod 4) i (qCoord w) (yCoord w + 1)
          (zCoord w) ∧
        (∀ j : Fin 3,
          ¬ firstLiftCarrySite (fin3ToFin5 j)
            (rootOfCoords
              (terminalReturnTailBase i (qCoord w))
              (yCoord w + 1) (zCoord w))) ∧
        (∀ c : TorusColor 5,
          ¬ finalLiftCarrySite c
          (rootOfCoords
            (terminalReturnTailBase i (qCoord w))
            (yCoord w + 1) (zCoord w)))

theorem ResetPortPreFinalTerminalFirstYTailPathOnGoal_of_split
    {baseRow : ResetPortBaseRow} {i : Fin 3}
    {sourceOk : RootState → Prop}
    (hSplit :
      ResetPortPreFinalTerminalFirstYTailSplitPathOnGoal
        baseRow i sourceOk) :
    ResetPortPreFinalTerminalFirstYTailPathOnGoal
      baseRow i sourceOk := by
  rcases hSplit.pathPrefix with ⟨x2, hsteps⟩
  refine ⟨x2, ?_⟩
  intro w hOk
  rcases hsteps w hOk with ⟨h1, h2, hNo⟩
  exact ⟨h1, h2, hSplit.read w hOk, hNo.1, hNo.2⟩

theorem resetPortPreFinalTerminalFirstYResidualPathOnGoal_of_yFirstTailPathOnGoal
    (baseRow : ResetPortBaseRow) (i : Fin 3)
    (sourceOk : RootState → Prop)
    (hTail :
      ResetPortPreFinalTerminalFirstYTailPathOnGoal
        baseRow i sourceOk) :
    ResetPortPreFinalTerminalFirstYResidualPathOnGoal
      baseRow i sourceOk (terminalFirstCarryReturn i) := by
  rcases hTail with ⟨x2, hsteps⟩
  refine ⟨x2,
      (fun w =>
        rootOfCoords
          (terminalReturnTailBase i (qCoord w))
          (yCoord w + 1) (zCoord w)),
      ?_⟩
  intro w hOk
  rcases hsteps w hOk with ⟨h1, h2, hBase, hFirst, hFinal⟩
  refine ⟨h1, h2, ?_⟩
  simpa [terminalFirstCarryReturn] using
    layerMap_resetPortDirOfBase_of_terminalTailIndexRead_no_site
      baseRow (3 : ZMod 4) i (qCoord w) (yCoord w + 1)
      (zCoord w) hBase hFirst hFinal

theorem resetPortPreFinalTerminalFirstYResidualPathOnGoal_of_yFirstTailSplitPathOnGoal
    (baseRow : ResetPortBaseRow) (i : Fin 3)
    (sourceOk : RootState → Prop)
    (hTail :
      ResetPortPreFinalTerminalFirstYTailSplitPathOnGoal
        baseRow i sourceOk) :
    ResetPortPreFinalTerminalFirstYResidualPathOnGoal
      baseRow i sourceOk (terminalFirstCarryReturn i) := by
  rcases hTail.pathPrefix with ⟨x2, hsteps⟩
  refine ⟨x2,
      (fun w =>
        rootOfCoords
          (terminalReturnTailBase i (qCoord w))
          (yCoord w + 1) (zCoord w)),
      ?_⟩
  intro w hOk
  rcases hsteps w hOk with ⟨h1, h2, hNo⟩
  refine ⟨h1, h2, ?_⟩
  simpa [terminalFirstCarryReturn] using
    layerMap_resetPortDirOfBase_of_terminalTailIndexRead_no_resetPortSites
      baseRow (3 : ZMod 4) i (qCoord w) (yCoord w + 1)
      (zCoord w) (hTail.read w hOk) hNo

def ResetPortPreFinalTerminalFirstCarryNoFinalYFirstResidualPathGoal
    (baseRow : ResetPortBaseRow) :
    Prop :=
  ∀ i : Fin 3,
    ResetPortPreFinalTerminalFirstYResidualPathOnGoal
      baseRow i
      (fun w =>
        NoFinalLiftSites w ∧
        firstLiftCarrySite (fin3ToFin5 i) w)
      (terminalFirstCarryReturn i)

def ResetPortPreFinalTerminalFirstCarryNoFinalYFirstTailPathGoal
    (baseRow : ResetPortBaseRow) :
    Prop :=
  ∀ i : Fin 3,
    ResetPortPreFinalTerminalFirstYTailPathOnGoal
      baseRow i
      (fun w =>
        NoFinalLiftSites w ∧
        firstLiftCarrySite (fin3ToFin5 i) w)

def ResetPortPreFinalTerminalFirstCarryNoFinalYFirstTailSplitPathGoal
    (baseRow : ResetPortBaseRow) :
    Prop :=
  ∀ i : Fin 3,
    ResetPortPreFinalTerminalFirstYTailSplitPathOnGoal
      baseRow i
      (fun w =>
        NoFinalLiftSites w ∧
        firstLiftCarrySite (fin3ToFin5 i) w)

theorem resetPortPreFinalTerminalFirstCarryNoFinalYFirstTailPathGoal_of_split
    {baseRow : ResetPortBaseRow}
    (hSplit :
      ResetPortPreFinalTerminalFirstCarryNoFinalYFirstTailSplitPathGoal
        baseRow) :
    ResetPortPreFinalTerminalFirstCarryNoFinalYFirstTailPathGoal
      baseRow := by
  intro i
  exact ResetPortPreFinalTerminalFirstYTailPathOnGoal_of_split
    (hSplit i)

theorem resetPortPreFinalTerminalFirstCarryNoFinalYFirstResidualPathGoal_of_tailPathGoal
    (baseRow : ResetPortBaseRow)
    (hTail :
      ResetPortPreFinalTerminalFirstCarryNoFinalYFirstTailPathGoal
        baseRow) :
    ResetPortPreFinalTerminalFirstCarryNoFinalYFirstResidualPathGoal
      baseRow := by
  intro i
  exact
    resetPortPreFinalTerminalFirstYResidualPathOnGoal_of_yFirstTailPathOnGoal
      baseRow i
      (fun w =>
        NoFinalLiftSites w ∧
        firstLiftCarrySite (fin3ToFin5 i) w)
      (hTail i)

theorem resetPortPreFinalTerminalFirstCarryNoFinalYFirstResidualPathGoal_of_tailSplitPathGoal
    (baseRow : ResetPortBaseRow)
    (hTail :
      ResetPortPreFinalTerminalFirstCarryNoFinalYFirstTailSplitPathGoal
        baseRow) :
    ResetPortPreFinalTerminalFirstCarryNoFinalYFirstResidualPathGoal
      baseRow := by
  intro i
  exact
    resetPortPreFinalTerminalFirstYResidualPathOnGoal_of_yFirstTailSplitPathOnGoal
      baseRow i
      (fun w =>
        NoFinalLiftSites w ∧
        firstLiftCarrySite (fin3ToFin5 i) w)
      (hTail i)

def ResetPortPreFinalTerminalFirstCarryNoFinalPathRealizationGoal
    (baseRow : ResetPortBaseRow) :
    Prop :=
  ∀ i : Fin 3,
    FourLayerPathOnGoal
      (resetPortDirOfBase baseRow) (fin3ToFin5 i)
      (fun w =>
        NoFinalLiftSites w ∧
        firstLiftCarrySite (fin3ToFin5 i) w)
      (terminalFirstCarryReturn i)

theorem resetPortPreFinalTerminalFirstCarryNoFinalPathGoal_of_yFirstResidualPathGoal
    (baseRow : ResetPortBaseRow)
    (hResidual :
      ResetPortPreFinalTerminalFirstCarryNoFinalYFirstResidualPathGoal
        baseRow) :
    ResetPortPreFinalTerminalFirstCarryNoFinalPathRealizationGoal
      baseRow := by
  intro i
  exact
    resetPortPreFinalTerminalFirstPathOnGoal_of_firstYResidualPathOnGoal
      baseRow i
      (fun w =>
        NoFinalLiftSites w ∧
        firstLiftCarrySite (fin3ToFin5 i) w)
      (terminalFirstCarryReturn i)
      (fun _w h => h.2)
      (fun _w h => h.1)
      (hResidual i)

def ResetPortPreFinalTerminalFirstCarryNoFinalRealizationGoal
    (baseRow : ResetPortBaseRow) :
    Prop :=
  ∀ i : Fin 3,
    FourLayerRealizationOnGoal
      (resetPortDirOfBase baseRow) (fin3ToFin5 i)
      (fun w =>
        NoFinalLiftSites w ∧
        firstLiftCarrySite (fin3ToFin5 i) w)
      (terminalFirstCarryReturn i)

theorem resetPortPreFinalTerminalFirstCarryNoFinalRealizationGoal_of_pathGoal
    (baseRow : ResetPortBaseRow)
    (hPath :
      ResetPortPreFinalTerminalFirstCarryNoFinalPathRealizationGoal
        baseRow) :
    ResetPortPreFinalTerminalFirstCarryNoFinalRealizationGoal
      baseRow := by
  intro i
  exact fourLayerRealizationOnGoal_of_pathOnGoal
    (resetPortDirOfBase baseRow) (fin3ToFin5 i)
    (fun w =>
      NoFinalLiftSites w ∧
      firstLiftCarrySite (fin3ToFin5 i) w)
    (terminalFirstCarryReturn i) (hPath i)

theorem resetPortPreFinalTerminalFirstCarryNoFinalRealizationGoal_of_yFirstResidualPathGoal
    (baseRow : ResetPortBaseRow)
    (hResidual :
      ResetPortPreFinalTerminalFirstCarryNoFinalYFirstResidualPathGoal
        baseRow) :
    ResetPortPreFinalTerminalFirstCarryNoFinalRealizationGoal
      baseRow :=
  resetPortPreFinalTerminalFirstCarryNoFinalRealizationGoal_of_pathGoal
    baseRow
    (resetPortPreFinalTerminalFirstCarryNoFinalPathGoal_of_yFirstResidualPathGoal
      baseRow hResidual)

theorem resetPortPreFinalTerminalFirstCarryNoFinalRealizationGoal_of_yFirstTailPathGoal
    (baseRow : ResetPortBaseRow)
    (hTail :
      ResetPortPreFinalTerminalFirstCarryNoFinalYFirstTailPathGoal
        baseRow) :
    ResetPortPreFinalTerminalFirstCarryNoFinalRealizationGoal
      baseRow :=
  resetPortPreFinalTerminalFirstCarryNoFinalRealizationGoal_of_yFirstResidualPathGoal
    baseRow
    (resetPortPreFinalTerminalFirstCarryNoFinalYFirstResidualPathGoal_of_tailPathGoal
      baseRow hTail)

theorem resetPortPreFinalTerminalFirstCarryNoFinalRealizationGoal_of_yFirstTailSplitPathGoal
    (baseRow : ResetPortBaseRow)
    (hTail :
      ResetPortPreFinalTerminalFirstCarryNoFinalYFirstTailSplitPathGoal
        baseRow) :
    ResetPortPreFinalTerminalFirstCarryNoFinalRealizationGoal
      baseRow :=
  resetPortPreFinalTerminalFirstCarryNoFinalRealizationGoal_of_yFirstResidualPathGoal
    baseRow
    (resetPortPreFinalTerminalFirstCarryNoFinalYFirstResidualPathGoal_of_tailSplitPathGoal
      baseRow hTail)

/-- Residual pre-final terminal first-carry sources where some final-stage site
is active for another color. These are left to the switching-ribbon proof. -/
def ResetPortPreFinalTerminalFirstCarryFinalConflictPathRealizationGoal
    (baseRow : ResetPortBaseRow) :
    Prop :=
  ∀ i : Fin 3,
    FourLayerPathOnGoal
      (resetPortDirOfBase baseRow) (fin3ToFin5 i)
      (fun w =>
        ¬ finalLiftCarrySite (fin3ToFin5 i) w ∧
        firstLiftCarrySite (fin3ToFin5 i) w ∧
        ¬ NoFinalLiftSites w)
      (terminalFirstCarryReturn i)

def ResetPortPreFinalTerminalFirstCarryFinalConflictRealizationGoal
    (baseRow : ResetPortBaseRow) :
    Prop :=
  ∀ i : Fin 3,
    FourLayerRealizationOnGoal
      (resetPortDirOfBase baseRow) (fin3ToFin5 i)
      (fun w =>
        ¬ finalLiftCarrySite (fin3ToFin5 i) w ∧
        firstLiftCarrySite (fin3ToFin5 i) w ∧
        ¬ NoFinalLiftSites w)
      (terminalFirstCarryReturn i)

theorem resetPortPreFinalTerminalFirstCarryFinalConflictRealizationGoal_of_pathGoal
    (baseRow : ResetPortBaseRow)
    (hPath :
      ResetPortPreFinalTerminalFirstCarryFinalConflictPathRealizationGoal
        baseRow) :
    ResetPortPreFinalTerminalFirstCarryFinalConflictRealizationGoal
      baseRow := by
  intro i
  exact fourLayerRealizationOnGoal_of_pathOnGoal
    (resetPortDirOfBase baseRow) (fin3ToFin5 i)
    (fun w =>
      ¬ finalLiftCarrySite (fin3ToFin5 i) w ∧
      firstLiftCarrySite (fin3ToFin5 i) w ∧
      ¬ NoFinalLiftSites w)
    (terminalFirstCarryReturn i) (hPath i)

theorem resetPortPreFinalTerminalFirstCarryRealizationGoal_of_yFirstNoFinal_and_finalConflict
    (baseRow : ResetPortBaseRow)
    (hNoFinalYFirst :
      ResetPortPreFinalTerminalFirstCarryNoFinalYFirstResidualPathGoal
        baseRow)
    (hFinalConflict :
      ResetPortPreFinalTerminalFirstCarryFinalConflictPathRealizationGoal
        baseRow) :
    ResetPortPreFinalTerminalFirstCarryRealizationGoal baseRow := by
  have hNoFinal :
      ResetPortPreFinalTerminalFirstCarryNoFinalRealizationGoal
        baseRow :=
    resetPortPreFinalTerminalFirstCarryNoFinalRealizationGoal_of_yFirstResidualPathGoal
      baseRow hNoFinalYFirst
  have hConflict :
      ResetPortPreFinalTerminalFirstCarryFinalConflictRealizationGoal
        baseRow :=
    resetPortPreFinalTerminalFirstCarryFinalConflictRealizationGoal_of_pathGoal
      baseRow hFinalConflict
  intro i w hw
  by_cases hNoFinalSites : NoFinalLiftSites w
  · exact hNoFinal i w ⟨hNoFinalSites, hw.2⟩
  · exact hConflict i w ⟨hw.1, hw.2, hNoFinalSites⟩

theorem resetPortPreFinalTerminalFirstCarryRealizationGoal_of_yFirstTailNoFinal_and_finalConflict
    (baseRow : ResetPortBaseRow)
    (hNoFinalTail :
      ResetPortPreFinalTerminalFirstCarryNoFinalYFirstTailPathGoal
        baseRow)
    (hFinalConflict :
      ResetPortPreFinalTerminalFirstCarryFinalConflictPathRealizationGoal
        baseRow) :
    ResetPortPreFinalTerminalFirstCarryRealizationGoal baseRow :=
  resetPortPreFinalTerminalFirstCarryRealizationGoal_of_yFirstNoFinal_and_finalConflict
    baseRow
    (resetPortPreFinalTerminalFirstCarryNoFinalYFirstResidualPathGoal_of_tailPathGoal
      baseRow hNoFinalTail)
    hFinalConflict

theorem
    resetPortPreFinalTerminalFirstCarryRealizationGoal_of_yFirstTailSplitNoFinal_and_finalConflict
    (baseRow : ResetPortBaseRow)
    (hNoFinalTail :
      ResetPortPreFinalTerminalFirstCarryNoFinalYFirstTailSplitPathGoal
        baseRow)
    (hFinalConflict :
      ResetPortPreFinalTerminalFirstCarryFinalConflictPathRealizationGoal
        baseRow) :
    ResetPortPreFinalTerminalFirstCarryRealizationGoal baseRow :=
  resetPortPreFinalTerminalFirstCarryRealizationGoal_of_yFirstNoFinal_and_finalConflict
    baseRow
    (resetPortPreFinalTerminalFirstCarryNoFinalYFirstResidualPathGoal_of_tailSplitPathGoal
      baseRow hNoFinalTail)
    hFinalConflict

theorem preFinalTerminalFirstCarryRealizationGoal_of_yFirstTailSplit
    (baseRow : ResetPortBaseRow)
    (hNoFinalTail :
      ResetPortPreFinalTerminalFirstCarryNoFinalYFirstTailSplitPathGoal
        baseRow)
    (hFinalConflict :
      ResetPortPreFinalTerminalFirstCarryFinalConflictPathRealizationGoal
        baseRow) :
    ResetPortPreFinalTerminalFirstCarryRealizationGoal baseRow :=
  resetPortPreFinalTerminalFirstCarryRealizationGoal_of_yFirstTailSplitNoFinal_and_finalConflict
    baseRow hNoFinalTail hFinalConflict

/-- The pure `Y` row-word target for `P0`/`P1`, before any terminal factor is
read in the `Q4` coordinate. -/
def preFinalYShiftReturn : RootState → RootState :=
  fun w => rootOfCoords (qCoord w) (yCoord w + 1) (zCoord w)

@[simp] theorem preFinalYShiftReturn_apply (w : RootState) :
    preFinalYShiftReturn w =
      rootOfCoords (qCoord w) (yCoord w + 1) (zCoord w) := rfl

/-- A `P0`/`P1` terminal factor read during the `Y` row-word circuit. -/
def preFinalYTerminalReturn (s : TerminalSymbol) : RootState → RootState :=
  fun w =>
    rootOfCoords (LowD5M4.F s (qCoord w)) (yCoord w + 1) (zCoord w)

@[simp] theorem preFinalYTerminalReturn_apply
    (s : TerminalSymbol) (w : RootState) :
    preFinalYTerminalReturn s w =
      rootOfCoords (LowD5M4.F s (qCoord w)) (yCoord w + 1) (zCoord w) :=
  rfl

theorem preFinalReturn_three_eq_yShiftReturn_of_y_ne_zero
    (w : RootState) (hY : yCoord w ≠ 0) :
    preFinalReturn 3 w = preFinalYShiftReturn w := by
  rw [preFinalReturn_three]
  simp [preFinalYShiftReturn, hY]

theorem preFinalReturn_three_eq_yTerminalF0Return_of_y_zero
    (w : RootState) (hY : yCoord w = 0) :
    preFinalReturn 3 w =
      preFinalYTerminalReturn TerminalSymbol.F0 w := by
  rw [preFinalReturn_three]
  simp [preFinalYTerminalReturn, hY]

theorem preFinalReturn_four_eq_yTerminalF0Return_of_y_one
    (w : RootState) (hY : yCoord w = 1) :
    preFinalReturn 4 w =
      preFinalYTerminalReturn TerminalSymbol.F0 w := by
  rw [preFinalReturn_four]
  simp [preFinalYTerminalReturn, hY]

theorem preFinalReturn_four_eq_yTerminalF2Return_of_y_two
    (w : RootState) (hY : yCoord w = 2) :
    preFinalReturn 4 w =
      preFinalYTerminalReturn TerminalSymbol.F2 w := by
  have h21 : (2 : ZMod 4) ≠ 1 := by decide
  rw [preFinalReturn_four]
  simp [preFinalYTerminalReturn, hY, h21]

theorem preFinalReturn_four_eq_yTerminalF1Return_of_y_three
    (w : RootState) (hY : yCoord w = 3) :
    preFinalReturn 4 w =
      preFinalYTerminalReturn TerminalSymbol.F1 w := by
  have h31 : (3 : ZMod 4) ≠ 1 := by decide
  have h32 : (3 : ZMod 4) ≠ 2 := by decide
  rw [preFinalReturn_four]
  simp [preFinalYTerminalReturn, hY, h31, h32]

theorem preFinalReturn_four_eq_yShiftReturn_of_y_ne_one_two_three
    (w : RootState) (hY1 : yCoord w ≠ 1) (hY2 : yCoord w ≠ 2)
    (hY3 : yCoord w ≠ 3) :
    preFinalReturn 4 w = preFinalYShiftReturn w := by
  rw [preFinalReturn_four]
  simp [preFinalYShiftReturn, hY1, hY2, hY3]

def ResetPortPreFinalP0YShiftRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  FourLayerRealizationOnGoal
    (resetPortDirOfBase baseRow) 3
    (fun w => ¬ finalLiftCarrySite 3 w ∧ yCoord w ≠ 0)
    preFinalYShiftReturn

def ResetPortPreFinalP0F0RealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  FourLayerRealizationOnGoal
    (resetPortDirOfBase baseRow) 3
    (fun w => ¬ finalLiftCarrySite 3 w ∧ yCoord w = 0)
    (preFinalYTerminalReturn TerminalSymbol.F0)

def ResetPortPreFinalP1YShiftRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  FourLayerRealizationOnGoal
    (resetPortDirOfBase baseRow) 4
    (fun w =>
      ¬ finalLiftCarrySite 4 w ∧
      yCoord w ≠ 1 ∧ yCoord w ≠ 2 ∧ yCoord w ≠ 3)
    preFinalYShiftReturn

def ResetPortPreFinalP1Y1F0RealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  FourLayerRealizationOnGoal
    (resetPortDirOfBase baseRow) 4
    (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 1)
    (preFinalYTerminalReturn TerminalSymbol.F0)

def ResetPortPreFinalP1Y2F2RealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  FourLayerRealizationOnGoal
    (resetPortDirOfBase baseRow) 4
    (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 2)
    (preFinalYTerminalReturn TerminalSymbol.F2)

def ResetPortPreFinalP1Y3F1RealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  FourLayerRealizationOnGoal
    (resetPortDirOfBase baseRow) 4
    (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 3)
    (preFinalYTerminalReturn TerminalSymbol.F1)

def ResetPortPreFinalP0YShiftPathRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  FourLayerPathOnGoal
    (resetPortDirOfBase baseRow) 3
    (fun w => ¬ finalLiftCarrySite 3 w ∧ yCoord w ≠ 0)
    preFinalYShiftReturn

def ResetPortPreFinalP0F0PathRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  FourLayerPathOnGoal
    (resetPortDirOfBase baseRow) 3
    (fun w => ¬ finalLiftCarrySite 3 w ∧ yCoord w = 0)
    (preFinalYTerminalReturn TerminalSymbol.F0)

def ResetPortPreFinalP1YShiftPathRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  FourLayerPathOnGoal
    (resetPortDirOfBase baseRow) 4
    (fun w =>
      ¬ finalLiftCarrySite 4 w ∧
      yCoord w ≠ 1 ∧ yCoord w ≠ 2 ∧ yCoord w ≠ 3)
    preFinalYShiftReturn

def ResetPortPreFinalP1Y1F0PathRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  FourLayerPathOnGoal
    (resetPortDirOfBase baseRow) 4
    (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 1)
    (preFinalYTerminalReturn TerminalSymbol.F0)

def ResetPortPreFinalP1Y2F2PathRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  FourLayerPathOnGoal
    (resetPortDirOfBase baseRow) 4
    (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 2)
    (preFinalYTerminalReturn TerminalSymbol.F2)

def ResetPortPreFinalP1Y3F1PathRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  FourLayerPathOnGoal
    (resetPortDirOfBase baseRow) 4
    (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 3)
    (preFinalYTerminalReturn TerminalSymbol.F1)

theorem resetPortPreFinalP0YShiftRealizationGoal_of_pathGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hPath : ResetPortPreFinalP0YShiftPathRealizationGoal baseRow) :
    ResetPortPreFinalP0YShiftRealizationGoal baseRow :=
  fourLayerRealizationOnGoal_of_pathOnGoal
    (resetPortDirOfBase baseRow) 3
    (fun w => ¬ finalLiftCarrySite 3 w ∧ yCoord w ≠ 0)
    preFinalYShiftReturn hPath

theorem resetPortPreFinalP0F0RealizationGoal_of_pathGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hPath : ResetPortPreFinalP0F0PathRealizationGoal baseRow) :
    ResetPortPreFinalP0F0RealizationGoal baseRow :=
  fourLayerRealizationOnGoal_of_pathOnGoal
    (resetPortDirOfBase baseRow) 3
    (fun w => ¬ finalLiftCarrySite 3 w ∧ yCoord w = 0)
    (preFinalYTerminalReturn TerminalSymbol.F0) hPath

theorem resetPortPreFinalP1YShiftRealizationGoal_of_pathGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hPath : ResetPortPreFinalP1YShiftPathRealizationGoal baseRow) :
    ResetPortPreFinalP1YShiftRealizationGoal baseRow :=
  fourLayerRealizationOnGoal_of_pathOnGoal
    (resetPortDirOfBase baseRow) 4
    (fun w =>
      ¬ finalLiftCarrySite 4 w ∧
      yCoord w ≠ 1 ∧ yCoord w ≠ 2 ∧ yCoord w ≠ 3)
    preFinalYShiftReturn hPath

theorem resetPortPreFinalP1Y1F0RealizationGoal_of_pathGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hPath : ResetPortPreFinalP1Y1F0PathRealizationGoal baseRow) :
    ResetPortPreFinalP1Y1F0RealizationGoal baseRow :=
  fourLayerRealizationOnGoal_of_pathOnGoal
    (resetPortDirOfBase baseRow) 4
    (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 1)
    (preFinalYTerminalReturn TerminalSymbol.F0) hPath

theorem resetPortPreFinalP1Y2F2RealizationGoal_of_pathGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hPath : ResetPortPreFinalP1Y2F2PathRealizationGoal baseRow) :
    ResetPortPreFinalP1Y2F2RealizationGoal baseRow :=
  fourLayerRealizationOnGoal_of_pathOnGoal
    (resetPortDirOfBase baseRow) 4
    (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 2)
    (preFinalYTerminalReturn TerminalSymbol.F2) hPath

theorem resetPortPreFinalP1Y3F1RealizationGoal_of_pathGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hPath : ResetPortPreFinalP1Y3F1PathRealizationGoal baseRow) :
    ResetPortPreFinalP1Y3F1RealizationGoal baseRow :=
  fourLayerRealizationOnGoal_of_pathOnGoal
    (resetPortDirOfBase baseRow) 4
    (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 3)
    (preFinalYTerminalReturn TerminalSymbol.F1) hPath

theorem resetPortPreFinalP0RealizationGoal_of_ySplit
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hYShift : ResetPortPreFinalP0YShiftRealizationGoal baseRow)
    (hF0 : ResetPortPreFinalP0F0RealizationGoal baseRow) :
    ResetPortPreFinalP0RealizationGoal baseRow := by
  intro w hNoFinal
  by_cases hY : yCoord w = 0
  · calc
      fourLayerReturn (resetPortDirOfBase baseRow) 3 w =
          preFinalYTerminalReturn TerminalSymbol.F0 w :=
            hF0 w ⟨hNoFinal, hY⟩
      _ = preFinalReturn 3 w :=
          (preFinalReturn_three_eq_yTerminalF0Return_of_y_zero w hY).symm
  · calc
      fourLayerReturn (resetPortDirOfBase baseRow) 3 w =
          preFinalYShiftReturn w :=
            hYShift w ⟨hNoFinal, hY⟩
      _ = preFinalReturn 3 w :=
          (preFinalReturn_three_eq_yShiftReturn_of_y_ne_zero w hY).symm

theorem resetPortPreFinalP0RealizationGoal_of_ySplitPathGoals
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hYShiftPath : ResetPortPreFinalP0YShiftPathRealizationGoal baseRow)
    (hF0Path : ResetPortPreFinalP0F0PathRealizationGoal baseRow) :
    ResetPortPreFinalP0RealizationGoal baseRow :=
  resetPortPreFinalP0RealizationGoal_of_ySplit baseRow
    (resetPortPreFinalP0YShiftRealizationGoal_of_pathGoal
      baseRow hYShiftPath)
    (resetPortPreFinalP0F0RealizationGoal_of_pathGoal baseRow hF0Path)

theorem resetPortPreFinalP1RealizationGoal_of_ySplit
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hYShift : ResetPortPreFinalP1YShiftRealizationGoal baseRow)
    (hF0 : ResetPortPreFinalP1Y1F0RealizationGoal baseRow)
    (hF2 : ResetPortPreFinalP1Y2F2RealizationGoal baseRow)
    (hF1 : ResetPortPreFinalP1Y3F1RealizationGoal baseRow) :
    ResetPortPreFinalP1RealizationGoal baseRow := by
  intro w hNoFinal
  by_cases hY1 : yCoord w = 1
  · calc
      fourLayerReturn (resetPortDirOfBase baseRow) 4 w =
          preFinalYTerminalReturn TerminalSymbol.F0 w :=
            hF0 w ⟨hNoFinal, hY1⟩
      _ = preFinalReturn 4 w :=
          (preFinalReturn_four_eq_yTerminalF0Return_of_y_one w hY1).symm
  · by_cases hY2 : yCoord w = 2
    · calc
        fourLayerReturn (resetPortDirOfBase baseRow) 4 w =
            preFinalYTerminalReturn TerminalSymbol.F2 w :=
              hF2 w ⟨hNoFinal, hY2⟩
        _ = preFinalReturn 4 w :=
            (preFinalReturn_four_eq_yTerminalF2Return_of_y_two
              w hY2).symm
    · by_cases hY3 : yCoord w = 3
      · calc
          fourLayerReturn (resetPortDirOfBase baseRow) 4 w =
              preFinalYTerminalReturn TerminalSymbol.F1 w :=
                hF1 w ⟨hNoFinal, hY3⟩
          _ = preFinalReturn 4 w :=
              (preFinalReturn_four_eq_yTerminalF1Return_of_y_three
                w hY3).symm
      · calc
          fourLayerReturn (resetPortDirOfBase baseRow) 4 w =
              preFinalYShiftReturn w :=
                hYShift w ⟨hNoFinal, hY1, hY2, hY3⟩
          _ = preFinalReturn 4 w :=
              (preFinalReturn_four_eq_yShiftReturn_of_y_ne_one_two_three
                w hY1 hY2 hY3).symm

theorem resetPortPreFinalP1RealizationGoal_of_ySplitPathGoals
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hYShiftPath : ResetPortPreFinalP1YShiftPathRealizationGoal baseRow)
    (hY1F0Path : ResetPortPreFinalP1Y1F0PathRealizationGoal baseRow)
    (hY2F2Path : ResetPortPreFinalP1Y2F2PathRealizationGoal baseRow)
    (hY3F1Path : ResetPortPreFinalP1Y3F1PathRealizationGoal baseRow) :
    ResetPortPreFinalP1RealizationGoal baseRow :=
  resetPortPreFinalP1RealizationGoal_of_ySplit baseRow
    (resetPortPreFinalP1YShiftRealizationGoal_of_pathGoal
      baseRow hYShiftPath)
    (resetPortPreFinalP1Y1F0RealizationGoal_of_pathGoal baseRow hY1F0Path)
    (resetPortPreFinalP1Y2F2RealizationGoal_of_pathGoal baseRow hY2F2Path)
    (resetPortPreFinalP1Y3F1RealizationGoal_of_pathGoal baseRow hY3F1Path)

/-- Terminal target on a final `Z` carry site when the first `Y` carry is not
active. -/
def terminalCoreFinalCarryReturn (i : Fin 3) : RootState → RootState :=
  fun w =>
    rootOfCoords
      (LowD5M4.F (terminalSymbolOfIndex i) (qCoord w))
      (yCoord w) (zCoord w + 1)

@[simp] theorem terminalCoreFinalCarryReturn_apply
    (i : Fin 3) (w : RootState) :
    terminalCoreFinalCarryReturn i w =
      rootOfCoords
        (LowD5M4.F (terminalSymbolOfIndex i) (qCoord w))
        (yCoord w) (zCoord w + 1) := rfl

/-- Terminal target on a final `Z` carry site when the first `Y` carry is also
active. -/
def terminalFirstFinalCarryReturn (i : Fin 3) : RootState → RootState :=
  fun w =>
    rootOfCoords
      (LowD5M4.F (terminalSymbolOfIndex i) (qCoord w))
      (yCoord w + 1) (zCoord w + 1)

@[simp] theorem terminalFirstFinalCarryReturn_apply
    (i : Fin 3) (w : RootState) :
    terminalFirstFinalCarryReturn i w =
      rootOfCoords
        (LowD5M4.F (terminalSymbolOfIndex i) (qCoord w))
        (yCoord w + 1) (zCoord w + 1) := rfl

/-- The state reached by the forced first layer at an active final `Z` carry
site. -/
def finalCarryZFirstState : RootState → RootState :=
  fun w => rootOfCoords (qCoord w) (yCoord w) (zCoord w + 1)

@[simp] theorem finalCarryZFirstState_apply (w : RootState) :
    finalCarryZFirstState w =
      rootOfCoords (qCoord w) (yCoord w) (zCoord w + 1) :=
  rfl

/-- The pure `Y` row-word target with the final `Z` carry attached. -/
def finalYShiftReturn : RootState → RootState :=
  fun w => rootOfCoords (qCoord w) (yCoord w + 1) (zCoord w + 1)

@[simp] theorem finalYShiftReturn_apply (w : RootState) :
    finalYShiftReturn w =
      rootOfCoords (qCoord w) (yCoord w + 1) (zCoord w + 1) := rfl

/-- A `P0`/`P1` terminal factor target with the final `Z` carry attached. -/
def finalYTerminalReturn (s : TerminalSymbol) : RootState → RootState :=
  fun w =>
    rootOfCoords (LowD5M4.F s (qCoord w)) (yCoord w + 1)
      (zCoord w + 1)

@[simp] theorem finalYTerminalReturn_apply
    (s : TerminalSymbol) (w : RootState) :
    finalYTerminalReturn s w =
      rootOfCoords (LowD5M4.F s (qCoord w)) (yCoord w + 1)
        (zCoord w + 1) := rfl

/-- A tail-path form for `P₀`/`P₁` terminal factors. The first three layers
reach the run-collapsed terminal tail with `Y` already advanced, and the fourth
layer reads the terminal symbol `s` from the paper `A₂` row word. The `zOut`
parameter lets the same interface cover the pre-final target and the target with
the final `Z` carry attached. -/
def ResetPortYTerminalTailPrefixPathOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop) (s : TerminalSymbol)
    (zOut : RootState → LowD5M4.Z) : Prop :=
  ∃ x1 x2 : RootState → RootState,
    ∀ w : RootState, sourceOk w →
      (LowD5M4Schedule.schedule
        (resetPortDirOfBase baseRow)).layerMap (0 : ZMod 4) c w =
        x1 w ∧
      (LowD5M4Schedule.schedule
        (resetPortDirOfBase baseRow)).layerMap (1 : ZMod 4) c (x1 w) =
        x2 w ∧
      (LowD5M4Schedule.schedule
        (resetPortDirOfBase baseRow)).layerMap (2 : ZMod 4) c (x2 w) =
        rootOfCoords
          (terminalReturnTailBaseOfSymbol s (qCoord w))
          (yCoord w + 1) (zOut w) ∧
      NoResetPortSites
        (rootOfCoords
          (terminalReturnTailBaseOfSymbol s (qCoord w))
          (yCoord w + 1) (zOut w))

/-- Last-layer terminal-symbol row-word read paired with
`ResetPortYTerminalTailPrefixPathOnGoal`. -/
def ResetPortYTerminalTailReadOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop) (s : TerminalSymbol)
    (zOut : RootState → LowD5M4.Z) : Prop :=
  ∀ w : RootState, sourceOk w →
    BaseRowReadsTerminalTailSymbol
      baseRow (3 : ZMod 4) c s (qCoord w) (yCoord w + 1) (zOut w)

/-- Split form for `P₀`/`P₁` terminal factors: prefix to the collapsed
terminal tail plus the last-layer terminal-symbol read. -/
structure ResetPortYTerminalTailSplitPathOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop) (s : TerminalSymbol)
    (zOut : RootState → LowD5M4.Z) :
    Prop where
  pathPrefix :
    ResetPortYTerminalTailPrefixPathOnGoal
      baseRow c sourceOk s zOut
  read :
    ResetPortYTerminalTailReadOnGoal
      baseRow c sourceOk s zOut

def ResetPortYTerminalTailPathOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop) (s : TerminalSymbol)
    (zOut : RootState → LowD5M4.Z) : Prop :=
  ∃ x1 x2 : RootState → RootState,
    ∀ w : RootState, sourceOk w →
      (LowD5M4Schedule.schedule
        (resetPortDirOfBase baseRow)).layerMap (0 : ZMod 4) c w =
        x1 w ∧
        (LowD5M4Schedule.schedule
          (resetPortDirOfBase baseRow)).layerMap (1 : ZMod 4) c (x1 w) =
          x2 w ∧
        (LowD5M4Schedule.schedule
          (resetPortDirOfBase baseRow)).layerMap (2 : ZMod 4) c (x2 w) =
          rootOfCoords
            (terminalReturnTailBaseOfSymbol s (qCoord w))
            (yCoord w + 1) (zOut w) ∧
        BaseRowReadsTerminalTailSymbol
          baseRow (3 : ZMod 4) c s (qCoord w) (yCoord w + 1)
          (zOut w) ∧
        (∀ j : Fin 3,
          ¬ firstLiftCarrySite (fin3ToFin5 j)
            (rootOfCoords
              (terminalReturnTailBaseOfSymbol s (qCoord w))
              (yCoord w + 1) (zOut w))) ∧
        (∀ d : TorusColor 5,
          ¬ finalLiftCarrySite d
          (rootOfCoords
            (terminalReturnTailBaseOfSymbol s (qCoord w))
            (yCoord w + 1) (zOut w)))

theorem ResetPortYTerminalTailPathOnGoal_of_split
    {baseRow : ResetPortBaseRow} {c : TorusColor 5}
    {sourceOk : RootState → Prop} {s : TerminalSymbol}
    {zOut : RootState → LowD5M4.Z}
    (hSplit :
      ResetPortYTerminalTailSplitPathOnGoal
        baseRow c sourceOk s zOut) :
    ResetPortYTerminalTailPathOnGoal
      baseRow c sourceOk s zOut := by
  rcases hSplit.pathPrefix with ⟨x1, x2, hsteps⟩
  refine ⟨x1, x2, ?_⟩
  intro w hOk
  rcases hsteps w hOk with ⟨h0, h1, h2, hNo⟩
  exact ⟨h0, h1, h2, hSplit.read w hOk, hNo.1, hNo.2⟩

theorem resetPortYTerminalPathOnGoal_of_tailPathOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop) (s : TerminalSymbol)
    (zOut : RootState → LowD5M4.Z)
    (hTail : ResetPortYTerminalTailPathOnGoal
      baseRow c sourceOk s zOut) :
    FourLayerPathOnGoal (resetPortDirOfBase baseRow) c sourceOk
      (fun w =>
        rootOfCoords (LowD5M4.F s (qCoord w)) (yCoord w + 1)
          (zOut w)) := by
  rcases hTail with ⟨x1, x2, hsteps⟩
  refine ⟨x1, x2,
      (fun w =>
        rootOfCoords
          (terminalReturnTailBaseOfSymbol s (qCoord w))
          (yCoord w + 1) (zOut w)),
      ?_⟩
  intro w hOk
  rcases hsteps w hOk with ⟨h0, h1, h2, hBase, hFirst, hFinal⟩
  refine ⟨h0, h1, h2, ?_⟩
  exact layerMap_resetPortDirOfBase_of_terminalTailSymbolRead_no_site
    baseRow (3 : ZMod 4) c s (qCoord w) (yCoord w + 1) (zOut w)
    hBase hFirst hFinal

theorem resetPortYTerminalPathOnGoal_of_tailSplitPathOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop) (s : TerminalSymbol)
    (zOut : RootState → LowD5M4.Z)
    (hTail : ResetPortYTerminalTailSplitPathOnGoal
      baseRow c sourceOk s zOut) :
    FourLayerPathOnGoal (resetPortDirOfBase baseRow) c sourceOk
      (fun w =>
        rootOfCoords (LowD5M4.F s (qCoord w)) (yCoord w + 1)
          (zOut w)) := by
  rcases hTail.pathPrefix with ⟨x1, x2, hsteps⟩
  refine ⟨x1, x2,
      (fun w =>
        rootOfCoords
          (terminalReturnTailBaseOfSymbol s (qCoord w))
          (yCoord w + 1) (zOut w)),
      ?_⟩
  intro w hOk
  rcases hsteps w hOk with ⟨h0, h1, h2, hNo⟩
  refine ⟨h0, h1, h2, ?_⟩
  exact layerMap_resetPortDirOfBase_of_terminalTailSymbolRead_no_resetPortSites
    baseRow (3 : ZMod 4) c s (qCoord w) (yCoord w + 1) (zOut w)
    (hTail.read w hOk) hNo

/-- The same tail-path interface specialized to the pre-final `P₀`/`P₁`
terminal-factor target. -/
def ResetPortPreFinalYTerminalTailPathOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop) (s : TerminalSymbol) : Prop :=
  ResetPortYTerminalTailPathOnGoal baseRow c sourceOk s zCoord

theorem resetPortPreFinalYTerminalPathOnGoal_of_tailPathOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop) (s : TerminalSymbol)
    (hTail : ResetPortPreFinalYTerminalTailPathOnGoal
      baseRow c sourceOk s) :
    FourLayerPathOnGoal (resetPortDirOfBase baseRow) c sourceOk
      (preFinalYTerminalReturn s) := by
  simpa [ResetPortPreFinalYTerminalTailPathOnGoal,
    preFinalYTerminalReturn]
    using resetPortYTerminalPathOnGoal_of_tailPathOnGoal
      baseRow c sourceOk s zCoord hTail

theorem resetPortPreFinalYTerminalPathOnGoal_of_tailSplitPathOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop) (s : TerminalSymbol)
    (hTail :
      ResetPortYTerminalTailSplitPathOnGoal baseRow c sourceOk s zCoord) :
    FourLayerPathOnGoal (resetPortDirOfBase baseRow) c sourceOk
      (preFinalYTerminalReturn s) := by
  simpa [preFinalYTerminalReturn]
    using resetPortYTerminalPathOnGoal_of_tailSplitPathOnGoal
      baseRow c sourceOk s zCoord hTail

/-- The same tail-path interface specialized to the final-`Z`-carry
`P₀`/`P₁` terminal-factor target. -/
def ResetPortFinalYTerminalTailPathOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop) (s : TerminalSymbol) : Prop :=
  ResetPortYTerminalTailPathOnGoal
    baseRow c sourceOk s (fun w => zCoord w + 1)

theorem resetPortFinalYTerminalPathOnGoal_of_tailPathOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop) (s : TerminalSymbol)
    (hTail : ResetPortFinalYTerminalTailPathOnGoal baseRow c sourceOk s) :
    FourLayerPathOnGoal (resetPortDirOfBase baseRow) c sourceOk
      (finalYTerminalReturn s) := by
  simpa [ResetPortFinalYTerminalTailPathOnGoal, finalYTerminalReturn]
    using resetPortYTerminalPathOnGoal_of_tailPathOnGoal
      baseRow c sourceOk s (fun w => zCoord w + 1) hTail

theorem resetPortFinalYTerminalPathOnGoal_of_tailSplitPathOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop) (s : TerminalSymbol)
    (hTail :
      ResetPortYTerminalTailSplitPathOnGoal
        baseRow c sourceOk s (fun w => zCoord w + 1)) :
    FourLayerPathOnGoal (resetPortDirOfBase baseRow) c sourceOk
      (finalYTerminalReturn s) := by
  simpa [finalYTerminalReturn]
    using resetPortYTerminalPathOnGoal_of_tailSplitPathOnGoal
      baseRow c sourceOk s (fun w => zCoord w + 1) hTail

/-- A last-step form for the pure `Y` row-word part of `P₀`/`P₁`. The first
three layers only have to reach the same `Q4` and `Y` coordinate with the chosen
output `Z`; the fourth layer then reads the `Y` lift direction. -/
def ResetPortYShiftLastStepPrefixPathOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop) (zOut : RootState → LowD5M4.Z) :
    Prop :=
  ∃ x1 x2 : RootState → RootState,
    ∀ w : RootState, sourceOk w →
      (LowD5M4Schedule.schedule
        (resetPortDirOfBase baseRow)).layerMap (0 : ZMod 4) c w =
        x1 w ∧
      (LowD5M4Schedule.schedule
        (resetPortDirOfBase baseRow)).layerMap (1 : ZMod 4) c (x1 w) =
        x2 w ∧
      (LowD5M4Schedule.schedule
        (resetPortDirOfBase baseRow)).layerMap (2 : ZMod 4) c (x2 w) =
        rootOfCoords (qCoord w) (yCoord w) (zOut w) ∧
      NoResetPortSites
        (rootOfCoords (qCoord w) (yCoord w) (zOut w))

/-- Last-layer pure `Y` row-word read paired with
`ResetPortYShiftLastStepPrefixPathOnGoal`. -/
def ResetPortYShiftLastStepReadOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop) (zOut : RootState → LowD5M4.Z) :
    Prop :=
  ∀ w : RootState, sourceOk w →
    BaseRowReadsYShift
      baseRow (3 : ZMod 4) c (qCoord w) (yCoord w) (zOut w)

/-- Split form for the pure `Y` row-word part of `P₀`/`P₁`: path prefix plus
the last-layer `liftYDirection5` read. -/
structure ResetPortYShiftLastStepSplitPathOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop) (zOut : RootState → LowD5M4.Z) :
    Prop where
  pathPrefix :
    ResetPortYShiftLastStepPrefixPathOnGoal
      baseRow c sourceOk zOut
  read :
    ResetPortYShiftLastStepReadOnGoal
      baseRow c sourceOk zOut

def ResetPortYShiftLastStepPathOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop) (zOut : RootState → LowD5M4.Z) :
    Prop :=
  ∃ x1 x2 : RootState → RootState,
    ∀ w : RootState, sourceOk w →
      (LowD5M4Schedule.schedule
        (resetPortDirOfBase baseRow)).layerMap (0 : ZMod 4) c w =
        x1 w ∧
        (LowD5M4Schedule.schedule
          (resetPortDirOfBase baseRow)).layerMap (1 : ZMod 4) c (x1 w) =
          x2 w ∧
        (LowD5M4Schedule.schedule
          (resetPortDirOfBase baseRow)).layerMap (2 : ZMod 4) c (x2 w) =
          rootOfCoords (qCoord w) (yCoord w) (zOut w) ∧
        BaseRowReadsYShift
          baseRow (3 : ZMod 4) c (qCoord w) (yCoord w) (zOut w) ∧
        (∀ j : Fin 3,
          ¬ firstLiftCarrySite (fin3ToFin5 j)
            (rootOfCoords (qCoord w) (yCoord w) (zOut w))) ∧
        (∀ d : TorusColor 5,
          ¬ finalLiftCarrySite d
            (rootOfCoords (qCoord w) (yCoord w) (zOut w)))

theorem ResetPortYShiftLastStepPathOnGoal_of_split
    {baseRow : ResetPortBaseRow} {c : TorusColor 5}
    {sourceOk : RootState → Prop} {zOut : RootState → LowD5M4.Z}
    (hSplit :
      ResetPortYShiftLastStepSplitPathOnGoal
        baseRow c sourceOk zOut) :
    ResetPortYShiftLastStepPathOnGoal
      baseRow c sourceOk zOut := by
  rcases hSplit.pathPrefix with ⟨x1, x2, hsteps⟩
  refine ⟨x1, x2, ?_⟩
  intro w hOk
  rcases hsteps w hOk with ⟨h0, h1, h2, hNo⟩
  exact ⟨h0, h1, h2, hSplit.read w hOk, hNo.1, hNo.2⟩

theorem resetPortYShiftPathOnGoal_of_lastStepPathOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop) (zOut : RootState → LowD5M4.Z)
      (hLast : ResetPortYShiftLastStepPathOnGoal
        baseRow c sourceOk zOut) :
      FourLayerPathOnGoal (resetPortDirOfBase baseRow) c sourceOk
        (fun w => rootOfCoords (qCoord w) (yCoord w + 1) (zOut w)) := by
    rcases hLast with ⟨x1, x2, hsteps⟩
    refine ⟨x1, x2,
      (fun w => rootOfCoords (qCoord w) (yCoord w) (zOut w)), ?_⟩
    intro w hOk
    rcases hsteps w hOk with ⟨h0, h1, h2, hBase, hFirst, hFinal⟩
    refine ⟨h0, h1, h2, ?_⟩
    exact layerMap_resetPortDirOfBase_of_yShiftRead_no_site
      baseRow (3 : ZMod 4) c (qCoord w) (yCoord w) (zOut w)
      hBase hFirst hFinal

theorem resetPortYShiftPathOnGoal_of_lastStepSplitPathOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop) (zOut : RootState → LowD5M4.Z)
    (hLast : ResetPortYShiftLastStepSplitPathOnGoal
      baseRow c sourceOk zOut) :
    FourLayerPathOnGoal (resetPortDirOfBase baseRow) c sourceOk
      (fun w => rootOfCoords (qCoord w) (yCoord w + 1) (zOut w)) := by
  rcases hLast.pathPrefix with ⟨x1, x2, hsteps⟩
  refine ⟨x1, x2,
    (fun w => rootOfCoords (qCoord w) (yCoord w) (zOut w)), ?_⟩
  intro w hOk
  rcases hsteps w hOk with ⟨h0, h1, h2, hNo⟩
  refine ⟨h0, h1, h2, ?_⟩
  exact layerMap_resetPortDirOfBase_of_yShiftRead_no_resetPortSites
    baseRow (3 : ZMod 4) c (qCoord w) (yCoord w) (zOut w)
    (hLast.read w hOk) hNo

/-- Pre-final specialization of the pure `Y` row-word last-step input. -/
def ResetPortPreFinalYShiftLastStepPathOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop) : Prop :=
  ResetPortYShiftLastStepPathOnGoal baseRow c sourceOk zCoord

theorem resetPortPreFinalYShiftPathOnGoal_of_lastStepPathOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop)
    (hLast : ResetPortPreFinalYShiftLastStepPathOnGoal
      baseRow c sourceOk) :
    FourLayerPathOnGoal (resetPortDirOfBase baseRow) c sourceOk
      preFinalYShiftReturn := by
  simpa [ResetPortPreFinalYShiftLastStepPathOnGoal,
    preFinalYShiftReturn]
    using resetPortYShiftPathOnGoal_of_lastStepPathOnGoal
      baseRow c sourceOk zCoord hLast

theorem resetPortPreFinalYShiftPathOnGoal_of_lastStepSplitPathOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop)
    (hLast : ResetPortYShiftLastStepSplitPathOnGoal
      baseRow c sourceOk zCoord) :
    FourLayerPathOnGoal (resetPortDirOfBase baseRow) c sourceOk
      preFinalYShiftReturn := by
  simpa [preFinalYShiftReturn]
    using resetPortYShiftPathOnGoal_of_lastStepSplitPathOnGoal
      baseRow c sourceOk zCoord hLast

/-- Final-carry specialization of the pure `Y` row-word last-step input. -/
def ResetPortFinalYShiftLastStepPathOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop) : Prop :=
  ResetPortYShiftLastStepPathOnGoal
    baseRow c sourceOk (fun w => zCoord w + 1)

theorem resetPortFinalYShiftPathOnGoal_of_lastStepPathOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop)
    (hLast : ResetPortFinalYShiftLastStepPathOnGoal baseRow c sourceOk) :
    FourLayerPathOnGoal (resetPortDirOfBase baseRow) c sourceOk
      finalYShiftReturn := by
  simpa [ResetPortFinalYShiftLastStepPathOnGoal, finalYShiftReturn]
    using resetPortYShiftPathOnGoal_of_lastStepPathOnGoal
      baseRow c sourceOk (fun w => zCoord w + 1) hLast

theorem resetPortFinalYShiftPathOnGoal_of_lastStepSplitPathOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop)
    (hLast : ResetPortYShiftLastStepSplitPathOnGoal
      baseRow c sourceOk (fun w => zCoord w + 1)) :
    FourLayerPathOnGoal (resetPortDirOfBase baseRow) c sourceOk
      finalYShiftReturn := by
  simpa [finalYShiftReturn]
    using resetPortYShiftPathOnGoal_of_lastStepSplitPathOnGoal
      baseRow c sourceOk (fun w => zCoord w + 1) hLast

theorem finalCarryReturn_terminal_eq_terminalCoreFinalCarryReturn_of_not_firstLiftCarrySite
    (i : Fin 3) (w : RootState)
    (hFirst : ¬ firstLiftCarrySite (fin3ToFin5 i) w) :
    finalCarryReturn (fin3ToFin5 i) w =
      terminalCoreFinalCarryReturn i w := by
  rw [finalCarryReturn_terminal_sites i w]
  simp [terminalCoreFinalCarryReturn, hFirst]

theorem finalCarryReturn_terminal_eq_terminalFirstFinalCarryReturn_of_firstLiftCarrySite
    (i : Fin 3) (w : RootState)
    (hFirst : firstLiftCarrySite (fin3ToFin5 i) w) :
    finalCarryReturn (fin3ToFin5 i) w =
      terminalFirstFinalCarryReturn i w := by
  rw [finalCarryReturn_terminal_sites i w]
  simp [terminalFirstFinalCarryReturn, hFirst]

theorem finalCarryReturn_three_eq_finalYShiftReturn_of_y_ne_zero
    (w : RootState) (hY : yCoord w ≠ 0) :
    finalCarryReturn 3 w = finalYShiftReturn w := by
  rw [finalCarryReturn_three]
  simp [finalYShiftReturn, hY]

theorem finalCarryReturn_three_eq_finalYTerminalF0Return_of_y_zero
    (w : RootState) (hY : yCoord w = 0) :
    finalCarryReturn 3 w = finalYTerminalReturn TerminalSymbol.F0 w := by
  rw [finalCarryReturn_three]
  simp [finalYTerminalReturn, hY]

theorem finalCarryReturn_four_eq_finalYTerminalF0Return_of_y_one
    (w : RootState) (hY : yCoord w = 1) :
    finalCarryReturn 4 w = finalYTerminalReturn TerminalSymbol.F0 w := by
  rw [finalCarryReturn_four]
  simp [finalYTerminalReturn, hY]

theorem finalCarryReturn_four_eq_finalYTerminalF2Return_of_y_two
    (w : RootState) (hY : yCoord w = 2) :
    finalCarryReturn 4 w = finalYTerminalReturn TerminalSymbol.F2 w := by
  have h21 : (2 : ZMod 4) ≠ 1 := by decide
  rw [finalCarryReturn_four]
  simp [finalYTerminalReturn, hY, h21]

theorem finalCarryReturn_four_eq_finalYTerminalF1Return_of_y_three
    (w : RootState) (hY : yCoord w = 3) :
    finalCarryReturn 4 w = finalYTerminalReturn TerminalSymbol.F1 w := by
  have h31 : (3 : ZMod 4) ≠ 1 := by decide
  have h32 : (3 : ZMod 4) ≠ 2 := by decide
  rw [finalCarryReturn_four]
  simp [finalYTerminalReturn, hY, h31, h32]

theorem finalCarryReturn_four_eq_finalYShiftReturn_of_y_ne_one_two_three
    (w : RootState) (hY1 : yCoord w ≠ 1) (hY2 : yCoord w ≠ 2)
    (hY3 : yCoord w ≠ 3) :
    finalCarryReturn 4 w = finalYShiftReturn w := by
  rw [finalCarryReturn_four]
  simp [finalYShiftReturn, hY1, hY2, hY3]

def ResetPortFinalCarryTerminalNoFirstRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  ∀ i : Fin 3,
    FourLayerRealizationOnGoal
      (resetPortDirOfBase baseRow) (fin3ToFin5 i)
      (fun w =>
        finalLiftCarrySite (fin3ToFin5 i) w ∧
        ¬ firstLiftCarrySite (fin3ToFin5 i) w)
      (terminalCoreFinalCarryReturn i)

def ResetPortFinalCarryTerminalFirstRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  ∀ i : Fin 3,
    FourLayerRealizationOnGoal
      (resetPortDirOfBase baseRow) (fin3ToFin5 i)
      (fun w =>
        finalLiftCarrySite (fin3ToFin5 i) w ∧
        firstLiftCarrySite (fin3ToFin5 i) w)
      (terminalFirstFinalCarryReturn i)

def ResetPortFinalCarryTerminalNoFirstPathRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  ∀ i : Fin 3,
    FourLayerPathOnGoal
      (resetPortDirOfBase baseRow) (fin3ToFin5 i)
      (fun w =>
        finalLiftCarrySite (fin3ToFin5 i) w ∧
        ¬ firstLiftCarrySite (fin3ToFin5 i) w)
      (terminalCoreFinalCarryReturn i)

def ResetPortFinalCarryTerminalFirstPathRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  ∀ i : Fin 3,
    FourLayerPathOnGoal
      (resetPortDirOfBase baseRow) (fin3ToFin5 i)
      (fun w =>
        finalLiftCarrySite (fin3ToFin5 i) w ∧
        firstLiftCarrySite (fin3ToFin5 i) w)
      (terminalFirstFinalCarryReturn i)

/-- Residual path input after the final-carry substitution has supplied the
first `z += 1` step.  The remaining obligation is only layers `1,2,3`. -/
def ResetPortFinalZFirstResidualPathOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop) (target : RootState → RootState) :
    Prop :=
  ∃ x2 x3 : RootState → RootState,
    ∀ w : RootState, sourceOk w →
      (LowD5M4Schedule.schedule
        (resetPortDirOfBase baseRow)).layerMap (1 : ZMod 4) c
          (finalCarryZFirstState w) =
        x2 w ∧
      (LowD5M4Schedule.schedule
        (resetPortDirOfBase baseRow)).layerMap (2 : ZMod 4) c (x2 w) =
        x3 w ∧
      (LowD5M4Schedule.schedule
        (resetPortDirOfBase baseRow)).layerMap (3 : ZMod 4) c (x3 w) =
        target w

theorem resetPortFinalPathOnGoal_of_zFirstResidualPathOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop) (target : RootState → RootState)
    (hFinal : ∀ w : RootState, sourceOk w → finalLiftCarrySite c w)
    (hResidual :
      ResetPortFinalZFirstResidualPathOnGoal
        baseRow c sourceOk target) :
    FourLayerPathOnGoal (resetPortDirOfBase baseRow) c sourceOk target := by
  rcases hResidual with ⟨x2, x3, hsteps⟩
  refine ⟨finalCarryZFirstState, x2, x3, ?_⟩
  intro w hOk
  rcases hsteps w hOk with ⟨h1, h2, h3⟩
  refine ⟨?_, h1, h2, h3⟩
  rw [layerMap_resetPortDirOfBase_color_of_final_site
    baseRow (0 : ZMod 4) c w (hFinal w hOk)]
  rfl

/-- Final-carry pure `Y` row-word input after the forced first `z += 1`
layer has fired.  The remaining layers `1,2,3` only have to reach the same
`Q4,Y` point with `Z` advanced, then read the `Y` lift direction. -/
def ResetPortFinalZFirstYShiftLastStepPrefixPathOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop) : Prop :=
  ∃ x2 : RootState → RootState,
    ∀ w : RootState, sourceOk w →
      (LowD5M4Schedule.schedule
        (resetPortDirOfBase baseRow)).layerMap (1 : ZMod 4) c
          (finalCarryZFirstState w) =
        x2 w ∧
      (LowD5M4Schedule.schedule
        (resetPortDirOfBase baseRow)).layerMap (2 : ZMod 4) c (x2 w) =
        rootOfCoords (qCoord w) (yCoord w) (zCoord w + 1) ∧
      NoResetPortSites
        (rootOfCoords (qCoord w) (yCoord w) (zCoord w + 1))

/-- Last-layer pure `Y` read after the final-carry forced `z += 1` step. -/
def ResetPortFinalZFirstYShiftLastStepReadOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop) : Prop :=
  ∀ w : RootState, sourceOk w →
    BaseRowReadsYShift
      baseRow (3 : ZMod 4) c (qCoord w) (yCoord w) (zCoord w + 1)

/-- Split form of the final-carry pure `Y` row-word residual after the forced
first `z += 1` layer. -/
structure ResetPortFinalZFirstYShiftLastStepSplitPathOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop) :
    Prop where
  pathPrefix :
    ResetPortFinalZFirstYShiftLastStepPrefixPathOnGoal
      baseRow c sourceOk
  read :
    ResetPortFinalZFirstYShiftLastStepReadOnGoal
      baseRow c sourceOk

def ResetPortFinalZFirstYShiftLastStepPathOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop) : Prop :=
  ∃ x2 : RootState → RootState,
    ∀ w : RootState, sourceOk w →
        (LowD5M4Schedule.schedule
          (resetPortDirOfBase baseRow)).layerMap (1 : ZMod 4) c
            (finalCarryZFirstState w) =
          x2 w ∧
        (LowD5M4Schedule.schedule
          (resetPortDirOfBase baseRow)).layerMap (2 : ZMod 4) c (x2 w) =
          rootOfCoords (qCoord w) (yCoord w) (zCoord w + 1) ∧
        BaseRowReadsYShift
          baseRow (3 : ZMod 4) c (qCoord w) (yCoord w)
          (zCoord w + 1) ∧
        (∀ j : Fin 3,
          ¬ firstLiftCarrySite (fin3ToFin5 j)
            (rootOfCoords (qCoord w) (yCoord w) (zCoord w + 1))) ∧
        (∀ d : TorusColor 5,
          ¬ finalLiftCarrySite d
            (rootOfCoords (qCoord w) (yCoord w) (zCoord w + 1)))

theorem ResetPortFinalZFirstYShiftLastStepPathOnGoal_of_split
    {baseRow : ResetPortBaseRow} {c : TorusColor 5}
    {sourceOk : RootState → Prop}
    (hSplit :
      ResetPortFinalZFirstYShiftLastStepSplitPathOnGoal
        baseRow c sourceOk) :
    ResetPortFinalZFirstYShiftLastStepPathOnGoal
      baseRow c sourceOk := by
  rcases hSplit.pathPrefix with ⟨x2, hsteps⟩
  refine ⟨x2, ?_⟩
  intro w hOk
  rcases hsteps w hOk with ⟨h1, h2, hNo⟩
  exact ⟨h1, h2, hSplit.read w hOk, hNo.1, hNo.2⟩

theorem resetPortFinalYShiftPathOnGoal_of_zFirstLastStepPathOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop)
    (hFinal : ∀ w : RootState, sourceOk w → finalLiftCarrySite c w)
    (hLast :
      ResetPortFinalZFirstYShiftLastStepPathOnGoal baseRow c sourceOk) :
    FourLayerPathOnGoal (resetPortDirOfBase baseRow) c sourceOk
      finalYShiftReturn := by
  rcases hLast with ⟨x2, hsteps⟩
  refine ⟨finalCarryZFirstState, x2,
    (fun w => rootOfCoords (qCoord w) (yCoord w) (zCoord w + 1)),
    ?_⟩
  intro w hOk
  rcases hsteps w hOk with ⟨h1, h2, hBase, hFirst, hFinalSites⟩
  refine ⟨?_, h1, h2, ?_⟩
  · rw [layerMap_resetPortDirOfBase_color_of_final_site
      baseRow (0 : ZMod 4) c w (hFinal w hOk)]
    rfl
  · simpa [finalYShiftReturn] using
      layerMap_resetPortDirOfBase_of_yShiftRead_no_site
        baseRow (3 : ZMod 4) c (qCoord w) (yCoord w)
        (zCoord w + 1) hBase hFirst hFinalSites

theorem resetPortFinalYShiftPathOnGoal_of_zFirstLastStepSplitPathOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop)
    (hFinal : ∀ w : RootState, sourceOk w → finalLiftCarrySite c w)
    (hLast :
      ResetPortFinalZFirstYShiftLastStepSplitPathOnGoal
        baseRow c sourceOk) :
    FourLayerPathOnGoal (resetPortDirOfBase baseRow) c sourceOk
      finalYShiftReturn := by
  rcases hLast.pathPrefix with ⟨x2, hsteps⟩
  refine ⟨finalCarryZFirstState, x2,
    (fun w => rootOfCoords (qCoord w) (yCoord w) (zCoord w + 1)),
    ?_⟩
  intro w hOk
  rcases hsteps w hOk with ⟨h1, h2, hNo⟩
  refine ⟨?_, h1, h2, ?_⟩
  · rw [layerMap_resetPortDirOfBase_color_of_final_site
      baseRow (0 : ZMod 4) c w (hFinal w hOk)]
    rfl
  · simpa [finalYShiftReturn] using
      layerMap_resetPortDirOfBase_of_yShiftRead_no_resetPortSites
        baseRow (3 : ZMod 4) c (qCoord w) (yCoord w)
        (zCoord w + 1) (hLast.read w hOk) hNo

/-- Final-carry `P₀`/`P₁` terminal-factor input after the forced first
`z += 1` layer has fired.  The residual layers reach the collapsed terminal
tail with `Y` and `Z` already advanced, then read the terminal row word. -/
def ResetPortFinalZFirstYTerminalTailPrefixPathOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop) (s : TerminalSymbol) : Prop :=
  ∃ x2 : RootState → RootState,
    ∀ w : RootState, sourceOk w →
      (LowD5M4Schedule.schedule
        (resetPortDirOfBase baseRow)).layerMap (1 : ZMod 4) c
          (finalCarryZFirstState w) =
        x2 w ∧
      (LowD5M4Schedule.schedule
        (resetPortDirOfBase baseRow)).layerMap (2 : ZMod 4) c (x2 w) =
        rootOfCoords
          (terminalReturnTailBaseOfSymbol s (qCoord w))
          (yCoord w + 1) (zCoord w + 1) ∧
      NoResetPortSites
        (rootOfCoords
          (terminalReturnTailBaseOfSymbol s (qCoord w))
          (yCoord w + 1) (zCoord w + 1))

/-- Last-layer terminal-symbol read after the final-carry forced `z += 1`
step. -/
def ResetPortFinalZFirstYTerminalTailReadOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop) (s : TerminalSymbol) : Prop :=
  ∀ w : RootState, sourceOk w →
    BaseRowReadsTerminalTailSymbol
      baseRow (3 : ZMod 4) c s (qCoord w) (yCoord w + 1)
        (zCoord w + 1)

/-- Split form of the final-carry terminal-factor residual after the forced
first `z += 1` layer. -/
structure ResetPortFinalZFirstYTerminalTailSplitPathOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop) (s : TerminalSymbol) :
    Prop where
  pathPrefix :
    ResetPortFinalZFirstYTerminalTailPrefixPathOnGoal
      baseRow c sourceOk s
  read :
    ResetPortFinalZFirstYTerminalTailReadOnGoal
      baseRow c sourceOk s

def ResetPortFinalZFirstYTerminalTailPathOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop) (s : TerminalSymbol) : Prop :=
  ∃ x2 : RootState → RootState,
    ∀ w : RootState, sourceOk w →
        (LowD5M4Schedule.schedule
          (resetPortDirOfBase baseRow)).layerMap (1 : ZMod 4) c
            (finalCarryZFirstState w) =
          x2 w ∧
        (LowD5M4Schedule.schedule
          (resetPortDirOfBase baseRow)).layerMap (2 : ZMod 4) c (x2 w) =
          rootOfCoords
            (terminalReturnTailBaseOfSymbol s (qCoord w))
            (yCoord w + 1) (zCoord w + 1) ∧
        BaseRowReadsTerminalTailSymbol
          baseRow (3 : ZMod 4) c s (qCoord w) (yCoord w + 1)
          (zCoord w + 1) ∧
        (∀ j : Fin 3,
          ¬ firstLiftCarrySite (fin3ToFin5 j)
            (rootOfCoords
              (terminalReturnTailBaseOfSymbol s (qCoord w))
              (yCoord w + 1) (zCoord w + 1))) ∧
        (∀ d : TorusColor 5,
          ¬ finalLiftCarrySite d
          (rootOfCoords
            (terminalReturnTailBaseOfSymbol s (qCoord w))
            (yCoord w + 1) (zCoord w + 1)))

theorem ResetPortFinalZFirstYTerminalTailPathOnGoal_of_split
    {baseRow : ResetPortBaseRow} {c : TorusColor 5}
    {sourceOk : RootState → Prop} {s : TerminalSymbol}
    (hSplit :
      ResetPortFinalZFirstYTerminalTailSplitPathOnGoal
        baseRow c sourceOk s) :
    ResetPortFinalZFirstYTerminalTailPathOnGoal
      baseRow c sourceOk s := by
  rcases hSplit.pathPrefix with ⟨x2, hsteps⟩
  refine ⟨x2, ?_⟩
  intro w hOk
  rcases hsteps w hOk with ⟨h1, h2, hNo⟩
  exact ⟨h1, h2, hSplit.read w hOk, hNo.1, hNo.2⟩

theorem resetPortFinalYTerminalPathOnGoal_of_zFirstTailPathOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop) (s : TerminalSymbol)
    (hFinal : ∀ w : RootState, sourceOk w → finalLiftCarrySite c w)
    (hTail :
      ResetPortFinalZFirstYTerminalTailPathOnGoal
        baseRow c sourceOk s) :
    FourLayerPathOnGoal (resetPortDirOfBase baseRow) c sourceOk
      (finalYTerminalReturn s) := by
  rcases hTail with ⟨x2, hsteps⟩
  refine ⟨finalCarryZFirstState, x2,
    (fun w =>
      rootOfCoords
        (terminalReturnTailBaseOfSymbol s (qCoord w))
        (yCoord w + 1) (zCoord w + 1)),
      ?_⟩
  intro w hOk
  rcases hsteps w hOk with ⟨h1, h2, hBase, hFirst, hFinalSites⟩
  refine ⟨?_, h1, h2, ?_⟩
  · rw [layerMap_resetPortDirOfBase_color_of_final_site
      baseRow (0 : ZMod 4) c w (hFinal w hOk)]
    rfl
  · simpa [finalYTerminalReturn] using
      layerMap_resetPortDirOfBase_of_terminalTailSymbolRead_no_site
        baseRow (3 : ZMod 4) c s (qCoord w) (yCoord w + 1)
        (zCoord w + 1) hBase hFirst hFinalSites

theorem resetPortFinalYTerminalPathOnGoal_of_zFirstTailSplitPathOnGoal
    (baseRow : ResetPortBaseRow) (c : TorusColor 5)
    (sourceOk : RootState → Prop) (s : TerminalSymbol)
    (hFinal : ∀ w : RootState, sourceOk w → finalLiftCarrySite c w)
    (hTail :
      ResetPortFinalZFirstYTerminalTailSplitPathOnGoal
        baseRow c sourceOk s) :
    FourLayerPathOnGoal (resetPortDirOfBase baseRow) c sourceOk
      (finalYTerminalReturn s) := by
  rcases hTail.pathPrefix with ⟨x2, hsteps⟩
  refine ⟨finalCarryZFirstState, x2,
    (fun w =>
      rootOfCoords
        (terminalReturnTailBaseOfSymbol s (qCoord w))
        (yCoord w + 1) (zCoord w + 1)),
      ?_⟩
  intro w hOk
  rcases hsteps w hOk with ⟨h1, h2, hNo⟩
  refine ⟨?_, h1, h2, ?_⟩
  · rw [layerMap_resetPortDirOfBase_color_of_final_site
      baseRow (0 : ZMod 4) c w (hFinal w hOk)]
    rfl
  · simpa [finalYTerminalReturn] using
      layerMap_resetPortDirOfBase_of_terminalTailSymbolRead_no_resetPortSites
        baseRow (3 : ZMod 4) c s (qCoord w) (yCoord w + 1)
        (zCoord w + 1) (hTail.read w hOk) hNo

def ResetPortFinalCarryTerminalNoFirstZFirstResidualPathGoal
    (baseRow : ResetPortBaseRow) :
    Prop :=
  ∀ i : Fin 3,
    ResetPortFinalZFirstResidualPathOnGoal
      baseRow (fin3ToFin5 i)
      (fun w =>
        finalLiftCarrySite (fin3ToFin5 i) w ∧
        ¬ firstLiftCarrySite (fin3ToFin5 i) w)
      (terminalCoreFinalCarryReturn i)

def ResetPortFinalCarryTerminalFirstZFirstResidualPathGoal
    (baseRow : ResetPortBaseRow) :
    Prop :=
  ∀ i : Fin 3,
    ResetPortFinalZFirstResidualPathOnGoal
      baseRow (fin3ToFin5 i)
      (fun w =>
        finalLiftCarrySite (fin3ToFin5 i) w ∧
        firstLiftCarrySite (fin3ToFin5 i) w)
      (terminalFirstFinalCarryReturn i)

theorem resetPortFinalCarryTerminalNoFirstPathGoal_of_zFirstResidualPathGoal
    (baseRow : ResetPortBaseRow)
    (hResidual :
      ResetPortFinalCarryTerminalNoFirstZFirstResidualPathGoal baseRow) :
    ResetPortFinalCarryTerminalNoFirstPathRealizationGoal baseRow := by
  intro i
  exact resetPortFinalPathOnGoal_of_zFirstResidualPathOnGoal
    baseRow (fin3ToFin5 i)
    (fun w =>
      finalLiftCarrySite (fin3ToFin5 i) w ∧
      ¬ firstLiftCarrySite (fin3ToFin5 i) w)
    (terminalCoreFinalCarryReturn i)
    (fun _w h => h.1)
    (hResidual i)

theorem resetPortFinalCarryTerminalFirstPathGoal_of_zFirstResidualPathGoal
    (baseRow : ResetPortBaseRow)
    (hResidual :
      ResetPortFinalCarryTerminalFirstZFirstResidualPathGoal baseRow) :
    ResetPortFinalCarryTerminalFirstPathRealizationGoal baseRow := by
  intro i
  exact resetPortFinalPathOnGoal_of_zFirstResidualPathOnGoal
    baseRow (fin3ToFin5 i)
    (fun w =>
      finalLiftCarrySite (fin3ToFin5 i) w ∧
      firstLiftCarrySite (fin3ToFin5 i) w)
    (terminalFirstFinalCarryReturn i)
    (fun _w h => h.1)
    (hResidual i)

theorem resetPortFinalCarryTerminalNoFirstRealizationGoal_of_pathGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hPath : ResetPortFinalCarryTerminalNoFirstPathRealizationGoal baseRow) :
    ResetPortFinalCarryTerminalNoFirstRealizationGoal baseRow := by
  intro i
  exact fourLayerRealizationOnGoal_of_pathOnGoal
    (resetPortDirOfBase baseRow) (fin3ToFin5 i)
    (fun w =>
      finalLiftCarrySite (fin3ToFin5 i) w ∧
      ¬ firstLiftCarrySite (fin3ToFin5 i) w)
    (terminalCoreFinalCarryReturn i) (hPath i)

theorem resetPortFinalCarryTerminalFirstRealizationGoal_of_pathGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hPath : ResetPortFinalCarryTerminalFirstPathRealizationGoal baseRow) :
    ResetPortFinalCarryTerminalFirstRealizationGoal baseRow := by
  intro i
  exact fourLayerRealizationOnGoal_of_pathOnGoal
    (resetPortDirOfBase baseRow) (fin3ToFin5 i)
    (fun w =>
      finalLiftCarrySite (fin3ToFin5 i) w ∧
      firstLiftCarrySite (fin3ToFin5 i) w)
    (terminalFirstFinalCarryReturn i) (hPath i)

theorem resetPortFinalCarryTerminalRealizationGoal_of_firstCarrySplit
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hNoFirst : ResetPortFinalCarryTerminalNoFirstRealizationGoal baseRow)
    (hFirst : ResetPortFinalCarryTerminalFirstRealizationGoal baseRow) :
    ResetPortFinalCarryTerminalRealizationGoal baseRow := by
  intro i w hFinal
  by_cases hFirstSite : firstLiftCarrySite (fin3ToFin5 i) w
  · calc
      fourLayerReturn (resetPortDirOfBase baseRow) (fin3ToFin5 i) w =
          terminalFirstFinalCarryReturn i w :=
            hFirst i w ⟨hFinal, hFirstSite⟩
      _ = finalCarryReturn (fin3ToFin5 i) w :=
          (finalCarryReturn_terminal_eq_terminalFirstFinalCarryReturn_of_firstLiftCarrySite
            i w hFirstSite).symm
  · calc
      fourLayerReturn (resetPortDirOfBase baseRow) (fin3ToFin5 i) w =
          terminalCoreFinalCarryReturn i w :=
            hNoFirst i w ⟨hFinal, hFirstSite⟩
      _ = finalCarryReturn (fin3ToFin5 i) w :=
          (finalCarryReturn_terminal_eq_terminalCoreFinalCarryReturn_of_not_firstLiftCarrySite
            i w hFirstSite).symm

theorem resetPortFinalCarryTerminalRealizationGoal_of_firstCarryPathGoals
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hNoFirstPath :
      ResetPortFinalCarryTerminalNoFirstPathRealizationGoal baseRow)
    (hFirstPath :
      ResetPortFinalCarryTerminalFirstPathRealizationGoal baseRow) :
    ResetPortFinalCarryTerminalRealizationGoal baseRow :=
  resetPortFinalCarryTerminalRealizationGoal_of_firstCarrySplit baseRow
    (resetPortFinalCarryTerminalNoFirstRealizationGoal_of_pathGoal
      baseRow hNoFirstPath)
    (resetPortFinalCarryTerminalFirstRealizationGoal_of_pathGoal
      baseRow hFirstPath)

def ResetPortFinalCarryP0YShiftRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  FourLayerRealizationOnGoal
    (resetPortDirOfBase baseRow) 3
    (fun w => finalLiftCarrySite 3 w ∧ yCoord w ≠ 0)
    finalYShiftReturn

def ResetPortFinalCarryP0F0RealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  FourLayerRealizationOnGoal
    (resetPortDirOfBase baseRow) 3
    (fun w => finalLiftCarrySite 3 w ∧ yCoord w = 0)
    (finalYTerminalReturn TerminalSymbol.F0)

def ResetPortFinalCarryP1YShiftRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  FourLayerRealizationOnGoal
    (resetPortDirOfBase baseRow) 4
    (fun w =>
      finalLiftCarrySite 4 w ∧
      yCoord w ≠ 1 ∧ yCoord w ≠ 2 ∧ yCoord w ≠ 3)
    finalYShiftReturn

def ResetPortFinalCarryP1Y1F0RealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  FourLayerRealizationOnGoal
    (resetPortDirOfBase baseRow) 4
    (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 1)
    (finalYTerminalReturn TerminalSymbol.F0)

def ResetPortFinalCarryP1Y2F2RealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  FourLayerRealizationOnGoal
    (resetPortDirOfBase baseRow) 4
    (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 2)
    (finalYTerminalReturn TerminalSymbol.F2)

def ResetPortFinalCarryP1Y3F1RealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  FourLayerRealizationOnGoal
    (resetPortDirOfBase baseRow) 4
    (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 3)
    (finalYTerminalReturn TerminalSymbol.F1)

def ResetPortFinalCarryP0YShiftPathRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  FourLayerPathOnGoal
    (resetPortDirOfBase baseRow) 3
    (fun w => finalLiftCarrySite 3 w ∧ yCoord w ≠ 0)
    finalYShiftReturn

def ResetPortFinalCarryP0F0PathRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  FourLayerPathOnGoal
    (resetPortDirOfBase baseRow) 3
    (fun w => finalLiftCarrySite 3 w ∧ yCoord w = 0)
    (finalYTerminalReturn TerminalSymbol.F0)

def ResetPortFinalCarryP1YShiftPathRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  FourLayerPathOnGoal
    (resetPortDirOfBase baseRow) 4
    (fun w =>
      finalLiftCarrySite 4 w ∧
      yCoord w ≠ 1 ∧ yCoord w ≠ 2 ∧ yCoord w ≠ 3)
    finalYShiftReturn

def ResetPortFinalCarryP1Y1F0PathRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  FourLayerPathOnGoal
    (resetPortDirOfBase baseRow) 4
    (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 1)
    (finalYTerminalReturn TerminalSymbol.F0)

def ResetPortFinalCarryP1Y2F2PathRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  FourLayerPathOnGoal
    (resetPortDirOfBase baseRow) 4
    (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 2)
    (finalYTerminalReturn TerminalSymbol.F2)

def ResetPortFinalCarryP1Y3F1PathRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  FourLayerPathOnGoal
    (resetPortDirOfBase baseRow) 4
    (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 3)
    (finalYTerminalReturn TerminalSymbol.F1)

theorem resetPortPreFinalP0YShiftPathRealizationGoal_of_lastStepPathOnGoal
    (baseRow : ResetPortBaseRow)
    (hLast :
      ResetPortPreFinalYShiftLastStepPathOnGoal baseRow 3
        (fun w => ¬ finalLiftCarrySite 3 w ∧ yCoord w ≠ 0)) :
    ResetPortPreFinalP0YShiftPathRealizationGoal baseRow :=
  resetPortPreFinalYShiftPathOnGoal_of_lastStepPathOnGoal
    baseRow 3
    (fun w => ¬ finalLiftCarrySite 3 w ∧ yCoord w ≠ 0) hLast

theorem resetPortPreFinalP1YShiftPathRealizationGoal_of_lastStepPathOnGoal
    (baseRow : ResetPortBaseRow)
    (hLast :
      ResetPortPreFinalYShiftLastStepPathOnGoal baseRow 4
        (fun w =>
          ¬ finalLiftCarrySite 4 w ∧
          yCoord w ≠ 1 ∧ yCoord w ≠ 2 ∧ yCoord w ≠ 3)) :
    ResetPortPreFinalP1YShiftPathRealizationGoal baseRow :=
  resetPortPreFinalYShiftPathOnGoal_of_lastStepPathOnGoal
    baseRow 4
    (fun w =>
      ¬ finalLiftCarrySite 4 w ∧
      yCoord w ≠ 1 ∧ yCoord w ≠ 2 ∧ yCoord w ≠ 3) hLast

theorem resetPortFinalCarryP0YShiftPathRealizationGoal_of_lastStepPathOnGoal
    (baseRow : ResetPortBaseRow)
    (hLast :
      ResetPortFinalYShiftLastStepPathOnGoal baseRow 3
        (fun w => finalLiftCarrySite 3 w ∧ yCoord w ≠ 0)) :
    ResetPortFinalCarryP0YShiftPathRealizationGoal baseRow :=
  resetPortFinalYShiftPathOnGoal_of_lastStepPathOnGoal
    baseRow 3
    (fun w => finalLiftCarrySite 3 w ∧ yCoord w ≠ 0) hLast

theorem resetPortFinalCarryP1YShiftPathRealizationGoal_of_lastStepPathOnGoal
    (baseRow : ResetPortBaseRow)
    (hLast :
      ResetPortFinalYShiftLastStepPathOnGoal baseRow 4
        (fun w =>
          finalLiftCarrySite 4 w ∧
          yCoord w ≠ 1 ∧ yCoord w ≠ 2 ∧ yCoord w ≠ 3)) :
    ResetPortFinalCarryP1YShiftPathRealizationGoal baseRow :=
  resetPortFinalYShiftPathOnGoal_of_lastStepPathOnGoal
    baseRow 4
    (fun w =>
      finalLiftCarrySite 4 w ∧
      yCoord w ≠ 1 ∧ yCoord w ≠ 2 ∧ yCoord w ≠ 3) hLast

theorem resetPortFinalCarryP0YShiftPathRealizationGoal_of_zFirstLastStepPathOnGoal
    (baseRow : ResetPortBaseRow)
    (hLast :
      ResetPortFinalZFirstYShiftLastStepPathOnGoal baseRow 3
        (fun w => finalLiftCarrySite 3 w ∧ yCoord w ≠ 0)) :
    ResetPortFinalCarryP0YShiftPathRealizationGoal baseRow :=
  resetPortFinalYShiftPathOnGoal_of_zFirstLastStepPathOnGoal
    baseRow 3
    (fun w => finalLiftCarrySite 3 w ∧ yCoord w ≠ 0)
    (fun _w h => h.1) hLast

theorem resetPortFinalCarryP1YShiftPathRealizationGoal_of_zFirstLastStepPathOnGoal
    (baseRow : ResetPortBaseRow)
    (hLast :
      ResetPortFinalZFirstYShiftLastStepPathOnGoal baseRow 4
        (fun w =>
          finalLiftCarrySite 4 w ∧
          yCoord w ≠ 1 ∧ yCoord w ≠ 2 ∧ yCoord w ≠ 3)) :
    ResetPortFinalCarryP1YShiftPathRealizationGoal baseRow :=
  resetPortFinalYShiftPathOnGoal_of_zFirstLastStepPathOnGoal
    baseRow 4
    (fun w =>
      finalLiftCarrySite 4 w ∧
      yCoord w ≠ 1 ∧ yCoord w ≠ 2 ∧ yCoord w ≠ 3)
    (fun _w h => h.1) hLast

theorem resetPortPreFinalP0F0PathRealizationGoal_of_tailPathOnGoal
    (baseRow : ResetPortBaseRow)
    (hTail :
      ResetPortPreFinalYTerminalTailPathOnGoal baseRow 3
        (fun w => ¬ finalLiftCarrySite 3 w ∧ yCoord w = 0)
        TerminalSymbol.F0) :
    ResetPortPreFinalP0F0PathRealizationGoal baseRow :=
  resetPortPreFinalYTerminalPathOnGoal_of_tailPathOnGoal
    baseRow 3
    (fun w => ¬ finalLiftCarrySite 3 w ∧ yCoord w = 0)
    TerminalSymbol.F0 hTail

theorem resetPortPreFinalP1Y1F0PathRealizationGoal_of_tailPathOnGoal
    (baseRow : ResetPortBaseRow)
    (hTail :
      ResetPortPreFinalYTerminalTailPathOnGoal baseRow 4
        (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 1)
        TerminalSymbol.F0) :
    ResetPortPreFinalP1Y1F0PathRealizationGoal baseRow :=
  resetPortPreFinalYTerminalPathOnGoal_of_tailPathOnGoal
    baseRow 4
    (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 1)
    TerminalSymbol.F0 hTail

theorem resetPortPreFinalP1Y2F2PathRealizationGoal_of_tailPathOnGoal
    (baseRow : ResetPortBaseRow)
    (hTail :
      ResetPortPreFinalYTerminalTailPathOnGoal baseRow 4
        (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 2)
        TerminalSymbol.F2) :
    ResetPortPreFinalP1Y2F2PathRealizationGoal baseRow :=
  resetPortPreFinalYTerminalPathOnGoal_of_tailPathOnGoal
    baseRow 4
    (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 2)
    TerminalSymbol.F2 hTail

theorem resetPortPreFinalP1Y3F1PathRealizationGoal_of_tailPathOnGoal
    (baseRow : ResetPortBaseRow)
    (hTail :
      ResetPortPreFinalYTerminalTailPathOnGoal baseRow 4
        (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 3)
        TerminalSymbol.F1) :
    ResetPortPreFinalP1Y3F1PathRealizationGoal baseRow :=
  resetPortPreFinalYTerminalPathOnGoal_of_tailPathOnGoal
    baseRow 4
    (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 3)
    TerminalSymbol.F1 hTail

theorem resetPortFinalCarryP0F0PathRealizationGoal_of_tailPathOnGoal
    (baseRow : ResetPortBaseRow)
    (hTail :
      ResetPortFinalYTerminalTailPathOnGoal baseRow 3
        (fun w => finalLiftCarrySite 3 w ∧ yCoord w = 0)
        TerminalSymbol.F0) :
    ResetPortFinalCarryP0F0PathRealizationGoal baseRow :=
  resetPortFinalYTerminalPathOnGoal_of_tailPathOnGoal
    baseRow 3
    (fun w => finalLiftCarrySite 3 w ∧ yCoord w = 0)
    TerminalSymbol.F0 hTail

theorem resetPortFinalCarryP1Y1F0PathRealizationGoal_of_tailPathOnGoal
    (baseRow : ResetPortBaseRow)
    (hTail :
      ResetPortFinalYTerminalTailPathOnGoal baseRow 4
        (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 1)
        TerminalSymbol.F0) :
    ResetPortFinalCarryP1Y1F0PathRealizationGoal baseRow :=
  resetPortFinalYTerminalPathOnGoal_of_tailPathOnGoal
    baseRow 4
    (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 1)
    TerminalSymbol.F0 hTail

theorem resetPortFinalCarryP1Y2F2PathRealizationGoal_of_tailPathOnGoal
    (baseRow : ResetPortBaseRow)
    (hTail :
      ResetPortFinalYTerminalTailPathOnGoal baseRow 4
        (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 2)
        TerminalSymbol.F2) :
    ResetPortFinalCarryP1Y2F2PathRealizationGoal baseRow :=
  resetPortFinalYTerminalPathOnGoal_of_tailPathOnGoal
    baseRow 4
    (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 2)
    TerminalSymbol.F2 hTail

theorem resetPortFinalCarryP1Y3F1PathRealizationGoal_of_tailPathOnGoal
    (baseRow : ResetPortBaseRow)
    (hTail :
      ResetPortFinalYTerminalTailPathOnGoal baseRow 4
        (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 3)
        TerminalSymbol.F1) :
    ResetPortFinalCarryP1Y3F1PathRealizationGoal baseRow :=
  resetPortFinalYTerminalPathOnGoal_of_tailPathOnGoal
    baseRow 4
    (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 3)
    TerminalSymbol.F1 hTail

theorem resetPortFinalCarryP0F0PathRealizationGoal_of_zFirstTailPathOnGoal
    (baseRow : ResetPortBaseRow)
    (hTail :
      ResetPortFinalZFirstYTerminalTailPathOnGoal baseRow 3
        (fun w => finalLiftCarrySite 3 w ∧ yCoord w = 0)
        TerminalSymbol.F0) :
    ResetPortFinalCarryP0F0PathRealizationGoal baseRow :=
  resetPortFinalYTerminalPathOnGoal_of_zFirstTailPathOnGoal
    baseRow 3
    (fun w => finalLiftCarrySite 3 w ∧ yCoord w = 0)
    TerminalSymbol.F0 (fun _w h => h.1) hTail

theorem resetPortFinalCarryP1Y1F0PathRealizationGoal_of_zFirstTailPathOnGoal
    (baseRow : ResetPortBaseRow)
    (hTail :
      ResetPortFinalZFirstYTerminalTailPathOnGoal baseRow 4
        (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 1)
        TerminalSymbol.F0) :
    ResetPortFinalCarryP1Y1F0PathRealizationGoal baseRow :=
  resetPortFinalYTerminalPathOnGoal_of_zFirstTailPathOnGoal
    baseRow 4
    (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 1)
    TerminalSymbol.F0 (fun _w h => h.1) hTail

theorem resetPortFinalCarryP1Y2F2PathRealizationGoal_of_zFirstTailPathOnGoal
    (baseRow : ResetPortBaseRow)
    (hTail :
      ResetPortFinalZFirstYTerminalTailPathOnGoal baseRow 4
        (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 2)
        TerminalSymbol.F2) :
    ResetPortFinalCarryP1Y2F2PathRealizationGoal baseRow :=
  resetPortFinalYTerminalPathOnGoal_of_zFirstTailPathOnGoal
    baseRow 4
    (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 2)
    TerminalSymbol.F2 (fun _w h => h.1) hTail

theorem resetPortFinalCarryP1Y3F1PathRealizationGoal_of_zFirstTailPathOnGoal
    (baseRow : ResetPortBaseRow)
    (hTail :
      ResetPortFinalZFirstYTerminalTailPathOnGoal baseRow 4
        (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 3)
        TerminalSymbol.F1) :
    ResetPortFinalCarryP1Y3F1PathRealizationGoal baseRow :=
  resetPortFinalYTerminalPathOnGoal_of_zFirstTailPathOnGoal
    baseRow 4
    (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 3)
    TerminalSymbol.F1 (fun _w h => h.1) hTail

theorem
    resetPortPreFinalP0YShiftPathRealizationGoal_of_lastStepSplitPathOnGoal
    (baseRow : ResetPortBaseRow)
    (hLast :
      ResetPortYShiftLastStepSplitPathOnGoal baseRow 3
        (fun w => ¬ finalLiftCarrySite 3 w ∧ yCoord w ≠ 0)
        zCoord) :
    ResetPortPreFinalP0YShiftPathRealizationGoal baseRow :=
  resetPortPreFinalYShiftPathOnGoal_of_lastStepSplitPathOnGoal
    baseRow 3
    (fun w => ¬ finalLiftCarrySite 3 w ∧ yCoord w ≠ 0) hLast

theorem
    resetPortPreFinalP1YShiftPathRealizationGoal_of_lastStepSplitPathOnGoal
    (baseRow : ResetPortBaseRow)
    (hLast :
      ResetPortYShiftLastStepSplitPathOnGoal baseRow 4
        (fun w =>
          ¬ finalLiftCarrySite 4 w ∧
          yCoord w ≠ 1 ∧ yCoord w ≠ 2 ∧ yCoord w ≠ 3)
        zCoord) :
    ResetPortPreFinalP1YShiftPathRealizationGoal baseRow :=
  resetPortPreFinalYShiftPathOnGoal_of_lastStepSplitPathOnGoal
    baseRow 4
    (fun w =>
      ¬ finalLiftCarrySite 4 w ∧
      yCoord w ≠ 1 ∧ yCoord w ≠ 2 ∧ yCoord w ≠ 3) hLast

theorem resetPortPreFinalP0F0PathRealizationGoal_of_tailSplitPathOnGoal
    (baseRow : ResetPortBaseRow)
    (hTail :
      ResetPortYTerminalTailSplitPathOnGoal baseRow 3
        (fun w => ¬ finalLiftCarrySite 3 w ∧ yCoord w = 0)
        TerminalSymbol.F0 zCoord) :
    ResetPortPreFinalP0F0PathRealizationGoal baseRow :=
  resetPortPreFinalYTerminalPathOnGoal_of_tailSplitPathOnGoal
    baseRow 3
    (fun w => ¬ finalLiftCarrySite 3 w ∧ yCoord w = 0)
    TerminalSymbol.F0 hTail

theorem resetPortPreFinalP1Y1F0PathRealizationGoal_of_tailSplitPathOnGoal
    (baseRow : ResetPortBaseRow)
    (hTail :
      ResetPortYTerminalTailSplitPathOnGoal baseRow 4
        (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 1)
        TerminalSymbol.F0 zCoord) :
    ResetPortPreFinalP1Y1F0PathRealizationGoal baseRow :=
  resetPortPreFinalYTerminalPathOnGoal_of_tailSplitPathOnGoal
    baseRow 4
    (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 1)
    TerminalSymbol.F0 hTail

theorem resetPortPreFinalP1Y2F2PathRealizationGoal_of_tailSplitPathOnGoal
    (baseRow : ResetPortBaseRow)
    (hTail :
      ResetPortYTerminalTailSplitPathOnGoal baseRow 4
        (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 2)
        TerminalSymbol.F2 zCoord) :
    ResetPortPreFinalP1Y2F2PathRealizationGoal baseRow :=
  resetPortPreFinalYTerminalPathOnGoal_of_tailSplitPathOnGoal
    baseRow 4
    (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 2)
    TerminalSymbol.F2 hTail

theorem resetPortPreFinalP1Y3F1PathRealizationGoal_of_tailSplitPathOnGoal
    (baseRow : ResetPortBaseRow)
    (hTail :
      ResetPortYTerminalTailSplitPathOnGoal baseRow 4
        (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 3)
        TerminalSymbol.F1 zCoord) :
    ResetPortPreFinalP1Y3F1PathRealizationGoal baseRow :=
  resetPortPreFinalYTerminalPathOnGoal_of_tailSplitPathOnGoal
    baseRow 4
    (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 3)
    TerminalSymbol.F1 hTail

theorem
    resetPortFinalCarryP0YShiftPathRealizationGoal_of_zFirstLastStepSplitPathOnGoal
    (baseRow : ResetPortBaseRow)
    (hLast :
      ResetPortFinalZFirstYShiftLastStepSplitPathOnGoal baseRow 3
        (fun w => finalLiftCarrySite 3 w ∧ yCoord w ≠ 0)) :
    ResetPortFinalCarryP0YShiftPathRealizationGoal baseRow :=
  resetPortFinalYShiftPathOnGoal_of_zFirstLastStepSplitPathOnGoal
    baseRow 3
    (fun w => finalLiftCarrySite 3 w ∧ yCoord w ≠ 0)
    (fun _w h => h.1) hLast

theorem
    resetPortFinalCarryP1YShiftPathRealizationGoal_of_zFirstLastStepSplitPathOnGoal
    (baseRow : ResetPortBaseRow)
    (hLast :
      ResetPortFinalZFirstYShiftLastStepSplitPathOnGoal baseRow 4
        (fun w =>
          finalLiftCarrySite 4 w ∧
          yCoord w ≠ 1 ∧ yCoord w ≠ 2 ∧ yCoord w ≠ 3)) :
    ResetPortFinalCarryP1YShiftPathRealizationGoal baseRow :=
  resetPortFinalYShiftPathOnGoal_of_zFirstLastStepSplitPathOnGoal
    baseRow 4
    (fun w =>
      finalLiftCarrySite 4 w ∧
      yCoord w ≠ 1 ∧ yCoord w ≠ 2 ∧ yCoord w ≠ 3)
    (fun _w h => h.1) hLast

theorem
    resetPortFinalCarryP0F0PathRealizationGoal_of_zFirstTailSplitPathOnGoal
    (baseRow : ResetPortBaseRow)
    (hTail :
      ResetPortFinalZFirstYTerminalTailSplitPathOnGoal baseRow 3
        (fun w => finalLiftCarrySite 3 w ∧ yCoord w = 0)
        TerminalSymbol.F0) :
    ResetPortFinalCarryP0F0PathRealizationGoal baseRow :=
  resetPortFinalYTerminalPathOnGoal_of_zFirstTailSplitPathOnGoal
    baseRow 3
    (fun w => finalLiftCarrySite 3 w ∧ yCoord w = 0)
    TerminalSymbol.F0 (fun _w h => h.1) hTail

theorem
    resetPortFinalCarryP1Y1F0PathRealizationGoal_of_zFirstTailSplitPathOnGoal
    (baseRow : ResetPortBaseRow)
    (hTail :
      ResetPortFinalZFirstYTerminalTailSplitPathOnGoal baseRow 4
        (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 1)
        TerminalSymbol.F0) :
    ResetPortFinalCarryP1Y1F0PathRealizationGoal baseRow :=
  resetPortFinalYTerminalPathOnGoal_of_zFirstTailSplitPathOnGoal
    baseRow 4
    (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 1)
    TerminalSymbol.F0 (fun _w h => h.1) hTail

theorem
    resetPortFinalCarryP1Y2F2PathRealizationGoal_of_zFirstTailSplitPathOnGoal
    (baseRow : ResetPortBaseRow)
    (hTail :
      ResetPortFinalZFirstYTerminalTailSplitPathOnGoal baseRow 4
        (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 2)
        TerminalSymbol.F2) :
    ResetPortFinalCarryP1Y2F2PathRealizationGoal baseRow :=
  resetPortFinalYTerminalPathOnGoal_of_zFirstTailSplitPathOnGoal
    baseRow 4
    (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 2)
    TerminalSymbol.F2 (fun _w h => h.1) hTail

theorem
    resetPortFinalCarryP1Y3F1PathRealizationGoal_of_zFirstTailSplitPathOnGoal
    (baseRow : ResetPortBaseRow)
    (hTail :
      ResetPortFinalZFirstYTerminalTailSplitPathOnGoal baseRow 4
        (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 3)
        TerminalSymbol.F1) :
    ResetPortFinalCarryP1Y3F1PathRealizationGoal baseRow :=
  resetPortFinalYTerminalPathOnGoal_of_zFirstTailSplitPathOnGoal
    baseRow 4
    (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 3)
    TerminalSymbol.F1 (fun _w h => h.1) hTail

theorem resetPortFinalCarryP0YShiftRealizationGoal_of_pathGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hPath : ResetPortFinalCarryP0YShiftPathRealizationGoal baseRow) :
    ResetPortFinalCarryP0YShiftRealizationGoal baseRow :=
  fourLayerRealizationOnGoal_of_pathOnGoal
    (resetPortDirOfBase baseRow) 3
    (fun w => finalLiftCarrySite 3 w ∧ yCoord w ≠ 0)
    finalYShiftReturn hPath

theorem resetPortFinalCarryP0F0RealizationGoal_of_pathGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hPath : ResetPortFinalCarryP0F0PathRealizationGoal baseRow) :
    ResetPortFinalCarryP0F0RealizationGoal baseRow :=
  fourLayerRealizationOnGoal_of_pathOnGoal
    (resetPortDirOfBase baseRow) 3
    (fun w => finalLiftCarrySite 3 w ∧ yCoord w = 0)
    (finalYTerminalReturn TerminalSymbol.F0) hPath

theorem resetPortFinalCarryP1YShiftRealizationGoal_of_pathGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hPath : ResetPortFinalCarryP1YShiftPathRealizationGoal baseRow) :
    ResetPortFinalCarryP1YShiftRealizationGoal baseRow :=
  fourLayerRealizationOnGoal_of_pathOnGoal
    (resetPortDirOfBase baseRow) 4
    (fun w =>
      finalLiftCarrySite 4 w ∧
      yCoord w ≠ 1 ∧ yCoord w ≠ 2 ∧ yCoord w ≠ 3)
    finalYShiftReturn hPath

theorem resetPortFinalCarryP1Y1F0RealizationGoal_of_pathGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hPath : ResetPortFinalCarryP1Y1F0PathRealizationGoal baseRow) :
    ResetPortFinalCarryP1Y1F0RealizationGoal baseRow :=
  fourLayerRealizationOnGoal_of_pathOnGoal
    (resetPortDirOfBase baseRow) 4
    (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 1)
    (finalYTerminalReturn TerminalSymbol.F0) hPath

theorem resetPortFinalCarryP1Y2F2RealizationGoal_of_pathGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hPath : ResetPortFinalCarryP1Y2F2PathRealizationGoal baseRow) :
    ResetPortFinalCarryP1Y2F2RealizationGoal baseRow :=
  fourLayerRealizationOnGoal_of_pathOnGoal
    (resetPortDirOfBase baseRow) 4
    (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 2)
    (finalYTerminalReturn TerminalSymbol.F2) hPath

theorem resetPortFinalCarryP1Y3F1RealizationGoal_of_pathGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hPath : ResetPortFinalCarryP1Y3F1PathRealizationGoal baseRow) :
    ResetPortFinalCarryP1Y3F1RealizationGoal baseRow :=
  fourLayerRealizationOnGoal_of_pathOnGoal
    (resetPortDirOfBase baseRow) 4
    (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 3)
    (finalYTerminalReturn TerminalSymbol.F1) hPath

theorem resetPortFinalCarryP0RealizationGoal_of_ySplit
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hYShift : ResetPortFinalCarryP0YShiftRealizationGoal baseRow)
    (hF0 : ResetPortFinalCarryP0F0RealizationGoal baseRow) :
    ResetPortFinalCarryP0RealizationGoal baseRow := by
  intro w hFinal
  by_cases hY : yCoord w = 0
  · calc
      fourLayerReturn (resetPortDirOfBase baseRow) 3 w =
          finalYTerminalReturn TerminalSymbol.F0 w :=
            hF0 w ⟨hFinal, hY⟩
      _ = finalCarryReturn 3 w :=
          (finalCarryReturn_three_eq_finalYTerminalF0Return_of_y_zero
            w hY).symm
  · calc
      fourLayerReturn (resetPortDirOfBase baseRow) 3 w =
          finalYShiftReturn w :=
            hYShift w ⟨hFinal, hY⟩
      _ = finalCarryReturn 3 w :=
          (finalCarryReturn_three_eq_finalYShiftReturn_of_y_ne_zero
            w hY).symm

theorem resetPortFinalCarryP0RealizationGoal_of_ySplitPathGoals
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hYShiftPath : ResetPortFinalCarryP0YShiftPathRealizationGoal baseRow)
    (hF0Path : ResetPortFinalCarryP0F0PathRealizationGoal baseRow) :
    ResetPortFinalCarryP0RealizationGoal baseRow :=
  resetPortFinalCarryP0RealizationGoal_of_ySplit baseRow
    (resetPortFinalCarryP0YShiftRealizationGoal_of_pathGoal
      baseRow hYShiftPath)
    (resetPortFinalCarryP0F0RealizationGoal_of_pathGoal baseRow hF0Path)

theorem resetPortFinalCarryP1RealizationGoal_of_ySplit
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hYShift : ResetPortFinalCarryP1YShiftRealizationGoal baseRow)
    (hF0 : ResetPortFinalCarryP1Y1F0RealizationGoal baseRow)
    (hF2 : ResetPortFinalCarryP1Y2F2RealizationGoal baseRow)
    (hF1 : ResetPortFinalCarryP1Y3F1RealizationGoal baseRow) :
    ResetPortFinalCarryP1RealizationGoal baseRow := by
  intro w hFinal
  by_cases hY1 : yCoord w = 1
  · calc
      fourLayerReturn (resetPortDirOfBase baseRow) 4 w =
          finalYTerminalReturn TerminalSymbol.F0 w :=
            hF0 w ⟨hFinal, hY1⟩
      _ = finalCarryReturn 4 w :=
          (finalCarryReturn_four_eq_finalYTerminalF0Return_of_y_one
            w hY1).symm
  · by_cases hY2 : yCoord w = 2
    · calc
        fourLayerReturn (resetPortDirOfBase baseRow) 4 w =
            finalYTerminalReturn TerminalSymbol.F2 w :=
              hF2 w ⟨hFinal, hY2⟩
        _ = finalCarryReturn 4 w :=
            (finalCarryReturn_four_eq_finalYTerminalF2Return_of_y_two
              w hY2).symm
    · by_cases hY3 : yCoord w = 3
      · calc
          fourLayerReturn (resetPortDirOfBase baseRow) 4 w =
              finalYTerminalReturn TerminalSymbol.F1 w :=
                hF1 w ⟨hFinal, hY3⟩
          _ = finalCarryReturn 4 w :=
              (finalCarryReturn_four_eq_finalYTerminalF1Return_of_y_three
                w hY3).symm
      · calc
          fourLayerReturn (resetPortDirOfBase baseRow) 4 w =
              finalYShiftReturn w :=
                hYShift w ⟨hFinal, hY1, hY2, hY3⟩
          _ = finalCarryReturn 4 w :=
              (finalCarryReturn_four_eq_finalYShiftReturn_of_y_ne_one_two_three
                w hY1 hY2 hY3).symm

theorem resetPortFinalCarryP1RealizationGoal_of_ySplitPathGoals
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hYShiftPath : ResetPortFinalCarryP1YShiftPathRealizationGoal baseRow)
    (hY1F0Path : ResetPortFinalCarryP1Y1F0PathRealizationGoal baseRow)
    (hY2F2Path : ResetPortFinalCarryP1Y2F2PathRealizationGoal baseRow)
    (hY3F1Path : ResetPortFinalCarryP1Y3F1PathRealizationGoal baseRow) :
    ResetPortFinalCarryP1RealizationGoal baseRow :=
  resetPortFinalCarryP1RealizationGoal_of_ySplit baseRow
    (resetPortFinalCarryP1YShiftRealizationGoal_of_pathGoal
      baseRow hYShiftPath)
    (resetPortFinalCarryP1Y1F0RealizationGoal_of_pathGoal baseRow hY1F0Path)
    (resetPortFinalCarryP1Y2F2RealizationGoal_of_pathGoal baseRow hY2F2Path)
    (resetPortFinalCarryP1Y3F1RealizationGoal_of_pathGoal baseRow hY3F1Path)

theorem paperReturn_terminal_of_no_final_site
    (i : Fin 3) (w : RootState)
    (hFinal : NoFinalLiftSites w) :
    paperReturn (fin3ToFin5 i) w =
      rootOfCoords
        (LowD5M4.F (terminalSymbolOfIndex i) (qCoord w))
        (if firstLiftCarrySite (fin3ToFin5 i) w then
          yCoord w + 1
        else
          yCoord w)
        (zCoord w) := by
  simp [paperReturn_apply_terminal_sites, hFinal (fin3ToFin5 i)]

theorem paperReturn_terminal_of_first_site_of_no_final_site
    (i : Fin 3) (w : RootState)
    (hFirst : firstLiftCarrySite (fin3ToFin5 i) w)
    (hFinal : NoFinalLiftSites w) :
    paperReturn (fin3ToFin5 i) w =
      rootOfCoords
        (LowD5M4.F (terminalSymbolOfIndex i) (qCoord w))
        (yCoord w + 1)
        (zCoord w) := by
  simp [paperReturn_apply_terminal_sites, hFirst, hFinal (fin3ToFin5 i)]

theorem paperReturn_terminal_of_final_site
    (i : Fin 3) (w : RootState)
    (hFinal : finalLiftCarrySite (fin3ToFin5 i) w) :
    paperReturn (fin3ToFin5 i) w =
      rootOfCoords
        (LowD5M4.F (terminalSymbolOfIndex i) (qCoord w))
        (if firstLiftCarrySite (fin3ToFin5 i) w then
          yCoord w + 1
        else
          yCoord w)
        (zCoord w + 1) := by
  simp [paperReturn_apply_terminal_sites, hFinal]

/-- The paper terminal-A2 path obligation on the region where no reset-port
substitution is active at the source. -/
def ResetPortTerminalCorePathOnGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  ∀ i : Fin 3,
    BaseRowNoResetFourLayerPathOnGoal
      baseRow (fin3ToFin5 i) NoResetPortSites (terminalCoreReturn i)

/-- A terminal-core path goal in the paper's collapsed-run form. The first
three layers only have to reach the terminal return tail
`q + Delta_i - a_i`; the last layer is then forced to use the terminal `A2`
row word at that tail. -/
def TerminalCoreTailPrefixPathGoal
    (baseRow : ResetPortBaseRow) : Prop :=
  ∀ i : Fin 3,
    ∃ x1 x2 : RootState → RootState,
      ∀ w : RootState, NoResetPortSites w →
        LowD5M4Schedule.rootStep
            (baseRow (0 : ZMod 4) w (fin3ToFin5 i)) w = x1 w ∧
        LowD5M4Schedule.rootStep
            (baseRow (1 : ZMod 4) (x1 w) (fin3ToFin5 i)) (x1 w) =
          x2 w ∧
        LowD5M4Schedule.rootStep
            (baseRow (2 : ZMod 4) (x2 w) (fin3ToFin5 i)) (x2 w) =
          rootOfCoords
            (terminalReturnTailBase i (qCoord w)) (yCoord w) (zCoord w) ∧
        NoResetPortSites (x1 w) ∧
        NoResetPortSites (x2 w) ∧
        NoResetPortSites
          (rootOfCoords
            (terminalReturnTailBase i (qCoord w)) (yCoord w) (zCoord w))

/-- Last-layer terminal-core row-word reads, separated from the prefix path to
the collapsed terminal tail. -/
def TerminalCoreTailReadGoal
    (baseRow : ResetPortBaseRow) : Prop :=
  ∀ i : Fin 3,
    ∀ w : RootState, NoResetPortSites w →
      BaseRowReadsTerminalTailIndex
        baseRow (3 : ZMod 4) i (qCoord w) (yCoord w) (zCoord w)

/-- Split terminal-core tail goal: prefix to the collapsed terminal tail plus
the last-layer terminal row-word read. -/
structure TerminalCoreTailSplitPathGoal
    (baseRow : ResetPortBaseRow) :
    Prop where
  pathPrefix : TerminalCoreTailPrefixPathGoal baseRow
  read : TerminalCoreTailReadGoal baseRow

def TerminalCoreTailPathGoal
    (baseRow : ResetPortBaseRow) : Prop :=
  ∀ i : Fin 3,
    ∃ x1 x2 : RootState → RootState,
      ∀ w : RootState, NoResetPortSites w →
        LowD5M4Schedule.rootStep
            (baseRow (0 : ZMod 4) w (fin3ToFin5 i)) w = x1 w ∧
        LowD5M4Schedule.rootStep
            (baseRow (1 : ZMod 4) (x1 w) (fin3ToFin5 i)) (x1 w) =
          x2 w ∧
          LowD5M4Schedule.rootStep
              (baseRow (2 : ZMod 4) (x2 w) (fin3ToFin5 i)) (x2 w) =
            rootOfCoords
              (terminalReturnTailBase i (qCoord w)) (yCoord w) (zCoord w) ∧
          BaseRowReadsTerminalTailIndex
            baseRow (3 : ZMod 4) i (qCoord w) (yCoord w) (zCoord w) ∧
          NoResetPortSites (x1 w) ∧
          NoResetPortSites (x2 w) ∧
          NoResetPortSites
            (rootOfCoords
              (terminalReturnTailBase i (qCoord w)) (yCoord w) (zCoord w))

theorem TerminalCoreTailPathGoal_of_split
    {baseRow : ResetPortBaseRow}
    (hSplit : TerminalCoreTailSplitPathGoal baseRow) :
    TerminalCoreTailPathGoal baseRow := by
  intro i
  rcases hSplit.pathPrefix i with ⟨x1, x2, hsteps⟩
  refine ⟨x1, x2, ?_⟩
  intro w hNo
  rcases hsteps w hNo with ⟨h0, h1, h2, hNo1, hNo2, hNo3⟩
  exact ⟨h0, h1, h2, hSplit.read i w hNo, hNo1, hNo2, hNo3⟩

theorem resetPortTerminalCorePathOnGoal_of_tailPathGoal
    (baseRow : ResetPortBaseRow)
    (hTail : TerminalCoreTailPathGoal baseRow) :
    ResetPortTerminalCorePathOnGoal baseRow := by
  intro i
  rcases hTail i with ⟨x1, x2, hsteps⟩
  refine ⟨x1, x2,
    (fun w =>
      rootOfCoords
        (terminalReturnTailBase i (qCoord w)) (yCoord w) (zCoord w)),
      ?_⟩
  intro w hNo
  rcases hsteps w hNo with
    ⟨h0, h1, h2, hrow, hNo1, hNo2, hNo3⟩
  refine ⟨h0, h1, h2, ?_, hNo, hNo1, hNo2, hNo3⟩
  dsimp [BaseRowReadsTerminalTailIndex] at hrow
  rw [hrow]
  simpa [terminalCoreReturn] using
    rootStep_terminalReturnTailBase_eq_F_terminalSymbolOfIndex
      i (qCoord w) (yCoord w) (zCoord w)

/-- Restricted terminal-core realization obtained from the conditional
base-row path interface. -/
def ResetPortTerminalCoreRealizationOnGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  ∀ i : Fin 3,
    FourLayerRealizationOnGoal
      (resetPortDirOfBase baseRow) (fin3ToFin5 i)
      NoResetPortSites (terminalCoreReturn i)

theorem resetPortTerminalCoreRealizationOnGoal_of_pathOnGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hTerminalCore : ResetPortTerminalCorePathOnGoal baseRow) :
    ResetPortTerminalCoreRealizationOnGoal baseRow := by
  intro i
  exact resetPortRealizationOnGoal_of_baseRowNoResetPathOnGoal
    baseRow (fin3ToFin5 i) NoResetPortSites
    (terminalCoreReturn i) (hTerminalCore i)

/-- The terminal-color return obligation restricted to sources with no active
reset-port substitution. -/
def ResetPortTerminalNoResetRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  ∀ i : Fin 3,
    FourLayerRealizationOnGoal
      (resetPortDirOfBase baseRow) (fin3ToFin5 i)
      NoResetPortSites (paperReturn (fin3ToFin5 i))

theorem resetPortTerminalNoResetRealizationGoal_of_coreRealizationOnGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hCore : ResetPortTerminalCoreRealizationOnGoal baseRow) :
    ResetPortTerminalNoResetRealizationGoal baseRow := by
  intro i w hNo
  calc
    fourLayerReturn (resetPortDirOfBase baseRow) (fin3ToFin5 i) w =
        terminalCoreReturn i w := hCore i w hNo
    _ = paperReturn (fin3ToFin5 i) w :=
        (paperReturn_terminal_eq_terminalCoreReturn_of_no_resetPortSites
          i w hNo).symm

theorem resetPortTerminalNoResetRealizationGoal_of_pathOnGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hTerminalCore : ResetPortTerminalCorePathOnGoal baseRow) :
    ResetPortTerminalNoResetRealizationGoal baseRow :=
  resetPortTerminalNoResetRealizationGoal_of_coreRealizationOnGoal
    baseRow
    (resetPortTerminalCoreRealizationOnGoal_of_pathOnGoal
      baseRow hTerminalCore)

theorem resetPortTerminalNoResetRealizationGoal_of_tailPathGoal
    (baseRow : ResetPortBaseRow)
    (hTail : TerminalCoreTailPathGoal baseRow) :
    ResetPortTerminalNoResetRealizationGoal baseRow :=
  resetPortTerminalNoResetRealizationGoal_of_pathOnGoal baseRow
    (resetPortTerminalCorePathOnGoal_of_tailPathGoal baseRow hTail)

/-- Residual pre-final terminal obligation after the paper terminal-A2 core has
handled the sources with no active reset-port substitution.  These are exactly
the no-first/no-final sources that still lie on another reset-port site. -/
def ResetPortPreFinalTerminalNoFirstResidualPathRealizationGoal
    (baseRow : ResetPortBaseRow) :
    Prop :=
  ∀ i : Fin 3,
    FourLayerPathOnGoal
      (resetPortDirOfBase baseRow) (fin3ToFin5 i)
      (fun w =>
        ¬ finalLiftCarrySite (fin3ToFin5 i) w ∧
        ¬ firstLiftCarrySite (fin3ToFin5 i) w ∧
        ¬ NoResetPortSites w)
      (terminalCoreReturn i)

def ResetPortPreFinalTerminalNoFirstResidualRealizationGoal
    (baseRow : ResetPortBaseRow) :
    Prop :=
  ∀ i : Fin 3,
    FourLayerRealizationOnGoal
      (resetPortDirOfBase baseRow) (fin3ToFin5 i)
      (fun w =>
        ¬ finalLiftCarrySite (fin3ToFin5 i) w ∧
        ¬ firstLiftCarrySite (fin3ToFin5 i) w ∧
        ¬ NoResetPortSites w)
      (terminalCoreReturn i)

theorem resetPortPreFinalTerminalNoFirstResidualRealizationGoal_of_pathGoal
    (baseRow : ResetPortBaseRow)
    (hPath :
      ResetPortPreFinalTerminalNoFirstResidualPathRealizationGoal baseRow) :
    ResetPortPreFinalTerminalNoFirstResidualRealizationGoal baseRow := by
  intro i
  exact fourLayerRealizationOnGoal_of_pathOnGoal
    (resetPortDirOfBase baseRow) (fin3ToFin5 i)
    (fun w =>
      ¬ finalLiftCarrySite (fin3ToFin5 i) w ∧
      ¬ firstLiftCarrySite (fin3ToFin5 i) w ∧
      ¬ NoResetPortSites w)
    (terminalCoreReturn i) (hPath i)

theorem resetPortPreFinalTerminalNoFirstRealizationGoal_of_coreTail_and_residual
    (baseRow : ResetPortBaseRow)
    (hCoreTail : TerminalCoreTailPathGoal baseRow)
    (hResidual :
      ResetPortPreFinalTerminalNoFirstResidualRealizationGoal baseRow) :
    ResetPortPreFinalTerminalNoFirstRealizationGoal baseRow := by
  have hCore : ResetPortTerminalCoreRealizationOnGoal baseRow :=
    resetPortTerminalCoreRealizationOnGoal_of_pathOnGoal baseRow
      (resetPortTerminalCorePathOnGoal_of_tailPathGoal baseRow hCoreTail)
  intro i w hw
  by_cases hNo : NoResetPortSites w
  · exact hCore i w hNo
  · exact hResidual i w ⟨hw.1, hw.2, hNo⟩

theorem resetPortPreFinalTerminalNoFirstRealizationGoal_of_coreTail_and_residualPath
    (baseRow : ResetPortBaseRow)
    (hCoreTail : TerminalCoreTailPathGoal baseRow)
    (hResidualPath :
      ResetPortPreFinalTerminalNoFirstResidualPathRealizationGoal baseRow) :
    ResetPortPreFinalTerminalNoFirstRealizationGoal baseRow :=
  resetPortPreFinalTerminalNoFirstRealizationGoal_of_coreTail_and_residual
    baseRow hCoreTail
    (resetPortPreFinalTerminalNoFirstResidualRealizationGoal_of_pathGoal
      baseRow hResidualPath)

/-- The terminal A2 part of the paper construction, separated from reset-port
sites. This is the Lean shape of the terminal-row first-return lemma needed
before adding the two unit-carry layers. -/
def ResetPortTerminalCorePathGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  ∀ i : Fin 3,
    BaseRowNoResetFourLayerPathGoal
      baseRow (fin3ToFin5 i) (terminalCoreReturn i)

theorem resetPortTerminalCorePathGoal_to_resetPortPath
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hTerminalCore : ResetPortTerminalCorePathGoal baseRow) :
    ∀ i : Fin 3,
      FourLayerPathGoal
        (resetPortDirOfBase baseRow) (fin3ToFin5 i)
        (terminalCoreReturn i) := by
  intro i
  exact resetPortPathGoal_of_baseRowNoResetPathGoal
    baseRow (fin3ToFin5 i) (terminalCoreReturn i) (hTerminalCore i)

/-- The three terminal-color return obligations from Table D54-reset-ports. -/
def ResetPortTerminalRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  ∀ i : Fin 3, ∀ w : RootState,
    fourLayerReturn (resetPortDirOfBase baseRow) (fin3ToFin5 i) w =
      paperReturn (fin3ToFin5 i) w

/-- The `P₀` color return obligation from Table D54-reset-ports. -/
def ResetPortP0RealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  ∀ w : RootState,
    fourLayerReturn (resetPortDirOfBase baseRow) 3 w =
      paperReturn 3 w

/-- The `P₁` color return obligation from Table D54-reset-ports. -/
def ResetPortP1RealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  ∀ w : RootState,
    fourLayerReturn (resetPortDirOfBase baseRow) 4 w =
      paperReturn 4 w

/-- Layer-by-layer terminal-color return obligations for the reset-port
direction table. -/
def ResetPortTerminalPathRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  ∀ i : Fin 3,
    FourLayerPathGoal
      (resetPortDirOfBase baseRow) (fin3ToFin5 i)
      (paperReturn (fin3ToFin5 i))

/-- Layer-by-layer `P₀` return obligation for the reset-port direction table. -/
def ResetPortP0PathRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  FourLayerPathGoal (resetPortDirOfBase baseRow) 3 (paperReturn 3)

/-- Layer-by-layer `P₁` return obligation for the reset-port direction table. -/
def ResetPortP1PathRealizationGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop :=
  FourLayerPathGoal (resetPortDirOfBase baseRow) 4 (paperReturn 4)

theorem resetPortTerminalRealizationGoal_of_pathGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hTerminalPath : ResetPortTerminalPathRealizationGoal baseRow) :
    ResetPortTerminalRealizationGoal baseRow := by
  intro i w
  rcases hTerminalPath i with ⟨x1, x2, x3, hsteps⟩
  rcases hsteps w with ⟨h0, h1, h2, h3⟩
  exact fourLayerReturn_eq_of_layerMap_steps
    (resetPortDirOfBase baseRow) (fin3ToFin5 i) w
    (x1 w) (x2 w) (x3 w) (paperReturn (fin3ToFin5 i) w)
    h0 h1 h2 h3

theorem resetPortP0RealizationGoal_of_pathGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hP0Path : ResetPortP0PathRealizationGoal baseRow) :
    ResetPortP0RealizationGoal baseRow := by
  intro w
  rcases hP0Path with ⟨x1, x2, x3, hsteps⟩
  rcases hsteps w with ⟨h0, h1, h2, h3⟩
  exact fourLayerReturn_eq_of_layerMap_steps
    (resetPortDirOfBase baseRow) 3 w
    (x1 w) (x2 w) (x3 w) (paperReturn 3 w)
    h0 h1 h2 h3

theorem resetPortP1RealizationGoal_of_pathGoal
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hP1Path : ResetPortP1PathRealizationGoal baseRow) :
    ResetPortP1RealizationGoal baseRow := by
  intro w
  rcases hP1Path with ⟨x1, x2, x3, hsteps⟩
  rcases hsteps w with ⟨h0, h1, h2, h3⟩
  exact fourLayerReturn_eq_of_layerMap_steps
    (resetPortDirOfBase baseRow) 4 w
    (x1 w) (x2 w) (x3 w) (paperReturn 4 w)
    h0 h1 h2 h3

theorem resetPortFourLayerRealizationGoal_of_colorGoals
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hTerminal : ResetPortTerminalRealizationGoal baseRow)
    (hP0 : ResetPortP0RealizationGoal baseRow)
    (hP1 : ResetPortP1RealizationGoal baseRow) :
    ResetPortFourLayerRealizationGoal baseRow := by
  intro c w
  fin_cases c
  · simpa [ResetPortTerminalRealizationGoal, resetPortDirOfBase,
      fin3ToFin5] using hTerminal 0 w
  · simpa [ResetPortTerminalRealizationGoal, resetPortDirOfBase,
      fin3ToFin5] using hTerminal 1 w
  · simpa [ResetPortTerminalRealizationGoal, resetPortDirOfBase,
      fin3ToFin5] using hTerminal 2 w
  · simpa [ResetPortP0RealizationGoal, resetPortDirOfBase] using hP0 w
  · simpa [ResetPortP1RealizationGoal, resetPortDirOfBase] using hP1 w

theorem resetPortFourLayerRealizationGoal_of_pathGoals
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hTerminalPath : ResetPortTerminalPathRealizationGoal baseRow)
    (hP0Path : ResetPortP0PathRealizationGoal baseRow)
    (hP1Path : ResetPortP1PathRealizationGoal baseRow) :
    ResetPortFourLayerRealizationGoal baseRow :=
  resetPortFourLayerRealizationGoal_of_colorGoals baseRow
    (resetPortTerminalRealizationGoal_of_pathGoal baseRow hTerminalPath)
    (resetPortP0RealizationGoal_of_pathGoal baseRow hP0Path)
    (resetPortP1RealizationGoal_of_pathGoal baseRow hP1Path)

/-- Once RF1/RF2 and the paper return-map equality are supplied, the structural
D5(4) root-flat certificate follows without the finite blob. -/
theorem finalLowD5M4RootFlatCertificateFamily_of_returnMapRealization
    (dir : ZMod 4 → RootState → TorusColor 5 → TorusDirection 5)
    (hRow : (LowD5M4Schedule.schedule dir).rowLatin)
    (hLayer : (LowD5M4Schedule.schedule dir).layerBijective)
    (hReturn : ReturnMapRealizationGoal dir) :
    FinalLowD5M4RootFlatCertificateFamily := by
  refine LowD5M4Structural.finalLowD5M4RootFlatCertificateFamily_of_returnRealization
    dir seedRootEquiv hRow hLayer ?_
  intro c x
  rw [hReturn c (seedRootEquiv x)]
  simp [paperReturn]

theorem finalLowD5M4RootFlatCertificateFamily_of_fourLayerRealization
    (dir : ZMod 4 → RootState → TorusColor 5 → TorusDirection 5)
    (hRow : (LowD5M4Schedule.schedule dir).rowLatin)
    (hLayer : (LowD5M4Schedule.schedule dir).layerBijective)
    (hFour : FourLayerRealizationGoal dir) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_returnMapRealization
    dir hRow hLayer (returnMapRealizationGoal_of_fourLayer dir hFour)

theorem finalLowD5M4RootFlatCertificateFamily_of_rowEquivFourLayer
    (row : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hLayer :
      (LowD5M4Schedule.schedule (dirOfRowEquiv row)).layerBijective)
    (hFour : FourLayerRealizationGoal (dirOfRowEquiv row)) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_fourLayerRealization
    (dirOfRowEquiv row) (rowLatin_of_rowEquiv row) hLayer hFour

/-- Specialized H2 assembly interface for the paper reset-port construction.
Once a base row family is chosen, the Table D54-reset-ports substitutions supply
RF1 automatically; the remaining obligations are RF2 and the four-layer return
calculation. -/
theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortBaseFourLayer
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hLayer : ResetPortLayerBijectiveGoal baseRow)
    (hFour : ResetPortFourLayerRealizationGoal baseRow) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_rowEquivFourLayer
    (resetPortRowOfBase baseRow) hLayer hFour

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortBaseFinalSplit
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hLayer : ResetPortLayerBijectiveGoal baseRow)
    (hNoFinal : ResetPortNoFinalSiteRealizationGoal baseRow)
    (hFinal : ResetPortFinalSiteRealizationGoal baseRow) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortBaseFourLayer
    baseRow hLayer
    (resetPortFourLayerRealizationGoal_of_finalSiteSplit
      baseRow hNoFinal hFinal)

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePreFinalFinalCarry
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hLayer : ResetPortLayerBijectiveGoal baseRow)
    (hPreFinal : ResetPortPreFinalRealizationGoal baseRow)
    (hFinalCarry : ResetPortFinalCarryRealizationGoal baseRow) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortBaseFourLayer
    baseRow hLayer
    (resetPortFourLayerRealizationGoal_of_preFinalFinalCarryGoals
      baseRow hPreFinal hFinalCarry)

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePreFinalFinalCarryColorGoals
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hLayer : ResetPortLayerBijectiveGoal baseRow)
    (hPreTerminal : ResetPortPreFinalTerminalRealizationGoal baseRow)
    (hPreP0 : ResetPortPreFinalP0RealizationGoal baseRow)
    (hPreP1 : ResetPortPreFinalP1RealizationGoal baseRow)
    (hFinalTerminal : ResetPortFinalCarryTerminalRealizationGoal baseRow)
    (hFinalP0 : ResetPortFinalCarryP0RealizationGoal baseRow)
    (hFinalP1 : ResetPortFinalCarryP1RealizationGoal baseRow) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePreFinalFinalCarry
    baseRow hLayer
    (resetPortPreFinalRealizationGoal_of_colorGoals
      baseRow hPreTerminal hPreP0 hPreP1)
    (resetPortFinalCarryRealizationGoal_of_colorGoals
      baseRow hFinalTerminal hFinalP0 hFinalP1)

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePreFinalFinalCarryPathGoals
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hLayer : ResetPortLayerBijectiveGoal baseRow)
    (hPreTerminalPath : ResetPortPreFinalTerminalPathRealizationGoal baseRow)
    (hPreP0Path : ResetPortPreFinalP0PathRealizationGoal baseRow)
    (hPreP1Path : ResetPortPreFinalP1PathRealizationGoal baseRow)
    (hFinalTerminalPath : ResetPortFinalCarryTerminalPathRealizationGoal baseRow)
    (hFinalP0Path : ResetPortFinalCarryP0PathRealizationGoal baseRow)
    (hFinalP1Path : ResetPortFinalCarryP1PathRealizationGoal baseRow) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePreFinalFinalCarry
    baseRow hLayer
    (resetPortPreFinalRealizationGoal_of_pathGoals
      baseRow hPreTerminalPath hPreP0Path hPreP1Path)
    (resetPortFinalCarryRealizationGoal_of_pathGoals
      baseRow hFinalTerminalPath hFinalP0Path hFinalP1Path)

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePreFinalTerminalFirstSplitPathGoals
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hLayer : ResetPortLayerBijectiveGoal baseRow)
    (hPreTerminalNoFirstPath :
      ResetPortPreFinalTerminalNoFirstPathRealizationGoal baseRow)
    (hPreTerminalFirstCarryPath :
      ResetPortPreFinalTerminalFirstCarryPathRealizationGoal baseRow)
    (hPreP0Path : ResetPortPreFinalP0PathRealizationGoal baseRow)
    (hPreP1Path : ResetPortPreFinalP1PathRealizationGoal baseRow)
    (hFinalTerminalPath : ResetPortFinalCarryTerminalPathRealizationGoal baseRow)
    (hFinalP0Path : ResetPortFinalCarryP0PathRealizationGoal baseRow)
    (hFinalP1Path : ResetPortFinalCarryP1PathRealizationGoal baseRow) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePreFinalFinalCarry
    baseRow hLayer
    (resetPortPreFinalRealizationGoal_of_colorGoals
      baseRow
      (resetPortPreFinalTerminalRealizationGoal_of_firstCarryPathGoals
        baseRow hPreTerminalNoFirstPath hPreTerminalFirstCarryPath)
      (resetPortPreFinalP0RealizationGoal_of_pathGoal baseRow hPreP0Path)
      (resetPortPreFinalP1RealizationGoal_of_pathGoal baseRow hPreP1Path))
    (resetPortFinalCarryRealizationGoal_of_pathGoals
      baseRow hFinalTerminalPath hFinalP0Path hFinalP1Path)

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePreFinalRowWordSplitPathGoals
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hLayer : ResetPortLayerBijectiveGoal baseRow)
    (hPreTerminalNoFirstPath :
      ResetPortPreFinalTerminalNoFirstPathRealizationGoal baseRow)
    (hPreTerminalFirstCarryPath :
      ResetPortPreFinalTerminalFirstCarryPathRealizationGoal baseRow)
    (hPreP0YShiftPath : ResetPortPreFinalP0YShiftPathRealizationGoal baseRow)
    (hPreP0F0Path : ResetPortPreFinalP0F0PathRealizationGoal baseRow)
    (hPreP1YShiftPath : ResetPortPreFinalP1YShiftPathRealizationGoal baseRow)
    (hPreP1Y1F0Path : ResetPortPreFinalP1Y1F0PathRealizationGoal baseRow)
    (hPreP1Y2F2Path : ResetPortPreFinalP1Y2F2PathRealizationGoal baseRow)
    (hPreP1Y3F1Path : ResetPortPreFinalP1Y3F1PathRealizationGoal baseRow)
    (hFinalTerminalPath : ResetPortFinalCarryTerminalPathRealizationGoal baseRow)
    (hFinalP0Path : ResetPortFinalCarryP0PathRealizationGoal baseRow)
    (hFinalP1Path : ResetPortFinalCarryP1PathRealizationGoal baseRow) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePreFinalFinalCarry
    baseRow hLayer
    (resetPortPreFinalRealizationGoal_of_colorGoals
      baseRow
      (resetPortPreFinalTerminalRealizationGoal_of_firstCarryPathGoals
        baseRow hPreTerminalNoFirstPath hPreTerminalFirstCarryPath)
      (resetPortPreFinalP0RealizationGoal_of_ySplitPathGoals
        baseRow hPreP0YShiftPath hPreP0F0Path)
      (resetPortPreFinalP1RealizationGoal_of_ySplitPathGoals
        baseRow hPreP1YShiftPath hPreP1Y1F0Path hPreP1Y2F2Path
          hPreP1Y3F1Path))
    (resetPortFinalCarryRealizationGoal_of_pathGoals
      baseRow hFinalTerminalPath hFinalP0Path hFinalP1Path)

/-- Package the paper row-word path goals for the pre-final `R_i` stage. This
is the Lean counterpart of the product of the terminal `A2` layer word and the
`Y`-coordinate row word, before the final `Z` carry is attached. -/
structure ResetPortPreFinalRowWordSplitPathGoals
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop where
  terminalNoFirst :
    ResetPortPreFinalTerminalNoFirstPathRealizationGoal baseRow
  terminalFirst :
    ResetPortPreFinalTerminalFirstCarryPathRealizationGoal baseRow
  p0YShift : ResetPortPreFinalP0YShiftPathRealizationGoal baseRow
  p0F0 : ResetPortPreFinalP0F0PathRealizationGoal baseRow
  p1YShift : ResetPortPreFinalP1YShiftPathRealizationGoal baseRow
  p1Y1F0 : ResetPortPreFinalP1Y1F0PathRealizationGoal baseRow
  p1Y2F2 : ResetPortPreFinalP1Y2F2PathRealizationGoal baseRow
  p1Y3F1 : ResetPortPreFinalP1Y3F1PathRealizationGoal baseRow

theorem resetPortPreFinalRealizationGoal_of_rowWordSplitPathGoals
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (h : ResetPortPreFinalRowWordSplitPathGoals baseRow) :
    ResetPortPreFinalRealizationGoal baseRow :=
  resetPortPreFinalRealizationGoal_of_colorGoals
    baseRow
    (resetPortPreFinalTerminalRealizationGoal_of_firstCarryPathGoals
      baseRow h.terminalNoFirst h.terminalFirst)
    (resetPortPreFinalP0RealizationGoal_of_ySplitPathGoals
      baseRow h.p0YShift h.p0F0)
    (resetPortPreFinalP1RealizationGoal_of_ySplitPathGoals
      baseRow h.p1YShift h.p1Y1F0 h.p1Y2F2 h.p1Y3F1)

/-- Package the paper row-word path goals on active final `Z` carry sites. -/
structure ResetPortFinalCarryRowWordSplitPathGoals
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    Prop where
  terminalNoFirst :
    ResetPortFinalCarryTerminalNoFirstPathRealizationGoal baseRow
  terminalFirst :
    ResetPortFinalCarryTerminalFirstPathRealizationGoal baseRow
  p0YShift : ResetPortFinalCarryP0YShiftPathRealizationGoal baseRow
  p0F0 : ResetPortFinalCarryP0F0PathRealizationGoal baseRow
  p1YShift : ResetPortFinalCarryP1YShiftPathRealizationGoal baseRow
  p1Y1F0 : ResetPortFinalCarryP1Y1F0PathRealizationGoal baseRow
  p1Y2F2 : ResetPortFinalCarryP1Y2F2PathRealizationGoal baseRow
  p1Y3F1 : ResetPortFinalCarryP1Y3F1PathRealizationGoal baseRow

theorem resetPortFinalCarryRealizationGoal_of_rowWordSplitPathGoals
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (h : ResetPortFinalCarryRowWordSplitPathGoals baseRow) :
    ResetPortFinalCarryRealizationGoal baseRow :=
  resetPortFinalCarryRealizationGoal_of_colorGoals
    baseRow
    (resetPortFinalCarryTerminalRealizationGoal_of_firstCarryPathGoals
      baseRow h.terminalNoFirst h.terminalFirst)
    (resetPortFinalCarryP0RealizationGoal_of_ySplitPathGoals
      baseRow h.p0YShift h.p0F0)
    (resetPortFinalCarryP1RealizationGoal_of_ySplitPathGoals
      baseRow h.p1YShift h.p1Y1F0 h.p1Y2F2 h.p1Y3F1)

/-- The full paper row-word split obligation: pre-final `R_i` paths and active
final `Z`-carry paths, grouped as the switching-ribbon proof should supply
them. -/
structure ResetPortFullRowWordSplitPathGoals
    (baseRow : ResetPortBaseRow) :
    Prop where
  preFinal : ResetPortPreFinalRowWordSplitPathGoals baseRow
  finalCarry : ResetPortFinalCarryRowWordSplitPathGoals baseRow

/-- A paper-tail version of the pre-final row-word split. The terminal-factor
fields are supplied at the collapsed terminal tail
`q + Delta_s - a_s`, matching the terminal `A₂` row-word calculation. -/
structure ResetPortPreFinalTailRowWordSplitPathGoals
    (baseRow : ResetPortBaseRow) :
    Prop where
  terminalNoFirst :
    ResetPortPreFinalTerminalNoFirstPathRealizationGoal baseRow
  terminalFirst :
    ResetPortPreFinalTerminalFirstCarryPathRealizationGoal baseRow
  p0YShiftLast :
    ResetPortPreFinalYShiftLastStepPathOnGoal baseRow 3
      (fun w => ¬ finalLiftCarrySite 3 w ∧ yCoord w ≠ 0)
  p0F0Tail :
    ResetPortPreFinalYTerminalTailPathOnGoal baseRow 3
      (fun w => ¬ finalLiftCarrySite 3 w ∧ yCoord w = 0)
      TerminalSymbol.F0
  p1YShiftLast :
    ResetPortPreFinalYShiftLastStepPathOnGoal baseRow 4
      (fun w =>
        ¬ finalLiftCarrySite 4 w ∧
        yCoord w ≠ 1 ∧ yCoord w ≠ 2 ∧ yCoord w ≠ 3)
  p1Y1F0Tail :
    ResetPortPreFinalYTerminalTailPathOnGoal baseRow 4
      (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 1)
      TerminalSymbol.F0
  p1Y2F2Tail :
    ResetPortPreFinalYTerminalTailPathOnGoal baseRow 4
      (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 2)
      TerminalSymbol.F2
  p1Y3F1Tail :
    ResetPortPreFinalYTerminalTailPathOnGoal baseRow 4
      (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 3)
      TerminalSymbol.F1

def resetPortPreFinalRowWordSplitPathGoals_of_tail
    {baseRow : ResetPortBaseRow}
    (h : ResetPortPreFinalTailRowWordSplitPathGoals baseRow) :
    ResetPortPreFinalRowWordSplitPathGoals baseRow where
  terminalNoFirst := h.terminalNoFirst
  terminalFirst := h.terminalFirst
  p0YShift :=
    resetPortPreFinalP0YShiftPathRealizationGoal_of_lastStepPathOnGoal
      baseRow h.p0YShiftLast
  p0F0 :=
    resetPortPreFinalP0F0PathRealizationGoal_of_tailPathOnGoal
      baseRow h.p0F0Tail
  p1YShift :=
    resetPortPreFinalP1YShiftPathRealizationGoal_of_lastStepPathOnGoal
      baseRow h.p1YShiftLast
  p1Y1F0 :=
    resetPortPreFinalP1Y1F0PathRealizationGoal_of_tailPathOnGoal
      baseRow h.p1Y1F0Tail
  p1Y2F2 :=
    resetPortPreFinalP1Y2F2PathRealizationGoal_of_tailPathOnGoal
      baseRow h.p1Y2F2Tail
  p1Y3F1 :=
    resetPortPreFinalP1Y3F1PathRealizationGoal_of_tailPathOnGoal
      baseRow h.p1Y3F1Tail

/-- A paper-tail version of the final-carry row-word split. It is the same
terminal-tail input as the pre-final package, with the final `Z` carry already
attached to the target. -/
structure ResetPortFinalCarryTailRowWordSplitPathGoals
    (baseRow : ResetPortBaseRow) :
    Prop where
  terminalNoFirst :
    ResetPortFinalCarryTerminalNoFirstPathRealizationGoal baseRow
  terminalFirst :
    ResetPortFinalCarryTerminalFirstPathRealizationGoal baseRow
  p0YShiftLast :
    ResetPortFinalYShiftLastStepPathOnGoal baseRow 3
      (fun w => finalLiftCarrySite 3 w ∧ yCoord w ≠ 0)
  p0F0Tail :
    ResetPortFinalYTerminalTailPathOnGoal baseRow 3
      (fun w => finalLiftCarrySite 3 w ∧ yCoord w = 0)
      TerminalSymbol.F0
  p1YShiftLast :
    ResetPortFinalYShiftLastStepPathOnGoal baseRow 4
      (fun w =>
        finalLiftCarrySite 4 w ∧
        yCoord w ≠ 1 ∧ yCoord w ≠ 2 ∧ yCoord w ≠ 3)
  p1Y1F0Tail :
    ResetPortFinalYTerminalTailPathOnGoal baseRow 4
      (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 1)
      TerminalSymbol.F0
  p1Y2F2Tail :
    ResetPortFinalYTerminalTailPathOnGoal baseRow 4
      (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 2)
      TerminalSymbol.F2
  p1Y3F1Tail :
    ResetPortFinalYTerminalTailPathOnGoal baseRow 4
      (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 3)
      TerminalSymbol.F1

def resetPortFinalCarryRowWordSplitPathGoals_of_tail
    {baseRow : ResetPortBaseRow}
    (h : ResetPortFinalCarryTailRowWordSplitPathGoals baseRow) :
    ResetPortFinalCarryRowWordSplitPathGoals baseRow where
  terminalNoFirst := h.terminalNoFirst
  terminalFirst := h.terminalFirst
  p0YShift :=
    resetPortFinalCarryP0YShiftPathRealizationGoal_of_lastStepPathOnGoal
      baseRow h.p0YShiftLast
  p0F0 :=
    resetPortFinalCarryP0F0PathRealizationGoal_of_tailPathOnGoal
      baseRow h.p0F0Tail
  p1YShift :=
    resetPortFinalCarryP1YShiftPathRealizationGoal_of_lastStepPathOnGoal
      baseRow h.p1YShiftLast
  p1Y1F0 :=
    resetPortFinalCarryP1Y1F0PathRealizationGoal_of_tailPathOnGoal
      baseRow h.p1Y1F0Tail
  p1Y2F2 :=
    resetPortFinalCarryP1Y2F2PathRealizationGoal_of_tailPathOnGoal
      baseRow h.p1Y2F2Tail
  p1Y3F1 :=
    resetPortFinalCarryP1Y3F1PathRealizationGoal_of_tailPathOnGoal
      baseRow h.p1Y3F1Tail

/-- Final-carry tail goals with the active-site `z += 1` first step split off
from the remaining terminal and `P₀`/`P₁` residual row-word paths. -/
structure ResetPortFinalCarryZFirstTailRowWordGoals
    (baseRow : ResetPortBaseRow) :
    Prop where
  terminalNoFirstZFirst :
    ResetPortFinalCarryTerminalNoFirstZFirstResidualPathGoal baseRow
  terminalFirstZFirst :
    ResetPortFinalCarryTerminalFirstZFirstResidualPathGoal baseRow
  p0YShiftZFirstLast :
    ResetPortFinalZFirstYShiftLastStepPathOnGoal baseRow 3
      (fun w => finalLiftCarrySite 3 w ∧ yCoord w ≠ 0)
  p0F0ZFirstTail :
    ResetPortFinalZFirstYTerminalTailPathOnGoal baseRow 3
      (fun w => finalLiftCarrySite 3 w ∧ yCoord w = 0)
      TerminalSymbol.F0
  p1YShiftZFirstLast :
    ResetPortFinalZFirstYShiftLastStepPathOnGoal baseRow 4
      (fun w =>
        finalLiftCarrySite 4 w ∧
        yCoord w ≠ 1 ∧ yCoord w ≠ 2 ∧ yCoord w ≠ 3)
  p1Y1F0ZFirstTail :
    ResetPortFinalZFirstYTerminalTailPathOnGoal baseRow 4
      (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 1)
      TerminalSymbol.F0
  p1Y2F2ZFirstTail :
    ResetPortFinalZFirstYTerminalTailPathOnGoal baseRow 4
      (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 2)
      TerminalSymbol.F2
  p1Y3F1ZFirstTail :
    ResetPortFinalZFirstYTerminalTailPathOnGoal baseRow 4
      (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 3)
      TerminalSymbol.F1

def resetPortFinalCarryRowWordSplitPathGoals_of_zFirstTail
    {baseRow : ResetPortBaseRow}
    (h : ResetPortFinalCarryZFirstTailRowWordGoals baseRow) :
    ResetPortFinalCarryRowWordSplitPathGoals baseRow where
  terminalNoFirst :=
    resetPortFinalCarryTerminalNoFirstPathGoal_of_zFirstResidualPathGoal
      baseRow h.terminalNoFirstZFirst
  terminalFirst :=
    resetPortFinalCarryTerminalFirstPathGoal_of_zFirstResidualPathGoal
      baseRow h.terminalFirstZFirst
  p0YShift :=
    resetPortFinalCarryP0YShiftPathRealizationGoal_of_zFirstLastStepPathOnGoal
      baseRow h.p0YShiftZFirstLast
  p0F0 :=
    resetPortFinalCarryP0F0PathRealizationGoal_of_zFirstTailPathOnGoal
      baseRow h.p0F0ZFirstTail
  p1YShift :=
    resetPortFinalCarryP1YShiftPathRealizationGoal_of_zFirstLastStepPathOnGoal
      baseRow h.p1YShiftZFirstLast
  p1Y1F0 :=
    resetPortFinalCarryP1Y1F0PathRealizationGoal_of_zFirstTailPathOnGoal
      baseRow h.p1Y1F0ZFirstTail
  p1Y2F2 :=
    resetPortFinalCarryP1Y2F2PathRealizationGoal_of_zFirstTailPathOnGoal
      baseRow h.p1Y2F2ZFirstTail
  p1Y3F1 :=
    resetPortFinalCarryP1Y3F1PathRealizationGoal_of_zFirstTailPathOnGoal
      baseRow h.p1Y3F1ZFirstTail

/-- The full paper-tail row-word split obligation, before converting to the
older concrete path-goal package. -/
structure ResetPortFullTailRowWordSplitPathGoals
    (baseRow : ResetPortBaseRow) :
    Prop where
  preFinal : ResetPortPreFinalTailRowWordSplitPathGoals baseRow
  finalCarry : ResetPortFinalCarryTailRowWordSplitPathGoals baseRow

def resetPortFullRowWordSplitPathGoals_of_tail
    {baseRow : ResetPortBaseRow}
    (h : ResetPortFullTailRowWordSplitPathGoals baseRow) :
    ResetPortFullRowWordSplitPathGoals baseRow where
  preFinal :=
    resetPortPreFinalRowWordSplitPathGoals_of_tail h.preFinal
  finalCarry :=
    resetPortFinalCarryRowWordSplitPathGoals_of_tail h.finalCarry

/-- Pre-final paper-tail goals with the terminal `A2` no-reset core split off
from the residual reset-port cases.  This keeps the terminal-row lemma separate
from the local switching-ribbon exceptions. -/
structure ResetPortPreFinalCoreSplitTailRowWordGoals
    (baseRow : ResetPortBaseRow) :
    Prop where
  terminalCoreTail : TerminalCoreTailPathGoal baseRow
  terminalNoFirstResidual :
    ResetPortPreFinalTerminalNoFirstResidualPathRealizationGoal baseRow
  terminalFirst :
    ResetPortPreFinalTerminalFirstCarryPathRealizationGoal baseRow
  p0YShiftLast :
    ResetPortPreFinalYShiftLastStepPathOnGoal baseRow 3
      (fun w => ¬ finalLiftCarrySite 3 w ∧ yCoord w ≠ 0)
  p0F0Tail :
    ResetPortPreFinalYTerminalTailPathOnGoal baseRow 3
      (fun w => ¬ finalLiftCarrySite 3 w ∧ yCoord w = 0)
      TerminalSymbol.F0
  p1YShiftLast :
    ResetPortPreFinalYShiftLastStepPathOnGoal baseRow 4
      (fun w =>
        ¬ finalLiftCarrySite 4 w ∧
        yCoord w ≠ 1 ∧ yCoord w ≠ 2 ∧ yCoord w ≠ 3)
  p1Y1F0Tail :
    ResetPortPreFinalYTerminalTailPathOnGoal baseRow 4
      (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 1)
      TerminalSymbol.F0
  p1Y2F2Tail :
    ResetPortPreFinalYTerminalTailPathOnGoal baseRow 4
      (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 2)
      TerminalSymbol.F2
  p1Y3F1Tail :
    ResetPortPreFinalYTerminalTailPathOnGoal baseRow 4
      (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 3)
      TerminalSymbol.F1

def resetPortPreFinalRealizationGoal_of_coreSplitTailRowWordGoals
    {baseRow : ResetPortBaseRow}
    (h : ResetPortPreFinalCoreSplitTailRowWordGoals baseRow) :
    ResetPortPreFinalRealizationGoal baseRow :=
  resetPortPreFinalRealizationGoal_of_colorGoals
    baseRow
    (resetPortPreFinalTerminalRealizationGoal_of_firstCarrySplit
      baseRow
      (resetPortPreFinalTerminalNoFirstRealizationGoal_of_coreTail_and_residualPath
        baseRow h.terminalCoreTail h.terminalNoFirstResidual)
      (resetPortPreFinalTerminalFirstCarryRealizationGoal_of_pathGoal
        baseRow h.terminalFirst))
    (resetPortPreFinalP0RealizationGoal_of_ySplitPathGoals
      baseRow
      (resetPortPreFinalP0YShiftPathRealizationGoal_of_lastStepPathOnGoal
        baseRow h.p0YShiftLast)
      (resetPortPreFinalP0F0PathRealizationGoal_of_tailPathOnGoal
        baseRow h.p0F0Tail))
    (resetPortPreFinalP1RealizationGoal_of_ySplitPathGoals
      baseRow
      (resetPortPreFinalP1YShiftPathRealizationGoal_of_lastStepPathOnGoal
        baseRow h.p1YShiftLast)
      (resetPortPreFinalP1Y1F0PathRealizationGoal_of_tailPathOnGoal
        baseRow h.p1Y1F0Tail)
      (resetPortPreFinalP1Y2F2PathRealizationGoal_of_tailPathOnGoal
        baseRow h.p1Y2F2Tail)
      (resetPortPreFinalP1Y3F1PathRealizationGoal_of_tailPathOnGoal
        baseRow h.p1Y3F1Tail))

/-- Pre-final paper-tail goals with both terminal simplifications exposed:
the no-first/no-reset terminal-A2 core is split off, and the active first
`Y` carry case supplies the collapsed terminal tail after the forced first step
unless it conflicts with another final-stage site. -/
structure ResetPortPreFinalCoreYFirstTailRowWordGoals
    (baseRow : ResetPortBaseRow) :
    Prop where
  terminalCoreTail : TerminalCoreTailPathGoal baseRow
  terminalNoFirstResidual :
    ResetPortPreFinalTerminalNoFirstResidualPathRealizationGoal baseRow
  terminalFirstNoFinalYFirstTail :
    ResetPortPreFinalTerminalFirstCarryNoFinalYFirstTailPathGoal
      baseRow
  terminalFirstFinalConflict :
    ResetPortPreFinalTerminalFirstCarryFinalConflictPathRealizationGoal
      baseRow
  p0YShiftLast :
    ResetPortPreFinalYShiftLastStepPathOnGoal baseRow 3
      (fun w => ¬ finalLiftCarrySite 3 w ∧ yCoord w ≠ 0)
  p0F0Tail :
    ResetPortPreFinalYTerminalTailPathOnGoal baseRow 3
      (fun w => ¬ finalLiftCarrySite 3 w ∧ yCoord w = 0)
      TerminalSymbol.F0
  p1YShiftLast :
    ResetPortPreFinalYShiftLastStepPathOnGoal baseRow 4
      (fun w =>
        ¬ finalLiftCarrySite 4 w ∧
        yCoord w ≠ 1 ∧ yCoord w ≠ 2 ∧ yCoord w ≠ 3)
  p1Y1F0Tail :
    ResetPortPreFinalYTerminalTailPathOnGoal baseRow 4
      (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 1)
      TerminalSymbol.F0
  p1Y2F2Tail :
    ResetPortPreFinalYTerminalTailPathOnGoal baseRow 4
      (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 2)
      TerminalSymbol.F2
  p1Y3F1Tail :
    ResetPortPreFinalYTerminalTailPathOnGoal baseRow 4
      (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 3)
      TerminalSymbol.F1

def resetPortPreFinalRealizationGoal_of_coreYFirstTailRowWordGoals
    {baseRow : ResetPortBaseRow}
    (h : ResetPortPreFinalCoreYFirstTailRowWordGoals baseRow) :
    ResetPortPreFinalRealizationGoal baseRow :=
  resetPortPreFinalRealizationGoal_of_colorGoals
    baseRow
    (resetPortPreFinalTerminalRealizationGoal_of_firstCarrySplit
      baseRow
      (resetPortPreFinalTerminalNoFirstRealizationGoal_of_coreTail_and_residualPath
        baseRow h.terminalCoreTail h.terminalNoFirstResidual)
      (resetPortPreFinalTerminalFirstCarryRealizationGoal_of_yFirstTailNoFinal_and_finalConflict
        baseRow h.terminalFirstNoFinalYFirstTail
          h.terminalFirstFinalConflict))
    (resetPortPreFinalP0RealizationGoal_of_ySplitPathGoals
      baseRow
      (resetPortPreFinalP0YShiftPathRealizationGoal_of_lastStepPathOnGoal
        baseRow h.p0YShiftLast)
      (resetPortPreFinalP0F0PathRealizationGoal_of_tailPathOnGoal
        baseRow h.p0F0Tail))
    (resetPortPreFinalP1RealizationGoal_of_ySplitPathGoals
      baseRow
      (resetPortPreFinalP1YShiftPathRealizationGoal_of_lastStepPathOnGoal
        baseRow h.p1YShiftLast)
      (resetPortPreFinalP1Y1F0PathRealizationGoal_of_tailPathOnGoal
        baseRow h.p1Y1F0Tail)
      (resetPortPreFinalP1Y2F2PathRealizationGoal_of_tailPathOnGoal
        baseRow h.p1Y2F2Tail)
      (resetPortPreFinalP1Y3F1PathRealizationGoal_of_tailPathOnGoal
        baseRow h.p1Y3F1Tail))

/-- Split version of the current pre-final paper-tail goal package.  Every
collapsed-tail field is supplied as a prefix path plus an explicit last-layer
row-word read. -/
structure ResetPortPreFinalCoreYFirstTailSplitRowWordGoals
    (baseRow : ResetPortBaseRow) :
    Prop where
  terminalCoreTail : TerminalCoreTailSplitPathGoal baseRow
  terminalNoFirstResidual :
    ResetPortPreFinalTerminalNoFirstResidualPathRealizationGoal baseRow
  terminalFirstNoFinalYFirstTail :
    ResetPortPreFinalTerminalFirstCarryNoFinalYFirstTailSplitPathGoal
      baseRow
  terminalFirstFinalConflict :
    ResetPortPreFinalTerminalFirstCarryFinalConflictPathRealizationGoal
      baseRow
  p0YShiftLast :
    ResetPortYShiftLastStepSplitPathOnGoal baseRow 3
      (fun w => ¬ finalLiftCarrySite 3 w ∧ yCoord w ≠ 0)
      zCoord
  p0F0Tail :
    ResetPortYTerminalTailSplitPathOnGoal baseRow 3
      (fun w => ¬ finalLiftCarrySite 3 w ∧ yCoord w = 0)
      TerminalSymbol.F0 zCoord
  p1YShiftLast :
    ResetPortYShiftLastStepSplitPathOnGoal baseRow 4
      (fun w =>
        ¬ finalLiftCarrySite 4 w ∧
        yCoord w ≠ 1 ∧ yCoord w ≠ 2 ∧ yCoord w ≠ 3)
      zCoord
  p1Y1F0Tail :
    ResetPortYTerminalTailSplitPathOnGoal baseRow 4
      (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 1)
      TerminalSymbol.F0 zCoord
  p1Y2F2Tail :
    ResetPortYTerminalTailSplitPathOnGoal baseRow 4
      (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 2)
      TerminalSymbol.F2 zCoord
  p1Y3F1Tail :
    ResetPortYTerminalTailSplitPathOnGoal baseRow 4
      (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 3)
      TerminalSymbol.F1 zCoord

def resetPortPreFinalCoreYFirstTailRowWordGoals_of_split
    {baseRow : ResetPortBaseRow}
    (h : ResetPortPreFinalCoreYFirstTailSplitRowWordGoals baseRow) :
    ResetPortPreFinalCoreYFirstTailRowWordGoals baseRow where
  terminalCoreTail := TerminalCoreTailPathGoal_of_split h.terminalCoreTail
  terminalNoFirstResidual := h.terminalNoFirstResidual
  terminalFirstNoFinalYFirstTail :=
    resetPortPreFinalTerminalFirstCarryNoFinalYFirstTailPathGoal_of_split
      h.terminalFirstNoFinalYFirstTail
  terminalFirstFinalConflict := h.terminalFirstFinalConflict
  p0YShiftLast := ResetPortYShiftLastStepPathOnGoal_of_split h.p0YShiftLast
  p0F0Tail := ResetPortYTerminalTailPathOnGoal_of_split h.p0F0Tail
  p1YShiftLast := ResetPortYShiftLastStepPathOnGoal_of_split h.p1YShiftLast
  p1Y1F0Tail := ResetPortYTerminalTailPathOnGoal_of_split h.p1Y1F0Tail
  p1Y2F2Tail := ResetPortYTerminalTailPathOnGoal_of_split h.p1Y2F2Tail
  p1Y3F1Tail := ResetPortYTerminalTailPathOnGoal_of_split h.p1Y3F1Tail

/-- Split version of the current final-carry Z-first tail package. -/
structure ResetPortFinalCarryZFirstTailSplitRowWordGoals
    (baseRow : ResetPortBaseRow) :
    Prop where
  terminalNoFirstZFirst :
    ResetPortFinalCarryTerminalNoFirstZFirstResidualPathGoal baseRow
  terminalFirstZFirst :
    ResetPortFinalCarryTerminalFirstZFirstResidualPathGoal baseRow
  p0YShiftZFirstLast :
    ResetPortFinalZFirstYShiftLastStepSplitPathOnGoal baseRow 3
      (fun w => finalLiftCarrySite 3 w ∧ yCoord w ≠ 0)
  p0F0ZFirstTail :
    ResetPortFinalZFirstYTerminalTailSplitPathOnGoal baseRow 3
      (fun w => finalLiftCarrySite 3 w ∧ yCoord w = 0)
      TerminalSymbol.F0
  p1YShiftZFirstLast :
    ResetPortFinalZFirstYShiftLastStepSplitPathOnGoal baseRow 4
      (fun w =>
        finalLiftCarrySite 4 w ∧
        yCoord w ≠ 1 ∧ yCoord w ≠ 2 ∧ yCoord w ≠ 3)
  p1Y1F0ZFirstTail :
    ResetPortFinalZFirstYTerminalTailSplitPathOnGoal baseRow 4
      (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 1)
      TerminalSymbol.F0
  p1Y2F2ZFirstTail :
    ResetPortFinalZFirstYTerminalTailSplitPathOnGoal baseRow 4
      (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 2)
      TerminalSymbol.F2
  p1Y3F1ZFirstTail :
    ResetPortFinalZFirstYTerminalTailSplitPathOnGoal baseRow 4
      (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 3)
      TerminalSymbol.F1

def resetPortFinalCarryZFirstTailRowWordGoals_of_split
    {baseRow : ResetPortBaseRow}
    (h : ResetPortFinalCarryZFirstTailSplitRowWordGoals baseRow) :
    ResetPortFinalCarryZFirstTailRowWordGoals baseRow where
  terminalNoFirstZFirst := h.terminalNoFirstZFirst
  terminalFirstZFirst := h.terminalFirstZFirst
  p0YShiftZFirstLast :=
    ResetPortFinalZFirstYShiftLastStepPathOnGoal_of_split
      h.p0YShiftZFirstLast
  p0F0ZFirstTail :=
    ResetPortFinalZFirstYTerminalTailPathOnGoal_of_split
      h.p0F0ZFirstTail
  p1YShiftZFirstLast :=
    ResetPortFinalZFirstYShiftLastStepPathOnGoal_of_split
      h.p1YShiftZFirstLast
  p1Y1F0ZFirstTail :=
    ResetPortFinalZFirstYTerminalTailPathOnGoal_of_split
      h.p1Y1F0ZFirstTail
  p1Y2F2ZFirstTail :=
    ResetPortFinalZFirstYTerminalTailPathOnGoal_of_split
      h.p1Y2F2ZFirstTail
  p1Y3F1ZFirstTail :=
    ResetPortFinalZFirstYTerminalTailPathOnGoal_of_split
      h.p1Y3F1ZFirstTail

def resetPortPreFinalRealizationGoal_of_coreYFirstTailSplitRowWordGoals
    {baseRow : ResetPortBaseRow}
    (h : ResetPortPreFinalCoreYFirstTailSplitRowWordGoals baseRow) :
    ResetPortPreFinalRealizationGoal baseRow :=
  resetPortPreFinalRealizationGoal_of_colorGoals
    baseRow
    (resetPortPreFinalTerminalRealizationGoal_of_firstCarrySplit
      baseRow
      (resetPortPreFinalTerminalNoFirstRealizationGoal_of_coreTail_and_residualPath
        baseRow
        (TerminalCoreTailPathGoal_of_split h.terminalCoreTail)
        h.terminalNoFirstResidual)
      (preFinalTerminalFirstCarryRealizationGoal_of_yFirstTailSplit
        baseRow h.terminalFirstNoFinalYFirstTail
          h.terminalFirstFinalConflict))
    (resetPortPreFinalP0RealizationGoal_of_ySplitPathGoals
      baseRow
      (resetPortPreFinalP0YShiftPathRealizationGoal_of_lastStepSplitPathOnGoal
        baseRow h.p0YShiftLast)
      (resetPortPreFinalP0F0PathRealizationGoal_of_tailSplitPathOnGoal
        baseRow h.p0F0Tail))
    (resetPortPreFinalP1RealizationGoal_of_ySplitPathGoals
      baseRow
      (resetPortPreFinalP1YShiftPathRealizationGoal_of_lastStepSplitPathOnGoal
        baseRow h.p1YShiftLast)
      (resetPortPreFinalP1Y1F0PathRealizationGoal_of_tailSplitPathOnGoal
        baseRow h.p1Y1F0Tail)
      (resetPortPreFinalP1Y2F2PathRealizationGoal_of_tailSplitPathOnGoal
        baseRow h.p1Y2F2Tail)
      (resetPortPreFinalP1Y3F1PathRealizationGoal_of_tailSplitPathOnGoal
        baseRow h.p1Y3F1Tail))

def resetPortFinalCarryRealizationGoal_of_zFirstTailSplitRowWordGoals
    {baseRow : ResetPortBaseRow}
    (h : ResetPortFinalCarryZFirstTailSplitRowWordGoals baseRow) :
    ResetPortFinalCarryRealizationGoal baseRow :=
  resetPortFinalCarryRealizationGoal_of_colorGoals
    baseRow
    (resetPortFinalCarryTerminalRealizationGoal_of_firstCarryPathGoals
      baseRow
      (resetPortFinalCarryTerminalNoFirstPathGoal_of_zFirstResidualPathGoal
        baseRow h.terminalNoFirstZFirst)
      (resetPortFinalCarryTerminalFirstPathGoal_of_zFirstResidualPathGoal
        baseRow h.terminalFirstZFirst))
    (resetPortFinalCarryP0RealizationGoal_of_ySplitPathGoals
      baseRow
      (resetPortFinalCarryP0YShiftPathRealizationGoal_of_zFirstLastStepSplitPathOnGoal
        baseRow h.p0YShiftZFirstLast)
      (resetPortFinalCarryP0F0PathRealizationGoal_of_zFirstTailSplitPathOnGoal
        baseRow h.p0F0ZFirstTail))
    (resetPortFinalCarryP1RealizationGoal_of_ySplitPathGoals
      baseRow
      (resetPortFinalCarryP1YShiftPathRealizationGoal_of_zFirstLastStepSplitPathOnGoal
        baseRow h.p1YShiftZFirstLast)
      (resetPortFinalCarryP1Y1F0PathRealizationGoal_of_zFirstTailSplitPathOnGoal
        baseRow h.p1Y1F0ZFirstTail)
      (resetPortFinalCarryP1Y2F2PathRealizationGoal_of_zFirstTailSplitPathOnGoal
        baseRow h.p1Y2F2ZFirstTail)
      (resetPortFinalCarryP1Y3F1PathRealizationGoal_of_zFirstTailSplitPathOnGoal
        baseRow h.p1Y3F1ZFirstTail))

/-- Full paper-tail goals with the pre-final terminal core split off and the
final-carry side kept in the existing tail path form. -/
structure ResetPortFullCoreSplitTailRowWordGoals
    (baseRow : ResetPortBaseRow) :
    Prop where
  preFinal : ResetPortPreFinalCoreSplitTailRowWordGoals baseRow
  finalCarry : ResetPortFinalCarryTailRowWordSplitPathGoals baseRow

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortBaseFullCoreSplitTailRowWordGoals
    (baseRow : ResetPortBaseRow)
    (hLayer : ResetPortLayerBijectiveGoal baseRow)
    (hGoals : ResetPortFullCoreSplitTailRowWordGoals baseRow) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePreFinalFinalCarry
    baseRow hLayer
    (resetPortPreFinalRealizationGoal_of_coreSplitTailRowWordGoals
      hGoals.preFinal)
    (resetPortFinalCarryRealizationGoal_of_rowWordSplitPathGoals
      baseRow
      (resetPortFinalCarryRowWordSplitPathGoals_of_tail
        hGoals.finalCarry))

/-- Full paper-tail goals with pre-final terminal core split and final-carry
terminal `z += 1` first steps split off. -/
structure ResetPortFullCoreZFirstTailRowWordGoals
    (baseRow : ResetPortBaseRow) :
    Prop where
  preFinal : ResetPortPreFinalCoreSplitTailRowWordGoals baseRow
  finalCarry : ResetPortFinalCarryZFirstTailRowWordGoals baseRow

/-- Full paper-tail goals with pre-final terminal first-`Y` and final-carry
first-`Z` forced steps split off. -/
structure ResetPortFullCoreYFirstZFirstTailRowWordGoals
    (baseRow : ResetPortBaseRow) :
    Prop where
  preFinal : ResetPortPreFinalCoreYFirstTailRowWordGoals baseRow
  finalCarry : ResetPortFinalCarryZFirstTailRowWordGoals baseRow

/-- Split version of the most decomposed paper-tail goal package. This is the
handoff closest to the paper row-word proof: residual path prefixes and
last-layer row-word reads are separate inputs. -/
structure ResetPortFullCoreYFirstZFirstTailSplitRowWordGoals
    (baseRow : ResetPortBaseRow) :
    Prop where
  preFinal : ResetPortPreFinalCoreYFirstTailSplitRowWordGoals baseRow
  finalCarry : ResetPortFinalCarryZFirstTailSplitRowWordGoals baseRow

def resetPortFullCoreYFirstZFirstTailRowWordGoals_of_split
    {baseRow : ResetPortBaseRow}
    (h : ResetPortFullCoreYFirstZFirstTailSplitRowWordGoals baseRow) :
    ResetPortFullCoreYFirstZFirstTailRowWordGoals baseRow where
  preFinal := resetPortPreFinalCoreYFirstTailRowWordGoals_of_split
    h.preFinal
  finalCarry := resetPortFinalCarryZFirstTailRowWordGoals_of_split
    h.finalCarry

/-- Prefix-path part of the current pre-final split handoff. The last-layer
row-word reads are supplied separately by `ResetPortPreFinalSplitReadGoals`. -/
structure ResetPortPreFinalSplitPrefixGoals
    (baseRow : ResetPortBaseRow) :
    Prop where
  terminalCoreTail : TerminalCoreTailPrefixPathGoal baseRow
  terminalNoFirstResidual :
    ResetPortPreFinalTerminalNoFirstResidualPathRealizationGoal baseRow
  terminalFirstNoFinalYFirstTail :
    ∀ i : Fin 3,
      ResetPortPreFinalTerminalFirstYTailPrefixPathOnGoal
        baseRow i
        (fun w =>
          NoFinalLiftSites w ∧
          firstLiftCarrySite (fin3ToFin5 i) w)
  terminalFirstFinalConflict :
    ResetPortPreFinalTerminalFirstCarryFinalConflictPathRealizationGoal
      baseRow
  p0YShiftLast :
    ResetPortYShiftLastStepPrefixPathOnGoal baseRow 3
      (fun w => ¬ finalLiftCarrySite 3 w ∧ yCoord w ≠ 0)
      zCoord
  p0F0Tail :
    ResetPortYTerminalTailPrefixPathOnGoal baseRow 3
      (fun w => ¬ finalLiftCarrySite 3 w ∧ yCoord w = 0)
      TerminalSymbol.F0 zCoord
  p1YShiftLast :
    ResetPortYShiftLastStepPrefixPathOnGoal baseRow 4
      (fun w =>
        ¬ finalLiftCarrySite 4 w ∧
        yCoord w ≠ 1 ∧ yCoord w ≠ 2 ∧ yCoord w ≠ 3)
      zCoord
  p1Y1F0Tail :
    ResetPortYTerminalTailPrefixPathOnGoal baseRow 4
      (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 1)
      TerminalSymbol.F0 zCoord
  p1Y2F2Tail :
    ResetPortYTerminalTailPrefixPathOnGoal baseRow 4
      (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 2)
      TerminalSymbol.F2 zCoord
  p1Y3F1Tail :
    ResetPortYTerminalTailPrefixPathOnGoal baseRow 4
      (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 3)
      TerminalSymbol.F1 zCoord

/-- Last-layer row-word read part of the current pre-final split handoff. -/
structure ResetPortPreFinalSplitReadGoals
    (baseRow : ResetPortBaseRow) :
    Prop where
  terminalCoreTail : TerminalCoreTailReadGoal baseRow
  terminalFirstNoFinalYFirstTail :
    ∀ i : Fin 3,
      ResetPortPreFinalTerminalFirstYTailReadOnGoal
        baseRow i
        (fun w =>
          NoFinalLiftSites w ∧
          firstLiftCarrySite (fin3ToFin5 i) w)
  p0YShiftLast :
    ResetPortYShiftLastStepReadOnGoal baseRow 3
      (fun w => ¬ finalLiftCarrySite 3 w ∧ yCoord w ≠ 0)
      zCoord
  p0F0Tail :
    ResetPortYTerminalTailReadOnGoal baseRow 3
      (fun w => ¬ finalLiftCarrySite 3 w ∧ yCoord w = 0)
      TerminalSymbol.F0 zCoord
  p1YShiftLast :
    ResetPortYShiftLastStepReadOnGoal baseRow 4
      (fun w =>
        ¬ finalLiftCarrySite 4 w ∧
        yCoord w ≠ 1 ∧ yCoord w ≠ 2 ∧ yCoord w ≠ 3)
      zCoord
  p1Y1F0Tail :
    ResetPortYTerminalTailReadOnGoal baseRow 4
      (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 1)
      TerminalSymbol.F0 zCoord
  p1Y2F2Tail :
    ResetPortYTerminalTailReadOnGoal baseRow 4
      (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 2)
      TerminalSymbol.F2 zCoord
  p1Y3F1Tail :
    ResetPortYTerminalTailReadOnGoal baseRow 4
      (fun w => ¬ finalLiftCarrySite 4 w ∧ yCoord w = 3)
      TerminalSymbol.F1 zCoord

def resetPortPreFinalSplitGoals_of_prefixRead
    {baseRow : ResetPortBaseRow}
    (hPrefix : ResetPortPreFinalSplitPrefixGoals baseRow)
    (hRead : ResetPortPreFinalSplitReadGoals baseRow) :
    ResetPortPreFinalCoreYFirstTailSplitRowWordGoals baseRow where
  terminalCoreTail :=
    { pathPrefix := hPrefix.terminalCoreTail
      read := hRead.terminalCoreTail }
  terminalNoFirstResidual := hPrefix.terminalNoFirstResidual
  terminalFirstNoFinalYFirstTail := fun i =>
    { pathPrefix := hPrefix.terminalFirstNoFinalYFirstTail i
      read := hRead.terminalFirstNoFinalYFirstTail i }
  terminalFirstFinalConflict := hPrefix.terminalFirstFinalConflict
  p0YShiftLast :=
    { pathPrefix := hPrefix.p0YShiftLast
      read := hRead.p0YShiftLast }
  p0F0Tail :=
    { pathPrefix := hPrefix.p0F0Tail
      read := hRead.p0F0Tail }
  p1YShiftLast :=
    { pathPrefix := hPrefix.p1YShiftLast
      read := hRead.p1YShiftLast }
  p1Y1F0Tail :=
    { pathPrefix := hPrefix.p1Y1F0Tail
      read := hRead.p1Y1F0Tail }
  p1Y2F2Tail :=
    { pathPrefix := hPrefix.p1Y2F2Tail
      read := hRead.p1Y2F2Tail }
  p1Y3F1Tail :=
    { pathPrefix := hPrefix.p1Y3F1Tail
      read := hRead.p1Y3F1Tail }

/-- Prefix-path part of the current final-carry Z-first split handoff. -/
structure ResetPortFinalZFirstSplitPrefixGoals
    (baseRow : ResetPortBaseRow) :
    Prop where
  terminalNoFirstZFirst :
    ResetPortFinalCarryTerminalNoFirstZFirstResidualPathGoal baseRow
  terminalFirstZFirst :
    ResetPortFinalCarryTerminalFirstZFirstResidualPathGoal baseRow
  p0YShiftZFirstLast :
    ResetPortFinalZFirstYShiftLastStepPrefixPathOnGoal baseRow 3
      (fun w => finalLiftCarrySite 3 w ∧ yCoord w ≠ 0)
  p0F0ZFirstTail :
    ResetPortFinalZFirstYTerminalTailPrefixPathOnGoal baseRow 3
      (fun w => finalLiftCarrySite 3 w ∧ yCoord w = 0)
      TerminalSymbol.F0
  p1YShiftZFirstLast :
    ResetPortFinalZFirstYShiftLastStepPrefixPathOnGoal baseRow 4
      (fun w =>
        finalLiftCarrySite 4 w ∧
        yCoord w ≠ 1 ∧ yCoord w ≠ 2 ∧ yCoord w ≠ 3)
  p1Y1F0ZFirstTail :
    ResetPortFinalZFirstYTerminalTailPrefixPathOnGoal baseRow 4
      (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 1)
      TerminalSymbol.F0
  p1Y2F2ZFirstTail :
    ResetPortFinalZFirstYTerminalTailPrefixPathOnGoal baseRow 4
      (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 2)
      TerminalSymbol.F2
  p1Y3F1ZFirstTail :
    ResetPortFinalZFirstYTerminalTailPrefixPathOnGoal baseRow 4
      (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 3)
      TerminalSymbol.F1

/-- Last-layer row-word read part of the current final-carry Z-first split
handoff. -/
structure ResetPortFinalZFirstSplitReadGoals
    (baseRow : ResetPortBaseRow) :
    Prop where
  p0YShiftZFirstLast :
    ResetPortFinalZFirstYShiftLastStepReadOnGoal baseRow 3
      (fun w => finalLiftCarrySite 3 w ∧ yCoord w ≠ 0)
  p0F0ZFirstTail :
    ResetPortFinalZFirstYTerminalTailReadOnGoal baseRow 3
      (fun w => finalLiftCarrySite 3 w ∧ yCoord w = 0)
      TerminalSymbol.F0
  p1YShiftZFirstLast :
    ResetPortFinalZFirstYShiftLastStepReadOnGoal baseRow 4
      (fun w =>
        finalLiftCarrySite 4 w ∧
        yCoord w ≠ 1 ∧ yCoord w ≠ 2 ∧ yCoord w ≠ 3)
  p1Y1F0ZFirstTail :
    ResetPortFinalZFirstYTerminalTailReadOnGoal baseRow 4
      (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 1)
      TerminalSymbol.F0
  p1Y2F2ZFirstTail :
    ResetPortFinalZFirstYTerminalTailReadOnGoal baseRow 4
      (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 2)
      TerminalSymbol.F2
  p1Y3F1ZFirstTail :
    ResetPortFinalZFirstYTerminalTailReadOnGoal baseRow 4
      (fun w => finalLiftCarrySite 4 w ∧ yCoord w = 3)
      TerminalSymbol.F1

def resetPortFinalZFirstSplitGoals_of_prefixRead
    {baseRow : ResetPortBaseRow}
    (hPrefix : ResetPortFinalZFirstSplitPrefixGoals baseRow)
    (hRead : ResetPortFinalZFirstSplitReadGoals baseRow) :
    ResetPortFinalCarryZFirstTailSplitRowWordGoals baseRow where
  terminalNoFirstZFirst := hPrefix.terminalNoFirstZFirst
  terminalFirstZFirst := hPrefix.terminalFirstZFirst
  p0YShiftZFirstLast :=
    { pathPrefix := hPrefix.p0YShiftZFirstLast
      read := hRead.p0YShiftZFirstLast }
  p0F0ZFirstTail :=
    { pathPrefix := hPrefix.p0F0ZFirstTail
      read := hRead.p0F0ZFirstTail }
  p1YShiftZFirstLast :=
    { pathPrefix := hPrefix.p1YShiftZFirstLast
      read := hRead.p1YShiftZFirstLast }
  p1Y1F0ZFirstTail :=
    { pathPrefix := hPrefix.p1Y1F0ZFirstTail
      read := hRead.p1Y1F0ZFirstTail }
  p1Y2F2ZFirstTail :=
    { pathPrefix := hPrefix.p1Y2F2ZFirstTail
      read := hRead.p1Y2F2ZFirstTail }
  p1Y3F1ZFirstTail :=
    { pathPrefix := hPrefix.p1Y3F1ZFirstTail
      read := hRead.p1Y3F1ZFirstTail }

/-- Prefix-path part of the full split handoff. -/
structure ResetPortFullSplitPrefixGoals
    (baseRow : ResetPortBaseRow) :
    Prop where
  preFinal : ResetPortPreFinalSplitPrefixGoals baseRow
  finalCarry : ResetPortFinalZFirstSplitPrefixGoals baseRow

/-- Last-layer row-word read part of the full split handoff. -/
structure ResetPortFullSplitReadGoals
    (baseRow : ResetPortBaseRow) :
    Prop where
  preFinal : ResetPortPreFinalSplitReadGoals baseRow
  finalCarry : ResetPortFinalZFirstSplitReadGoals baseRow

/-- Sources where a pre-final terminal color has already taken its first
`Y`-carry step but no final `Z`-carry site is active. -/
def preFinalTerminalFirstYTailSource
    (i : Fin 3) (w : RootState) : Prop :=
  NoFinalLiftSites w ∧ firstLiftCarrySite (fin3ToFin5 i) w

/-- Pre-final `P₀` sources where only the pure `Y` row-word factor is read. -/
def preFinalP0YShiftSource (w : RootState) : Prop :=
  ¬ finalLiftCarrySite 3 w ∧ yCoord w ≠ 0

/-- Pre-final `P₀` sources where the terminal factor is `F₀`. -/
def preFinalP0F0Source (w : RootState) : Prop :=
  ¬ finalLiftCarrySite 3 w ∧ yCoord w = 0

/-- Pre-final `P₁` sources where only the pure `Y` row-word factor is read. -/
def preFinalP1YShiftSource (w : RootState) : Prop :=
  ¬ finalLiftCarrySite 4 w ∧
    yCoord w ≠ 1 ∧ yCoord w ≠ 2 ∧ yCoord w ≠ 3

/-- Pre-final `P₁` sources where the terminal factor is `F₀`. -/
def preFinalP1Y1F0Source (w : RootState) : Prop :=
  ¬ finalLiftCarrySite 4 w ∧ yCoord w = 1

/-- Pre-final `P₁` sources where the terminal factor is `F₂`. -/
def preFinalP1Y2F2Source (w : RootState) : Prop :=
  ¬ finalLiftCarrySite 4 w ∧ yCoord w = 2

/-- Pre-final `P₁` sources where the terminal factor is `F₁`. -/
def preFinalP1Y3F1Source (w : RootState) : Prop :=
  ¬ finalLiftCarrySite 4 w ∧ yCoord w = 3

/-- Final-carry `P₀` sources where only the pure `Y` row-word factor is read. -/
def finalZFirstP0YShiftSource (w : RootState) : Prop :=
  finalLiftCarrySite 3 w ∧ yCoord w ≠ 0

/-- Final-carry `P₀` sources where the terminal factor is `F₀`. -/
def finalZFirstP0F0Source (w : RootState) : Prop :=
  finalLiftCarrySite 3 w ∧ yCoord w = 0

/-- Final-carry `P₁` sources where only the pure `Y` row-word factor is read. -/
def finalZFirstP1YShiftSource (w : RootState) : Prop :=
  finalLiftCarrySite 4 w ∧
    yCoord w ≠ 1 ∧ yCoord w ≠ 2 ∧ yCoord w ≠ 3

/-- Final-carry `P₁` sources where the terminal factor is `F₀`. -/
def finalZFirstP1Y1F0Source (w : RootState) : Prop :=
  finalLiftCarrySite 4 w ∧ yCoord w = 1

/-- Final-carry `P₁` sources where the terminal factor is `F₂`. -/
def finalZFirstP1Y2F2Source (w : RootState) : Prop :=
  finalLiftCarrySite 4 w ∧ yCoord w = 2

/-- Final-carry `P₁` sources where the terminal factor is `F₁`. -/
def finalZFirstP1Y3F1Source (w : RootState) : Prop :=
  finalLiftCarrySite 4 w ∧ yCoord w = 3

/-- Prefix-path goals for the pre-final terminal colors, separated according
to the terminal core and reset-port exceptional sources. -/
structure ResetPortPreFinalTerminalPrefixGoals
    (baseRow : ResetPortBaseRow) :
    Prop where
  terminalCoreTail : TerminalCoreTailPrefixPathGoal baseRow
  terminalNoFirstResidual :
    ResetPortPreFinalTerminalNoFirstResidualPathRealizationGoal baseRow
  terminalFirstNoFinalYFirstTail :
    ∀ i : Fin 3,
      ResetPortPreFinalTerminalFirstYTailPrefixPathOnGoal
        baseRow i (preFinalTerminalFirstYTailSource i)
  terminalFirstFinalConflict :
    ResetPortPreFinalTerminalFirstCarryFinalConflictPathRealizationGoal
      baseRow

/-- Prefix-path goals for the pre-final `P₀`/`P₁` row-word factors. -/
structure ResetPortPreFinalP0P1RowWordPrefixGoals
    (baseRow : ResetPortBaseRow) :
    Prop where
  p0YShiftLast :
    ResetPortYShiftLastStepPrefixPathOnGoal
      baseRow 3 preFinalP0YShiftSource zCoord
  p0F0Tail :
    ResetPortYTerminalTailPrefixPathOnGoal
      baseRow 3 preFinalP0F0Source TerminalSymbol.F0 zCoord
  p1YShiftLast :
    ResetPortYShiftLastStepPrefixPathOnGoal
      baseRow 4 preFinalP1YShiftSource zCoord
  p1Y1F0Tail :
    ResetPortYTerminalTailPrefixPathOnGoal
      baseRow 4 preFinalP1Y1F0Source TerminalSymbol.F0 zCoord
  p1Y2F2Tail :
    ResetPortYTerminalTailPrefixPathOnGoal
      baseRow 4 preFinalP1Y2F2Source TerminalSymbol.F2 zCoord
  p1Y3F1Tail :
    ResetPortYTerminalTailPrefixPathOnGoal
      baseRow 4 preFinalP1Y3F1Source TerminalSymbol.F1 zCoord

/-- Prefix-path goals for the final-carry terminal colors after the forced
first `Z` step has been split away. -/
structure ResetPortFinalZFirstTerminalPrefixGoals
    (baseRow : ResetPortBaseRow) :
    Prop where
  terminalNoFirstZFirst :
    ResetPortFinalCarryTerminalNoFirstZFirstResidualPathGoal baseRow
  terminalFirstZFirst :
    ResetPortFinalCarryTerminalFirstZFirstResidualPathGoal baseRow

/-- Prefix-path goals for the final-carry `P₀`/`P₁` row-word factors after
the forced first `Z` step. -/
structure ResetPortFinalZFirstP0P1RowWordPrefixGoals
    (baseRow : ResetPortBaseRow) :
    Prop where
  p0YShiftZFirstLast :
    ResetPortFinalZFirstYShiftLastStepPrefixPathOnGoal
      baseRow 3 finalZFirstP0YShiftSource
  p0F0ZFirstTail :
    ResetPortFinalZFirstYTerminalTailPrefixPathOnGoal
      baseRow 3 finalZFirstP0F0Source TerminalSymbol.F0
  p1YShiftZFirstLast :
    ResetPortFinalZFirstYShiftLastStepPrefixPathOnGoal
      baseRow 4 finalZFirstP1YShiftSource
  p1Y1F0ZFirstTail :
    ResetPortFinalZFirstYTerminalTailPrefixPathOnGoal
      baseRow 4 finalZFirstP1Y1F0Source TerminalSymbol.F0
  p1Y2F2ZFirstTail :
    ResetPortFinalZFirstYTerminalTailPrefixPathOnGoal
      baseRow 4 finalZFirstP1Y2F2Source TerminalSymbol.F2
  p1Y3F1ZFirstTail :
    ResetPortFinalZFirstYTerminalTailPrefixPathOnGoal
      baseRow 4 finalZFirstP1Y3F1Source TerminalSymbol.F1

def resetPortPreFinalSplitPrefixGoals_of_paperPrefixGoals
    {baseRow : ResetPortBaseRow}
    (hTerminal : ResetPortPreFinalTerminalPrefixGoals baseRow)
    (hP0P1 : ResetPortPreFinalP0P1RowWordPrefixGoals baseRow) :
    ResetPortPreFinalSplitPrefixGoals baseRow where
  terminalCoreTail := hTerminal.terminalCoreTail
  terminalNoFirstResidual := hTerminal.terminalNoFirstResidual
  terminalFirstNoFinalYFirstTail := fun i => by
    simpa [preFinalTerminalFirstYTailSource] using
      hTerminal.terminalFirstNoFinalYFirstTail i
  terminalFirstFinalConflict := hTerminal.terminalFirstFinalConflict
  p0YShiftLast := by
    simpa [preFinalP0YShiftSource] using hP0P1.p0YShiftLast
  p0F0Tail := by
    simpa [preFinalP0F0Source] using hP0P1.p0F0Tail
  p1YShiftLast := by
    simpa [preFinalP1YShiftSource] using hP0P1.p1YShiftLast
  p1Y1F0Tail := by
    simpa [preFinalP1Y1F0Source] using hP0P1.p1Y1F0Tail
  p1Y2F2Tail := by
    simpa [preFinalP1Y2F2Source] using hP0P1.p1Y2F2Tail
  p1Y3F1Tail := by
    simpa [preFinalP1Y3F1Source] using hP0P1.p1Y3F1Tail

def resetPortFinalZFirstSplitPrefixGoals_of_paperPrefixGoals
    {baseRow : ResetPortBaseRow}
    (hTerminal : ResetPortFinalZFirstTerminalPrefixGoals baseRow)
    (hP0P1 : ResetPortFinalZFirstP0P1RowWordPrefixGoals baseRow) :
    ResetPortFinalZFirstSplitPrefixGoals baseRow where
  terminalNoFirstZFirst := hTerminal.terminalNoFirstZFirst
  terminalFirstZFirst := hTerminal.terminalFirstZFirst
  p0YShiftZFirstLast := by
    simpa [finalZFirstP0YShiftSource] using hP0P1.p0YShiftZFirstLast
  p0F0ZFirstTail := by
    simpa [finalZFirstP0F0Source] using hP0P1.p0F0ZFirstTail
  p1YShiftZFirstLast := by
    simpa [finalZFirstP1YShiftSource] using hP0P1.p1YShiftZFirstLast
  p1Y1F0ZFirstTail := by
    simpa [finalZFirstP1Y1F0Source] using hP0P1.p1Y1F0ZFirstTail
  p1Y2F2ZFirstTail := by
    simpa [finalZFirstP1Y2F2Source] using hP0P1.p1Y2F2ZFirstTail
  p1Y3F1ZFirstTail := by
    simpa [finalZFirstP1Y3F1Source] using hP0P1.p1Y3F1ZFirstTail

/-- Paper-prefix package mirroring §11: terminal colors, pre-final `P₀`/`P₁`,
and final-carry terminal and `P₀`/`P₁` residuals. -/
structure ResetPortFullPaperPrefixGoals
    (baseRow : ResetPortBaseRow) :
    Prop where
  preFinalTerminal : ResetPortPreFinalTerminalPrefixGoals baseRow
  preFinalP0P1 : ResetPortPreFinalP0P1RowWordPrefixGoals baseRow
  finalCarryTerminal : ResetPortFinalZFirstTerminalPrefixGoals baseRow
  finalCarryP0P1 : ResetPortFinalZFirstP0P1RowWordPrefixGoals baseRow

def resetPortFullPaperPrefixGoals_of_components
    {baseRow : ResetPortBaseRow}
    (preFinalTerminal : ResetPortPreFinalTerminalPrefixGoals baseRow)
    (preFinalP0P1 : ResetPortPreFinalP0P1RowWordPrefixGoals baseRow)
    (finalCarryTerminal : ResetPortFinalZFirstTerminalPrefixGoals baseRow)
    (finalCarryP0P1 : ResetPortFinalZFirstP0P1RowWordPrefixGoals baseRow) :
    ResetPortFullPaperPrefixGoals baseRow where
  preFinalTerminal := preFinalTerminal
  preFinalP0P1 := preFinalP0P1
  finalCarryTerminal := finalCarryTerminal
  finalCarryP0P1 := finalCarryP0P1

def resetPortFullSplitPrefixGoals_of_paperPrefixGoals
    {baseRow : ResetPortBaseRow}
    (hPrefix : ResetPortFullPaperPrefixGoals baseRow) :
    ResetPortFullSplitPrefixGoals baseRow where
  preFinal :=
    resetPortPreFinalSplitPrefixGoals_of_paperPrefixGoals
      hPrefix.preFinalTerminal hPrefix.preFinalP0P1
  finalCarry :=
    resetPortFinalZFirstSplitPrefixGoals_of_paperPrefixGoals
      hPrefix.finalCarryTerminal hPrefix.finalCarryP0P1

/-- Paper-row-word read goals for the pre-final terminal colors. -/
structure ResetPortPreFinalTerminalReadGoals
    (baseRow : ResetPortBaseRow) :
    Prop where
  terminalCoreTail : TerminalCoreTailReadGoal baseRow
  terminalFirstNoFinalYFirstTail :
    ∀ i : Fin 3,
      ResetPortPreFinalTerminalFirstYTailReadOnGoal
        baseRow i (preFinalTerminalFirstYTailSource i)

/-- Paper-row-word read goals for the pre-final `P₀`/`P₁` factors. -/
structure ResetPortPreFinalP0P1RowWordReadGoals
    (baseRow : ResetPortBaseRow) :
    Prop where
  p0YShiftLast :
    ResetPortYShiftLastStepReadOnGoal
      baseRow 3 preFinalP0YShiftSource zCoord
  p0F0Tail :
    ResetPortYTerminalTailReadOnGoal
      baseRow 3 preFinalP0F0Source TerminalSymbol.F0 zCoord
  p1YShiftLast :
    ResetPortYShiftLastStepReadOnGoal
      baseRow 4 preFinalP1YShiftSource zCoord
  p1Y1F0Tail :
    ResetPortYTerminalTailReadOnGoal
      baseRow 4 preFinalP1Y1F0Source TerminalSymbol.F0 zCoord
  p1Y2F2Tail :
    ResetPortYTerminalTailReadOnGoal
      baseRow 4 preFinalP1Y2F2Source TerminalSymbol.F2 zCoord
  p1Y3F1Tail :
    ResetPortYTerminalTailReadOnGoal
      baseRow 4 preFinalP1Y3F1Source TerminalSymbol.F1 zCoord

/-- Paper-row-word read goals for the final-carry `P₀`/`P₁` factors after
the forced first `Z` step. -/
structure ResetPortFinalZFirstP0P1RowWordReadGoals
    (baseRow : ResetPortBaseRow) :
    Prop where
  p0YShiftZFirstLast :
    ResetPortFinalZFirstYShiftLastStepReadOnGoal
      baseRow 3 finalZFirstP0YShiftSource
  p0F0ZFirstTail :
    ResetPortFinalZFirstYTerminalTailReadOnGoal
      baseRow 3 finalZFirstP0F0Source TerminalSymbol.F0
  p1YShiftZFirstLast :
    ResetPortFinalZFirstYShiftLastStepReadOnGoal
      baseRow 4 finalZFirstP1YShiftSource
  p1Y1F0ZFirstTail :
    ResetPortFinalZFirstYTerminalTailReadOnGoal
      baseRow 4 finalZFirstP1Y1F0Source TerminalSymbol.F0
  p1Y2F2ZFirstTail :
    ResetPortFinalZFirstYTerminalTailReadOnGoal
      baseRow 4 finalZFirstP1Y2F2Source TerminalSymbol.F2
  p1Y3F1ZFirstTail :
    ResetPortFinalZFirstYTerminalTailReadOnGoal
      baseRow 4 finalZFirstP1Y3F1Source TerminalSymbol.F1

def resetPortPreFinalSplitReadGoals_of_paperRowWordReadGoals
    {baseRow : ResetPortBaseRow}
    (hTerminal : ResetPortPreFinalTerminalReadGoals baseRow)
    (hP0P1 : ResetPortPreFinalP0P1RowWordReadGoals baseRow) :
    ResetPortPreFinalSplitReadGoals baseRow where
  terminalCoreTail := hTerminal.terminalCoreTail
  terminalFirstNoFinalYFirstTail := fun i => by
    simpa [preFinalTerminalFirstYTailSource] using
      hTerminal.terminalFirstNoFinalYFirstTail i
  p0YShiftLast := by
    simpa [preFinalP0YShiftSource] using hP0P1.p0YShiftLast
  p0F0Tail := by
    simpa [preFinalP0F0Source] using hP0P1.p0F0Tail
  p1YShiftLast := by
    simpa [preFinalP1YShiftSource] using hP0P1.p1YShiftLast
  p1Y1F0Tail := by
    simpa [preFinalP1Y1F0Source] using hP0P1.p1Y1F0Tail
  p1Y2F2Tail := by
    simpa [preFinalP1Y2F2Source] using hP0P1.p1Y2F2Tail
  p1Y3F1Tail := by
    simpa [preFinalP1Y3F1Source] using hP0P1.p1Y3F1Tail

def resetPortFinalZFirstSplitReadGoals_of_paperRowWordReadGoals
    {baseRow : ResetPortBaseRow}
    (hP0P1 : ResetPortFinalZFirstP0P1RowWordReadGoals baseRow) :
    ResetPortFinalZFirstSplitReadGoals baseRow where
  p0YShiftZFirstLast := by
    simpa [finalZFirstP0YShiftSource] using hP0P1.p0YShiftZFirstLast
  p0F0ZFirstTail := by
    simpa [finalZFirstP0F0Source] using hP0P1.p0F0ZFirstTail
  p1YShiftZFirstLast := by
    simpa [finalZFirstP1YShiftSource] using hP0P1.p1YShiftZFirstLast
  p1Y1F0ZFirstTail := by
    simpa [finalZFirstP1Y1F0Source] using hP0P1.p1Y1F0ZFirstTail
  p1Y2F2ZFirstTail := by
    simpa [finalZFirstP1Y2F2Source] using hP0P1.p1Y2F2ZFirstTail
  p1Y3F1ZFirstTail := by
    simpa [finalZFirstP1Y3F1Source] using hP0P1.p1Y3F1ZFirstTail

/-- Paper-row-word read package mirroring §11: terminal colors, pre-final
`P₀`/`P₁`, and final-carry `P₀`/`P₁`. -/
structure ResetPortFullPaperRowWordReadGoals
    (baseRow : ResetPortBaseRow) :
    Prop where
  preFinalTerminal : ResetPortPreFinalTerminalReadGoals baseRow
  preFinalP0P1 : ResetPortPreFinalP0P1RowWordReadGoals baseRow
  finalCarryP0P1 : ResetPortFinalZFirstP0P1RowWordReadGoals baseRow

def resetPortFullPaperRowWordReadGoals_of_components
    {baseRow : ResetPortBaseRow}
    (preFinalTerminal : ResetPortPreFinalTerminalReadGoals baseRow)
    (preFinalP0P1 : ResetPortPreFinalP0P1RowWordReadGoals baseRow)
    (finalCarryP0P1 : ResetPortFinalZFirstP0P1RowWordReadGoals baseRow) :
    ResetPortFullPaperRowWordReadGoals baseRow where
  preFinalTerminal := preFinalTerminal
  preFinalP0P1 := preFinalP0P1
  finalCarryP0P1 := finalCarryP0P1

def resetPortFullSplitReadGoals_of_paperRowWordReadGoals
    {baseRow : ResetPortBaseRow}
    (hRead : ResetPortFullPaperRowWordReadGoals baseRow) :
    ResetPortFullSplitReadGoals baseRow where
  preFinal :=
    resetPortPreFinalSplitReadGoals_of_paperRowWordReadGoals
      hRead.preFinalTerminal hRead.preFinalP0P1
  finalCarry :=
    resetPortFinalZFirstSplitReadGoals_of_paperRowWordReadGoals
      hRead.finalCarryP0P1

/-- Full paper-table H2 return-realization handoff: prefix paths plus the
last-layer row-word read table. -/
structure ResetPortFullPaperTableGoals
    (baseRow : ResetPortBaseRow) :
    Prop where
  prefixGoals : ResetPortFullPaperPrefixGoals baseRow
  rowReadGoals : ResetPortFullPaperRowWordReadGoals baseRow

def resetPortFullPaperTableGoals_of_fields
    {baseRow : ResetPortBaseRow}
    (prefixGoals : ResetPortFullPaperPrefixGoals baseRow)
    (rowReadGoals : ResetPortFullPaperRowWordReadGoals baseRow) :
    ResetPortFullPaperTableGoals baseRow where
  prefixGoals := prefixGoals
  rowReadGoals := rowReadGoals

def resetPortFullPaperTableGoals_of_components
    {baseRow : ResetPortBaseRow}
    (preFinalTerminalPrefix :
      ResetPortPreFinalTerminalPrefixGoals baseRow)
    (preFinalP0P1Prefix :
      ResetPortPreFinalP0P1RowWordPrefixGoals baseRow)
    (finalCarryTerminalPrefix :
      ResetPortFinalZFirstTerminalPrefixGoals baseRow)
    (finalCarryP0P1Prefix :
      ResetPortFinalZFirstP0P1RowWordPrefixGoals baseRow)
    (preFinalTerminalRead :
      ResetPortPreFinalTerminalReadGoals baseRow)
    (preFinalP0P1Read :
      ResetPortPreFinalP0P1RowWordReadGoals baseRow)
    (finalCarryP0P1Read :
      ResetPortFinalZFirstP0P1RowWordReadGoals baseRow) :
    ResetPortFullPaperTableGoals baseRow :=
  resetPortFullPaperTableGoals_of_fields
    (resetPortFullPaperPrefixGoals_of_components
      preFinalTerminalPrefix
      preFinalP0P1Prefix
      finalCarryTerminalPrefix
      finalCarryP0P1Prefix)
    (resetPortFullPaperRowWordReadGoals_of_components
      preFinalTerminalRead
      preFinalP0P1Read
      finalCarryP0P1Read)

def ResetPortFullPaperTableGoals.splitPrefixGoals
    {baseRow : ResetPortBaseRow}
    (hTable : ResetPortFullPaperTableGoals baseRow) :
    ResetPortFullSplitPrefixGoals baseRow :=
  resetPortFullSplitPrefixGoals_of_paperPrefixGoals
    hTable.prefixGoals

def ResetPortFullPaperTableGoals.splitReadGoals
    {baseRow : ResetPortBaseRow}
    (hTable : ResetPortFullPaperTableGoals baseRow) :
    ResetPortFullSplitReadGoals baseRow :=
  resetPortFullSplitReadGoals_of_paperRowWordReadGoals
    hTable.rowReadGoals

def resetPortFullSplitGoals_of_prefixRead
    {baseRow : ResetPortBaseRow}
    (hPrefix : ResetPortFullSplitPrefixGoals baseRow)
    (hRead : ResetPortFullSplitReadGoals baseRow) :
    ResetPortFullCoreYFirstZFirstTailSplitRowWordGoals baseRow where
  preFinal :=
    resetPortPreFinalSplitGoals_of_prefixRead
      hPrefix.preFinal hRead.preFinal
  finalCarry :=
    resetPortFinalZFirstSplitGoals_of_prefixRead
      hPrefix.finalCarry hRead.finalCarry

def ResetPortFullPaperTableGoals.splitGoals
    {baseRow : ResetPortBaseRow}
    (hTable : ResetPortFullPaperTableGoals baseRow) :
    ResetPortFullCoreYFirstZFirstTailSplitRowWordGoals baseRow :=
  resetPortFullSplitGoals_of_prefixRead
    hTable.splitPrefixGoals hTable.splitReadGoals

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortBaseFullCoreZFirstTailGoals
    (baseRow : ResetPortBaseRow)
    (hLayer : ResetPortLayerBijectiveGoal baseRow)
    (hGoals : ResetPortFullCoreZFirstTailRowWordGoals baseRow) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePreFinalFinalCarry
    baseRow hLayer
    (resetPortPreFinalRealizationGoal_of_coreSplitTailRowWordGoals
      hGoals.preFinal)
    (resetPortFinalCarryRealizationGoal_of_rowWordSplitPathGoals
      baseRow
      (resetPortFinalCarryRowWordSplitPathGoals_of_zFirstTail
        hGoals.finalCarry))

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortBaseFullCoreYFirstZFirstTailGoals
    (baseRow : ResetPortBaseRow)
    (hLayer : ResetPortLayerBijectiveGoal baseRow)
    (hGoals : ResetPortFullCoreYFirstZFirstTailRowWordGoals baseRow) :
    FinalLowD5M4RootFlatCertificateFamily :=
    finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePreFinalFinalCarry
      baseRow hLayer
      (resetPortPreFinalRealizationGoal_of_coreYFirstTailRowWordGoals
        hGoals.preFinal)
      (resetPortFinalCarryRealizationGoal_of_rowWordSplitPathGoals
        baseRow
        (resetPortFinalCarryRowWordSplitPathGoals_of_zFirstTail
          hGoals.finalCarry))

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortBaseFullCoreYFirstZFirstTailSplitGoals
    (baseRow : ResetPortBaseRow)
    (hLayer : ResetPortLayerBijectiveGoal baseRow)
    (hGoals : ResetPortFullCoreYFirstZFirstTailSplitRowWordGoals baseRow) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePreFinalFinalCarry
    baseRow hLayer
    (resetPortPreFinalRealizationGoal_of_coreYFirstTailSplitRowWordGoals
      hGoals.preFinal)
    (resetPortFinalCarryRealizationGoal_of_zFirstTailSplitRowWordGoals
      hGoals.finalCarry)

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePrefixReadGoals
    (baseRow : ResetPortBaseRow)
    (hLayer : ResetPortLayerBijectiveGoal baseRow)
    (hPrefix : ResetPortFullSplitPrefixGoals baseRow)
    (hRead : ResetPortFullSplitReadGoals baseRow) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortBaseFullCoreYFirstZFirstTailSplitGoals
    baseRow hLayer
    (resetPortFullSplitGoals_of_prefixRead hPrefix hRead)

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePaperTableGoals
    (baseRow : ResetPortBaseRow)
    (hLayer : ResetPortLayerBijectiveGoal baseRow)
    (hTable : ResetPortFullPaperTableGoals baseRow) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePrefixReadGoals
    baseRow hLayer
    hTable.splitPrefixGoals
    hTable.splitReadGoals

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePaperTableFields
    (baseRow : ResetPortBaseRow)
    (hLayer : ResetPortLayerBijectiveGoal baseRow)
    (prefixGoals : ResetPortFullPaperPrefixGoals baseRow)
    (rowReadGoals : ResetPortFullPaperRowWordReadGoals baseRow) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePaperTableGoals
    baseRow hLayer
    (resetPortFullPaperTableGoals_of_fields prefixGoals rowReadGoals)

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortBaseFullRowWordSplitPathGoal
    (baseRow : ResetPortBaseRow)
    (hLayer : ResetPortLayerBijectiveGoal baseRow)
    (hPaths : ResetPortFullRowWordSplitPathGoals baseRow) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePreFinalFinalCarry
    baseRow hLayer
    (resetPortPreFinalRealizationGoal_of_rowWordSplitPathGoals
      baseRow hPaths.preFinal)
    (resetPortFinalCarryRealizationGoal_of_rowWordSplitPathGoals
      baseRow hPaths.finalCarry)

/-- H2 realization data after RF2/layer-bijectivity has already been closed,
with the switching-ribbon prefixes and concrete row-word reads kept separate. -/
structure ResetPortH2PrefixReadData where
  baseRow : ResetPortBaseRow
  layerBijective : ResetPortLayerBijectiveGoal baseRow
  prefixGoals : ResetPortFullSplitPrefixGoals baseRow
  readGoals : ResetPortFullSplitReadGoals baseRow

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PrefixReadData
    (data : ResetPortH2PrefixReadData) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePrefixReadGoals
    data.baseRow data.layerBijective data.prefixGoals data.readGoals

/-- H2 realization data using the paper-row-word read table rather than the
fully expanded split read fields. -/
structure ResetPortH2PrefixRowReadData where
  baseRow : ResetPortBaseRow
  layerBijective : ResetPortLayerBijectiveGoal baseRow
  prefixGoals : ResetPortFullSplitPrefixGoals baseRow
  rowReadGoals : ResetPortFullPaperRowWordReadGoals baseRow

def resetPortH2PrefixReadData_of_prefixRowReadData
    (data : ResetPortH2PrefixRowReadData) :
    ResetPortH2PrefixReadData where
  baseRow := data.baseRow
  layerBijective := data.layerBijective
  prefixGoals := data.prefixGoals
  readGoals :=
    resetPortFullSplitReadGoals_of_paperRowWordReadGoals
      data.rowReadGoals

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PrefixRowRead
    (data : ResetPortH2PrefixRowReadData) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PrefixReadData
    (resetPortH2PrefixReadData_of_prefixRowReadData data)

/-- H2 realization data using the paper table for both prefix paths and
last-layer row-word reads. -/
structure ResetPortH2PrefixTableData where
  baseRow : ResetPortBaseRow
  layerBijective : ResetPortLayerBijectiveGoal baseRow
  tableGoals : ResetPortFullPaperTableGoals baseRow

def resetPortH2PrefixRowReadData_of_prefixTableData
    (data : ResetPortH2PrefixTableData) :
    ResetPortH2PrefixRowReadData where
  baseRow := data.baseRow
  layerBijective := data.layerBijective
  prefixGoals :=
    resetPortFullSplitPrefixGoals_of_paperPrefixGoals
      data.tableGoals.prefixGoals
  rowReadGoals := data.tableGoals.rowReadGoals

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PrefixTable
    (data : ResetPortH2PrefixTableData) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePaperTableGoals
    data.baseRow data.layerBijective data.tableGoals

/-- A paper §11 realization package for the H2 `D5(4)` slot. The data are the
physical reset-port row schedule, RF2/layer-bijectivity for that schedule, and
the switching-ribbon path goals after the pre-final/final-carry row-word split. -/
structure ResetPortH2RealizationData where
  baseRow : ResetPortBaseRow
  layerBijective : ResetPortLayerBijectiveGoal baseRow
  paths : ResetPortFullRowWordSplitPathGoals baseRow

/-- Paper-facing H2 realization data. Compared with `ResetPortH2RealizationData`,
this keeps RF2 in the form used by the paper's partial-exchange lemma. -/
structure ResetPortH2PaperRealizationData where
  baseRow : ResetPortBaseRow
  layerData : ResetPortPartialExchangeLayerData baseRow
  paths : ResetPortFullRowWordSplitPathGoals baseRow

def resetPortH2RealizationData_of_paperRealizationData
    (data : ResetPortH2PaperRealizationData) :
    ResetPortH2RealizationData where
  baseRow := data.baseRow
  layerBijective :=
    resetPortLayerBijective_of_partialExchangeLayerData
      data.baseRow data.layerData
  paths := data.paths

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortH2RealizationData
    (data : ResetPortH2RealizationData) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortBaseFullRowWordSplitPathGoal
    data.baseRow data.layerBijective data.paths

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperRealizationData
    (data : ResetPortH2PaperRealizationData) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortH2RealizationData
    (resetPortH2RealizationData_of_paperRealizationData data)

/-- Paper-facing H2 data with the `P₀`/`P₁` terminal factors supplied directly in
collapsed terminal-tail form. -/
structure ResetPortH2PaperTailRealizationData where
  baseRow : ResetPortBaseRow
  layerData : ResetPortPartialExchangeLayerData baseRow
  paths : ResetPortFullTailRowWordSplitPathGoals baseRow

def resetPortH2PaperRealizationData_of_tailRealizationData
    (data : ResetPortH2PaperTailRealizationData) :
    ResetPortH2PaperRealizationData where
  baseRow := data.baseRow
  layerData := data.layerData
  paths := resetPortFullRowWordSplitPathGoals_of_tail data.paths

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperTailRealizationData
    (data : ResetPortH2PaperTailRealizationData) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperRealizationData
    (resetPortH2PaperRealizationData_of_tailRealizationData data)

/-- Most paper-specialized H2 handoff currently exposed: RF2 is supplied as
single-site switching data and the `P₀`/`P₁` factors are supplied in collapsed
terminal-tail form. -/
structure ResetPortH2PaperSingletonTailRealizationData where
  baseRow : ResetPortBaseRow
  layerData : ResetPortSingletonSwitchLayerData baseRow
  paths : ResetPortFullTailRowWordSplitPathGoals baseRow

def resetPortH2PaperTailRealizationData_of_singletonTailRealizationData
    (data : ResetPortH2PaperSingletonTailRealizationData) :
    ResetPortH2PaperTailRealizationData where
  baseRow := data.baseRow
  layerData :=
    resetPortPartialExchangeLayerData_of_singletonSwitchLayerData
      data.baseRow data.layerData
  paths := data.paths

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperSingletonTailRealizationData
    (data : ResetPortH2PaperSingletonTailRealizationData) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperTailRealizationData
    (resetPortH2PaperTailRealizationData_of_singletonTailRealizationData data)

/-- Singleton RF2 H2 data with the terminal no-reset core split out of the
pre-final terminal no-first obligation. -/
structure ResetPortH2PaperSingletonCoreSplitTailRealizationData where
  baseRow : ResetPortBaseRow
  layerData : ResetPortSingletonSwitchLayerData baseRow
  goals : ResetPortFullCoreSplitTailRowWordGoals baseRow

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperSingletonCoreSplitData
    (data : ResetPortH2PaperSingletonCoreSplitTailRealizationData) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortBaseFullCoreSplitTailRowWordGoals
    data.baseRow
    (resetPortLayerBijective_of_singletonSwitchLayerData
      data.baseRow data.layerData)
    data.goals

/-- Singleton RF2 H2 data with the pre-final terminal core split and the
final-carry terminal `z += 1` first step split. -/
structure ResetPortH2PaperSingletonCoreZFirstTailData where
  baseRow : ResetPortBaseRow
  layerData : ResetPortSingletonSwitchLayerData baseRow
  goals : ResetPortFullCoreZFirstTailRowWordGoals baseRow

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperSingletonCoreZFirstData
    (data : ResetPortH2PaperSingletonCoreZFirstTailData) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortBaseFullCoreZFirstTailGoals
    data.baseRow
    (resetPortLayerBijective_of_singletonSwitchLayerData
      data.baseRow data.layerData)
    data.goals

/-- Most decomposed singleton-RF2 §11 H2 handoff: pre-final terminal first-`Y`
tail goals and final-carry first-`Z` residuals. -/
structure ResetPortH2PaperSingletonCoreYFirstZFirstTailData where
  baseRow : ResetPortBaseRow
  layerData : ResetPortSingletonSwitchLayerData baseRow
  goals : ResetPortFullCoreYFirstZFirstTailRowWordGoals baseRow

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperSingletonCoreYFirstZFirstData
    (data : ResetPortH2PaperSingletonCoreYFirstZFirstTailData) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortBaseFullCoreYFirstZFirstTailGoals
    data.baseRow
    (resetPortLayerBijective_of_singletonSwitchLayerData
      data.baseRow data.layerData)
    data.goals

/-- Paper §11 H2 handoff using RF2 class (ii) directly: every layer/color row
is supplied as a skew-product lift in the paper seed coordinates, and the
return-map calculation is supplied in the core-Y-first/Z-first tail form. -/
structure ResetPortH2PaperSkewProductCoreYFirstZFirstTailData where
  baseRow : ResetPortBaseRow
  layerData : ResetPortLayerSkewProductData baseRow
  goals : ResetPortFullCoreYFirstZFirstTailRowWordGoals baseRow

/-- Paper §11 H2 handoff using direct layer equivalence RF2 data.  This is the
compatibility form after RF2 has already been transported to explicit root-state
equivalences. -/
structure ResetPortH2PaperLayerEquivCoreYFirstZFirstTailData where
  baseRow : ResetPortBaseRow
  layerData : ResetPortLayerEquivData baseRow
  goals : ResetPortFullCoreYFirstZFirstTailRowWordGoals baseRow

noncomputable def resetPortH2PaperLayerEquivCoreYFirstZFirstTailData_of_skewProductData
    (data : ResetPortH2PaperSkewProductCoreYFirstZFirstTailData) :
    ResetPortH2PaperLayerEquivCoreYFirstZFirstTailData where
  baseRow := data.baseRow
  layerData :=
    resetPortLayerEquivData_of_layerSkewProductData
      data.baseRow data.layerData
  goals := data.goals

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperLayerEquivCoreYFirstZFirstData
    (data : ResetPortH2PaperLayerEquivCoreYFirstZFirstTailData) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortBaseFullCoreYFirstZFirstTailGoals
    data.baseRow
    (resetPortLayerBijective_of_layerEquivData
      data.baseRow data.layerData)
    data.goals

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperSkewProductCoreYFirstZFirstData
    (data : ResetPortH2PaperSkewProductCoreYFirstZFirstTailData) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperLayerEquivCoreYFirstZFirstData
    (resetPortH2PaperLayerEquivCoreYFirstZFirstTailData_of_skewProductData data)

/-- Layer-equivalence RF2 H2 data with split row-word goals. This is the same
paper handoff as `ResetPortH2PaperLayerEquivCoreYFirstZFirstTailData`, but the
collapsed-tail path prefixes and last-layer row-word reads are separate. -/
structure ResetPortH2PaperLayerEquivCoreYFirstZFirstTailSplitData where
  baseRow : ResetPortBaseRow
  layerData : ResetPortLayerEquivData baseRow
  goals : ResetPortFullCoreYFirstZFirstTailSplitRowWordGoals baseRow

def resetPortH2PaperLayerEquivCoreYFirstZFirstTailData_of_splitData
    (data : ResetPortH2PaperLayerEquivCoreYFirstZFirstTailSplitData) :
    ResetPortH2PaperLayerEquivCoreYFirstZFirstTailData where
  baseRow := data.baseRow
  layerData := data.layerData
  goals := resetPortFullCoreYFirstZFirstTailRowWordGoals_of_split
    data.goals

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperLayerEquivCoreYFirstZFirstSplitData
    (data : ResetPortH2PaperLayerEquivCoreYFirstZFirstTailSplitData) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortBaseFullCoreYFirstZFirstTailSplitGoals
    data.baseRow
    (resetPortLayerBijective_of_layerEquivData
      data.baseRow data.layerData)
    data.goals

/-- Layer-equivalence RF2 H2 data with the prefix and last-layer read handoffs
kept separate. Use this when RF2 has already been transported to root-state
equivalences, but the switching-ribbon and row-word-read proofs are still
developed independently. -/
structure ResetPortH2PaperLayerEquivPrefixReadData where
  baseRow : ResetPortBaseRow
  layerData : ResetPortLayerEquivData baseRow
  prefixGoals : ResetPortFullSplitPrefixGoals baseRow
  readGoals : ResetPortFullSplitReadGoals baseRow

def resetPortH2PrefixReadData_of_layerEquivPrefixReadData
    (data : ResetPortH2PaperLayerEquivPrefixReadData) :
    ResetPortH2PrefixReadData where
  baseRow := data.baseRow
  layerBijective :=
    resetPortLayerBijective_of_layerEquivData
      data.baseRow data.layerData
  prefixGoals := data.prefixGoals
  readGoals := data.readGoals

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperLayerEquivPrefixRead
    (data : ResetPortH2PaperLayerEquivPrefixReadData) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PrefixReadData
    (resetPortH2PrefixReadData_of_layerEquivPrefixReadData data)

/-- Layer-equivalence RF2 H2 data using the paper-row-word read table. -/
structure ResetPortH2LayerEquivPrefixRowReadData where
  baseRow : ResetPortBaseRow
  layerData : ResetPortLayerEquivData baseRow
  prefixGoals : ResetPortFullSplitPrefixGoals baseRow
  rowReadGoals : ResetPortFullPaperRowWordReadGoals baseRow

def resetPortH2PrefixRowReadData_of_layerEquivPrefixRowReadData
    (data : ResetPortH2LayerEquivPrefixRowReadData) :
    ResetPortH2PrefixRowReadData where
  baseRow := data.baseRow
  layerBijective :=
    resetPortLayerBijective_of_layerEquivData
      data.baseRow data.layerData
  prefixGoals := data.prefixGoals
  rowReadGoals := data.rowReadGoals

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortH2LayerEquivPrefixRowRead
    (data : ResetPortH2LayerEquivPrefixRowReadData) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PrefixRowRead
    (resetPortH2PrefixRowReadData_of_layerEquivPrefixRowReadData data)

/-- Layer-equivalence RF2 H2 data using the full paper-table handoff. -/
structure ResetPortH2LayerEquivPrefixTableData where
  baseRow : ResetPortBaseRow
  layerData : ResetPortLayerEquivData baseRow
  tableGoals : ResetPortFullPaperTableGoals baseRow

def resetPortH2PrefixTableData_of_layerEquivPrefixTableData
    (data : ResetPortH2LayerEquivPrefixTableData) :
    ResetPortH2PrefixTableData where
  baseRow := data.baseRow
  layerBijective :=
    resetPortLayerBijective_of_layerEquivData
      data.baseRow data.layerData
  tableGoals := data.tableGoals

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortH2LayerEquivPrefixTable
    (data : ResetPortH2LayerEquivPrefixTableData) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePaperTableGoals
    data.baseRow
    (resetPortLayerBijective_of_layerEquivData
      data.baseRow data.layerData)
    data.tableGoals

/-- Skew-product RF2 H2 data with split row-word goals. This is the cleanest
current paper-facing H2 entry: RF2 is class (ii), and return realization is
given as residual prefixes plus last-layer row-word reads. -/
structure ResetPortH2PaperSkewProductCoreYFirstZFirstTailSplitData where
  baseRow : ResetPortBaseRow
  layerData : ResetPortLayerSkewProductData baseRow
  goals : ResetPortFullCoreYFirstZFirstTailSplitRowWordGoals baseRow

noncomputable def resetPortH2PaperLayerEquivCoreYFirstZFirstTailSplitData_of_skewProductSplitData
    (data : ResetPortH2PaperSkewProductCoreYFirstZFirstTailSplitData) :
    ResetPortH2PaperLayerEquivCoreYFirstZFirstTailSplitData where
  baseRow := data.baseRow
  layerData :=
    resetPortLayerEquivData_of_layerSkewProductData
      data.baseRow data.layerData
  goals := data.goals

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperSkewProductSplitData
    (data : ResetPortH2PaperSkewProductCoreYFirstZFirstTailSplitData) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperLayerEquivCoreYFirstZFirstSplitData
    (resetPortH2PaperLayerEquivCoreYFirstZFirstTailSplitData_of_skewProductSplitData data)

/-- Skew-product RF2 H2 data with prefix paths and last-layer row-word reads
supplied as two independent packages. This is useful when the switching-ribbon
path proof and the concrete row-word read proof are developed separately. -/
structure ResetPortH2PaperSkewProductPrefixReadData where
  baseRow : ResetPortBaseRow
  layerData : ResetPortLayerSkewProductData baseRow
  prefixGoals : ResetPortFullSplitPrefixGoals baseRow
  readGoals : ResetPortFullSplitReadGoals baseRow

noncomputable def resetPortH2PaperLayerEquivPrefixReadData_of_skewProductPrefixReadData
    (data : ResetPortH2PaperSkewProductPrefixReadData) :
    ResetPortH2PaperLayerEquivPrefixReadData where
  baseRow := data.baseRow
  layerData :=
    resetPortLayerEquivData_of_layerSkewProductData
      data.baseRow data.layerData
  prefixGoals := data.prefixGoals
  readGoals := data.readGoals

def resetPortH2PaperSkewProductSplitData_of_prefixReadData
    (data : ResetPortH2PaperSkewProductPrefixReadData) :
    ResetPortH2PaperSkewProductCoreYFirstZFirstTailSplitData where
  baseRow := data.baseRow
  layerData := data.layerData
  goals := resetPortFullSplitGoals_of_prefixRead
    data.prefixGoals data.readGoals

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperSkewProductPrefixReadData
    (data : ResetPortH2PaperSkewProductPrefixReadData) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperSkewProductSplitData
    (resetPortH2PaperSkewProductSplitData_of_prefixReadData data)

/-- Skew-product RF2 H2 data using the paper-row-word read table. This is the
most compact §11-aligned handoff exposed here. -/
structure ResetPortH2SkewProductPrefixRowReadData where
  baseRow : ResetPortBaseRow
  layerData : ResetPortLayerSkewProductData baseRow
  prefixGoals : ResetPortFullSplitPrefixGoals baseRow
  rowReadGoals : ResetPortFullPaperRowWordReadGoals baseRow

noncomputable def resetPortH2LayerEquivPrefixRowReadData_of_skewProductData
    (data : ResetPortH2SkewProductPrefixRowReadData) :
    ResetPortH2LayerEquivPrefixRowReadData where
  baseRow := data.baseRow
  layerData :=
    resetPortLayerEquivData_of_layerSkewProductData
      data.baseRow data.layerData
  prefixGoals := data.prefixGoals
  rowReadGoals := data.rowReadGoals

def resetPortH2PaperSkewProductPrefixReadData_of_prefixRowReadData
    (data : ResetPortH2SkewProductPrefixRowReadData) :
    ResetPortH2PaperSkewProductPrefixReadData where
  baseRow := data.baseRow
  layerData := data.layerData
  prefixGoals := data.prefixGoals
  readGoals :=
    resetPortFullSplitReadGoals_of_paperRowWordReadGoals
      data.rowReadGoals

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortH2SkewProductPrefixRowRead
    (data : ResetPortH2SkewProductPrefixRowReadData) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperSkewProductPrefixReadData
    (resetPortH2PaperSkewProductPrefixReadData_of_prefixRowReadData data)

/-- Skew-product RF2 H2 data using the full paper-table handoff. -/
structure ResetPortH2SkewProductPrefixTableData where
  baseRow : ResetPortBaseRow
  layerData : ResetPortLayerSkewProductData baseRow
  tableGoals : ResetPortFullPaperTableGoals baseRow

noncomputable def resetPortH2LayerEquivPrefixTableData_of_skewProductData
    (data : ResetPortH2SkewProductPrefixTableData) :
    ResetPortH2LayerEquivPrefixTableData where
  baseRow := data.baseRow
  layerData :=
    resetPortLayerEquivData_of_layerSkewProductData
      data.baseRow data.layerData
  tableGoals := data.tableGoals

def resetPortH2SkewProductPrefixRowReadData_of_prefixTableData
    (data : ResetPortH2SkewProductPrefixTableData) :
    ResetPortH2SkewProductPrefixRowReadData where
  baseRow := data.baseRow
  layerData := data.layerData
  prefixGoals :=
    resetPortFullSplitPrefixGoals_of_paperPrefixGoals
      data.tableGoals.prefixGoals
  rowReadGoals := data.tableGoals.rowReadGoals

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortH2SkewProductPrefixTable
    (data : ResetPortH2SkewProductPrefixTableData) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePaperTableGoals
    data.baseRow
    (resetPortLayerBijective_of_layerSkewProductData
      data.baseRow data.layerData)
    data.tableGoals

/-- Main-facing paper §11 H2 table data. The audited D54 reset table is already
closed in `D54ResetData`; this package contains the row family, skew-product
RF2 data, and paper prefix/read table goals that still have to be realized. -/
abbrev ResetPortH2PaperTableData :=
  ResetPortH2SkewProductPrefixTableData

theorem ResetPortH2PaperTableData.layerBijective
    (data : ResetPortH2PaperTableData) :
    ResetPortLayerBijectiveGoal data.baseRow :=
  resetPortLayerBijective_of_layerSkewProductData
    data.baseRow data.layerData

def resetPortH2PrefixTableData_of_paperTableData
    (data : ResetPortH2PaperTableData) :
    ResetPortH2PrefixTableData where
  baseRow := data.baseRow
  layerBijective := data.layerBijective
  tableGoals := data.tableGoals

def resetPortH2PaperTableData_of_fields
    (baseRow : ResetPortBaseRow)
    (layerData : ResetPortLayerSkewProductData baseRow)
    (tableGoals : ResetPortFullPaperTableGoals baseRow) :
    ResetPortH2PaperTableData where
  baseRow := baseRow
  layerData := layerData
  tableGoals := tableGoals

def resetPortH2PaperTableData_of_prefixReadFields
    (baseRow : ResetPortBaseRow)
    (layerData : ResetPortLayerSkewProductData baseRow)
    (prefixGoals : ResetPortFullPaperPrefixGoals baseRow)
    (rowReadGoals : ResetPortFullPaperRowWordReadGoals baseRow) :
    ResetPortH2PaperTableData :=
  resetPortH2PaperTableData_of_fields baseRow layerData
    (resetPortFullPaperTableGoals_of_fields prefixGoals rowReadGoals)

def resetPortH2PaperTableData_of_components
    (baseRow : ResetPortBaseRow)
    (layerData : ResetPortLayerSkewProductData baseRow)
    (preFinalTerminalPrefix :
      ResetPortPreFinalTerminalPrefixGoals baseRow)
    (preFinalP0P1Prefix :
      ResetPortPreFinalP0P1RowWordPrefixGoals baseRow)
    (finalCarryTerminalPrefix :
      ResetPortFinalZFirstTerminalPrefixGoals baseRow)
    (finalCarryP0P1Prefix :
      ResetPortFinalZFirstP0P1RowWordPrefixGoals baseRow)
    (preFinalTerminalRead :
      ResetPortPreFinalTerminalReadGoals baseRow)
    (preFinalP0P1Read :
      ResetPortPreFinalP0P1RowWordReadGoals baseRow)
    (finalCarryP0P1Read :
      ResetPortFinalZFirstP0P1RowWordReadGoals baseRow) :
    ResetPortH2PaperTableData :=
  resetPortH2PaperTableData_of_fields baseRow layerData
    (resetPortFullPaperTableGoals_of_components
      preFinalTerminalPrefix
      preFinalP0P1Prefix
      finalCarryTerminalPrefix
      finalCarryP0P1Prefix
      preFinalTerminalRead
      preFinalP0P1Read
      finalCarryP0P1Read)

theorem nonempty_resetPortH2PaperTableData_of_fields
    (baseRow : ResetPortBaseRow)
    (layerData : ResetPortLayerSkewProductData baseRow)
    (tableGoals : ResetPortFullPaperTableGoals baseRow) :
    Nonempty ResetPortH2PaperTableData :=
  ⟨resetPortH2PaperTableData_of_fields baseRow layerData tableGoals⟩

theorem nonempty_resetPortH2PaperTableData_of_prefixReadFields
    (baseRow : ResetPortBaseRow)
    (layerData : ResetPortLayerSkewProductData baseRow)
    (prefixGoals : ResetPortFullPaperPrefixGoals baseRow)
    (rowReadGoals : ResetPortFullPaperRowWordReadGoals baseRow) :
    Nonempty ResetPortH2PaperTableData :=
  ⟨resetPortH2PaperTableData_of_prefixReadFields
    baseRow layerData prefixGoals rowReadGoals⟩

theorem nonempty_resetPortH2PaperTableData_of_components
    (baseRow : ResetPortBaseRow)
    (layerData : ResetPortLayerSkewProductData baseRow)
    (preFinalTerminalPrefix :
      ResetPortPreFinalTerminalPrefixGoals baseRow)
    (preFinalP0P1Prefix :
      ResetPortPreFinalP0P1RowWordPrefixGoals baseRow)
    (finalCarryTerminalPrefix :
      ResetPortFinalZFirstTerminalPrefixGoals baseRow)
    (finalCarryP0P1Prefix :
      ResetPortFinalZFirstP0P1RowWordPrefixGoals baseRow)
    (preFinalTerminalRead :
      ResetPortPreFinalTerminalReadGoals baseRow)
    (preFinalP0P1Read :
      ResetPortPreFinalP0P1RowWordReadGoals baseRow)
    (finalCarryP0P1Read :
      ResetPortFinalZFirstP0P1RowWordReadGoals baseRow) :
    Nonempty ResetPortH2PaperTableData :=
  ⟨resetPortH2PaperTableData_of_components
    baseRow
    layerData
    preFinalTerminalPrefix
    preFinalP0P1Prefix
    finalCarryTerminalPrefix
    finalCarryP0P1Prefix
    preFinalTerminalRead
    preFinalP0P1Read
    finalCarryP0P1Read⟩

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperTableData
    (data : ResetPortH2PaperTableData) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PrefixTable
    (resetPortH2PrefixTableData_of_paperTableData data)

theorem finalLowD5M4RootFlatCertificateFamily_of_nonemptyResetPortH2PaperTableData
    (hData : Nonempty ResetPortH2PaperTableData) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperTableData
    (Classical.choice hData)

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperTableFields
    (baseRow : ResetPortBaseRow)
    (layerData : ResetPortLayerSkewProductData baseRow)
    (tableGoals : ResetPortFullPaperTableGoals baseRow) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperTableData
    (resetPortH2PaperTableData_of_fields baseRow layerData tableGoals)

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperPrefixReadFields
    (baseRow : ResetPortBaseRow)
    (layerData : ResetPortLayerSkewProductData baseRow)
    (prefixGoals : ResetPortFullPaperPrefixGoals baseRow)
    (rowReadGoals : ResetPortFullPaperRowWordReadGoals baseRow) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperTableData
    (resetPortH2PaperTableData_of_prefixReadFields
      baseRow layerData prefixGoals rowReadGoals)

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperComponents
    (baseRow : ResetPortBaseRow)
    (layerData : ResetPortLayerSkewProductData baseRow)
    (preFinalTerminalPrefix :
      ResetPortPreFinalTerminalPrefixGoals baseRow)
    (preFinalP0P1Prefix :
      ResetPortPreFinalP0P1RowWordPrefixGoals baseRow)
    (finalCarryTerminalPrefix :
      ResetPortFinalZFirstTerminalPrefixGoals baseRow)
    (finalCarryP0P1Prefix :
      ResetPortFinalZFirstP0P1RowWordPrefixGoals baseRow)
    (preFinalTerminalRead :
      ResetPortPreFinalTerminalReadGoals baseRow)
    (preFinalP0P1Read :
      ResetPortPreFinalP0P1RowWordReadGoals baseRow)
    (finalCarryP0P1Read :
      ResetPortFinalZFirstP0P1RowWordReadGoals baseRow) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperTableData
    (resetPortH2PaperTableData_of_components
      baseRow
      layerData
      preFinalTerminalPrefix
      preFinalP0P1Prefix
      finalCarryTerminalPrefix
      finalCarryP0P1Prefix
      preFinalTerminalRead
      preFinalP0P1Read
      finalCarryP0P1Read)

/-- Full paper §11 H2 package: the audited D54 reset-port table certificate is
kept beside the skew-product RF2/table realization data. -/
structure ResetPortH2PaperCertificateData where
  resetTable : D54ResetTableCertificate
  baseRow : ResetPortBaseRow
  layerData : ResetPortLayerSkewProductData baseRow
  tableGoals : ResetPortFullPaperTableGoals baseRow

def resetPortH2PaperCertificateData_of_fields
    (baseRow : ResetPortBaseRow)
    (layerData : ResetPortLayerSkewProductData baseRow)
    (tableGoals : ResetPortFullPaperTableGoals baseRow) :
    ResetPortH2PaperCertificateData where
  resetTable := d54ResetTableCertificate
  baseRow := baseRow
  layerData := layerData
  tableGoals := tableGoals

def resetPortH2PaperCertificateData_of_prefixReadFields
    (baseRow : ResetPortBaseRow)
    (layerData : ResetPortLayerSkewProductData baseRow)
    (prefixGoals : ResetPortFullPaperPrefixGoals baseRow)
    (rowReadGoals : ResetPortFullPaperRowWordReadGoals baseRow) :
    ResetPortH2PaperCertificateData :=
  resetPortH2PaperCertificateData_of_fields baseRow layerData
    (resetPortFullPaperTableGoals_of_fields prefixGoals rowReadGoals)

def resetPortH2PaperCertificateData_of_components
    (baseRow : ResetPortBaseRow)
    (layerData : ResetPortLayerSkewProductData baseRow)
    (preFinalTerminalPrefix :
      ResetPortPreFinalTerminalPrefixGoals baseRow)
    (preFinalP0P1Prefix :
      ResetPortPreFinalP0P1RowWordPrefixGoals baseRow)
    (finalCarryTerminalPrefix :
      ResetPortFinalZFirstTerminalPrefixGoals baseRow)
    (finalCarryP0P1Prefix :
      ResetPortFinalZFirstP0P1RowWordPrefixGoals baseRow)
    (preFinalTerminalRead :
      ResetPortPreFinalTerminalReadGoals baseRow)
    (preFinalP0P1Read :
      ResetPortPreFinalP0P1RowWordReadGoals baseRow)
    (finalCarryP0P1Read :
      ResetPortFinalZFirstP0P1RowWordReadGoals baseRow) :
    ResetPortH2PaperCertificateData :=
  resetPortH2PaperCertificateData_of_fields baseRow layerData
    (resetPortFullPaperTableGoals_of_components
      preFinalTerminalPrefix
      preFinalP0P1Prefix
      finalCarryTerminalPrefix
      finalCarryP0P1Prefix
      preFinalTerminalRead
      preFinalP0P1Read
      finalCarryP0P1Read)

theorem ResetPortH2PaperCertificateData.resetSitesEqFirstLift
    (data : ResetPortH2PaperCertificateData) :
    d54TerminalResetSites = firstLiftSites := by
  simpa [firstLiftSites, firstLiftSiteOfIndex] using
    data.resetTable.resetSitesEqLowD5M4

theorem ResetPortH2PaperCertificateData.firstLiftSitesNodup
    (data : ResetPortH2PaperCertificateData) :
    firstLiftSites.Nodup := by
  rw [← data.resetSitesEqFirstLift]
  exact data.resetTable.resetSitesNodup

theorem ResetPortH2PaperCertificateData.firstLiftSitesDisjointSelector
    (data : ResetPortH2PaperCertificateData) :
    listsDisjoint firstLiftSites d54TerminalSelector := by
  rw [← data.resetSitesEqFirstLift]
  exact data.resetTable.resetSitesDisjointSelector

theorem ResetPortH2PaperCertificateData.finalCylindersEqFinalLift
    (data : ResetPortH2PaperCertificateData) :
    d54FinalCylinders = finalLiftCylinders := by
  simpa [finalLiftCylinders, finalLiftCylinderOfColor] using
    data.resetTable.finalCylindersEqLowD5M4

theorem ResetPortH2PaperCertificateData.finalLiftCylindersNodup
    (data : ResetPortH2PaperCertificateData) :
    finalLiftCylinders.Nodup := by
  rw [← data.finalCylindersEqFinalLift]
  exact data.resetTable.finalCylindersNodup

theorem ResetPortH2PaperCertificateData.finalLiftCylindersAvoidLiftedSelector
    (data : ResetPortH2PaperCertificateData) :
    cylindersAvoidPoints finalLiftCylinders d54LiftedSelector := by
  rw [← data.finalCylindersEqFinalLift]
  exact data.resetTable.finalCylindersAvoidLiftedSelector

theorem ResetPortH2PaperCertificateData.reservePointsAvoidFinalLiftCylinders
    (data : ResetPortH2PaperCertificateData) :
    reservesAvoidCylinders reservePoints finalLiftCylinders := by
  rw [← data.finalCylindersEqFinalLift]
  exact data.resetTable.reservePointsAvoidFinalCylinders

theorem ResetPortH2PaperCertificateData.reservePointsDisjointLiftedSelector
    (data : ResetPortH2PaperCertificateData) :
    listsDisjoint reservePoints d54LiftedSelector :=
  data.resetTable.reservePointsDisjointLiftedSelector

theorem ResetPortH2PaperCertificateData.reservePointsNodup
    (data : ResetPortH2PaperCertificateData) :
    d54ReservePoints.Nodup :=
  data.resetTable.reservePointsNodup

theorem ResetPortH2PaperCertificateData.reservePointsCount
    (data : ResetPortH2PaperCertificateData) :
    d54ReservePoints.length = 8 :=
  data.resetTable.reservePointsCount

theorem ResetPortH2PaperCertificateData.firstLiftSite_ne_selector_of_mem
    (data : ResetPortH2PaperCertificateData)
    {site selector : TerminalQ 4}
    (hSite : site ∈ firstLiftSites)
    (hSelector : selector ∈ d54TerminalSelector) :
    site ≠ selector :=
  listsDisjoint_ne_of_mem
    data.firstLiftSitesDisjointSelector hSite hSelector

theorem ResetPortH2PaperCertificateData.firstLiftSiteOfIndex_ne_selectorSite
    (data : ResetPortH2PaperCertificateData)
    (i j : Fin 3) :
    firstLiftSiteOfIndex i ≠ d54TerminalSelectorSite j :=
  data.firstLiftSite_ne_selector_of_mem
    (firstLiftSiteOfIndex_mem_firstLiftSites i)
    (d54TerminalSelectorSite_mem_d54TerminalSelector j)

theorem ResetPortH2PaperCertificateData.finalLiftCylinder_avoids_selector_of_mem
    (data : ResetPortH2PaperCertificateData)
    {cylinder : D54Cylinder} {point : D54Point}
    (hCylinder : cylinder ∈ finalLiftCylinders)
    (hPoint : point ∈ d54LiftedSelector) :
    D54ResetData.cylinderAvoidsPoint cylinder point = true :=
  cylindersAvoidPoints_avoid_of_mem
    data.finalLiftCylindersAvoidLiftedSelector hCylinder hPoint

theorem ResetPortH2PaperCertificateData.finalLiftCylinder_avoids_liftedSelectorPoint
    (data : ResetPortH2PaperCertificateData)
    (c : TorusColor 5) (i : Fin 3) :
    D54ResetData.cylinderAvoidsPoint
      (finalLiftCylinderOfColor c) (d54LiftedSelectorPointOfIndex i) =
        true :=
  data.finalLiftCylinder_avoids_selector_of_mem
    (finalLiftCylinderOfColor_mem_finalLiftCylinders c)
    (d54LiftedSelectorPointOfIndex_mem_d54LiftedSelector i)

theorem ResetPortH2PaperCertificateData.finalLiftCylinder_ne_selector_of_mem
    (data : ResetPortH2PaperCertificateData)
    {cylinder : D54Cylinder} {point : D54Point}
    (hCylinder : cylinder ∈ finalLiftCylinders)
    (hPoint : point ∈ d54LiftedSelector) :
    cylinder.q ≠ point.q ∨ cylinder.y ≠ point.y :=
  cylindersAvoidPoints_ne_or_ne_of_mem
    data.finalLiftCylindersAvoidLiftedSelector hCylinder hPoint

theorem ResetPortH2PaperCertificateData.finalLiftCylinder_ne_liftedSelectorPoint
    (data : ResetPortH2PaperCertificateData)
    (c : TorusColor 5) (i : Fin 3) :
    (finalLiftCylinderOfColor c).q ≠
        (d54LiftedSelectorPointOfIndex i).q ∨
      (finalLiftCylinderOfColor c).y ≠
        (d54LiftedSelectorPointOfIndex i).y :=
  data.finalLiftCylinder_ne_selector_of_mem
    (finalLiftCylinderOfColor_mem_finalLiftCylinders c)
    (d54LiftedSelectorPointOfIndex_mem_d54LiftedSelector i)

theorem ResetPortH2PaperCertificateData.reservePoint_avoids_finalLift_of_mem
    (data : ResetPortH2PaperCertificateData)
    {point : D54Point} {cylinder : D54Cylinder}
    (hPoint : point ∈ reservePoints)
    (hCylinder : cylinder ∈ finalLiftCylinders) :
    D54ResetData.reserveAvoidsCylinder point cylinder = true :=
  reservesAvoidCylinders_avoid_of_mem
    data.reservePointsAvoidFinalLiftCylinders hPoint hCylinder

theorem ResetPortH2PaperCertificateData.reservePoint_avoids_finalLiftCylinder
    (data : ResetPortH2PaperCertificateData)
    (role : D54ReserveRole) (c : TorusColor 5) :
    D54ResetData.reserveAvoidsCylinder
      (d54ReserveD54PointOfRole role) (finalLiftCylinderOfColor c) =
        true :=
  data.reservePoint_avoids_finalLift_of_mem
    (d54ReserveD54PointOfRole_mem_reservePoints role)
    (finalLiftCylinderOfColor_mem_finalLiftCylinders c)

theorem ResetPortH2PaperCertificateData.reservePoint_ne_finalLift_of_mem
    (data : ResetPortH2PaperCertificateData)
    {point : D54Point} {cylinder : D54Cylinder}
    (hPoint : point ∈ reservePoints)
    (hCylinder : cylinder ∈ finalLiftCylinders) :
    point.q ≠ cylinder.q ∨ point.y ≠ cylinder.y :=
  reservesAvoidCylinders_ne_or_ne_of_mem
    data.reservePointsAvoidFinalLiftCylinders hPoint hCylinder

theorem ResetPortH2PaperCertificateData.reservePoint_ne_finalLiftCylinder
    (data : ResetPortH2PaperCertificateData)
    (role : D54ReserveRole) (c : TorusColor 5) :
    (d54ReserveD54PointOfRole role).q ≠
        (finalLiftCylinderOfColor c).q ∨
      (d54ReserveD54PointOfRole role).y ≠
        (finalLiftCylinderOfColor c).y :=
  data.reservePoint_ne_finalLift_of_mem
    (d54ReserveD54PointOfRole_mem_reservePoints role)
    (finalLiftCylinderOfColor_mem_finalLiftCylinders c)

theorem ResetPortH2PaperCertificateData.reservePoint_ne_selector_of_mem
    (data : ResetPortH2PaperCertificateData)
    {point selector : D54Point}
    (hPoint : point ∈ reservePoints)
    (hSelector : selector ∈ d54LiftedSelector) :
    point ≠ selector :=
  listsDisjoint_ne_of_mem
    data.reservePointsDisjointLiftedSelector hPoint hSelector

theorem ResetPortH2PaperCertificateData.reservePoint_ne_liftedSelectorPoint
    (data : ResetPortH2PaperCertificateData)
    (role : D54ReserveRole) (i : Fin 3) :
    d54ReserveD54PointOfRole role ≠ d54LiftedSelectorPointOfIndex i :=
  data.reservePoint_ne_selector_of_mem
    (d54ReserveD54PointOfRole_mem_reservePoints role)
    (d54LiftedSelectorPointOfIndex_mem_d54LiftedSelector i)

def resetPortH2SkewProductPrefixTableData_of_paperCertificateData
    (data : ResetPortH2PaperCertificateData) :
    ResetPortH2SkewProductPrefixTableData where
  baseRow := data.baseRow
  layerData := data.layerData
  tableGoals := data.tableGoals

def resetPortH2PaperCertificateData_of_skewProductPrefixTableData
    (data : ResetPortH2SkewProductPrefixTableData) :
    ResetPortH2PaperCertificateData where
  resetTable := d54ResetTableCertificate
  baseRow := data.baseRow
  layerData := data.layerData
  tableGoals := data.tableGoals

def resetPortH2PaperCertificateData_of_paperTableData
    (data : ResetPortH2PaperTableData) :
    ResetPortH2PaperCertificateData :=
  resetPortH2PaperCertificateData_of_skewProductPrefixTableData data

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortH2PaperCertificate
    (data : ResetPortH2PaperCertificateData) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePaperTableGoals
    data.baseRow
    (resetPortLayerBijective_of_layerSkewProductData
      data.baseRow data.layerData)
    data.tableGoals

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortBaseFullRowWordSplitPathGoals
    (baseRow : ResetPortBaseRow)
    (hLayer : ResetPortLayerBijectiveGoal baseRow)
    (hPreTerminalNoFirstPath :
      ResetPortPreFinalTerminalNoFirstPathRealizationGoal baseRow)
    (hPreTerminalFirstCarryPath :
      ResetPortPreFinalTerminalFirstCarryPathRealizationGoal baseRow)
    (hPreP0YShiftPath : ResetPortPreFinalP0YShiftPathRealizationGoal baseRow)
    (hPreP0F0Path : ResetPortPreFinalP0F0PathRealizationGoal baseRow)
    (hPreP1YShiftPath : ResetPortPreFinalP1YShiftPathRealizationGoal baseRow)
    (hPreP1Y1F0Path : ResetPortPreFinalP1Y1F0PathRealizationGoal baseRow)
    (hPreP1Y2F2Path : ResetPortPreFinalP1Y2F2PathRealizationGoal baseRow)
    (hPreP1Y3F1Path : ResetPortPreFinalP1Y3F1PathRealizationGoal baseRow)
    (hFinalTerminalNoFirstPath :
      ResetPortFinalCarryTerminalNoFirstPathRealizationGoal baseRow)
    (hFinalTerminalFirstPath :
      ResetPortFinalCarryTerminalFirstPathRealizationGoal baseRow)
    (hFinalP0YShiftPath : ResetPortFinalCarryP0YShiftPathRealizationGoal baseRow)
    (hFinalP0F0Path : ResetPortFinalCarryP0F0PathRealizationGoal baseRow)
    (hFinalP1YShiftPath : ResetPortFinalCarryP1YShiftPathRealizationGoal baseRow)
    (hFinalP1Y1F0Path : ResetPortFinalCarryP1Y1F0PathRealizationGoal baseRow)
    (hFinalP1Y2F2Path : ResetPortFinalCarryP1Y2F2PathRealizationGoal baseRow)
    (hFinalP1Y3F1Path : ResetPortFinalCarryP1Y3F1PathRealizationGoal baseRow) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortBaseFullRowWordSplitPathGoal
    baseRow hLayer
    { preFinal :=
        { terminalNoFirst := hPreTerminalNoFirstPath
          terminalFirst := hPreTerminalFirstCarryPath
          p0YShift := hPreP0YShiftPath
          p0F0 := hPreP0F0Path
          p1YShift := hPreP1YShiftPath
          p1Y1F0 := hPreP1Y1F0Path
          p1Y2F2 := hPreP1Y2F2Path
          p1Y3F1 := hPreP1Y3F1Path }
      finalCarry :=
        { terminalNoFirst := hFinalTerminalNoFirstPath
          terminalFirst := hFinalTerminalFirstPath
          p0YShift := hFinalP0YShiftPath
          p0F0 := hFinalP0F0Path
          p1YShift := hFinalP1YShiftPath
          p1Y1F0 := hFinalP1Y1F0Path
          p1Y2F2 := hFinalP1Y2F2Path
          p1Y3F1 := hFinalP1Y3F1Path } }

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortBaseColorGoals
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hLayer : ResetPortLayerBijectiveGoal baseRow)
    (hTerminal : ResetPortTerminalRealizationGoal baseRow)
    (hP0 : ResetPortP0RealizationGoal baseRow)
    (hP1 : ResetPortP1RealizationGoal baseRow) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortBaseFourLayer
    baseRow hLayer
    (resetPortFourLayerRealizationGoal_of_colorGoals
      baseRow hTerminal hP0 hP1)

theorem finalLowD5M4RootFlatCertificateFamily_of_resetPortBasePathGoals
    (baseRow : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (hLayer : ResetPortLayerBijectiveGoal baseRow)
    (hTerminalPath : ResetPortTerminalPathRealizationGoal baseRow)
    (hP0Path : ResetPortP0PathRealizationGoal baseRow)
    (hP1Path : ResetPortP1PathRealizationGoal baseRow) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_resetPortBaseFourLayer
    baseRow hLayer
    (resetPortFourLayerRealizationGoal_of_pathGoals
      baseRow hTerminalPath hP0Path hP1Path)

end LowD5M4Realization
end EvenV11
