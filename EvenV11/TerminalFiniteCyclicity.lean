import EvenV11.TerminalA2LowMod
import EvenV11.UnitCarry

/-!
# Terminal A₂ finite cyclicity (paper low-modulus / rank-three checks)

Faithful Lean port of the finite terminal-word cyclicity verified by
`scripts/verify_finite_checks.py` (`check_terminal_words`) and used by
`lem:terminal-m4-finite-check`, `lem:small-terminal-marked-parents`,
`lem:rank-three-folded-word-verification`:
* the three terminal carriers `Fᵢ = terminalReturn` are `m²`-cycles at `m=6`;
* the rank-three folded words `W₄ = F₁F₀²` (16-cycle, `m=4`) and
  `W₆ = F₁²F₀³` (36-cycle, `m=6`) are full cycles.
Explicit orbits + `decide` (Seed pattern); no proof holes, no `native_decide`.
-/

set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

namespace EvenV11
namespace TerminalFiniteCyclicity

open EvenV11

def F4 (i : Fin 3) : TerminalQ 4 → TerminalQ 4 := terminalReturn (m := 4) i
def F6 (i : Fin 3) : TerminalQ 6 → TerminalQ 6 := terminalReturn (m := 6) i
def W4 : TerminalQ 4 → TerminalQ 4 := fun z => F4 1 (F4 0 (F4 0 z))
def W6 : TerminalQ 6 → TerminalQ 6 := fun z => F6 1 (F6 1 (F6 0 (F6 0 (F6 0 z))))

/-! ## Rank-three folded words -/

def w4Orbit : Fin 16 → TerminalQ 4
  | 0 => (0, 0)
  | 1 => (0, 2)
  | 2 => (0, 1)
  | 3 => (1, 2)
  | 4 => (1, 0)
  | 5 => (1, 1)
  | 6 => (1, 3)
  | 7 => (2, 1)
  | 8 => (2, 2)
  | 9 => (2, 0)
  | 10 => (2, 3)
  | 11 => (3, 1)
  | 12 => (3, 0)
  | 13 => (3, 2)
  | 14 => (0, 3)
  | _ => (3, 3)
theorem w4Orbit_bijective : Function.Bijective w4Orbit := by decide
theorem w4Orbit_step : ∀ i : Fin 16, w4Orbit (i + 1) = W4 (w4Orbit i) := by
  decide
noncomputable def w4Coord : Shared.CycleCoordinate 16 W4 :=
  Shared.CycleCoordinate.ofFinEquiv (Equiv.ofBijective w4Orbit w4Orbit_bijective) w4Orbit_step
/-- `W4` is a single 16-cycle on `TerminalQ 4` (paper finite check). -/
theorem w4_singleCycle : Shared.IsSingleCycleMap W4 :=
  Shared.CycleCoordinate.singleCycle w4Coord

def w6Orbit : Fin 36 → TerminalQ 6
  | 0 => (0, 0)
  | 1 => (3, 1)
  | 2 => (4, 5)
  | 3 => (4, 4)
  | 4 => (4, 3)
  | 5 => (5, 1)
  | 6 => (0, 3)
  | 7 => (1, 0)
  | 8 => (2, 2)
  | 9 => (3, 5)
  | 10 => (4, 2)
  | 11 => (2, 3)
  | 12 => (5, 5)
  | 13 => (0, 2)
  | 14 => (1, 5)
  | 15 => (2, 1)
  | 16 => (3, 4)
  | 17 => (5, 0)
  | 18 => (1, 2)
  | 19 => (2, 5)
  | 20 => (3, 3)
  | 21 => (0, 5)
  | 22 => (1, 1)
  | 23 => (1, 4)
  | 24 => (4, 0)
  | 25 => (5, 3)
  | 26 => (0, 1)
  | 27 => (1, 3)
  | 28 => (3, 0)
  | 29 => (3, 2)
  | 30 => (0, 4)
  | 31 => (2, 0)
  | 32 => (2, 4)
  | 33 => (4, 1)
  | 34 => (5, 4)
  | _ => (5, 2)
theorem w6Orbit_bijective : Function.Bijective w6Orbit := by decide
theorem w6Orbit_step : ∀ i : Fin 36, w6Orbit (i + 1) = W6 (w6Orbit i) := by
  decide
noncomputable def w6Coord : Shared.CycleCoordinate 36 W6 :=
  Shared.CycleCoordinate.ofFinEquiv (Equiv.ofBijective w6Orbit w6Orbit_bijective) w6Orbit_step
/-- `W6` is a single 36-cycle on `TerminalQ 6` (paper finite check). -/
theorem w6_singleCycle : Shared.IsSingleCycleMap W6 :=
  Shared.CycleCoordinate.singleCycle w6Coord


/-! ## `m = 4` terminal carriers (paper terminal A₂ finite check) -/

/-- The color-0 carrier orbit at `m = 4`, transcribed from the terminal `A₂`
appendix table. -/
def f4c0Orbit : Fin 16 → TerminalQ 4
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (3, 2)
  | 3 => (3, 3)
  | 4 => (3, 0)
  | 5 => (2, 1)
  | 6 => (2, 2)
  | 7 => (1, 3)
  | 8 => (1, 0)
  | 9 => (1, 1)
  | 10 => (0, 2)
  | 11 => (0, 3)
  | 12 => (3, 1)
  | 13 => (2, 3)
  | 14 => (2, 0)
  | _ => (1, 2)

theorem f4c0Orbit_bijective : Function.Bijective f4c0Orbit := by
  decide

theorem f4c0Orbit_step : ∀ i : Fin 16, f4c0Orbit (i + 1) = (F4 0) (f4c0Orbit i) := by
  decide

noncomputable def f4c0Coord : Shared.CycleCoordinate 16 (F4 0) :=
  Shared.CycleCoordinate.ofFinEquiv
    (Equiv.ofBijective f4c0Orbit f4c0Orbit_bijective) f4c0Orbit_step

/-- `(F4 0)` is a single 16-cycle on `TerminalQ 4` (paper finite check). -/
theorem f4c0_singleCycle : Shared.IsSingleCycleMap (F4 0) :=
  Shared.CycleCoordinate.singleCycle f4c0Coord

/-- The color-1 carrier orbit at `m = 4`, transcribed from the terminal `A₂`
appendix table. -/
def f4c1Orbit : Fin 16 → TerminalQ 4
  | 0 => (0, 0)
  | 1 => (2, 3)
  | 2 => (3, 3)
  | 3 => (1, 2)
  | 4 => (3, 1)
  | 5 => (0, 1)
  | 6 => (1, 0)
  | 7 => (2, 0)
  | 8 => (3, 0)
  | 9 => (0, 3)
  | 10 => (1, 3)
  | 11 => (2, 2)
  | 12 => (3, 2)
  | 13 => (0, 2)
  | 14 => (1, 1)
  | _ => (2, 1)

theorem f4c1Orbit_bijective : Function.Bijective f4c1Orbit := by
  decide

theorem f4c1Orbit_step : ∀ i : Fin 16, f4c1Orbit (i + 1) = (F4 1) (f4c1Orbit i) := by
  decide

noncomputable def f4c1Coord : Shared.CycleCoordinate 16 (F4 1) :=
  Shared.CycleCoordinate.ofFinEquiv
    (Equiv.ofBijective f4c1Orbit f4c1Orbit_bijective) f4c1Orbit_step

/-- `(F4 1)` is a single 16-cycle on `TerminalQ 4` (paper finite check). -/
theorem f4c1_singleCycle : Shared.IsSingleCycleMap (F4 1) :=
  Shared.CycleCoordinate.singleCycle f4c1Coord

/-- The color-2 carrier orbit at `m = 4`, transcribed from the terminal `A₂`
appendix table. -/
def f4c2Orbit : Fin 16 → TerminalQ 4
  | 0 => (0, 0)
  | 1 => (1, 0)
  | 2 => (2, 3)
  | 3 => (0, 2)
  | 4 => (2, 1)
  | 5 => (3, 0)
  | 6 => (1, 3)
  | 7 => (3, 2)
  | 8 => (0, 1)
  | 9 => (1, 1)
  | 10 => (2, 0)
  | 11 => (3, 3)
  | 12 => (0, 3)
  | 13 => (1, 2)
  | 14 => (2, 2)
  | _ => (3, 1)

theorem f4c2Orbit_bijective : Function.Bijective f4c2Orbit := by
  decide

theorem f4c2Orbit_step : ∀ i : Fin 16, f4c2Orbit (i + 1) = (F4 2) (f4c2Orbit i) := by
  decide

noncomputable def f4c2Coord : Shared.CycleCoordinate 16 (F4 2) :=
  Shared.CycleCoordinate.ofFinEquiv
    (Equiv.ofBijective f4c2Orbit f4c2Orbit_bijective) f4c2Orbit_step

/-- `(F4 2)` is a single 16-cycle on `TerminalQ 4` (paper finite check). -/
theorem f4c2_singleCycle : Shared.IsSingleCycleMap (F4 2) :=
  Shared.CycleCoordinate.singleCycle f4c2Coord

/-- All three `m=4` terminal carriers are 16-cycles. -/
theorem f4_all_singleCycle : ∀ i : Fin 3, Shared.IsSingleCycleMap (F4 i)
  | 0 => f4c0_singleCycle
  | 1 => f4c1_singleCycle
  | 2 => f4c2_singleCycle

/-! ## `m = 6` terminal carriers (small terminal parent) -/

def f6c0Orbit : Fin 36 → TerminalQ 6
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (5, 2)
  | 3 => (5, 3)
  | 4 => (5, 4)
  | 5 => (4, 0)
  | 6 => (4, 1)
  | 7 => (3, 2)
  | 8 => (3, 3)
  | 9 => (3, 4)
  | 10 => (3, 5)
  | 11 => (3, 0)
  | 12 => (2, 1)
  | 13 => (2, 2)
  | 14 => (1, 3)
  | 15 => (1, 4)
  | 16 => (1, 5)
  | 17 => (1, 0)
  | 18 => (1, 1)
  | 19 => (0, 2)
  | 20 => (0, 3)
  | 21 => (5, 5)
  | 22 => (5, 0)
  | 23 => (5, 1)
  | 24 => (4, 2)
  | 25 => (4, 3)
  | 26 => (4, 4)
  | 27 => (4, 5)
  | 28 => (3, 1)
  | 29 => (2, 3)
  | 30 => (2, 4)
  | 31 => (2, 5)
  | 32 => (2, 0)
  | 33 => (1, 2)
  | 34 => (0, 4)
  | _ => (0, 5)
theorem f6c0Orbit_bijective : Function.Bijective f6c0Orbit := by decide
theorem f6c0Orbit_step : ∀ i : Fin 36, f6c0Orbit (i + 1) = (F6 0) (f6c0Orbit i) := by
  decide
noncomputable def f6c0Coord : Shared.CycleCoordinate 36 (F6 0) :=
  Shared.CycleCoordinate.ofFinEquiv (Equiv.ofBijective f6c0Orbit f6c0Orbit_bijective) f6c0Orbit_step
/-- `(F6 0)` is a single 36-cycle on `TerminalQ 6` (paper finite check). -/
theorem f6c0_singleCycle : Shared.IsSingleCycleMap (F6 0) :=
  Shared.CycleCoordinate.singleCycle f6c0Coord

def f6c1Orbit : Fin 36 → TerminalQ 6
  | 0 => (0, 0)
  | 1 => (1, 5)
  | 2 => (2, 5)
  | 3 => (3, 5)
  | 4 => (4, 5)
  | 5 => (0, 4)
  | 6 => (2, 3)
  | 7 => (3, 3)
  | 8 => (4, 3)
  | 9 => (5, 3)
  | 10 => (1, 2)
  | 11 => (3, 1)
  | 12 => (4, 1)
  | 13 => (5, 1)
  | 14 => (0, 1)
  | 15 => (1, 0)
  | 16 => (2, 0)
  | 17 => (3, 0)
  | 18 => (5, 5)
  | 19 => (0, 5)
  | 20 => (1, 4)
  | 21 => (2, 4)
  | 22 => (3, 4)
  | 23 => (4, 4)
  | 24 => (5, 4)
  | 25 => (0, 3)
  | 26 => (1, 3)
  | 27 => (2, 2)
  | 28 => (3, 2)
  | 29 => (4, 2)
  | 30 => (5, 2)
  | 31 => (0, 2)
  | 32 => (1, 1)
  | 33 => (2, 1)
  | 34 => (4, 0)
  | _ => (5, 0)
theorem f6c1Orbit_bijective : Function.Bijective f6c1Orbit := by decide
theorem f6c1Orbit_step : ∀ i : Fin 36, f6c1Orbit (i + 1) = (F6 1) (f6c1Orbit i) := by
  decide
noncomputable def f6c1Coord : Shared.CycleCoordinate 36 (F6 1) :=
  Shared.CycleCoordinate.ofFinEquiv (Equiv.ofBijective f6c1Orbit f6c1Orbit_bijective) f6c1Orbit_step
/-- `(F6 1)` is a single 36-cycle on `TerminalQ 6` (paper finite check). -/
theorem f6c1_singleCycle : Shared.IsSingleCycleMap (F6 1) :=
  Shared.CycleCoordinate.singleCycle f6c1Coord

def f6c2Orbit : Fin 36 → TerminalQ 6
  | 0 => (0, 0)
  | 1 => (1, 0)
  | 2 => (2, 5)
  | 3 => (3, 4)
  | 4 => (4, 3)
  | 5 => (0, 2)
  | 6 => (2, 1)
  | 7 => (3, 0)
  | 8 => (4, 5)
  | 9 => (5, 4)
  | 10 => (1, 3)
  | 11 => (3, 2)
  | 12 => (4, 1)
  | 13 => (5, 0)
  | 14 => (0, 5)
  | 15 => (1, 5)
  | 16 => (2, 4)
  | 17 => (3, 3)
  | 18 => (5, 2)
  | 19 => (0, 1)
  | 20 => (1, 1)
  | 21 => (2, 0)
  | 22 => (3, 5)
  | 23 => (4, 4)
  | 24 => (5, 3)
  | 25 => (0, 3)
  | 26 => (1, 2)
  | 27 => (2, 2)
  | 28 => (3, 1)
  | 29 => (4, 0)
  | 30 => (5, 5)
  | 31 => (0, 4)
  | 32 => (1, 4)
  | 33 => (2, 3)
  | 34 => (4, 2)
  | _ => (5, 1)
theorem f6c2Orbit_bijective : Function.Bijective f6c2Orbit := by decide
theorem f6c2Orbit_step : ∀ i : Fin 36, f6c2Orbit (i + 1) = (F6 2) (f6c2Orbit i) := by
  decide
noncomputable def f6c2Coord : Shared.CycleCoordinate 36 (F6 2) :=
  Shared.CycleCoordinate.ofFinEquiv (Equiv.ofBijective f6c2Orbit f6c2Orbit_bijective) f6c2Orbit_step
/-- `(F6 2)` is a single 36-cycle on `TerminalQ 6` (paper finite check). -/
theorem f6c2_singleCycle : Shared.IsSingleCycleMap (F6 2) :=
  Shared.CycleCoordinate.singleCycle f6c2Coord

/-- All three `m=6` terminal carriers are 36-cycles. -/
theorem f6_all_singleCycle : ∀ i : Fin 3, Shared.IsSingleCycleMap (F6 i)
  | 0 => f6c0_singleCycle
  | 1 => f6c1_singleCycle
  | 2 => f6c2_singleCycle

end TerminalFiniteCyclicity
end EvenV11
