import EvenV11.TerminalA2LowMod
import EvenV11.UnitCarry
import EvenV11.D54Reset

/-!
# D5(4) parity-reset construction (H2) — scaffold

Concrete construction of the `D5(4)` root-flat certificate (paper §11), built
entirely from existing Bundle B (unit-carry) + the terminal A2 carriers.

Coordinates: `RootState = Q4 × Y × Z` with `Q4 = TerminalQ 4` (16), `Y = Z = ZMod 4`.
The five color returns are a two-stage skew tower over the terminal carriers
`F_i = terminalSymbolStep 4 (F0/F1/F2)`. See `docs/H2_D5M4_RECIPE_20260603.md`.

Status: scaffold (definitions + single-cycle obligations). Proofs TODO.
-/

namespace EvenV11
namespace LowD5M4

abbrev Q4 := TerminalQ 4
abbrev Y := ZMod 4
abbrev Z := ZMod 4

/-- The three terminal `A₂` carriers at `m = 4`, each a 16-cycle on `Q4`. -/
def F (s : TerminalSymbol) : Q4 → Q4 := terminalSymbolStep 4 s

/-- Reset sites in `Q4` (paper §11). -/
def p0 : Q4 := ((0 : ZMod 4), (0 : ZMod 4))
def p1 : Q4 := ((1 : ZMod 4), (0 : ZMod 4))
def p2 : Q4 := ((2 : ZMod 4), (2 : ZMod 4))

/-- First-stage lift `T_i` on `Q4 × Y`: `(q,y) ↦ (F_i q, y + 1_{q=p_i})`. -/
def T (s : TerminalSymbol) (pSite : Q4) : Q4 × Y → Q4 × Y :=
  additiveSkewMap (F s) (pointCarry pSite (1 : ZMod 4))

/-- `P₀ (q,y) = (F₀^{1_{y=0}} q, y+1)` — word-skew whose `Y`-monodromy is `F₀`. -/
def P0 : Q4 × Y → Q4 × Y :=
  fun qy => (if qy.2 = 0 then F TerminalSymbol.F0 qy.1 else qy.1, qy.2 + 1)

/-- `P₁ (q,y) = (F₁^{1_{y=3}} F₂^{1_{y=2}} F₀^{1_{y=1}} q, y+1)` — monodromy `W`.
At each `y` exactly one factor fires, so this flat form equals the displayed word. -/
def P1 : Q4 × Y → Q4 × Y :=
  fun qy =>
    ((if qy.2 = 1 then F TerminalSymbol.F0 qy.1
      else if qy.2 = 2 then F TerminalSymbol.F2 qy.1
      else if qy.2 = 3 then F TerminalSymbol.F1 qy.1 else qy.1), qy.2 + 1)

/-- Final-stage `Z`-lift sites `a_i ∈ Q4 × Y` (paper Table D54-reset-ports). -/
def a0 : Q4 × Y := (((0 : ZMod 4), (0 : ZMod 4)), (0 : ZMod 4))
def a1 : Q4 × Y := (((0 : ZMod 4), (0 : ZMod 4)), (1 : ZMod 4))
def a2 : Q4 × Y := (((0 : ZMod 4), (0 : ZMod 4)), (2 : ZMod 4))
def a3 : Q4 × Y := (((0 : ZMod 4), (0 : ZMod 4)), (3 : ZMod 4))
def a4 : Q4 × Y := (((0 : ZMod 4), (1 : ZMod 4)), (0 : ZMod 4))

/-- The five base returns on `Q4 × Y` (before the `Z`-lift). -/
def baseReturn : Fin 5 → (Q4 × Y → Q4 × Y)
  | 0 => T TerminalSymbol.F0 p0
  | 1 => T TerminalSymbol.F1 p1
  | 2 => T TerminalSymbol.F2 p2
  | 3 => P0
  | 4 => P1

/-- `Z`-lift site for each color. -/
def liftSite : Fin 5 → (Q4 × Y)
  | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3 | 4 => a4

/-- The five full color returns `R̂_i` on `(Q4 × Y) × Z`. -/
def fullReturn (i : Fin 5) : (Q4 × Y) × Z → (Q4 × Y) × Z :=
  additiveSkewMap (baseReturn i) (pointCarry (liftSite i) (1 : ZMod 4))

/-! ## Terminal carriers `F_i` are 16-cycles (explicit orbits, computed by `#eval`) -/

private def q (x y : ZMod 4) : Q4 := (x, y)

/-- Explicit orbit of `F₀` from `(0,0)`. -/
def f0Orbit : Fin 16 → Q4
  | 0 => q 0 0 | 1 => q 0 1 | 2 => q 3 2 | 3 => q 3 3
  | 4 => q 3 0 | 5 => q 2 1 | 6 => q 2 2 | 7 => q 1 3
  | 8 => q 1 0 | 9 => q 1 1 | 10 => q 0 2 | 11 => q 0 3
  | 12 => q 3 1 | 13 => q 2 3 | 14 => q 2 0 | _ => q 1 2

/-- Explicit orbit of `F₁` from `(0,0)`. -/
def f1Orbit : Fin 16 → Q4
  | 0 => q 0 0 | 1 => q 2 3 | 2 => q 3 3 | 3 => q 1 2
  | 4 => q 3 1 | 5 => q 0 1 | 6 => q 1 0 | 7 => q 2 0
  | 8 => q 3 0 | 9 => q 0 3 | 10 => q 1 3 | 11 => q 2 2
  | 12 => q 3 2 | 13 => q 0 2 | 14 => q 1 1 | _ => q 2 1

/-- Explicit orbit of `F₂` from `(0,0)`. -/
def f2Orbit : Fin 16 → Q4
  | 0 => q 0 0 | 1 => q 1 0 | 2 => q 2 3 | 3 => q 0 2
  | 4 => q 2 1 | 5 => q 3 0 | 6 => q 1 3 | 7 => q 3 2
  | 8 => q 0 1 | 9 => q 1 1 | 10 => q 2 0 | 11 => q 3 3
  | 12 => q 0 3 | 13 => q 1 2 | 14 => q 2 2 | _ => q 3 1

theorem f0Orbit_bijective : Function.Bijective f0Orbit := by decide
theorem f1Orbit_bijective : Function.Bijective f1Orbit := by decide
theorem f2Orbit_bijective : Function.Bijective f2Orbit := by decide

theorem f0Orbit_step : ∀ i : Fin 16, f0Orbit (i + 1) = F TerminalSymbol.F0 (f0Orbit i) := by
  decide
theorem f1Orbit_step : ∀ i : Fin 16, f1Orbit (i + 1) = F TerminalSymbol.F1 (f1Orbit i) := by
  decide
theorem f2Orbit_step : ∀ i : Fin 16, f2Orbit (i + 1) = F TerminalSymbol.F2 (f2Orbit i) := by
  decide

/-! ## First-stage single cycles `T_i` (point-carry `+1` over the `F_i` 16-cycle) -/

noncomputable def f0Coord : Shared.CycleCoordinate 16 (F TerminalSymbol.F0) :=
  Shared.CycleCoordinate.ofFinEquiv (Equiv.ofBijective f0Orbit f0Orbit_bijective) f0Orbit_step
noncomputable def f1Coord : Shared.CycleCoordinate 16 (F TerminalSymbol.F1) :=
  Shared.CycleCoordinate.ofFinEquiv (Equiv.ofBijective f1Orbit f1Orbit_bijective) f1Orbit_step
noncomputable def f2Coord : Shared.CycleCoordinate 16 (F TerminalSymbol.F2) :=
  Shared.CycleCoordinate.ofFinEquiv (Equiv.ofBijective f2Orbit f2Orbit_bijective) f2Orbit_step

theorem T0_singleCycle : Shared.IsSingleCycleMap (T TerminalSymbol.F0 p0) :=
  pointCarrySingleCycle (F TerminalSymbol.F0) f0Coord.equiv.symm (f0Coord.equiv 0) p0
    (1 : ZMod 4) (fun x => f0Coord.rank_step x) isUnit_one

theorem T1_singleCycle : Shared.IsSingleCycleMap (T TerminalSymbol.F1 p1) :=
  pointCarrySingleCycle (F TerminalSymbol.F1) f1Coord.equiv.symm (f1Coord.equiv 0) p1
    (1 : ZMod 4) (fun x => f1Coord.rank_step x) isUnit_one

theorem T2_singleCycle : Shared.IsSingleCycleMap (T TerminalSymbol.F2 p2) :=
  pointCarrySingleCycle (F TerminalSymbol.F2) f2Coord.equiv.symm (f2Coord.equiv 0) p2
    (1 : ZMod 4) (fun x => f2Coord.rank_step x) isUnit_one

/-! ## Second-stage `Z`-lift: full 256-cycles `R̂_i` (point-carry over the 64-cycle base) -/

theorem baseReturn0_singleCycle : Shared.IsSingleCycleMap (baseReturn 0) := T0_singleCycle
theorem baseReturn1_singleCycle : Shared.IsSingleCycleMap (baseReturn 1) := T1_singleCycle
theorem baseReturn2_singleCycle : Shared.IsSingleCycleMap (baseReturn 2) := T2_singleCycle

theorem fullReturn0_singleCycle : Shared.IsSingleCycleMap (fullReturn 0) :=
  Shared.single_cycle_of_skewProduct_zmod_additive_unit_sum_of_base_cycle
    (baseReturn 0) (pointCarry (liftSite 0) (1 : ZMod 4)) baseReturn0_singleCycle
    (by decide) (pointCarryUnit (liftSite 0) isUnit_one)

theorem fullReturn1_singleCycle : Shared.IsSingleCycleMap (fullReturn 1) :=
  Shared.single_cycle_of_skewProduct_zmod_additive_unit_sum_of_base_cycle
    (baseReturn 1) (pointCarry (liftSite 1) (1 : ZMod 4)) baseReturn1_singleCycle
    (by decide) (pointCarryUnit (liftSite 1) isUnit_one)

theorem fullReturn2_singleCycle : Shared.IsSingleCycleMap (fullReturn 2) :=
  Shared.single_cycle_of_skewProduct_zmod_additive_unit_sum_of_base_cycle
    (baseReturn 2) (pointCarry (liftSite 2) (1 : ZMod 4)) baseReturn2_singleCycle
    (by decide) (pointCarryUnit (liftSite 2) isUnit_one)

/-! ## `P₀`, `P₁` single cycles (fiber monodromy `F₀` / `W` over the `Y`-base) -/

/-- `P₀` with base/fiber order swapped: `(y,q) ↦ (y+1, F₀^{1_{y=0}} q)`. -/
def fiberStep0 : Y → Q4 → Q4 := fun y q => if y = 0 then F TerminalSymbol.F0 q else q
def fiberStep1 : Y → Q4 → Q4 := fun y q =>
  if y = 1 then F TerminalSymbol.F0 q
  else if y = 2 then F TerminalSymbol.F2 q
  else if y = 3 then F TerminalSymbol.F1 q else q

def P0' : Y × Q4 → Y × Q4 := Shared.skewProductMap (fun y : Y => y + 1) fiberStep0
def P1' : Y × Q4 → Y × Q4 := Shared.skewProductMap (fun y : Y => y + 1) fiberStep1

private theorem ybij : Function.Bijective (fun y : Y => y + 1) :=
  (Equiv.addRight (1 : Y)).bijective

private theorem fiber0_bij : ∀ y, Function.Bijective (fiberStep0 y) := by
  intro y
  by_cases h : y = 0
  · simpa [fiberStep0, h] using (Shared.CycleCoordinate.singleCycle f0Coord).1
  · simpa [fiberStep0, h] using Function.bijective_id

private theorem fiber1_bij : ∀ y, Function.Bijective (fiberStep1 y) := by
  intro y
  by_cases h1 : y = 1
  · simpa [fiberStep1, h1] using (Shared.CycleCoordinate.singleCycle f0Coord).1
  · by_cases h2 : y = 2
    · simpa [fiberStep1, h1, h2] using (Shared.CycleCoordinate.singleCycle f2Coord).1
    · by_cases h3 : y = 3
      · simpa [fiberStep1, h1, h2, h3] using (Shared.CycleCoordinate.singleCycle f1Coord).1
      · simpa [fiberStep1, h1, h2, h3] using Function.bijective_id

private theorem ybase_return : (fun y : Y => y + 1)^[4] 0 = 0 := by decide
private theorem ybase_cover :
    ∀ b : Y, ∃ k : Nat, k < 4 ∧ (fun y : Y => y + 1)^[k] 0 = b := by decide

theorem P0'_monodromy : Shared.sectionReturn P0' 0 4 = F TerminalSymbol.F0 := by decide
theorem P1'_monodromy :
    Shared.sectionReturn P1' 0 4 = wordEval (terminalSymbolStep 4) terminalResetTrace4 := by
  decide

theorem P0'_singleCycle : Shared.IsSingleCycleMap P0' :=
  Shared.single_cycle_of_skewProduct_base_orbit_monodromy
    (fun y : Y => y + 1) fiberStep0 0 4 ybij fiber0_bij ybase_return ybase_cover
    (by change Shared.IsSingleCycleMap (Shared.sectionReturn P0' 0 4)
        rw [P0'_monodromy]; exact Shared.CycleCoordinate.singleCycle f0Coord)

theorem P1'_singleCycle : Shared.IsSingleCycleMap P1' :=
  Shared.single_cycle_of_skewProduct_base_orbit_monodromy
    (fun y : Y => y + 1) fiberStep1 0 4 ybij fiber1_bij ybase_return ybase_cover
    (by change Shared.IsSingleCycleMap (Shared.sectionReturn P1' 0 4)
        rw [P1'_monodromy]; exact terminalResetTrace4_singleCycle)

theorem P0_singleCycle : Shared.IsSingleCycleMap P0 :=
  Shared.single_cycle_of_equiv_conj (Equiv.prodComm Y Q4) P0 P0' P0'_singleCycle
    (by intro x; obtain ⟨y, q⟩ := x
        simp [Equiv.prodComm, P0, P0', fiberStep0, Shared.skewProductMap])

theorem P1_singleCycle : Shared.IsSingleCycleMap P1 :=
  Shared.single_cycle_of_equiv_conj (Equiv.prodComm Y Q4) P1 P1' P1'_singleCycle
    (by intro x; obtain ⟨y, q⟩ := x
        simp [Equiv.prodComm, P1, P1', fiberStep1, Shared.skewProductMap])

theorem baseReturn3_singleCycle : Shared.IsSingleCycleMap (baseReturn 3) := P0_singleCycle
theorem baseReturn4_singleCycle : Shared.IsSingleCycleMap (baseReturn 4) := P1_singleCycle

theorem fullReturn3_singleCycle : Shared.IsSingleCycleMap (fullReturn 3) :=
  Shared.single_cycle_of_skewProduct_zmod_additive_unit_sum_of_base_cycle
    (baseReturn 3) (pointCarry (liftSite 3) (1 : ZMod 4)) baseReturn3_singleCycle
    (by decide) (pointCarryUnit (liftSite 3) isUnit_one)

theorem fullReturn4_singleCycle : Shared.IsSingleCycleMap (fullReturn 4) :=
  Shared.single_cycle_of_skewProduct_zmod_additive_unit_sum_of_base_cycle
    (baseReturn 4) (pointCarry (liftSite 4) (1 : ZMod 4)) baseReturn4_singleCycle
    (by decide) (pointCarryUnit (liftSite 4) isUnit_one)

/-- All five color returns are single cycles (256-cycles on `Q4 × Y × Z`). -/
theorem fullReturn_singleCycle : ∀ i : Fin 5, Shared.IsSingleCycleMap (fullReturn i)
  | 0 => fullReturn0_singleCycle
  | 1 => fullReturn1_singleCycle
  | 2 => fullReturn2_singleCycle
  | 3 => fullReturn3_singleCycle
  | 4 => fullReturn4_singleCycle

end LowD5M4
end EvenV11
