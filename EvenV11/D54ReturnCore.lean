import EvenV11.D54ResetData
import EvenV11.LowD5M4RibbonInterface
import EvenV11.StandardRootFlatLift

/-!
# D5(4) H2 return core and paper-realization handoff

This module fixes the notation used in the paper supplement against the Lean
objects that already exist in `LowD5M4Seed`.

The split is intentional:

* `F`, `Rbase`, `Rhat`, and `W` are the finite return-level core.  Their
  cyclicity is already proved in `LowD5M4Seed`/`D54Reset`.
* `D54ProductBaseRealization`, `D54FiveSwitchRealization`, and
  `D54PaperRealization` are the remaining paper-facing row/ribbon handoff
  targets.  Filling one of these gives the existing H2 structural certificate.
-/

namespace EvenV11
namespace H2
namespace D54

open Shared
open LowD5M4RibbonInterface
open LowD5M4Structural

abbrev Z4 := ZMod 4
abbrev Q4 := LowD5M4.Q4
abbrev Y4 := LowD5M4.Y
abbrev Zed4 := LowD5M4.Z
abbrev X4 := Q4 × Y4
abbrev Seed := LowD5M4Structural.Seed
abbrev RootState := LowD5M4Structural.RootState
abbrev TerminalRootState := Fin 2 → Z4

/-- The terminal symbols indexed as in the supplement: `0,1,2 = F0,F1,F2`. -/
def terminalSymbol : Fin 3 → TerminalSymbol
  | 0 => TerminalSymbol.F0
  | 1 => TerminalSymbol.F1
  | 2 => TerminalSymbol.F2

/-- The three collapsed terminal returns on `Q4`. -/
def F (i : Fin 3) : Q4 → Q4 :=
  LowD5M4.F (terminalSymbol i)

/-- The `D54ReturnCore` terminal maps are exactly the paper's collapsed
terminal returns at `m = 4`, not a separate generated convention. -/
theorem F_eq_terminalReturn (i : Fin 3) (q : Q4) :
    F i q = terminalReturn (m := 4) i q := by
  fin_cases i <;>
    simp [F, terminalSymbol, LowD5M4.F, terminalSymbolStep]

theorem F_fun_eq_terminalReturn (i : Fin 3) :
    F i = terminalReturn (m := 4) i := by
  funext q
  exact F_eq_terminalReturn i q

/-- Reset sites `p_i` used in the first `Y`-lift. -/
def pReset : Fin 3 → Q4
  | 0 => LowD5M4.p0
  | 1 => LowD5M4.p1
  | 2 => LowD5M4.p2

/-- First `Y`-lift maps `T_i`. -/
def T (i : Fin 3) : X4 → X4 :=
  LowD5M4.T (terminalSymbol i) (pReset i)

/-- The two row-color base returns from the supplement. -/
abbrev P0 : X4 → X4 := LowD5M4.P0
abbrev P1 : X4 → X4 := LowD5M4.P1

/-- The five base returns on `Q4 × Y`. -/
abbrev Rbase : Fin 5 → X4 → X4 := LowD5M4.baseReturn

/-- The final `Z`-lift sites `b_i`. -/
abbrev bSite : Fin 5 → X4 := LowD5M4.liftSite

/-- The full return maps `Rhat_i` on `Q4 × Y × Z`. -/
abbrev Rhat : Fin 5 → Seed → Seed := LowD5M4.fullReturn

/-- Product-base return before the final `Z` carry is inserted. -/
def RbaseNeutral (i : Fin 5) : Seed → Seed :=
  fun s => (Rbase i s.1, s.2)

/-- The final `Z` carry, read after the product-base return has moved the
`Q4 × Y` coordinate.  This is equivalent to the original carry at `bSite i`
because `Rbase i` is bijective. -/
def postBaseCarry (i : Fin 5) : Seed → Seed :=
  fun s =>
    (s.1,
      s.2 +
        if s.1 = Rbase i (bSite i) then
          (1 : Zed4)
        else
          0)

/-- A seed-side two-stage layer model for `Rhat`: layer `0` performs the product
base return, layer `1` performs the corresponding post-base `Z` carry, and the
remaining two layers are neutral.  The physical realization still has to prove
that its rows are conjugate to a paper switch model, but this closes the finite
return calculation of that model. -/
def seedTwoStageFullReturnLayer
    (t : ZMod 4) (c : TorusColor 5) : Seed → Seed :=
  if t = (0 : ZMod 4) then
    RbaseNeutral c
  else if t = (1 : ZMod 4) then
    postBaseCarry c
  else
    id

/-- Fold four seed-side layer maps in the same layer order as
`RootFlatSchedule.returnMap` for `m = 4`. -/
def seedLayerReturn
    (layer : ZMod 4 → TorusColor 5 → Seed → Seed)
    (c : TorusColor 5) : Seed → Seed :=
  fun s =>
    (List.range 4).foldl
      (fun x (t : Nat) => layer (t : ZMod 4) c x) s

/-- The odd reset word `W = F1 ∘ F2 ∘ F0`. -/
def W : Q4 → Q4 :=
  fun q => F 1 (F 2 (F 0 q))

/-- A two-letter terminal relation used as a conjugacy-invariant audit target:
`F0 ∘ F2` has exact order `33` on `Q4`. -/
def terminalF0F2 : Q4 → Q4 :=
  fun q => F 0 (F 2 q)

/-- Standard D3 root section coordinates for the terminal A2 block, written as
the paper pair `Q4`. -/
def terminalRootPair (w : TerminalRootState) : Q4 :=
  (w 0, w 1)

def terminalPairRoot (q : Q4) : TerminalRootState :=
  fun j => if j = (0 : Fin 2) then q.1 else q.2

@[simp] theorem terminalRootPair_terminalPairRoot (q : Q4) :
    terminalRootPair (terminalPairRoot q) = q := by
  ext <;> simp [terminalRootPair, terminalPairRoot]

@[simp] theorem terminalPairRoot_terminalRootPair
    (w : TerminalRootState) :
    terminalPairRoot (terminalRootPair w) = w := by
  funext j
  fin_cases j <;> simp [terminalRootPair, terminalPairRoot]

def terminalRootEquiv : TerminalRootState ≃ Q4 where
  toFun := terminalRootPair
  invFun := terminalPairRoot
  left_inv := terminalPairRoot_terminalRootPair
  right_inv := terminalRootPair_terminalPairRoot

/-- Standard D3 root step in the terminal root section.  Direction `0` and `1`
increment the two root coordinates; direction `2` is the last torus direction
and is neutral in the root chart. -/
def terminalStandardRootStep
    (d : TorusDirection 3) : TerminalRootState → TerminalRootState :=
  StandardRootFlatLift.rootStep (n := 2) (m := 4) d

/-- Standard D3 root-flat schedule built from an explicit terminal direction
table. -/
def terminalStandardSchedule
    (dir : ZMod 4 → TerminalRootState → TorusColor 3 → TorusDirection 3) :
    RootFlatSchedule (TorusColor 3) (TorusDirection 3) TerminalRootState 4 where
  dir := dir
  step := terminalStandardRootStep

/-- The paper terminal return transported through the plain standard root
coordinate chart.  This is a useful negative control: it is too rigid for the
paper realization. -/
def terminalFixedChartReturn
    (c : TorusColor 3) : TerminalRootState → TerminalRootState :=
  fun w =>
    terminalRootEquiv.symm
      (terminalReturn (m := 4) c (terminalRootEquiv w))

def terminalFixedChartObstructionSource : TerminalRootState :=
  terminalPairRoot (D54ResetData.d54q4 0 0)

theorem no_four_terminalStandardRootSteps_to_fixedChartReturn_color1 :
    ∀ d0 d1 d2 d3 : TorusDirection 3,
      terminalStandardRootStep d3
          (terminalStandardRootStep d2
            (terminalStandardRootStep d1
              (terminalStandardRootStep d0
                terminalFixedChartObstructionSource))) ≠
        terminalFixedChartReturn (1 : TorusColor 3)
          terminalFixedChartObstructionSource := by
  decide

theorem terminalStandardReturnMap_ne_fixedChartReturn_color1
    (dir : ZMod 4 → TerminalRootState → TorusColor 3 → TorusDirection 3) :
    (terminalStandardSchedule dir).returnMap (1 : TorusColor 3)
        terminalFixedChartObstructionSource ≠
      terminalFixedChartReturn (1 : TorusColor 3)
        terminalFixedChartObstructionSource := by
  intro hReturn
  let x1 :=
    terminalStandardRootStep
      (dir (0 : ZMod 4) terminalFixedChartObstructionSource
        (1 : TorusColor 3))
      terminalFixedChartObstructionSource
  let x2 :=
    terminalStandardRootStep
      (dir (1 : ZMod 4) x1 (1 : TorusColor 3)) x1
  let x3 :=
    terminalStandardRootStep
      (dir (2 : ZMod 4) x2 (1 : TorusColor 3)) x2
  have hSteps :
      terminalStandardRootStep
          (dir (3 : ZMod 4) x3 (1 : TorusColor 3)) x3 =
        terminalFixedChartReturn (1 : TorusColor 3)
          terminalFixedChartObstructionSource := by
    simpa [RootFlatSchedule.returnMap, RootFlatSchedule.layerMap,
      terminalStandardSchedule, List.range, x1, x2, x3] using hReturn
  exact no_four_terminalStandardRootSteps_to_fixedChartReturn_color1
    (dir (0 : ZMod 4) terminalFixedChartObstructionSource
      (1 : TorusColor 3))
    (dir (1 : ZMod 4) x1 (1 : TorusColor 3))
    (dir (2 : ZMod 4) x2 (1 : TorusColor 3))
    (dir (3 : ZMod 4) x3 (1 : TorusColor 3))
    hSteps

/-- The tempting but wrong terminal row: read `omega(z-a_c)` separately for each
source color `c`.  This is the color-anchored candidate used in an earlier H1/H2
sketch; it is not a Latin row. -/
def colorAnchoredTerminalDir (w : TerminalRootState)
    (c : TorusColor 3) : TorusDirection 3 :=
  terminalRowEquiv
    (terminalOmega (terminalRootPair w - terminalVertex (m := 4) c)) c

def terminalOrigin : TerminalRootState :=
  terminalPairRoot (D54ResetData.d54q4 0 0)

theorem colorAnchoredTerminalDir_origin_values :
    colorAnchoredTerminalDir terminalOrigin 0 = 1 ∧
    colorAnchoredTerminalDir terminalOrigin 1 = 2 ∧
    colorAnchoredTerminalDir terminalOrigin 2 = 2 := by
  decide

theorem colorAnchoredTerminalDir_origin_not_bijective :
    ¬ Function.Bijective (colorAnchoredTerminalDir terminalOrigin) := by
  intro hbij
  have hdup :
      colorAnchoredTerminalDir terminalOrigin (1 : TorusColor 3) =
        colorAnchoredTerminalDir terminalOrigin (2 : TorusColor 3) := by
    decide
  have hne : (1 : TorusColor 3) ≠ (2 : TorusColor 3) := by
    decide
  exact hne (hbij.1 hdup)

theorem F_cycle (i : Fin 3) : Shared.IsSingleCycleMap (F i) := by
  fin_cases i
  · simpa [F, terminalSymbol] using
      (Shared.CycleCoordinate.singleCycle LowD5M4.f0Coord)
  · simpa [F, terminalSymbol] using
      (Shared.CycleCoordinate.singleCycle LowD5M4.f1Coord)
  · simpa [F, terminalSymbol] using
      (Shared.CycleCoordinate.singleCycle LowD5M4.f2Coord)

theorem terminalReturn4_singleCycle (i : Fin 3) :
    Shared.IsSingleCycleMap (terminalReturn (m := 4) i) := by
  rw [← F_fun_eq_terminalReturn i]
  exact F_cycle i

theorem W_eq_terminalResetTrace4 :
    W = wordEval (terminalSymbolStep 4) terminalResetTrace4 := by
  funext q
  rw [terminalResetTrace4_eval]
  rfl

theorem W_cycle : Shared.IsSingleCycleMap W := by
  rw [W_eq_terminalResetTrace4]
  exact terminalResetTrace4_singleCycle

set_option maxRecDepth 20000 in
theorem terminalF0F2_iterate_33 :
    ∀ q : Q4, (terminalF0F2^[33]) q = q := by
  decide

set_option maxRecDepth 20000 in
theorem terminalF0F2_no_positive_iterate_lt33 :
    ∀ n : Nat, n ∈ List.range 33 → n ≠ 0 →
      ∃ q : Q4, (terminalF0F2^[n]) q ≠ q := by
  decide

theorem Rbase_cycle (i : Fin 5) :
    Shared.IsSingleCycleMap (Rbase i) := by
  fin_cases i
  · exact LowD5M4.baseReturn0_singleCycle
  · exact LowD5M4.baseReturn1_singleCycle
  · exact LowD5M4.baseReturn2_singleCycle
  · exact LowD5M4.baseReturn3_singleCycle
  · exact LowD5M4.baseReturn4_singleCycle

theorem RbaseNeutral_bijective (i : Fin 5) :
    Function.Bijective (RbaseNeutral i) := by
  constructor
  · intro s₁ s₂ hs
    have hx0 := congrArg (fun s : Seed => s.1) hs
    have hx : s₁.1 = s₂.1 :=
      (Rbase_cycle i).1.1 (by simpa [RbaseNeutral] using hx0)
    have hz0 := congrArg (fun s : Seed => s.2) hs
    have hz : s₁.2 = s₂.2 :=
      by simpa [RbaseNeutral] using hz0
    exact Prod.ext hx hz
  · intro s
    rcases (Rbase_cycle i).1.2 s.1 with ⟨x, hx⟩
    exact ⟨(x, s.2), by simp [RbaseNeutral, hx]⟩

theorem RbaseNeutral_iterate_z
    (i : Fin 5) (n : Nat) (s : Seed) :
    (((RbaseNeutral i)^[n]) s).2 = s.2 := by
  induction n generalizing s with
  | zero =>
      simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      simpa [RbaseNeutral] using ih s

/-- The product-base return cannot be the final H2 return: it preserves the
neutral `Z` coordinate and therefore has four separate `Z` fibers.  The final
five local switches are exactly what insert the missing unit carry. -/
theorem RbaseNeutral_not_singleCycle
    (i : Fin 5) :
    ¬ Shared.IsSingleCycleMap (RbaseNeutral i) := by
  intro hcycle
  let x : Seed := ((((0 : Z4), (0 : Z4)), (0 : Z4)), (0 : Z4))
  let y : Seed := ((((0 : Z4), (0 : Z4)), (0 : Z4)), (1 : Z4))
  rcases hcycle.2 x y with ⟨n, hn⟩
  have hz := congrArg Prod.snd hn
  rw [RbaseNeutral_iterate_z i n x] at hz
  have hne : (0 : Z4) ≠ (1 : Z4) := by decide
  exact hne (by simpa [x, y] using hz)

theorem postBaseCarry_bijective (i : Fin 5) :
    Function.Bijective (postBaseCarry i) := by
  constructor
  · intro s₁ s₂ hs
    have hx0 := congrArg (fun s : Seed => s.1) hs
    have hx : s₁.1 = s₂.1 :=
      by simpa [postBaseCarry] using hx0
    have hz0 := congrArg (fun s : Seed => s.2) hs
    have hz :
        s₁.2 +
            (if s₁.1 = Rbase i (bSite i) then (1 : Zed4) else 0) =
          s₂.2 +
            (if s₂.1 = Rbase i (bSite i) then (1 : Zed4) else 0) :=
      by
        simpa [postBaseCarry] using hz0
    have hzSame :
        s₁.2 +
            (if s₂.1 = Rbase i (bSite i) then (1 : Zed4) else 0) =
          s₂.2 +
            (if s₂.1 = Rbase i (bSite i) then (1 : Zed4) else 0) := by
      simpa [hx] using hz
    have hz' : s₁.2 = s₂.2 := by
      simpa using hzSame
    exact Prod.ext hx hz'
  · intro s
    refine
      ⟨(s.1,
          s.2 -
            (if s.1 = Rbase i (bSite i) then (1 : Zed4) else 0)),
        ?_⟩
    simp [postBaseCarry]

/-- The two-stage seed model inserts the final carry immediately after the
product-base return.  Testing the transported site `Rbase_i b_i` after the base
move is equivalent to testing the original site `b_i` before the move. -/
theorem postBaseCarry_after_RbaseNeutral_eq_Rhat
    (i : Fin 5) (s : Seed) :
    postBaseCarry i (RbaseNeutral i s) = Rhat i s := by
  rcases s with ⟨x, z⟩
  by_cases hx : x = bSite i
  · simp [postBaseCarry, RbaseNeutral, Rhat, LowD5M4.fullReturn,
      bSite, UnitCarry.additiveSkewMap, Shared.skewProductMap,
      UnitCarry.pointCarry, hx]
  · have hRx : Rbase i x ≠ Rbase i (bSite i) := by
      intro h
      exact hx ((Rbase_cycle i).1.1 h)
    simp [postBaseCarry, RbaseNeutral, Rhat, LowD5M4.fullReturn,
      bSite, UnitCarry.additiveSkewMap, Shared.skewProductMap,
      UnitCarry.pointCarry, hx, hRx]

set_option maxRecDepth 100000 in
theorem seedLayerReturn_twoStageFullReturnLayer :
    ∀ c : TorusColor 5, ∀ s : Seed,
      seedLayerReturn seedTwoStageFullReturnLayer c s =
        postBaseCarry c (RbaseNeutral c s) := by
  decide

theorem seedTwoStageFullReturnLayer_return_eq_Rhat :
    ∀ c : TorusColor 5, ∀ s : Seed,
      seedLayerReturn seedTwoStageFullReturnLayer c s = Rhat c s := by
  intro c s
  rw [seedLayerReturn_twoStageFullReturnLayer]
  exact postBaseCarry_after_RbaseNeutral_eq_Rhat c s

theorem seedTwoStageFullReturnLayer_bijective :
    ∀ t : ZMod 4, ∀ c : TorusColor 5,
      Function.Bijective (seedTwoStageFullReturnLayer t c) := by
  intro t c
  by_cases h0 : t = (0 : ZMod 4)
  · simpa [seedTwoStageFullReturnLayer, h0] using
      RbaseNeutral_bijective c
  · by_cases h1 : t = (1 : ZMod 4)
    · simpa [seedTwoStageFullReturnLayer, h0, h1] using
        postBaseCarry_bijective c
    · simp [seedTwoStageFullReturnLayer, h0, h1]

theorem Rhat_cycle (i : Fin 5) :
    Shared.IsSingleCycleMap (Rhat i) :=
  LowD5M4.fullReturn_singleCycle i

theorem seedTwoStageFullReturnLayer_return_singleCycle
    (c : TorusColor 5) :
    Shared.IsSingleCycleMap
      (seedLayerReturn seedTwoStageFullReturnLayer c) := by
  have h :
      seedLayerReturn seedTwoStageFullReturnLayer c = Rhat c := by
    funext s
    exact seedTwoStageFullReturnLayer_return_eq_Rhat c s
  rw [h]
  exact Rhat_cycle c

/-- Existing Lean `fullReturn` is definitionally the paper-level `Rhat`. -/
theorem D54_fullReturn_eq_Rhat (i : Fin 5) (s : Seed) :
    LowD5M4.fullReturn i s = Rhat i s :=
  rfl

/-- If each physical layer is conjugate to a seed-side layer model, and the
seed-side four-layer fold is the target return, then the physical first return is
conjugate to that target.  This is the fold lemma used to reduce H2's RF3
calculation to per-layer row/ribbon calculations. -/
theorem physical_returnMap_conj_of_seedLayerReturn_eq
    (rows : PhysicalLayerRows)
    (e : Seed ≃ RootState)
    (layer : ZMod 4 → TorusColor 5 → Seed → Seed)
    (target : TorusColor 5 → Seed → Seed)
    (hLayer :
      ∀ t c s,
        (LowD5M4RibbonInterface.schedule rows).layerMap t c (e s) =
          e (layer t c s))
    (hReturn : ∀ c s, seedLayerReturn layer c s = target c s) :
    ∀ c : TorusColor 5, ∀ w : RootState,
      (LowD5M4RibbonInterface.schedule rows).returnMap c w =
        e (target c (e.symm w)) := by
  intro c w
  let s : Seed := e.symm w
  have hws : e s = w := by
    simp [s]
  have hFold :
      ∀ ts : List Nat, ∀ x : Seed,
        ts.foldl
            (fun y (t : Nat) =>
              (LowD5M4RibbonInterface.schedule rows).layerMap
                (t : ZMod 4) c y)
            (e x) =
          e
            (ts.foldl
              (fun y (t : Nat) => layer (t : ZMod 4) c y) x) := by
    intro ts
    induction ts with
    | nil =>
        intro x
        rfl
    | cons t ts ih =>
        intro x
        simp [List.foldl_cons, hLayer (t : ZMod 4) c x, ih]
  calc
    (LowD5M4RibbonInterface.schedule rows).returnMap c w
        =
          (LowD5M4RibbonInterface.schedule rows).returnMap c (e s) := by
            rw [hws]
    _ =
          e
            ((List.range 4).foldl
              (fun y (t : Nat) => layer (t : ZMod 4) c y) s) := by
            simpa [Shared.RootFlatSchedule.returnMap] using
              hFold (List.range 4) s
    _ = e (seedLayerReturn layer c s) := by
          rfl
    _ = e (target c s) := by
          rw [hReturn c s]
    _ = e (target c (e.symm w)) := by
          rfl

/-- RF2 is automatic from a layerwise conjugacy to bijective seed-side layers.
This removes a duplicate obligation from paper-row proofs: once each displayed
physical layer is identified with the intended seed switch layer, bijectivity is
transported through the return-section equivalence. -/
theorem physical_layerBijective_of_seedLayer_conj
    (rows : PhysicalLayerRows)
    (e : Seed ≃ RootState)
    (layer : ZMod 4 → TorusColor 5 → Seed → Seed)
    (hSeed : ∀ t c, Function.Bijective (layer t c))
    (hLayer :
      ∀ t c s,
        (LowD5M4RibbonInterface.schedule rows).layerMap t c (e s) =
          e (layer t c s)) :
    PhysicalRowsLayerBijectiveGoal rows := by
  intro t c
  constructor
  · intro w₁ w₂ hw
    apply e.symm.injective
    apply (hSeed t c).1
    apply e.injective
    calc
      e (layer t c (e.symm w₁))
          =
        (LowD5M4RibbonInterface.schedule rows).layerMap
          t c (e (e.symm w₁)) := by
            rw [hLayer t c (e.symm w₁)]
      _ = (LowD5M4RibbonInterface.schedule rows).layerMap t c w₁ := by
            simp
      _ = (LowD5M4RibbonInterface.schedule rows).layerMap t c w₂ := hw
      _ = (LowD5M4RibbonInterface.schedule rows).layerMap
          t c (e (e.symm w₂)) := by
            simp
      _ = e (layer t c (e.symm w₂)) := hLayer t c (e.symm w₂)
  · intro w
    rcases (hSeed t c).2 (e.symm w) with ⟨s, hs⟩
    refine ⟨e s, ?_⟩
    calc
      (LowD5M4RibbonInterface.schedule rows).layerMap t c (e s)
          = e (layer t c s) := hLayer t c s
      _ = e (e.symm w) := by rw [hs]
      _ = w := by simp

/-- Seed-side row-equivalence table for a four-layer D5(4) row construction. -/
abbrev D54SeedRow :=
  ZMod 4 → Seed → TorusColor 5 ≃ TorusDirection 5

/-- Turn a seed-side row table into displayed physical rows by transporting the
source state through the return-section equivalence.  The direction labels are
unchanged. -/
def physicalRowsOfSeedRow
    (e : Seed ≃ RootState) (row : D54SeedRow) : PhysicalLayerRows where
  layer0 := fun w => row (0 : ZMod 4) (e.symm w)
  layer1 := fun w => row (1 : ZMod 4) (e.symm w)
  layer2 := fun w => row (2 : ZMod 4) (e.symm w)
  layer3 := fun w => row (3 : ZMod 4) (e.symm w)

theorem physicalRowsOfSeedRow_row
    (e : Seed ≃ RootState) (row : D54SeedRow) :
    ∀ t w, (physicalRowsOfSeedRow e row).row t w = row t (e.symm w) := by
  intro t w
  fin_cases t <;> rfl

def seedLayerOfSeedRow
    (seedStep : TorusDirection 5 → Seed → Seed) (row : D54SeedRow) :
    ZMod 4 → TorusColor 5 → Seed → Seed :=
  fun t c s => seedStep ((row t s) c) s

def transportedSeedStep
    (e : Seed ≃ RootState) : TorusDirection 5 → Seed → Seed :=
  fun δ s => e.symm (LowD5M4Schedule.rootStep δ (e s))

theorem transportedSeedStep_conj
    (e : Seed ≃ RootState) :
    ∀ δ s, e (transportedSeedStep e δ s) =
      LowD5M4Schedule.rootStep δ (e s) := by
  intro δ s
  simp [transportedSeedStep]

/-- If the seed-side generator step is transported to the standard D5 root step,
then the physical rows obtained from the same seed row are layerwise conjugate to
the seed-side layer maps. -/
theorem physicalRowsOfSeedRow_layerMap_conj
    (e : Seed ≃ RootState) (row : D54SeedRow)
    (seedStep : TorusDirection 5 → Seed → Seed)
    (hStep :
      ∀ δ s, e (seedStep δ s) = LowD5M4Schedule.rootStep δ (e s)) :
    ∀ t c s,
      (LowD5M4RibbonInterface.schedule (physicalRowsOfSeedRow e row)).layerMap
          t c (e s) =
        e (seedLayerOfSeedRow seedStep row t c s) := by
  intro t c s
  calc
    (LowD5M4RibbonInterface.schedule (physicalRowsOfSeedRow e row)).layerMap
          t c (e s)
        =
      LowD5M4Schedule.rootStep
        (((physicalRowsOfSeedRow e row).row t (e s)) c) (e s) := by
          rfl
    _ = LowD5M4Schedule.rootStep ((row t s) c) (e s) := by
          rw [physicalRowsOfSeedRow_row e row t (e s)]
          simp
    _ = e (seedStep ((row t s) c) s) := by
          exact (hStep ((row t s) c) s).symm
    _ = e (seedLayerOfSeedRow seedStep row t c s) := rfl

/-- Transport a root-flat schedule on an arbitrary 256-state model to the
standard `D5(4)` root chart.  This is the direct-RF route, separate from the
paper `fullReturn` ribbon handoff. -/
def transportedRootDir {α : Type*}
    (S : Shared.RootFlatSchedule
      (TorusColor 5) (TorusDirection 5) α 4)
    (e : α ≃ RootState) :
    ZMod 4 → RootState → TorusColor 5 → TorusDirection 5 :=
  fun t w c => S.dir t (e.symm w) c

theorem transportedRootSchedule_layerMap_conj {α : Type*}
    (S : Shared.RootFlatSchedule
      (TorusColor 5) (TorusDirection 5) α 4)
    (e : α ≃ RootState)
    (hStep :
      ∀ δ x, e (S.step δ x) = LowD5M4Schedule.rootStep δ (e x)) :
    ∀ t c x,
      (LowD5M4Schedule.schedule (transportedRootDir S e)).layerMap
          t c (e x) =
        e (S.layerMap t c x) := by
  intro t c x
  simp [LowD5M4Schedule.schedule, transportedRootDir,
    Shared.RootFlatSchedule.layerMap, hStep]

theorem transportedRootSchedule_layerBijective {α : Type*}
    (S : Shared.RootFlatSchedule
      (TorusColor 5) (TorusDirection 5) α 4)
    (e : α ≃ RootState)
    (hLayer : S.layerBijective)
    (hStep :
      ∀ δ x, e (S.step δ x) = LowD5M4Schedule.rootStep δ (e x)) :
    (LowD5M4Schedule.schedule (transportedRootDir S e)).layerBijective := by
  intro t c
  constructor
  · intro w₁ w₂ hw
    have h₁ :=
      transportedRootSchedule_layerMap_conj S e hStep t c (e.symm w₁)
    have h₂ :=
      transportedRootSchedule_layerMap_conj S e hStep t c (e.symm w₂)
    have h₁' :
        (LowD5M4Schedule.schedule (transportedRootDir S e)).layerMap
            t c w₁ =
          e (S.layerMap t c (e.symm w₁)) := by
      simpa using h₁
    have h₂' :
        (LowD5M4Schedule.schedule (transportedRootDir S e)).layerMap
            t c w₂ =
          e (S.layerMap t c (e.symm w₂)) := by
      simpa using h₂
    apply e.symm.injective
    exact (hLayer t c).1 (by
      apply e.injective
      calc
        e (S.layerMap t c (e.symm w₁))
            =
          (LowD5M4Schedule.schedule (transportedRootDir S e)).layerMap
              t c w₁ := h₁'.symm
        _ =
          (LowD5M4Schedule.schedule (transportedRootDir S e)).layerMap
              t c w₂ := hw
        _ = e (S.layerMap t c (e.symm w₂)) := h₂')
  · intro w
    rcases (hLayer t c).2 (e.symm w) with ⟨x, hx⟩
    refine ⟨e x, ?_⟩
    calc
      (LowD5M4Schedule.schedule (transportedRootDir S e)).layerMap
          t c (e x)
          = e (S.layerMap t c x) :=
            transportedRootSchedule_layerMap_conj S e hStep t c x
      _ = e (e.symm w) := by rw [hx]
      _ = w := by simp

theorem transportedRootSchedule_returnMap_conj {α : Type*}
    (S : Shared.RootFlatSchedule
      (TorusColor 5) (TorusDirection 5) α 4)
    (e : α ≃ RootState)
    (hStep :
      ∀ δ x, e (S.step δ x) = LowD5M4Schedule.rootStep δ (e x)) :
    ∀ c x,
      (LowD5M4Schedule.schedule (transportedRootDir S e)).returnMap
          c (e x) =
        e (S.returnMap c x) := by
  intro c x
  have hFold :
      ∀ ts : List Nat, ∀ y : α,
        ts.foldl
            (fun z (t : Nat) =>
              (LowD5M4Schedule.schedule (transportedRootDir S e)).layerMap
                (t : ZMod 4) c z)
            (e y) =
          e
            (ts.foldl
              (fun z (t : Nat) => S.layerMap (t : ZMod 4) c z) y) := by
    intro ts
    induction ts with
    | nil =>
        intro y
        rfl
    | cons t ts ih =>
        intro y
        simp [List.foldl_cons,
          transportedRootSchedule_layerMap_conj S e hStep (t : ZMod 4) c y,
          ih]
  simpa [Shared.RootFlatSchedule.returnMap] using
    hFold (List.range 4) x

/-- Direct RF transport bridge.  A root-flat schedule on any finite 256-state
model whose step maps are conjugate to the standard D5 root steps yields the
active direct H2 RF data.  This is useful for generated certificates, but it is
not the paper `LowD5M4.fullReturn` realization route. -/
def resetPortH2RootFlatCycleData_of_conjugateSchedule {α : Type*}
    (S : Shared.RootFlatSchedule
      (TorusColor 5) (TorusDirection 5) α 4)
    (e : α ≃ RootState)
    (hRow : S.rowLatin)
    (hLayer : S.layerBijective)
    (hReturn : S.returnsSingleCycle)
    (hStep :
      ∀ δ x, e (S.step δ x) = LowD5M4Schedule.rootStep δ (e x)) :
    ResetPortH2RootFlatCycleData where
  dir := transportedRootDir S e
  rowLatin := by
    intro t w
    exact hRow t (e.symm w)
  layerBijective :=
    transportedRootSchedule_layerBijective S e hLayer hStep
  returnsSingleCycle := by
    intro c
    exact single_cycle_of_equiv_conj e
      ((LowD5M4Schedule.schedule (transportedRootDir S e)).returnMap c)
      (S.returnMap c)
      (hReturn c)
      (by
        intro x
        apply e.injective
        simp [transportedRootSchedule_returnMap_conj S e hStep c x])

/-- Packaged direct-RF input for generated finite certificates.  This is
intentionally separate from `D54FiveSwitchRealization`: it proves the D5(4)
root-flat certificate by transporting an already-cyclic root-flat schedule, but
does not identify the returns with the paper's `LowD5M4.fullReturn` maps. -/
structure D54ConjugateDirectRFInput where
  State : Type*
  schedule :
    Shared.RootFlatSchedule
      (TorusColor 5) (TorusDirection 5) State 4
  e : State ≃ RootState
  rowLatin : schedule.rowLatin
  layerBijective : schedule.layerBijective
  returnsSingleCycle : schedule.returnsSingleCycle
  stepConj :
    ∀ δ x, e (schedule.step δ x) =
      LowD5M4Schedule.rootStep δ (e x)

def D54ConjugateDirectRFInput.toDirectRFData
    (H : D54ConjugateDirectRFInput) :
    ResetPortH2RootFlatCycleData :=
  resetPortH2RootFlatCycleData_of_conjugateSchedule
    H.schedule H.e H.rowLatin H.layerBijective
    H.returnsSingleCycle H.stepConj

theorem D54ConjugateDirectRFInput.lowBaseFamily
    (H : D54ConjugateDirectRFInput) :
    FinalLowD5M4RootFlatCertificateFamily :=
  LowD5M4Structural.finalLowD5M4RootFlatCertificateFamily_of_rootFlatCycleData
    H.toDirectRFData

theorem pReset_eq_d54TerminalResetSite (i : Fin 3) :
    pReset i = D54ResetData.d54TerminalResetSite i := by
  fin_cases i <;> rfl

theorem bSite_eq_d54FinalCylinderOfColor (i : Fin 5) :
    D54ResetData.d54FinalCylinderOfColor i =
      { q := (bSite i).1, y := (bSite i).2 } := by
  exact D54ResetData.d54FinalCylinderOfColor_eq_lowD5M4_liftSite i

abbrev C4List : List Q4 := D54ResetData.d54TerminalSelector
abbrev ChatList : List D54ResetData.D54Point := D54ResetData.d54LiftedSelector
abbrev finalCylinders : List D54ResetData.D54Cylinder :=
  D54ResetData.d54FinalCylinders
abbrev reservePoints : List D54ResetData.D54Point :=
  D54ResetData.reservePoints

def q4 (x y : Nat) : Q4 := D54ResetData.d54q4 x y

def c0 : Q4 := q4 0 3
def c1 : Q4 := q4 3 0
def c2 : Q4 := q4 3 3

theorem C4List_eq : C4List = [c0, c1, c2] :=
  rfl

def cx0 : X4 := (c0, (0 : Y4))
def cx1 : X4 := (c1, (0 : Y4))
def cx2 : X4 := (c2, (0 : Y4))

def CXList : List X4 := [cx0, cx1, cx2]

def chat0 : Seed := (cx0, (0 : Zed4))
def chat1 : Seed := (cx1, (0 : Zed4))
def chat2 : Seed := (cx2, (0 : Zed4))

def ChatSeedList : List Seed := [chat0, chat1, chat2]

/-- The terminal protected neighborhood
`C4 ∪ F1(C4) ∪ F2(C4) ∪ F1⁻¹(C4) ∪ F2⁻¹(C4)`, normalized as the paper table. -/
def NTList : List Q4 :=
  [q4 0 3, q4 1 2, q4 1 3, q4 2 0,
   q4 2 1, q4 2 3, q4 3 0, q4 3 3]

/-- The lifted protected neighborhood `Nhat = NT × {0} × {0}` in D54 table
coordinates. -/
def NhatList : List D54ResetData.D54Point :=
  NTList.map fun q => { q := q, y := (0 : Y4), z := (0 : Zed4) }

/-- First hit of `targets` under positive iterates of `f`, searched up to
`limit`.  The returned natural number is the positive hitting time. -/
def firstHitListAux {α : Type*} [DecidableEq α]
    (f : α → α) (targets : List α) : Nat → α → Option (Nat × α)
  | 0, _ => none
  | n + 1, x =>
      let y := f x
      if y ∈ targets then
        some (1, y)
      else
        match firstHitListAux f targets n y with
        | none => none
        | some (k, z) => some (k + 1, z)

def firstHitList {α : Type*} [DecidableEq α]
    (limit : Nat) (f : α → α) (targets : List α) (x : α) :
    Option (Nat × α) :=
  firstHitListAux f targets limit x

def FInv (i : Fin 3) : Q4 → Q4 :=
  (F i)^[15]

def terminalSigma : Q4 → Q4 :=
  fun q => FInv 2 (F 1 q)

/-- Unnormalized one-step terminal selector neighborhood.  The theorem
`NTList_mem_iff_terminalNeighborhoodList_mem` below records that it has exactly
the normalized protected-neighborhood entries in `NTList`. -/
def terminalNeighborhoodList : List Q4 :=
  C4List ++ C4List.map (F 1) ++ C4List.map (F 2) ++
    C4List.map (FInv 1) ++ C4List.map (FInv 2)

theorem C4_terminal_comparison_table :
    terminalSigma c0 = c1 ∧
    terminalSigma c1 = c2 ∧
    terminalSigma c2 = c0 := by
  decide

theorem C4_terminal_F1_successor_table :
    firstHitList 16 (F 1) C4List c0 = some (9, c2) ∧
    firstHitList 16 (F 1) C4List c1 = some (1, c0) ∧
    firstHitList 16 (F 1) C4List c2 = some (6, c1) := by
  decide

theorem C4_terminal_F2_successor_table :
    firstHitList 16 (F 2) C4List c0 = some (9, c1) ∧
    firstHitList 16 (F 2) C4List c1 = some (6, c2) ∧
    firstHitList 16 (F 2) C4List c2 = some (1, c0) := by
  decide

def TInv (i : Fin 3) : X4 → X4 :=
  (T i)^[63]

def sigmaX : X4 → X4 :=
  fun x => TInv 2 (T 1 x)

set_option maxRecDepth 20000 in
theorem CX_comparison_table :
    sigmaX cx0 = cx1 ∧
    sigmaX cx1 = cx2 ∧
    sigmaX cx2 = cx0 := by
  decide

set_option maxRecDepth 20000 in
theorem CX_T1_successor_table :
    firstHitList 64 (T 1) CXList cx0 = some (9, cx2) ∧
    firstHitList 64 (T 1) CXList cx1 = some (1, cx0) ∧
    firstHitList 64 (T 1) CXList cx2 = some (54, cx1) := by
  decide

set_option maxRecDepth 20000 in
theorem CX_T2_successor_table :
    firstHitList 64 (T 2) CXList cx0 = some (57, cx1) ∧
    firstHitList 64 (T 2) CXList cx1 = some (6, cx2) ∧
    firstHitList 64 (T 2) CXList cx2 = some (1, cx0) := by
  decide

def RhatInv (i : Fin 5) : Seed → Seed :=
  (Rhat i)^[255]

def sigmaHat : Seed → Seed :=
  fun s => RhatInv 2 (Rhat 1 s)

set_option maxRecDepth 50000 in
theorem Chat_comparison_table :
    sigmaHat chat0 = chat1 ∧
    sigmaHat chat1 = chat2 ∧
    sigmaHat chat2 = chat0 := by
  decide

set_option maxRecDepth 50000 in
theorem Chat_Rhat1_successor_chat0 :
    firstHitList 256 (Rhat 1) ChatSeedList chat0 = some (9, chat2) := by
  decide

set_option maxRecDepth 50000 in
theorem Chat_Rhat1_successor_chat1 :
    firstHitList 256 (Rhat 1) ChatSeedList chat1 = some (1, chat0) := by
  decide

set_option maxRecDepth 50000 in
theorem Chat_Rhat1_successor_chat2 :
    firstHitList 256 (Rhat 1) ChatSeedList chat2 = some (246, chat1) := by
  decide

theorem Chat_Rhat1_successor_table :
    firstHitList 256 (Rhat 1) ChatSeedList chat0 = some (9, chat2) ∧
    firstHitList 256 (Rhat 1) ChatSeedList chat1 = some (1, chat0) ∧
    firstHitList 256 (Rhat 1) ChatSeedList chat2 = some (246, chat1) := by
  exact ⟨Chat_Rhat1_successor_chat0,
    Chat_Rhat1_successor_chat1, Chat_Rhat1_successor_chat2⟩

set_option maxRecDepth 50000 in
theorem Chat_Rhat2_successor_chat0 :
    firstHitList 256 (Rhat 2) ChatSeedList chat0 = some (249, chat1) := by
  decide

set_option maxRecDepth 50000 in
theorem Chat_Rhat2_successor_chat1 :
    firstHitList 256 (Rhat 2) ChatSeedList chat1 = some (6, chat2) := by
  decide

set_option maxRecDepth 50000 in
theorem Chat_Rhat2_successor_chat2 :
    firstHitList 256 (Rhat 2) ChatSeedList chat2 = some (1, chat0) := by
  decide

theorem Chat_Rhat2_successor_table :
    firstHitList 256 (Rhat 2) ChatSeedList chat0 = some (249, chat1) ∧
    firstHitList 256 (Rhat 2) ChatSeedList chat1 = some (6, chat2) ∧
    firstHitList 256 (Rhat 2) ChatSeedList chat2 = some (1, chat0) := by
  exact ⟨Chat_Rhat2_successor_chat0,
    Chat_Rhat2_successor_chat1, Chat_Rhat2_successor_chat2⟩

theorem C4List_nodup : C4List.Nodup :=
  D54ResetData.d54TerminalSelector_nodup

theorem ChatList_nodup : ChatList.Nodup := by
  decide

theorem reservePoints_nodup : reservePoints.Nodup := by
  decide

theorem NTList_nodup : NTList.Nodup := by
  decide

theorem NhatList_nodup : NhatList.Nodup := by
  decide

theorem NTList_mem_iff_terminalNeighborhoodList_mem :
    ∀ q : Q4, q ∈ NTList ↔ q ∈ terminalNeighborhoodList := by
  decide

theorem C4List_subset_NTList :
    ∀ q : Q4, q ∈ C4List → q ∈ NTList := by
  decide

theorem ChatList_subset_NhatList :
    ∀ p : D54ResetData.D54Point, p ∈ ChatList → p ∈ NhatList := by
  decide

theorem mem_NhatList_of_mem_NTList {q : Q4}
    (hq : q ∈ NTList) :
    ({ q := q, y := (0 : Y4), z := (0 : Zed4) } :
      D54ResetData.D54Point) ∈ NhatList := by
  exact List.mem_map.2 ⟨q, hq, rfl⟩

theorem mem_NTList_of_mem_NhatList
    {p : D54ResetData.D54Point}
    (hp : p ∈ NhatList) :
    p.q ∈ NTList ∧ p.y = (0 : Y4) ∧ p.z = (0 : Zed4) := by
  rcases List.mem_map.1 hp with ⟨q, hq, hpq⟩
  subst hpq
  exact ⟨hq, rfl, rfl⟩

theorem resetSites_avoid_NTList :
    ∀ i : Fin 3, pReset i ∉ NTList := by
  decide

theorem resetSites_disjoint_C4List :
    D54ResetData.listsDisjoint
      D54ResetData.d54TerminalResetSites C4List :=
  D54ResetData.d54TerminalResetSites_disjoint_selector

theorem finalCylinders_avoid_ChatList :
    D54ResetData.cylindersAvoidPoints finalCylinders ChatList :=
  D54ResetData.d54FinalCylinders_avoid_liftedSelector

theorem reservePoints_avoid_finalCylinders :
    D54ResetData.reservesAvoidCylinders reservePoints finalCylinders :=
  D54ResetData.d54ReservePoints_avoid_finalCylinders

theorem reservePoints_disjoint_ChatList :
    D54ResetData.listsDisjoint reservePoints ChatList :=
  D54ResetData.d54ReservePoints_disjoint_liftedSelector

theorem finalCylinders_avoid_NhatList :
    D54ResetData.cylindersAvoidPoints finalCylinders NhatList := by
  rfl

theorem reservePoints_disjoint_NhatList :
    D54ResetData.listsDisjoint reservePoints NhatList := by
  rfl

/-- The finite comparison/successor tables for the terminal selector, its
`Y`-lift, and the final `Z`-lift.  This is the return-level part of the paper's
marked-selector argument, separated from the physical ribbon realization. -/
structure D54SelectorTables where
  terminalComparison :
    terminalSigma c0 = c1 ∧
    terminalSigma c1 = c2 ∧
    terminalSigma c2 = c0
  terminalF1Successor :
    firstHitList 16 (F 1) C4List c0 = some (9, c2) ∧
    firstHitList 16 (F 1) C4List c1 = some (1, c0) ∧
    firstHitList 16 (F 1) C4List c2 = some (6, c1)
  terminalF2Successor :
    firstHitList 16 (F 2) C4List c0 = some (9, c1) ∧
    firstHitList 16 (F 2) C4List c1 = some (6, c2) ∧
    firstHitList 16 (F 2) C4List c2 = some (1, c0)
  liftedComparison :
    sigmaX cx0 = cx1 ∧
    sigmaX cx1 = cx2 ∧
    sigmaX cx2 = cx0
  liftedT1Successor :
    firstHitList 64 (T 1) CXList cx0 = some (9, cx2) ∧
    firstHitList 64 (T 1) CXList cx1 = some (1, cx0) ∧
    firstHitList 64 (T 1) CXList cx2 = some (54, cx1)
  liftedT2Successor :
    firstHitList 64 (T 2) CXList cx0 = some (57, cx1) ∧
    firstHitList 64 (T 2) CXList cx1 = some (6, cx2) ∧
    firstHitList 64 (T 2) CXList cx2 = some (1, cx0)
  finalComparison :
    sigmaHat chat0 = chat1 ∧
    sigmaHat chat1 = chat2 ∧
    sigmaHat chat2 = chat0
  finalRhat1Successor :
    firstHitList 256 (Rhat 1) ChatSeedList chat0 = some (9, chat2) ∧
    firstHitList 256 (Rhat 1) ChatSeedList chat1 = some (1, chat0) ∧
    firstHitList 256 (Rhat 1) ChatSeedList chat2 = some (246, chat1)
  finalRhat2Successor :
    firstHitList 256 (Rhat 2) ChatSeedList chat0 = some (249, chat1) ∧
    firstHitList 256 (Rhat 2) ChatSeedList chat1 = some (6, chat2) ∧
    firstHitList 256 (Rhat 2) ChatSeedList chat2 = some (1, chat0)

def d54SelectorTables : D54SelectorTables where
  terminalComparison := C4_terminal_comparison_table
  terminalF1Successor := C4_terminal_F1_successor_table
  terminalF2Successor := C4_terminal_F2_successor_table
  liftedComparison := CX_comparison_table
  liftedT1Successor := CX_T1_successor_table
  liftedT2Successor := CX_T2_successor_table
  finalComparison := Chat_comparison_table
  finalRhat1Successor := Chat_Rhat1_successor_table
  finalRhat2Successor := Chat_Rhat2_successor_table

/-- Support and reserve facts needed by the D54 switch/ribbon proof. -/
structure D54SupportTables where
  selectorNodup : C4List.Nodup
  liftedSelectorNodup : ChatList.Nodup
  reservePointsNodup : reservePoints.Nodup
  terminalProtectedNodup : NTList.Nodup
  liftedProtectedNodup : NhatList.Nodup
  selectorSubsetProtected :
    ∀ q : Q4, q ∈ C4List → q ∈ NTList
  liftedSelectorSubsetProtected :
    ∀ p : D54ResetData.D54Point, p ∈ ChatList → p ∈ NhatList
  terminalProtectedNeighborhoodMem :
    ∀ q : Q4, q ∈ NTList ↔ q ∈ terminalNeighborhoodList
  resetSitesDisjointSelector :
    D54ResetData.listsDisjoint
      D54ResetData.d54TerminalResetSites C4List
  resetSitesAvoidProtected :
    ∀ i : Fin 3, pReset i ∉ NTList
  finalCylindersAvoidSelector :
    D54ResetData.cylindersAvoidPoints finalCylinders ChatList
  finalCylindersAvoidProtected :
    D54ResetData.cylindersAvoidPoints finalCylinders NhatList
  reserveAvoidFinalCylinders :
    D54ResetData.reservesAvoidCylinders reservePoints finalCylinders
  reserveDisjointSelector :
    D54ResetData.listsDisjoint reservePoints ChatList
  reserveDisjointProtected :
    D54ResetData.listsDisjoint reservePoints NhatList

def d54SupportTables : D54SupportTables where
  selectorNodup := C4List_nodup
  liftedSelectorNodup := ChatList_nodup
  reservePointsNodup := reservePoints_nodup
  terminalProtectedNodup := NTList_nodup
  liftedProtectedNodup := NhatList_nodup
  selectorSubsetProtected := C4List_subset_NTList
  liftedSelectorSubsetProtected := ChatList_subset_NhatList
  terminalProtectedNeighborhoodMem := NTList_mem_iff_terminalNeighborhoodList_mem
  resetSitesDisjointSelector := resetSites_disjoint_C4List
  resetSitesAvoidProtected := resetSites_avoid_NTList
  finalCylindersAvoidSelector := finalCylinders_avoid_ChatList
  finalCylindersAvoidProtected := finalCylinders_avoid_NhatList
  reserveAvoidFinalCylinders := reservePoints_avoid_finalCylinders
  reserveDisjointSelector := reservePoints_disjoint_ChatList
  reserveDisjointProtected := reservePoints_disjoint_NhatList

/-- Return-level terminal data already formalized by the finite tables.  This is
not the physical row realization; it is the finite core that the physical
terminal theorem must realize. -/
structure TerminalA2M4ReturnCore where
  terminalReturnModel : Fin 3 → Q4 → Q4
  terminalReturn_eq_F : ∀ i q, terminalReturnModel i q = F i q
  terminalReturn_eq_paper :
    ∀ i q, terminalReturnModel i q = terminalReturn (m := 4) i q
  F_singleCycle : ∀ i, Shared.IsSingleCycleMap (terminalReturnModel i)
  resetTraceSingleCycle : Shared.IsSingleCycleMap W
  selectorNodup : C4List.Nodup
  resetSitesDisjointSelector :
    D54ResetData.listsDisjoint
      D54ResetData.d54TerminalResetSites C4List

/-- The terminal return-level core, obtained from existing finite tables. -/
def terminal_A2_m4_return_core : TerminalA2M4ReturnCore where
  terminalReturnModel := F
  terminalReturn_eq_F := by
    intro i q
    rfl
  terminalReturn_eq_paper := by
    intro i q
    exact F_eq_terminalReturn i q
  F_singleCycle := F_cycle
  resetTraceSingleCycle := W_cycle
  selectorNodup := C4List_nodup
  resetSitesDisjointSelector := resetSites_disjoint_C4List

/-- Seed-side row-equivalence table for the terminal A2 block. -/
abbrev TerminalSeedRow :=
  ZMod 4 → Q4 → TorusColor 3 ≃ TorusDirection 3

def terminalScheduleOfSeedRow
    (eT : Q4 ≃ TerminalRootState) (row : TerminalSeedRow) :
    RootFlatSchedule (TorusColor 3) (TorusDirection 3) TerminalRootState 4 where
  dir := fun t w c => row t (eT.symm w) c
  step := terminalStandardRootStep

def terminalSeedLayerOfRow
    (seedStep : TorusDirection 3 → Q4 → Q4) (row : TerminalSeedRow) :
    ZMod 4 → TorusColor 3 → Q4 → Q4 :=
  fun t c q => seedStep ((row t q) c) q

def terminalTransportedSeedStep
    (eT : Q4 ≃ TerminalRootState) : TorusDirection 3 → Q4 → Q4 :=
  fun δ q => eT.symm (terminalStandardRootStep δ (eT q))

theorem terminalTransportedSeedStep_conj
    (eT : Q4 ≃ TerminalRootState) :
    ∀ δ q, eT (terminalTransportedSeedStep eT δ q) =
      terminalStandardRootStep δ (eT q) := by
  intro δ q
  simp [terminalTransportedSeedStep]

def terminalSeedLayerReturn
    (layer : ZMod 4 → TorusColor 3 → Q4 → Q4)
    (c : TorusColor 3) : Q4 → Q4 :=
  fun q =>
    (List.range 4).foldl
      (fun x (t : Nat) => layer (t : ZMod 4) c x) q

/-- Terminal version of the seed-row transport bridge. -/
theorem terminalScheduleOfSeedRow_layerMap_conj
    (eT : Q4 ≃ TerminalRootState) (row : TerminalSeedRow)
    (seedStep : TorusDirection 3 → Q4 → Q4)
    (hStep :
      ∀ δ q, eT (seedStep δ q) = terminalStandardRootStep δ (eT q)) :
    ∀ t c q,
      (terminalScheduleOfSeedRow eT row).layerMap t c (eT q) =
        eT (terminalSeedLayerOfRow seedStep row t c q) := by
  intro t c q
  simp [terminalScheduleOfSeedRow, Shared.RootFlatSchedule.layerMap,
    terminalSeedLayerOfRow, hStep]

theorem terminal_layerBijective_of_seedLayer_conj
    (eT : Q4 ≃ TerminalRootState)
    (rows : RootFlatSchedule
      (TorusColor 3) (TorusDirection 3) TerminalRootState 4)
    (layer : ZMod 4 → TorusColor 3 → Q4 → Q4)
    (hSeed : ∀ t c, Function.Bijective (layer t c))
    (hLayer : ∀ t c q, rows.layerMap t c (eT q) = eT (layer t c q)) :
    rows.layerBijective := by
  intro t c
  constructor
  · intro w₁ w₂ hw
    apply eT.symm.injective
    apply (hSeed t c).1
    apply eT.injective
    calc
      eT (layer t c (eT.symm w₁))
          = rows.layerMap t c (eT (eT.symm w₁)) := by
            rw [hLayer t c (eT.symm w₁)]
      _ = rows.layerMap t c w₁ := by simp
      _ = rows.layerMap t c w₂ := hw
      _ = rows.layerMap t c (eT (eT.symm w₂)) := by simp
      _ = eT (layer t c (eT.symm w₂)) := hLayer t c (eT.symm w₂)
  · intro w
    rcases (hSeed t c).2 (eT.symm w) with ⟨q, hq⟩
    refine ⟨eT q, ?_⟩
    calc
      rows.layerMap t c (eT q) = eT (layer t c q) := hLayer t c q
      _ = eT (eT.symm w) := by rw [hq]
      _ = w := by simp

theorem terminal_returnMap_conj_of_seedLayerReturn_eq
    (eT : Q4 ≃ TerminalRootState) (row : TerminalSeedRow)
    (seedStep : TorusDirection 3 → Q4 → Q4)
    (hStep :
      ∀ δ q, eT (seedStep δ q) = terminalStandardRootStep δ (eT q)) :
    ∀ c q,
      eT.symm ((terminalScheduleOfSeedRow eT row).returnMap c (eT q)) =
        terminalSeedLayerReturn
          (terminalSeedLayerOfRow seedStep row) c q := by
  intro c q
  have hFold :
      ∀ ts : List Nat, ∀ x : Q4,
        ts.foldl
            (fun y (t : Nat) =>
              (terminalScheduleOfSeedRow eT row).layerMap
                (t : ZMod 4) c y)
            (eT x) =
          eT
            (ts.foldl
              (fun y (t : Nat) =>
                terminalSeedLayerOfRow seedStep row (t : ZMod 4) c y) x) := by
    intro ts
    induction ts with
    | nil =>
        intro x
        rfl
    | cons t ts ih =>
        intro x
        simp [List.foldl_cons,
          terminalScheduleOfSeedRow_layerMap_conj
            eT row seedStep hStep (t : ZMod 4) c x,
          ih]
  apply eT.injective
  calc
    eT (eT.symm ((terminalScheduleOfSeedRow eT row).returnMap c (eT q)))
        = (terminalScheduleOfSeedRow eT row).returnMap c (eT q) := by
          simp
    _ =
      eT
        (terminalSeedLayerReturn
          (terminalSeedLayerOfRow seedStep row) c q) := by
          simpa [Shared.RootFlatSchedule.returnMap, terminalSeedLayerReturn]
            using hFold (List.range 4) q

/-- Paper-facing terminal A2 realization target at `m = 4`.  It says that an
actual D3 root-flat schedule realizes the collapsed terminal returns `F_i`
through a return-section equivalence.  The equivalence is deliberately a field:
the standard chart `terminalRootEquiv` is too rigid for the paper's
run-collapse correspondence. -/
structure TerminalA2M4PhysicalRealization where
  rows : RootFlatSchedule
    (TorusColor 3) (TorusDirection 3) TerminalRootState 4
  eT : Q4 ≃ TerminalRootState
  step_eq_standard : rows.step = terminalStandardRootStep
  rowLatin : rows.rowLatin
  layerBijective : rows.layerBijective
  return_eq_F :
    ∀ c : TorusColor 3, ∀ q : Q4,
      eT.symm (rows.returnMap c (eT q)) = F c q

/-- Seed-row form of the terminal A2 realization.  The caller supplies the
paper's terminal seed row, a seed-side generator step, and the finite fold equal
to `F_i`; Lean constructs the physical terminal schedule and RF2. -/
structure TerminalA2M4SeedRowRealization where
  eT : Q4 ≃ TerminalRootState
  seedStep : TorusDirection 3 → Q4 → Q4
  seedRow : TerminalSeedRow
  stepConj :
    ∀ δ q, eT (seedStep δ q) = terminalStandardRootStep δ (eT q)
  seedLayerBijective :
    ∀ t : ZMod 4, ∀ c : TorusColor 3,
      Function.Bijective (terminalSeedLayerOfRow seedStep seedRow t c)
  seedReturn_eq_F :
    ∀ c q,
      terminalSeedLayerReturn
        (terminalSeedLayerOfRow seedStep seedRow) c q = F c q

def TerminalA2M4SeedRowRealization.rows
    (H : TerminalA2M4SeedRowRealization) :
    RootFlatSchedule (TorusColor 3) (TorusDirection 3) TerminalRootState 4 :=
  terminalScheduleOfSeedRow H.eT H.seedRow

def TerminalA2M4SeedRowRealization.toPhysicalRealization
    (H : TerminalA2M4SeedRowRealization) :
    TerminalA2M4PhysicalRealization where
  rows := H.rows
  eT := H.eT
  step_eq_standard := rfl
  rowLatin := by
    intro t w
    exact (H.seedRow t (H.eT.symm w)).bijective
  layerBijective :=
    terminal_layerBijective_of_seedLayer_conj H.eT H.rows
      (terminalSeedLayerOfRow H.seedStep H.seedRow)
      H.seedLayerBijective
      (terminalScheduleOfSeedRow_layerMap_conj
        H.eT H.seedRow H.seedStep H.stepConj)
  return_eq_F := by
    intro c q
    calc
      H.eT.symm (H.rows.returnMap c (H.eT q))
          =
        terminalSeedLayerReturn
          (terminalSeedLayerOfRow H.seedStep H.seedRow) c q :=
          terminal_returnMap_conj_of_seedLayerReturn_eq
            H.eT H.seedRow H.seedStep H.stepConj c q
      _ = F c q := H.seedReturn_eq_F c q

/-- Terminal seed-row realization with the seed generator step fixed as the
pullback of the standard terminal root step through `eT`. -/
structure TerminalA2M4TransportedSeedRowRealization where
  eT : Q4 ≃ TerminalRootState
  seedRow : TerminalSeedRow
  seedLayerBijective :
    ∀ t : ZMod 4, ∀ c : TorusColor 3,
      Function.Bijective
        (terminalSeedLayerOfRow (terminalTransportedSeedStep eT) seedRow t c)
  seedReturn_eq_F :
    ∀ c q,
      terminalSeedLayerReturn
        (terminalSeedLayerOfRow (terminalTransportedSeedStep eT) seedRow) c q =
          F c q

def TerminalA2M4TransportedSeedRowRealization.toSeedRowRealization
    (H : TerminalA2M4TransportedSeedRowRealization) :
    TerminalA2M4SeedRowRealization where
  eT := H.eT
  seedStep := terminalTransportedSeedStep H.eT
  seedRow := H.seedRow
  stepConj := terminalTransportedSeedStep_conj H.eT
  seedLayerBijective := H.seedLayerBijective
  seedReturn_eq_F := H.seedReturn_eq_F

def TerminalA2M4TransportedSeedRowRealization.toPhysicalRealization
    (H : TerminalA2M4TransportedSeedRowRealization) :
    TerminalA2M4PhysicalRealization :=
  H.toSeedRowRealization.toPhysicalRealization

theorem TerminalA2M4PhysicalRealization.returnsSingleCycle
    (H : TerminalA2M4PhysicalRealization) :
    H.rows.returnsSingleCycle := by
  intro c
  exact single_cycle_of_equiv_conj H.eT
    (H.rows.returnMap c)
    (F c)
    (F_cycle c)
    (H.return_eq_F c)

theorem TerminalA2M4PhysicalRealization.return_eq_terminalReturn
    (H : TerminalA2M4PhysicalRealization) :
    ∀ c : TorusColor 3, ∀ q : Q4,
      H.eT.symm (H.rows.returnMap c (H.eT q)) =
        terminalReturn (m := 4) c q := by
  intro c q
  rw [← F_eq_terminalReturn c q]
  exact H.return_eq_F c q

/-- The actual two-letter terminal return relation on physical terminal root
states.  It is the physical counterpart of `terminalF0F2 = F0 o F2`. -/
def TerminalA2M4PhysicalRealization.actualF0F2
    (H : TerminalA2M4PhysicalRealization) :
    TerminalRootState → TerminalRootState :=
  fun w => H.rows.returnMap 0 (H.rows.returnMap 2 w)

theorem TerminalA2M4PhysicalRealization.actualF0F2_conj
    (H : TerminalA2M4PhysicalRealization) (q : Q4) :
    H.eT.symm (H.actualF0F2 (H.eT q)) = terminalF0F2 q := by
  unfold TerminalA2M4PhysicalRealization.actualF0F2 terminalF0F2
  have h2sym := H.return_eq_F (2 : TorusColor 3) q
  have h2 :
      H.rows.returnMap (2 : TorusColor 3) (H.eT q) = H.eT (F 2 q) := by
    apply H.eT.symm.injective
    simpa using h2sym
  rw [h2]
  exact H.return_eq_F (0 : TorusColor 3) (F 2 q)

theorem TerminalA2M4PhysicalRealization.actualF0F2_iterate_conj
    (H : TerminalA2M4PhysicalRealization) :
    ∀ n q,
      H.eT.symm ((H.actualF0F2)^[n] (H.eT q)) =
        (terminalF0F2^[n]) q := by
  intro n
  induction n with
  | zero =>
      intro q
      simp
  | succ n ih =>
      intro q
      have hN := ih q
      have hNmap :
          (H.actualF0F2)^[n] (H.eT q) =
            H.eT ((terminalF0F2^[n]) q) := by
        apply H.eT.symm.injective
        simpa using hN
      calc
        H.eT.symm ((H.actualF0F2)^[n + 1] (H.eT q))
            =
          H.eT.symm
            (H.actualF0F2 ((H.actualF0F2)^[n] (H.eT q))) := by
              rw [Function.iterate_succ_apply']
        _ =
          H.eT.symm
            (H.actualF0F2 (H.eT ((terminalF0F2^[n]) q))) := by
              rw [hNmap]
        _ = terminalF0F2 ((terminalF0F2^[n]) q) :=
              H.actualF0F2_conj ((terminalF0F2^[n]) q)
        _ = (terminalF0F2^[n + 1]) q := by
              rw [Function.iterate_succ_apply']

theorem TerminalA2M4PhysicalRealization.actualF0F2_iterate_33
    (H : TerminalA2M4PhysicalRealization) :
    ∀ w : TerminalRootState, ((H.actualF0F2)^[33]) w = w := by
  intro w
  let q := H.eT.symm w
  have hw : H.eT q = w := by
    simp [q]
  rw [← hw]
  apply H.eT.symm.injective
  rw [H.actualF0F2_iterate_conj 33 q]
  simp [terminalF0F2_iterate_33]

theorem TerminalA2M4PhysicalRealization.actualF0F2_no_positive_iterate_lt33
    (H : TerminalA2M4PhysicalRealization) :
    ∀ n : Nat, n ∈ List.range 33 → n ≠ 0 →
      ∃ w : TerminalRootState, ((H.actualF0F2)^[n]) w ≠ w := by
  intro n hn hne
  rcases terminalF0F2_no_positive_iterate_lt33 n hn hne with ⟨q, hq⟩
  refine ⟨H.eT q, ?_⟩
  intro hw
  apply hq
  have hconj := H.actualF0F2_iterate_conj n q
  rw [hw] at hconj
  simpa using hconj.symm

theorem TerminalA2M4PhysicalRealization.rows_eq_terminalStandardSchedule
    (H : TerminalA2M4PhysicalRealization) :
    H.rows = terminalStandardSchedule H.rows.dir := by
  rcases H with ⟨rows, _eT, hstep, _hrow, _hlayer, _hret⟩
  cases rows with
  | mk dir step =>
      dsimp [terminalStandardSchedule] at hstep ⊢
      cases hstep
      rfl

theorem TerminalA2M4PhysicalRealization.not_terminalRootEquivSection
    (H : TerminalA2M4PhysicalRealization) :
    H.eT ≠ terminalRootEquiv.symm := by
  intro hEq
  have hRet :=
    H.return_eq_terminalReturn (1 : TorusColor 3)
      (D54ResetData.d54q4 0 0)
  have hMap :
      H.rows.returnMap (1 : TorusColor 3)
          terminalFixedChartObstructionSource =
        terminalFixedChartReturn (1 : TorusColor 3)
          terminalFixedChartObstructionSource := by
    apply terminalRootEquiv.injective
    simpa [hEq, terminalFixedChartObstructionSource,
      terminalFixedChartReturn] using hRet
  have hRows := H.rows_eq_terminalStandardSchedule
  rw [hRows] at hMap
  exact terminalStandardReturnMap_ne_fixedChartReturn_color1
    H.rows.dir hMap

theorem TerminalA2M4PhysicalRealization.not_colorAnchoredOriginRow
    (H : TerminalA2M4PhysicalRealization) :
    ¬ (∀ c : TorusColor 3,
      H.rows.dir (0 : Z4) terminalOrigin c =
        colorAnchoredTerminalDir terminalOrigin c) := by
  intro hrow
  have hbij :
      Function.Bijective
        (fun c : TorusColor 3 => H.rows.dir (0 : Z4) terminalOrigin c) :=
    H.rowLatin 0 terminalOrigin
  have hdup :
      H.rows.dir (0 : Z4) terminalOrigin (1 : TorusColor 3) =
        H.rows.dir (0 : Z4) terminalOrigin (2 : TorusColor 3) := by
    rw [hrow 1, hrow 2]
    decide
  have hne : (1 : TorusColor 3) ≠ (2 : TorusColor 3) := by
    decide
  exact hne (hbij.1 hdup)

/-- Completed return-level D54 core.  The only missing H2 part is now the
physical row/ribbon realization that transports these maps to root-flat rows. -/
structure D54ReturnLevelCore where
  terminal : TerminalA2M4ReturnCore
  selectorTables : D54SelectorTables
  supportTables : D54SupportTables
  baseSingleCycle : ∀ i : Fin 5, Shared.IsSingleCycleMap (Rbase i)
  fullSingleCycle : ∀ i : Fin 5, Shared.IsSingleCycleMap (Rhat i)
  fullReturn_eq_Rhat : ∀ i s, LowD5M4.fullReturn i s = Rhat i s
  terminalF0F2Order33 :
    ∀ q : Q4, (terminalF0F2^[33]) q = q
  terminalF0F2NoSmallerPositiveOrder :
    ∀ n : Nat, n ∈ List.range 33 → n ≠ 0 →
      ∃ q : Q4, (terminalF0F2^[n]) q ≠ q
  twoStageLayerBijective :
    ∀ t : ZMod 4, ∀ c : TorusColor 5,
      Function.Bijective (seedTwoStageFullReturnLayer t c)
  twoStageReturn_eq_Rhat :
    ∀ c : TorusColor 5, ∀ s : Seed,
      seedLayerReturn seedTwoStageFullReturnLayer c s = Rhat c s
  twoStageReturnSingleCycle :
    ∀ c : TorusColor 5,
      Shared.IsSingleCycleMap
        (seedLayerReturn seedTwoStageFullReturnLayer c)

def d54ReturnLevelCore : D54ReturnLevelCore where
  terminal := terminal_A2_m4_return_core
  selectorTables := d54SelectorTables
  supportTables := d54SupportTables
  baseSingleCycle := Rbase_cycle
  fullSingleCycle := Rhat_cycle
  fullReturn_eq_Rhat := D54_fullReturn_eq_Rhat
  terminalF0F2Order33 := terminalF0F2_iterate_33
  terminalF0F2NoSmallerPositiveOrder :=
    terminalF0F2_no_positive_iterate_lt33
  twoStageLayerBijective := seedTwoStageFullReturnLayer_bijective
  twoStageReturn_eq_Rhat := seedTwoStageFullReturnLayer_return_eq_Rhat
  twoStageReturnSingleCycle := seedTwoStageFullReturnLayer_return_singleCycle

/-- Product rows before the five final `Z`-carry switches.  The return map must
be conjugate to `(x,z) ↦ (Rbase_i x,z)`. -/
structure D54ProductBaseRealization where
  rows0 : PhysicalLayerRows
  e0 : Seed ≃ RootState
  layerBijective0 : PhysicalRowsLayerBijectiveGoal rows0
  returnMapConj_RbaseNeutral :
    ∀ c : TorusColor 5, ∀ w : RootState,
      (LowD5M4RibbonInterface.schedule rows0).returnMap c w =
        e0 (RbaseNeutral c (e0.symm w))

/-- Layer-model form of `D54ProductBaseRealization`.  This is usually the proof
shape produced by expanding the terminal `A2` block, `Y` row word, and neutral
`Z` row: first prove each physical layer is conjugate to a seed-side layer map,
then prove the four seed layers fold to `RbaseNeutral`. -/
structure D54ProductBaseLayerModelRealization where
  rows0 : PhysicalLayerRows
  e0 : Seed ≃ RootState
  layerBijective0 : PhysicalRowsLayerBijectiveGoal rows0
  seedLayer0 : ZMod 4 → TorusColor 5 → Seed → Seed
  layerMapConj0 :
    ∀ t c s,
      (LowD5M4RibbonInterface.schedule rows0).layerMap t c (e0 s) =
        e0 (seedLayer0 t c s)
  seedReturn_eq_RbaseNeutral :
    ∀ c s, seedLayerReturn seedLayer0 c s = RbaseNeutral c s

def D54ProductBaseLayerModelRealization.toProductBaseRealization
    (H : D54ProductBaseLayerModelRealization) :
    D54ProductBaseRealization where
  rows0 := H.rows0
  e0 := H.e0
  layerBijective0 := H.layerBijective0
  returnMapConj_RbaseNeutral :=
    physical_returnMap_conj_of_seedLayerReturn_eq
      H.rows0 H.e0 H.seedLayer0 RbaseNeutral
      H.layerMapConj0 H.seedReturn_eq_RbaseNeutral

/-- Product-base layer-conjugacy target with RF2 derived from seed-layer
bijectivity.  This is the form expected from an explicit terminal/product row
expansion: identify every physical layer with a seed-side layer and prove the
seed-side layer is bijective. -/
structure D54ProductBaseLayerConjRealization where
  rows0 : PhysicalLayerRows
  e0 : Seed ≃ RootState
  seedLayer0 : ZMod 4 → TorusColor 5 → Seed → Seed
  seedLayerBijective0 :
    ∀ t : ZMod 4, ∀ c : TorusColor 5,
      Function.Bijective (seedLayer0 t c)
  layerMapConj0 :
    ∀ t c s,
      (LowD5M4RibbonInterface.schedule rows0).layerMap t c (e0 s) =
        e0 (seedLayer0 t c s)
  seedReturn_eq_RbaseNeutral :
    ∀ c s, seedLayerReturn seedLayer0 c s = RbaseNeutral c s

def D54ProductBaseLayerConjRealization.toLayerModelRealization
    (H : D54ProductBaseLayerConjRealization) :
    D54ProductBaseLayerModelRealization where
  rows0 := H.rows0
  e0 := H.e0
  layerBijective0 :=
    physical_layerBijective_of_seedLayer_conj
      H.rows0 H.e0 H.seedLayer0
      H.seedLayerBijective0 H.layerMapConj0
  seedLayer0 := H.seedLayer0
  layerMapConj0 := H.layerMapConj0
  seedReturn_eq_RbaseNeutral := H.seedReturn_eq_RbaseNeutral

def D54ProductBaseLayerConjRealization.toProductBaseRealization
    (H : D54ProductBaseLayerConjRealization) :
    D54ProductBaseRealization :=
  H.toLayerModelRealization.toProductBaseRealization

/-- Product-base realization in the form closest to a row transcription: provide
a seed-side row table, a seed-side generator step transported to the standard
root step, and the seed fold equal to `RbaseNeutral`. -/
structure D54ProductBaseSeedRowRealization where
  e0 : Seed ≃ RootState
  seedStep0 : TorusDirection 5 → Seed → Seed
  seedRow0 : D54SeedRow
  stepConj0 :
    ∀ δ s, e0 (seedStep0 δ s) = LowD5M4Schedule.rootStep δ (e0 s)
  seedLayerBijective0 :
    ∀ t : ZMod 4, ∀ c : TorusColor 5,
      Function.Bijective (seedLayerOfSeedRow seedStep0 seedRow0 t c)
  seedReturn_eq_RbaseNeutral :
    ∀ c s,
      seedLayerReturn (seedLayerOfSeedRow seedStep0 seedRow0) c s =
        RbaseNeutral c s

def D54ProductBaseSeedRowRealization.rows0
    (H : D54ProductBaseSeedRowRealization) : PhysicalLayerRows :=
  physicalRowsOfSeedRow H.e0 H.seedRow0

def D54ProductBaseSeedRowRealization.toLayerConjRealization
    (H : D54ProductBaseSeedRowRealization) :
    D54ProductBaseLayerConjRealization where
  rows0 := H.rows0
  e0 := H.e0
  seedLayer0 := seedLayerOfSeedRow H.seedStep0 H.seedRow0
  seedLayerBijective0 := H.seedLayerBijective0
  layerMapConj0 :=
    physicalRowsOfSeedRow_layerMap_conj H.e0 H.seedRow0
      H.seedStep0 H.stepConj0
  seedReturn_eq_RbaseNeutral := H.seedReturn_eq_RbaseNeutral

def D54ProductBaseSeedRowRealization.toProductBaseRealization
    (H : D54ProductBaseSeedRowRealization) :
    D54ProductBaseRealization :=
  H.toLayerConjRealization.toProductBaseRealization

/-- Product-base seed-row realization with the seed generator step fixed as the
pullback of the standard D5 root step through `e0`. -/
structure D54ProductBaseTransportedSeedRowRealization where
  e0 : Seed ≃ RootState
  seedRow0 : D54SeedRow
  seedLayerBijective0 :
    ∀ t : ZMod 4, ∀ c : TorusColor 5,
      Function.Bijective
        (seedLayerOfSeedRow (transportedSeedStep e0) seedRow0 t c)
  seedReturn_eq_RbaseNeutral :
    ∀ c s,
      seedLayerReturn
          (seedLayerOfSeedRow (transportedSeedStep e0) seedRow0) c s =
        RbaseNeutral c s

def D54ProductBaseTransportedSeedRowRealization.toSeedRowRealization
    (H : D54ProductBaseTransportedSeedRowRealization) :
    D54ProductBaseSeedRowRealization where
  e0 := H.e0
  seedStep0 := transportedSeedStep H.e0
  seedRow0 := H.seedRow0
  stepConj0 := transportedSeedStep_conj H.e0
  seedLayerBijective0 := H.seedLayerBijective0
  seedReturn_eq_RbaseNeutral := H.seedReturn_eq_RbaseNeutral

def D54ProductBaseTransportedSeedRowRealization.toLayerConjRealization
    (H : D54ProductBaseTransportedSeedRowRealization) :
    D54ProductBaseLayerConjRealization :=
  H.toSeedRowRealization.toLayerConjRealization

def D54ProductBaseTransportedSeedRowRealization.toProductBaseRealization
    (H : D54ProductBaseTransportedSeedRowRealization) :
    D54ProductBaseRealization :=
  H.toSeedRowRealization.toProductBaseRealization

/-- A product-base realization is not yet the final H2 realization: every
product-base return map is conjugate to `RbaseNeutral`, hence still preserves
the neutral `Z` fiber and is not a single cycle. -/
theorem D54ProductBaseRealization.returnMap_not_singleCycle
    (H : D54ProductBaseRealization) (c : TorusColor 5) :
    ¬ Shared.IsSingleCycleMap
      ((LowD5M4RibbonInterface.schedule H.rows0).returnMap c) := by
  intro hcycle
  exact RbaseNeutral_not_singleCycle c
    (Shared.single_cycle_of_equiv_conj H.e0.symm
      (RbaseNeutral c)
      ((LowD5M4RibbonInterface.schedule H.rows0).returnMap c)
      hcycle
      (by
        intro w
        exact (H.returnMapConj_RbaseNeutral c w).symm))

theorem D54ProductBaseLayerConjRealization.returnMapConj_RbaseNeutral
    (H : D54ProductBaseLayerConjRealization) :
    ∀ c : TorusColor 5, ∀ w : RootState,
      (LowD5M4RibbonInterface.schedule H.rows0).returnMap c w =
        H.e0 (RbaseNeutral c (H.e0.symm w)) :=
  H.toProductBaseRealization.returnMapConj_RbaseNeutral

theorem D54ProductBaseLayerConjRealization.returnMap_not_singleCycle
    (H : D54ProductBaseLayerConjRealization) (c : TorusColor 5) :
    ¬ Shared.IsSingleCycleMap
      ((LowD5M4RibbonInterface.schedule H.rows0).returnMap c) :=
  H.toProductBaseRealization.returnMap_not_singleCycle c

theorem D54ProductBaseSeedRowRealization.returnMapConj_RbaseNeutral
    (H : D54ProductBaseSeedRowRealization) :
    ∀ c : TorusColor 5, ∀ w : RootState,
      (LowD5M4RibbonInterface.schedule H.rows0).returnMap c w =
        H.e0 (RbaseNeutral c (H.e0.symm w)) :=
  H.toLayerConjRealization.returnMapConj_RbaseNeutral

theorem D54ProductBaseSeedRowRealization.returnMap_not_singleCycle
    (H : D54ProductBaseSeedRowRealization) (c : TorusColor 5) :
    ¬ Shared.IsSingleCycleMap
      ((LowD5M4RibbonInterface.schedule H.rows0).returnMap c) :=
  H.toProductBaseRealization.returnMap_not_singleCycle c

/-- Fixed two-stage seed-model realization target.  This is not a construction
of the paper rows by itself; it is a useful narrowed handoff: once physical rows
are known to be layerwise conjugate to `seedTwoStageFullReturnLayer`, the return
conjugacy to `LowD5M4.fullReturn` follows from the closed seed fold theorem. -/
structure D54TwoStageLayerModelRealization where
  rows : PhysicalLayerRows
  e : Seed ≃ RootState
  layerBijective : PhysicalRowsLayerBijectiveGoal rows
  layerMapConj_twoStage :
    ∀ t c s,
      (LowD5M4RibbonInterface.schedule rows).layerMap t c (e s) =
        e (seedTwoStageFullReturnLayer t c s)

/-- Two-stage layer-conjugacy target with RF2 derived automatically from
`seedTwoStageFullReturnLayer_bijective`.  A proof of this object is enough for
the unmarked H2 ribbon handoff; adding singleton-switch data yields the
paper-order final switch certificate below. -/
structure D54TwoStageLayerConjRealization where
  rows : PhysicalLayerRows
  e : Seed ≃ RootState
  layerMapConj_twoStage :
    ∀ t c s,
      (LowD5M4RibbonInterface.schedule rows).layerMap t c (e s) =
        e (seedTwoStageFullReturnLayer t c s)

def D54TwoStageLayerConjRealization.toLayerModelRealization
    (H : D54TwoStageLayerConjRealization) :
    D54TwoStageLayerModelRealization where
  rows := H.rows
  e := H.e
  layerBijective :=
    physical_layerBijective_of_seedLayer_conj
      H.rows H.e seedTwoStageFullReturnLayer
      seedTwoStageFullReturnLayer_bijective
      H.layerMapConj_twoStage
  layerMapConj_twoStage := H.layerMapConj_twoStage

/-- Final two-stage realization in seed-row form.  Compared with
`D54TwoStageLayerConjRealization`, this records the actual seed-side generator
step and row table whose transported physical rows realize the fixed
`seedTwoStageFullReturnLayer` model. -/
structure D54TwoStageSeedRowRealization where
  e : Seed ≃ RootState
  seedStep : TorusDirection 5 → Seed → Seed
  seedRow : D54SeedRow
  stepConj :
    ∀ δ s, e (seedStep δ s) = LowD5M4Schedule.rootStep δ (e s)
  seedLayer_eq_twoStage :
    ∀ t c s,
      seedLayerOfSeedRow seedStep seedRow t c s =
        seedTwoStageFullReturnLayer t c s

def D54TwoStageSeedRowRealization.rows
    (H : D54TwoStageSeedRowRealization) : PhysicalLayerRows :=
  physicalRowsOfSeedRow H.e H.seedRow

theorem D54TwoStageSeedRowRealization.seedLayerBijective
    (H : D54TwoStageSeedRowRealization) :
    ∀ t : ZMod 4, ∀ c : TorusColor 5,
      Function.Bijective (seedLayerOfSeedRow H.seedStep H.seedRow t c) := by
  intro t c
  have h := seedTwoStageFullReturnLayer_bijective t c
  simpa [H.seedLayer_eq_twoStage t c] using h

def D54TwoStageSeedRowRealization.toLayerConjRealization
    (H : D54TwoStageSeedRowRealization) :
    D54TwoStageLayerConjRealization where
  rows := H.rows
  e := H.e
  layerMapConj_twoStage := by
    intro t c s
    calc
      (LowD5M4RibbonInterface.schedule H.rows).layerMap t c (H.e s)
          =
        H.e (seedLayerOfSeedRow H.seedStep H.seedRow t c s) :=
          physicalRowsOfSeedRow_layerMap_conj H.e H.seedRow
            H.seedStep H.stepConj t c s
      _ = H.e (seedTwoStageFullReturnLayer t c s) := by
            rw [H.seedLayer_eq_twoStage t c s]

/-- Final two-stage seed-row realization with the seed generator step fixed as
the pullback of the standard D5 root step through `e`. -/
structure D54TwoStageTransportedSeedRowRealization where
  e : Seed ≃ RootState
  seedRow : D54SeedRow
  seedLayer_eq_twoStage :
    ∀ t c s,
      seedLayerOfSeedRow (transportedSeedStep e) seedRow t c s =
        seedTwoStageFullReturnLayer t c s

def D54TwoStageTransportedSeedRowRealization.toSeedRowRealization
    (H : D54TwoStageTransportedSeedRowRealization) :
    D54TwoStageSeedRowRealization where
  e := H.e
  seedStep := transportedSeedStep H.e
  seedRow := H.seedRow
  stepConj := transportedSeedStep_conj H.e
  seedLayer_eq_twoStage := H.seedLayer_eq_twoStage

def D54TwoStageTransportedSeedRowRealization.toLayerConjRealization
    (H : D54TwoStageTransportedSeedRowRealization) :
    D54TwoStageLayerConjRealization :=
  H.toSeedRowRealization.toLayerConjRealization

def D54TwoStageLayerModelRealization.toMapConjRibbonCollapseInput
    (H : D54TwoStageLayerModelRealization) :
    PhysicalRowsMapConjRibbonCollapseInput where
  rows := H.rows
  e := H.e
  layerBijective := H.layerBijective
  returnMapConj := by
    simpa [PhysicalRowsReturnMapConjGoal, Rhat] using
      physical_returnMap_conj_of_seedLayerReturn_eq
        H.rows H.e seedTwoStageFullReturnLayer Rhat
        H.layerMapConj_twoStage
        seedTwoStageFullReturnLayer_return_eq_Rhat

theorem D54TwoStageLayerModelRealization.nonemptyRibbonData
    (H : D54TwoStageLayerModelRealization) :
    Nonempty ResetPortH2RowEquivRibbonRealizationData :=
  H.toMapConjRibbonCollapseInput.nonemptyRibbonData

theorem D54TwoStageLayerModelRealization.lowBaseFamily
    (H : D54TwoStageLayerModelRealization) :
    FinalLowD5M4RootFlatCertificateFamily :=
  H.toMapConjRibbonCollapseInput.lowBaseFamily

theorem D54TwoStageLayerConjRealization.nonemptyRibbonData
    (H : D54TwoStageLayerConjRealization) :
    Nonempty ResetPortH2RowEquivRibbonRealizationData :=
  H.toLayerModelRealization.nonemptyRibbonData

theorem D54TwoStageLayerConjRealization.lowBaseFamily
    (H : D54TwoStageLayerConjRealization) :
    FinalLowD5M4RootFlatCertificateFamily :=
  H.toLayerModelRealization.lowBaseFamily

theorem D54TwoStageLayerConjRealization.returnMapConj_Rhat
    (H : D54TwoStageLayerConjRealization) :
    PhysicalRowsReturnMapConjGoal H.rows H.e :=
  H.toLayerModelRealization.toMapConjRibbonCollapseInput.returnMapConj

/-- The five local switches after the product base has been built.  This is the
precise row-level target needed by the current H2 handoff. -/
structure D54FiveSwitchRealization where
  rows : PhysicalLayerRows
  rf2 : PhysicalSingletonSwitchLayerData rows
  e : Seed ≃ RootState
  returnMapConj_Rhat : PhysicalRowsReturnMapConjGoal rows e

theorem singleton_partialExchange_conj
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β)
    (T R : β ≃ β) (T' R' : α ≃ α) (p : α)
    (hT : ∀ x, T (e x) = e (T' x))
    (hR : ∀ x, R (e x) = e (R' x))
    (chooseLeft : Bool) :
    ∀ x,
      (if chooseLeft then
        partialExchangeLeft T R ({e p} : Set β)
      else
        partialExchangeRight T R ({e p} : Set β)) (e x) =
        e
          ((if chooseLeft then
            partialExchangeLeft T' R' ({p} : Set α)
          else
            partialExchangeRight T' R' ({p} : Set α)) x) := by
  intro x
  by_cases hx : x = p
  · subst x
    cases chooseLeft <;>
      simp [partialExchangeLeft, partialExchangeRight, hT, hR]
  · have hxe : e x ≠ e p := by
      intro h
      exact hx (e.injective h)
    cases chooseLeft <;>
      simp [partialExchangeLeft, partialExchangeRight, hx, hxe, hT, hR]

/-- Seed-side mirror of the singleton physical RF2 data.  It says that each
physical comparison pair `T/R` and singleton site is transported from a
seed-side pair.  The resulting seed layer is the exact partial exchange seen by
the final return calculation. -/
structure D54SeedSingletonSwitchLayerData
    (rows : PhysicalLayerRows)
    (rf2 : PhysicalSingletonSwitchLayerData rows)
    (e : Seed ≃ RootState) where
  seedT : ZMod 4 → TorusColor 5 → Seed ≃ Seed
  seedR : ZMod 4 → TorusColor 5 → Seed ≃ Seed
  seedSite : ZMod 4 → TorusColor 5 → Seed
  siteConj : ∀ t c, rf2.site t c = e (seedSite t c)
  T_conj : ∀ t c s, rf2.T t c (e s) = e (seedT t c s)
  R_conj : ∀ t c s, rf2.R t c (e s) = e (seedR t c s)

def D54SeedSingletonSwitchLayerData.seedLayer
    {rows : PhysicalLayerRows}
    {rf2 : PhysicalSingletonSwitchLayerData rows}
    {e : Seed ≃ RootState}
    (H : D54SeedSingletonSwitchLayerData rows rf2 e) :
    ZMod 4 → TorusColor 5 → Seed → Seed :=
  fun t c =>
    if rf2.chooseLeft t c then
      partialExchangeLeft (H.seedT t c) (H.seedR t c)
        ({H.seedSite t c} : Set Seed)
    else
      partialExchangeRight (H.seedT t c) (H.seedR t c)
        ({H.seedSite t c} : Set Seed)

theorem D54SeedSingletonSwitchLayerData.layerMapConj
    {rows : PhysicalLayerRows}
    {rf2 : PhysicalSingletonSwitchLayerData rows}
    {e : Seed ≃ RootState}
    (H : D54SeedSingletonSwitchLayerData rows rf2 e) :
    ∀ t c s,
      (LowD5M4RibbonInterface.schedule rows).layerMap t c (e s) =
        e (H.seedLayer t c s) := by
  intro t c s
  calc
    (LowD5M4RibbonInterface.schedule rows).layerMap t c (e s)
        =
          (if rf2.chooseLeft t c then
            partialExchangeLeft (rf2.T t c) (rf2.R t c)
              ({rf2.site t c} : Set RootState)
          else
            partialExchangeRight (rf2.T t c) (rf2.R t c)
              ({rf2.site t c} : Set RootState)) (e s) :=
            rf2.layerMap_eq t c (e s)
    _ =
          (if rf2.chooseLeft t c then
            partialExchangeLeft (rf2.T t c) (rf2.R t c)
              ({e (H.seedSite t c)} : Set RootState)
          else
            partialExchangeRight (rf2.T t c) (rf2.R t c)
              ({e (H.seedSite t c)} : Set RootState)) (e s) := by
            rw [H.siteConj t c]
    _ = e (H.seedLayer t c s) := by
          exact singleton_partialExchange_conj e
            (rf2.T t c) (rf2.R t c)
            (H.seedT t c) (H.seedR t c)
            (H.seedSite t c)
            (H.T_conj t c) (H.R_conj t c)
            (rf2.chooseLeft t c) s

/-- The seed-side singleton switch inherits the common-image condition from the
physical RF2 certificate. -/
theorem D54SeedSingletonSwitchLayerData.seedCommonImage
    {rows : PhysicalLayerRows}
    {rf2 : PhysicalSingletonSwitchLayerData rows}
    {e : Seed ≃ RootState}
    (H : D54SeedSingletonSwitchLayerData rows rf2 e)
    (t : ZMod 4) (c : TorusColor 5) :
    H.seedT t c (H.seedSite t c) =
      H.seedR t c (H.seedSite t c) := by
  apply e.injective
  calc
    e (H.seedT t c (H.seedSite t c))
        = rf2.T t c (e (H.seedSite t c)) := by
            rw [H.T_conj t c (H.seedSite t c)]
    _ = rf2.T t c (rf2.site t c) := by
          rw [H.siteConj t c]
    _ = rf2.R t c (rf2.site t c) :=
          rf2.commonImage t c
    _ = rf2.R t c (e (H.seedSite t c)) := by
          rw [H.siteConj t c]
    _ = e (H.seedR t c (H.seedSite t c)) := by
          rw [H.R_conj t c (H.seedSite t c)]

/-- Each seed-side singleton switch layer is bijective.  This is the seed-level
mirror of RF2 and is useful for finite fold audits of the final switch word. -/
theorem D54SeedSingletonSwitchLayerData.seedLayerBijective
    {rows : PhysicalLayerRows}
    {rf2 : PhysicalSingletonSwitchLayerData rows}
    {e : Seed ≃ RootState}
    (H : D54SeedSingletonSwitchLayerData rows rf2 e)
    (t : ZMod 4) (c : TorusColor 5) :
    Function.Bijective (H.seedLayer t c) := by
  have hpair :=
    partialExchangePair_bijective_singleton_of_common_image
      (H.seedT t c) (H.seedR t c) (H.seedSite t c)
      (H.seedCommonImage t c)
  by_cases hchoose : rf2.chooseLeft t c
  · simpa [D54SeedSingletonSwitchLayerData.seedLayer, hchoose] using hpair.1
  · simpa [D54SeedSingletonSwitchLayerData.seedLayer, hchoose] using hpair.2

/-- Final five-switch target in seed-switch form.  Compared with
`D54FiveSwitchLayerModelRealization`, this pins the seed layer to the same
singleton partial exchanges used for physical RF2. -/
structure D54FiveSwitchSeedSwitchRealization where
  rows : PhysicalLayerRows
  rf2 : PhysicalSingletonSwitchLayerData rows
  e : Seed ≃ RootState
  seedSwitch :
    D54SeedSingletonSwitchLayerData rows rf2 e
  seedReturn_eq_Rhat :
    ∀ c s, seedLayerReturn seedSwitch.seedLayer c s = Rhat c s

/-- Seed-side RF2 for the final five-switch model.  The physical RF2 is supplied
by `rf2`; this theorem records the matching seed-level bijectivity forced by the
same singleton switch data. -/
theorem D54FiveSwitchSeedSwitchRealization.seedLayerBijective
    (H : D54FiveSwitchSeedSwitchRealization)
    (t : ZMod 4) (c : TorusColor 5) :
    Function.Bijective (H.seedSwitch.seedLayer t c) :=
  H.seedSwitch.seedLayerBijective t c

/-- Layer-model form of the final H2 target.  This separates the remaining hard
proof into:

* construction of the final physical rows and singleton-switch RF2 data;
* per-layer conjugacy to seed-side maps;
* a seed-side four-layer calculation equal to `Rhat = LowD5M4.fullReturn`.
-/
structure D54FiveSwitchLayerModelRealization where
  rows : PhysicalLayerRows
  rf2 : PhysicalSingletonSwitchLayerData rows
  e : Seed ≃ RootState
  seedLayer : ZMod 4 → TorusColor 5 → Seed → Seed
  layerMapConj :
    ∀ t c s,
      (LowD5M4RibbonInterface.schedule rows).layerMap t c (e s) =
        e (seedLayer t c s)
  seedReturn_eq_Rhat :
    ∀ c s, seedLayerReturn seedLayer c s = Rhat c s

def D54FiveSwitchSeedSwitchRealization.toLayerModelRealization
    (H : D54FiveSwitchSeedSwitchRealization) :
    D54FiveSwitchLayerModelRealization where
  rows := H.rows
  rf2 := H.rf2
  e := H.e
  seedLayer := H.seedSwitch.seedLayer
  layerMapConj := H.seedSwitch.layerMapConj
  seedReturn_eq_Rhat := H.seedReturn_eq_Rhat

def D54FiveSwitchLayerModelRealization.toFiveSwitchRealization
    (H : D54FiveSwitchLayerModelRealization) :
    D54FiveSwitchRealization where
  rows := H.rows
  rf2 := H.rf2
  e := H.e
  returnMapConj_Rhat := by
    simpa [PhysicalRowsReturnMapConjGoal, Rhat] using
      physical_returnMap_conj_of_seedLayerReturn_eq
        H.rows H.e H.seedLayer Rhat H.layerMapConj H.seedReturn_eq_Rhat

/-- Two-stage audit target plus singleton-switch RF2 data.  This is a narrower
way to supply the final five-switch realization: prove the physical rows are
layerwise conjugate to the closed `seedTwoStageFullReturnLayer` model, and give
the singleton-switch RF2 certificate for the same rows. -/
structure D54TwoStageSingletonSwitchRealization where
  twoStage : D54TwoStageLayerModelRealization
  rf2 : PhysicalSingletonSwitchLayerData twoStage.rows

/-- Singleton-switch version of the two-stage layer-conjugacy target, with RF2
transported from the same singleton data and the layer-model RF2 derived from
seed bijectivity. -/
structure D54TwoStageLayerConjSingletonSwitchRealization where
  twoStage : D54TwoStageLayerConjRealization
  rf2 : PhysicalSingletonSwitchLayerData twoStage.rows

/-- Seed-row version of the final two-stage singleton-switch target.  This is
closest to a literal row construction: the physical rows are transported from the
seed row table, while RF2 is still supplied by the singleton-switch certificate
for those transported rows. -/
structure D54TwoStageSeedRowSingletonSwitchRealization where
  seedRows : D54TwoStageSeedRowRealization
  rf2 : PhysicalSingletonSwitchLayerData seedRows.rows

/-- Final singleton-switch target with transported seed generator step. -/
structure D54TwoStageTransportedSeedRowSingletonSwitchRealization where
  seedRows : D54TwoStageTransportedSeedRowRealization
  rf2 : PhysicalSingletonSwitchLayerData seedRows.toSeedRowRealization.rows

def D54TwoStageLayerConjSingletonSwitchRealization.toTwoStageSingletonSwitchRealization
    (H : D54TwoStageLayerConjSingletonSwitchRealization) :
    D54TwoStageSingletonSwitchRealization where
  twoStage := H.twoStage.toLayerModelRealization
  rf2 := H.rf2

def D54TwoStageSeedRowSingletonSwitchRealization.toLayerConjSingletonSwitchRealization
    (H : D54TwoStageSeedRowSingletonSwitchRealization) :
    D54TwoStageLayerConjSingletonSwitchRealization where
  twoStage := H.seedRows.toLayerConjRealization
  rf2 := H.rf2

def D54TwoStageTransportedSeedRowSingletonSwitchRealization.toSeedRowSingletonSwitchRealization
    (H : D54TwoStageTransportedSeedRowSingletonSwitchRealization) :
    D54TwoStageSeedRowSingletonSwitchRealization where
  seedRows := H.seedRows.toSeedRowRealization
  rf2 := H.rf2

def D54TwoStageTransportedSeedRowSingletonSwitchRealization.toLayerConjSingletonSwitchRealization
    (H : D54TwoStageTransportedSeedRowSingletonSwitchRealization) :
    D54TwoStageLayerConjSingletonSwitchRealization :=
  H.toSeedRowSingletonSwitchRealization.toLayerConjSingletonSwitchRealization

def D54TwoStageSingletonSwitchRealization.toFiveSwitchLayerModelRealization
    (H : D54TwoStageSingletonSwitchRealization) :
    D54FiveSwitchLayerModelRealization where
  rows := H.twoStage.rows
  rf2 := H.rf2
  e := H.twoStage.e
  seedLayer := seedTwoStageFullReturnLayer
  layerMapConj := H.twoStage.layerMapConj_twoStage
  seedReturn_eq_Rhat := seedTwoStageFullReturnLayer_return_eq_Rhat

def D54TwoStageSingletonSwitchRealization.toFiveSwitchRealization
    (H : D54TwoStageSingletonSwitchRealization) :
    D54FiveSwitchRealization :=
  H.toFiveSwitchLayerModelRealization.toFiveSwitchRealization

def D54TwoStageLayerConjSingletonSwitchRealization.toFiveSwitchRealization
    (H : D54TwoStageLayerConjSingletonSwitchRealization) :
    D54FiveSwitchRealization :=
  H.toTwoStageSingletonSwitchRealization.toFiveSwitchRealization

def D54FiveSwitchSeedSwitchRealization.toFiveSwitchRealization
    (H : D54FiveSwitchSeedSwitchRealization) :
    D54FiveSwitchRealization :=
  H.toLayerModelRealization.toFiveSwitchRealization

theorem D54FiveSwitchSeedSwitchRealization.returnMapConj_Rhat
    (H : D54FiveSwitchSeedSwitchRealization) :
    PhysicalRowsReturnMapConjGoal H.rows H.e :=
  H.toFiveSwitchRealization.returnMapConj_Rhat

def D54FiveSwitchRealization.toPhysicalRowsSingletonSwitchMapConjInput
    (H : D54FiveSwitchRealization) :
    PhysicalRowsSingletonSwitchMapConjInput where
  rows := H.rows
  rf2 := H.rf2
  e := H.e
  returnMapConj := H.returnMapConj_Rhat

theorem D54FiveSwitchRealization.nonemptyRibbonData
    (H : D54FiveSwitchRealization) :
    Nonempty ResetPortH2RowEquivRibbonRealizationData :=
  H.toPhysicalRowsSingletonSwitchMapConjInput.nonemptyRibbonData

theorem D54FiveSwitchRealization.lowBaseFamily
    (H : D54FiveSwitchRealization) :
    FinalLowD5M4RootFlatCertificateFamily :=
  H.toPhysicalRowsSingletonSwitchMapConjInput.lowBaseFamily

theorem D54TwoStageSingletonSwitchRealization.nonemptyRibbonData
    (H : D54TwoStageSingletonSwitchRealization) :
    Nonempty ResetPortH2RowEquivRibbonRealizationData :=
  H.toFiveSwitchRealization.nonemptyRibbonData

theorem D54TwoStageSingletonSwitchRealization.lowBaseFamily
    (H : D54TwoStageSingletonSwitchRealization) :
    FinalLowD5M4RootFlatCertificateFamily :=
  H.toFiveSwitchRealization.lowBaseFamily

theorem D54TwoStageLayerConjSingletonSwitchRealization.nonemptyRibbonData
    (H : D54TwoStageLayerConjSingletonSwitchRealization) :
    Nonempty ResetPortH2RowEquivRibbonRealizationData :=
  H.toTwoStageSingletonSwitchRealization.nonemptyRibbonData

theorem D54TwoStageLayerConjSingletonSwitchRealization.lowBaseFamily
    (H : D54TwoStageLayerConjSingletonSwitchRealization) :
    FinalLowD5M4RootFlatCertificateFamily :=
  H.toTwoStageSingletonSwitchRealization.lowBaseFamily

theorem D54TwoStageSeedRowSingletonSwitchRealization.nonemptyRibbonData
    (H : D54TwoStageSeedRowSingletonSwitchRealization) :
    Nonempty ResetPortH2RowEquivRibbonRealizationData :=
  H.toLayerConjSingletonSwitchRealization.nonemptyRibbonData

theorem D54TwoStageSeedRowSingletonSwitchRealization.lowBaseFamily
    (H : D54TwoStageSeedRowSingletonSwitchRealization) :
    FinalLowD5M4RootFlatCertificateFamily :=
  H.toLayerConjSingletonSwitchRealization.lowBaseFamily

theorem D54TwoStageTransportedSeedRowSingletonSwitchRealization.nonemptyRibbonData
    (H : D54TwoStageTransportedSeedRowSingletonSwitchRealization) :
    Nonempty ResetPortH2RowEquivRibbonRealizationData :=
  H.toSeedRowSingletonSwitchRealization.nonemptyRibbonData

theorem D54TwoStageTransportedSeedRowSingletonSwitchRealization.lowBaseFamily
    (H : D54TwoStageTransportedSeedRowSingletonSwitchRealization) :
    FinalLowD5M4RootFlatCertificateFamily :=
  H.toSeedRowSingletonSwitchRealization.lowBaseFamily

theorem D54FiveSwitchSeedSwitchRealization.nonemptyRibbonData
    (H : D54FiveSwitchSeedSwitchRealization) :
    Nonempty ResetPortH2RowEquivRibbonRealizationData :=
  H.toFiveSwitchRealization.nonemptyRibbonData

theorem D54FiveSwitchSeedSwitchRealization.lowBaseFamily
    (H : D54FiveSwitchSeedSwitchRealization) :
    FinalLowD5M4RootFlatCertificateFamily :=
  H.toFiveSwitchRealization.lowBaseFamily

/-- Paper-faithful H2 payload: the row/ribbon realization plus the finite
selector/support/reserve tables used by the paper reset. -/
structure D54PaperRealization extends D54FiveSwitchRealization where
  resetTable : D54ResetData.D54ResetTableCertificate
  finalCylindersAvoidSelector :
    D54ResetData.cylindersAvoidPoints finalCylinders ChatList
  finalCylindersAvoidProtected :
    D54ResetData.cylindersAvoidPoints finalCylinders NhatList
  reserveAvoidFinalCylinders :
    D54ResetData.reservesAvoidCylinders reservePoints finalCylinders
  reserveDisjointSelector :
    D54ResetData.listsDisjoint reservePoints ChatList
  reserveDisjointProtected :
    D54ResetData.listsDisjoint reservePoints NhatList

def D54PaperRealization.toFiveSwitchRealization
    (H : D54PaperRealization) : D54FiveSwitchRealization where
  rows := H.rows
  rf2 := H.rf2
  e := H.e
  returnMapConj_Rhat := H.returnMapConj_Rhat

/-- The table/support side of the paper payload is already finite and closed in
`D54ResetData`.  Thus the only live H2 content needed to build a
`D54PaperRealization` is the final five-switch row/ribbon realization. -/
def D54PaperRealization.ofFiveSwitchRealization
    (H : D54FiveSwitchRealization) : D54PaperRealization where
  toD54FiveSwitchRealization := H
  resetTable := D54ResetData.d54ResetTableCertificate
  finalCylindersAvoidSelector := finalCylinders_avoid_ChatList
  finalCylindersAvoidProtected := finalCylinders_avoid_NhatList
  reserveAvoidFinalCylinders := reservePoints_avoid_finalCylinders
  reserveDisjointSelector := reservePoints_disjoint_ChatList
  reserveDisjointProtected := reservePoints_disjoint_NhatList

def D54PaperRealization.ofFiveSwitchSeedSwitchRealization
    (H : D54FiveSwitchSeedSwitchRealization) :
    D54PaperRealization :=
  D54PaperRealization.ofFiveSwitchRealization H.toFiveSwitchRealization

def D54PaperRealization.ofTwoStageSingletonSwitchRealization
    (H : D54TwoStageSingletonSwitchRealization) :
    D54PaperRealization :=
  D54PaperRealization.ofFiveSwitchRealization H.toFiveSwitchRealization

def D54PaperRealization.ofTwoStageLayerConjSingletonSwitchRealization
    (H : D54TwoStageLayerConjSingletonSwitchRealization) :
    D54PaperRealization :=
  D54PaperRealization.ofTwoStageSingletonSwitchRealization
    H.toTwoStageSingletonSwitchRealization

def D54PaperRealization.ofTwoStageSeedRowSingletonSwitchRealization
    (H : D54TwoStageSeedRowSingletonSwitchRealization) :
    D54PaperRealization :=
  D54PaperRealization.ofTwoStageLayerConjSingletonSwitchRealization
    H.toLayerConjSingletonSwitchRealization

def D54PaperRealization.ofTwoStageTransportedSeedRowSingletonSwitchRealization
    (H : D54TwoStageTransportedSeedRowSingletonSwitchRealization) :
    D54PaperRealization :=
  D54PaperRealization.ofTwoStageSeedRowSingletonSwitchRealization
    H.toSeedRowSingletonSwitchRealization

theorem D54PaperRealization.lowBaseFamily
    (H : D54PaperRealization) :
    FinalLowD5M4RootFlatCertificateFamily :=
  H.toFiveSwitchRealization.lowBaseFamily

theorem D54PaperRealization.nonemptyRibbonData
    (H : D54PaperRealization) :
    Nonempty ResetPortH2RowEquivRibbonRealizationData :=
  H.toFiveSwitchRealization.nonemptyRibbonData

/-- Paper-order construction ladder.  The terminal and product fields document
the provenance of the final five-switch realization; the final H2 consumer only
needs the five-switch rows plus the D54 table facts. -/
structure D54PaperRealizationLadder where
  terminal : TerminalA2M4PhysicalRealization
  productBase : D54ProductBaseRealization
  fiveSwitch : D54FiveSwitchRealization
  resetTable : D54ResetData.D54ResetTableCertificate
  finalCylindersAvoidSelector :
    D54ResetData.cylindersAvoidPoints finalCylinders ChatList
  finalCylindersAvoidProtected :
    D54ResetData.cylindersAvoidPoints finalCylinders NhatList
  reserveAvoidFinalCylinders :
    D54ResetData.reservesAvoidCylinders reservePoints finalCylinders
  reserveDisjointSelector :
    D54ResetData.listsDisjoint reservePoints ChatList
  reserveDisjointProtected :
    D54ResetData.listsDisjoint reservePoints NhatList

def D54PaperRealizationLadder.toPaperRealization
    (H : D54PaperRealizationLadder) :
    D54PaperRealization where
  toD54FiveSwitchRealization := H.fiveSwitch
  resetTable := H.resetTable
  finalCylindersAvoidSelector := H.finalCylindersAvoidSelector
  finalCylindersAvoidProtected := H.finalCylindersAvoidProtected
  reserveAvoidFinalCylinders := H.reserveAvoidFinalCylinders
  reserveDisjointSelector := H.reserveDisjointSelector
  reserveDisjointProtected := H.reserveDisjointProtected

/-- Build the paper-order ladder once the three genuine construction stages have
been supplied.  The reset/support table fields are filled by the closed finite
D54 data. -/
def D54PaperRealizationLadder.ofStages
    (terminal : TerminalA2M4PhysicalRealization)
    (productBase : D54ProductBaseRealization)
    (fiveSwitch : D54FiveSwitchRealization) :
    D54PaperRealizationLadder where
  terminal := terminal
  productBase := productBase
  fiveSwitch := fiveSwitch
  resetTable := D54ResetData.d54ResetTableCertificate
  finalCylindersAvoidSelector := finalCylinders_avoid_ChatList
  finalCylindersAvoidProtected := finalCylinders_avoid_NhatList
  reserveAvoidFinalCylinders := reservePoints_avoid_finalCylinders
  reserveDisjointSelector := reservePoints_disjoint_ChatList
  reserveDisjointProtected := reservePoints_disjoint_NhatList

def D54PaperRealizationLadder.ofStagesTwoStageSingletonSwitch
    (terminal : TerminalA2M4PhysicalRealization)
    (productBase : D54ProductBaseRealization)
    (twoStageSwitch : D54TwoStageSingletonSwitchRealization) :
    D54PaperRealizationLadder :=
  D54PaperRealizationLadder.ofStages terminal productBase
    twoStageSwitch.toFiveSwitchRealization

def D54PaperRealizationLadder.ofStagesTwoStageLayerConjSingletonSwitch
    (terminal : TerminalA2M4PhysicalRealization)
    (productBase : D54ProductBaseRealization)
    (twoStageSwitch : D54TwoStageLayerConjSingletonSwitchRealization) :
    D54PaperRealizationLadder :=
  D54PaperRealizationLadder.ofStagesTwoStageSingletonSwitch
    terminal productBase
    twoStageSwitch.toTwoStageSingletonSwitchRealization

def D54PaperRealizationLadder.ofLayerConjStages
    (terminal : TerminalA2M4PhysicalRealization)
    (productBase : D54ProductBaseLayerConjRealization)
    (twoStageSwitch : D54TwoStageLayerConjSingletonSwitchRealization) :
    D54PaperRealizationLadder :=
  D54PaperRealizationLadder.ofStagesTwoStageLayerConjSingletonSwitch
    terminal productBase.toProductBaseRealization twoStageSwitch

def D54PaperRealizationLadder.ofSeedRowStages
    (terminal : TerminalA2M4PhysicalRealization)
    (productBase : D54ProductBaseSeedRowRealization)
    (twoStageSwitch : D54TwoStageSeedRowSingletonSwitchRealization) :
    D54PaperRealizationLadder :=
  D54PaperRealizationLadder.ofLayerConjStages
    terminal productBase.toLayerConjRealization
    twoStageSwitch.toLayerConjSingletonSwitchRealization

def D54PaperRealizationLadder.ofAllSeedRowStages
    (terminal : TerminalA2M4SeedRowRealization)
    (productBase : D54ProductBaseSeedRowRealization)
    (twoStageSwitch : D54TwoStageSeedRowSingletonSwitchRealization) :
    D54PaperRealizationLadder :=
  D54PaperRealizationLadder.ofSeedRowStages
    terminal.toPhysicalRealization productBase twoStageSwitch

def D54PaperRealizationLadder.ofTransportedSeedRowStages
    (terminal : TerminalA2M4TransportedSeedRowRealization)
    (productBase : D54ProductBaseTransportedSeedRowRealization)
    (twoStageSwitch : D54TwoStageTransportedSeedRowSingletonSwitchRealization) :
    D54PaperRealizationLadder :=
  D54PaperRealizationLadder.ofAllSeedRowStages
    terminal.toSeedRowRealization
    productBase.toSeedRowRealization
    twoStageSwitch.toSeedRowSingletonSwitchRealization

theorem D54PaperRealizationLadder.lowBaseFamily
    (H : D54PaperRealizationLadder) :
    FinalLowD5M4RootFlatCertificateFamily :=
  H.toPaperRealization.lowBaseFamily

theorem D54PaperRealizationLadder.terminalReturnsSingleCycle
    (H : D54PaperRealizationLadder) :
    H.terminal.rows.returnsSingleCycle :=
  H.terminal.returnsSingleCycle

/-- Final assembly theorem for the current H2 route.  The hard content is now
exactly the construction of `D54PaperRealization`. -/
theorem finalLowD5M4RootFlatCertificateFamily_of_paperRealization
    (H : D54PaperRealization) :
    FinalLowD5M4RootFlatCertificateFamily :=
  H.lowBaseFamily

/-- Smallest current H2 closing theorem: once the final physical rows, singleton
RF2 data, and return conjugacy to `LowD5M4.fullReturn` are constructed, the
`D5(4)` root-flat certificate follows. -/
theorem finalLowD5M4RootFlatCertificateFamily_of_fiveSwitchRealization
    (H : D54FiveSwitchRealization) :
    FinalLowD5M4RootFlatCertificateFamily :=
  H.lowBaseFamily

theorem finalLowD5M4RootFlatCertificateFamily_of_paperRealizationLadder
    (H : D54PaperRealizationLadder) :
    FinalLowD5M4RootFlatCertificateFamily :=
  H.lowBaseFamily

theorem finalLowD5M4RootFlatCertificateFamily_of_paperStagesTwoStageSingleton
    (terminal : TerminalA2M4PhysicalRealization)
    (productBase : D54ProductBaseRealization)
    (twoStageSwitch : D54TwoStageSingletonSwitchRealization) :
    FinalLowD5M4RootFlatCertificateFamily :=
  (D54PaperRealizationLadder.ofStagesTwoStageSingletonSwitch
    terminal productBase twoStageSwitch).lowBaseFamily

theorem finalLowD5M4RootFlatCertificateFamily_of_paperStagesTwoStageLayerConjSingleton
    (terminal : TerminalA2M4PhysicalRealization)
    (productBase : D54ProductBaseRealization)
    (twoStageSwitch : D54TwoStageLayerConjSingletonSwitchRealization) :
    FinalLowD5M4RootFlatCertificateFamily :=
  (D54PaperRealizationLadder.ofStagesTwoStageLayerConjSingletonSwitch
    terminal productBase twoStageSwitch).lowBaseFamily

theorem finalLowD5M4RootFlatCertificateFamily_of_paperLayerConjStages
    (terminal : TerminalA2M4PhysicalRealization)
    (productBase : D54ProductBaseLayerConjRealization)
    (twoStageSwitch : D54TwoStageLayerConjSingletonSwitchRealization) :
    FinalLowD5M4RootFlatCertificateFamily :=
  (D54PaperRealizationLadder.ofLayerConjStages
    terminal productBase twoStageSwitch).lowBaseFamily

theorem finalLowD5M4RootFlatCertificateFamily_of_paperSeedRowStages
    (terminal : TerminalA2M4PhysicalRealization)
    (productBase : D54ProductBaseSeedRowRealization)
    (twoStageSwitch : D54TwoStageSeedRowSingletonSwitchRealization) :
    FinalLowD5M4RootFlatCertificateFamily :=
  (D54PaperRealizationLadder.ofSeedRowStages
    terminal productBase twoStageSwitch).lowBaseFamily

theorem finalLowD5M4RootFlatCertificateFamily_of_paperAllSeedRowStages
    (terminal : TerminalA2M4SeedRowRealization)
    (productBase : D54ProductBaseSeedRowRealization)
    (twoStageSwitch : D54TwoStageSeedRowSingletonSwitchRealization) :
    FinalLowD5M4RootFlatCertificateFamily :=
  (D54PaperRealizationLadder.ofAllSeedRowStages
    terminal productBase twoStageSwitch).lowBaseFamily

theorem finalLowD5M4RootFlatCertificateFamily_of_paperTransportedSeedRowStages
    (terminal : TerminalA2M4TransportedSeedRowRealization)
    (productBase : D54ProductBaseTransportedSeedRowRealization)
    (twoStageSwitch : D54TwoStageTransportedSeedRowSingletonSwitchRealization) :
    FinalLowD5M4RootFlatCertificateFamily :=
  (D54PaperRealizationLadder.ofTransportedSeedRowStages
    terminal productBase twoStageSwitch).lowBaseFamily

end D54
end H2
end EvenV11
