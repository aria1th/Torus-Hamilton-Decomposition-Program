import EvenV11.D54ResetData
import EvenV11.LowD5M4RibbonInterface

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

set_option maxRecDepth 100000 in
theorem seedTwoStageFullReturnLayer_return_eq_Rhat :
    ∀ c : TorusColor 5, ∀ s : Seed,
      seedLayerReturn seedTwoStageFullReturnLayer c s = Rhat c s := by
  decide

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
  resetSitesDisjointSelector :
    D54ResetData.listsDisjoint
      D54ResetData.d54TerminalResetSites C4List
  finalCylindersAvoidSelector :
    D54ResetData.cylindersAvoidPoints finalCylinders ChatList
  reserveAvoidFinalCylinders :
    D54ResetData.reservesAvoidCylinders reservePoints finalCylinders
  reserveDisjointSelector :
    D54ResetData.listsDisjoint reservePoints ChatList

def d54SupportTables : D54SupportTables where
  selectorNodup := C4List_nodup
  resetSitesDisjointSelector := resetSites_disjoint_C4List
  finalCylindersAvoidSelector := finalCylinders_avoid_ChatList
  reserveAvoidFinalCylinders := reservePoints_avoid_finalCylinders
  reserveDisjointSelector := reservePoints_disjoint_ChatList

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

/-- Paper-facing terminal A2 realization target at `m = 4`.  It says that an
actual D3 root-flat schedule realizes the collapsed terminal returns `F_i`
through a return-section equivalence.  The equivalence is deliberately a field:
the standard chart `terminalRootEquiv` is too rigid for the paper's
run-collapse correspondence. -/
structure TerminalA2M4PhysicalRealization where
  rows : RootFlatSchedule
    (TorusColor 3) (TorusDirection 3) TerminalRootState 4
  eT : Q4 ≃ TerminalRootState
  rowLatin : rows.rowLatin
  layerBijective : rows.layerBijective
  return_eq_F :
    ∀ c : TorusColor 3, ∀ q : Q4,
      eT.symm (rows.returnMap c (eT q)) = F c q

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
  reserveAvoidFinalCylinders :
    D54ResetData.reservesAvoidCylinders reservePoints finalCylinders
  reserveDisjointSelector :
    D54ResetData.listsDisjoint reservePoints ChatList

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
  reserveAvoidFinalCylinders := reservePoints_avoid_finalCylinders
  reserveDisjointSelector := reservePoints_disjoint_ChatList

def D54PaperRealization.ofFiveSwitchSeedSwitchRealization
    (H : D54FiveSwitchSeedSwitchRealization) :
    D54PaperRealization :=
  D54PaperRealization.ofFiveSwitchRealization H.toFiveSwitchRealization

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
  reserveAvoidFinalCylinders :
    D54ResetData.reservesAvoidCylinders reservePoints finalCylinders
  reserveDisjointSelector :
    D54ResetData.listsDisjoint reservePoints ChatList

def D54PaperRealizationLadder.toPaperRealization
    (H : D54PaperRealizationLadder) :
    D54PaperRealization where
  toD54FiveSwitchRealization := H.fiveSwitch
  resetTable := H.resetTable
  finalCylindersAvoidSelector := H.finalCylindersAvoidSelector
  reserveAvoidFinalCylinders := H.reserveAvoidFinalCylinders
  reserveDisjointSelector := H.reserveDisjointSelector

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
  reserveAvoidFinalCylinders := reservePoints_avoid_finalCylinders
  reserveDisjointSelector := reservePoints_disjoint_ChatList

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

end D54
end H2
end EvenV11
