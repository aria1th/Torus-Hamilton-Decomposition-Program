import EvenV11.V28Hard.HEDWitness
import EvenV11.FoldedCommonEdgeWitness
import EvenV11.LowD7M4Finite
import EvenV11.LowD7M6Finite

/-!
# `HEDWitness 6 4` / `HEDWitness 6 6` — the dimension-7 chain-propagation bases

G3 of the growth-engine plan (`docs/GROWTH_ENGINE_DESIGN_20260610.md` §3 G3);
paper `thm:low-modulus-input-instantiated` + `prop:rank-three-chain-bases` of
the rewritten manuscript (`/data/angel/repos/etc/even_modulus_rewrite_20260610/`,
`subtex/final_induction_framework.tex`).  This file instantiates the two base
witnesses `HED(7, 4)` and `HED(7, 6)` (root dimension `n = 6`) from data that
is already certified in-repo:

* **cycleData** — the H3/H4 pointwise schedules of `LowD7M4Finite` /
  `LowD7M6Finite` (a concrete `dir` on `Fin 4096` / `Fin 46656` with RF1/RF2/RF3
  verified by `native_decide`), transported to the standard lift
  `RootState 6 m = Fin 6 → ZMod m` along the certified little-endian radix
  equivalence `rootIndexEquiv` (the generic conjugation transport below mirrors
  `D54ReturnCore.resetPortH2RootFlatCycleData_of_conjugateSchedule`).
* **selector** — the printed marked witnesses of `FoldedCommonEdgeWitness`:
  colors `(0, 1)` with selector code `68` and common image `1352` at `m = 4`;
  colors `(2, 5)` with selector `2910` and image `10908` at `m = 6`; protected
  neighborhoods `{68, 886, 1352, 3143}` / `{2910, 10908, 41532, 42623}`.  The
  radix-`m` codes decode little-endian in the coordinate order
  `(y0, y1, q0, q1, z0, z1)` — exactly `LowD7M4Finite.rootVecOfIndex`'s
  convention; the selector closure clauses
  `R_a(c) = R_b(c) = I` are re-verified against the actual transported
  schedule by `native_decide` (the decode/indexing cross-check of the
  gate-report mirror `certificates/scripts/check_hed_clauses.py`).
* **reserve** — the ten reserve singletons of `FoldedReserveSeparation`
  (codes `240`–`249` / `1260`–`1269`) in the printed fixed-fiber form
  `(y; m-1, m-1; 0, 0)`; the free coordinates are the two `y`-coordinates.
* **chain** — the REAL chained `7 → 9` rows from `GuideLocality`'s audited
  growth-row tables (supports `[0, 2, 7, 5]` / `[1, 2, 0, 8]`, leaf lines
  `(0, 2)` / `(1, 2)`, quotient generators `(7, 5)` / `(2, 8)`, boundary-avoiding
  phases `ρ = 1, 5`, deltas `2, 1` over `ZMod 9`), chart
  `ZMod 9 \ {0, 1}` and terminal carrier `{3, 4, 6}` (the
  `check_hed_clauses.py` chain-datum bookkeeping items 2 and 5).  The
  `oldGens` lists are the rows' oriented nonzero endpoint pairs
  (`GuideLocality.chainedHighEvenRowNonzeroPairs` — the old generators with
  nonzero image in `P/L`, the only ones the row tests).
* **usedTraces** — the seven-site switching ledger `FoldedSiteTrace.foldedSites4/6`
  (codes `[0, 16, 1092, 128, 144, 32, 96]` / `[0, 36, 1014, 324, 1224, 792, 288]`)
  decoded to states.

This closes the BASE of the chain-propagation driver
(`HEDWitness.propagate`): together with the G4/G5 step family it discharges
H6′.`chainPropagation`.

`native_decide` is used for the Bool clause audits: the selector audits fold
the marked returns through the inventoried `dir` blobs, and the reserve /
separation audits compare `ZMod m`-cast state lists whose kernel reduction is
infeasible at `m = 6` (the casts, not the list sizes, are the cost; plain
`decide`/`decide +kernel` hit `maxRecDepth`/heartbeat walls).  The file is
added to the progress gate's `native_decide` inventory exactly like
`LowD7M4Finite`.  The decode anchors and chain-chart arithmetic close by plain
`decide`.  No `sorry`, no `axiom`.
-/

set_option linter.style.setOption false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000
set_option linter.style.nativeDecide false

namespace EvenV11
namespace V28Hard
namespace HEDBaseWitnesses

open Shared StandardRootFlatLift RootFlatCycle HEDWitness

/-! ## Generic conjugation transport onto the standard lift

`LowD7M4Finite`/`LowD7M6Finite` realize their schedules on packed index types
(`Fin 4096`/`Fin 46656`); `RootFlatCycleData n m` wants the standard lift
`RootState n m = Fin n → ZMod m`.  The bridge is the schedule conjugation along
the certified equivalence whose step fact `e (S.step δ x) = rootStep δ (e x)`
those files prove (`step_rootStep`).  This is the dimension-agnostic form of
`D54ReturnCore.resetPortH2RootFlatCycleData_of_conjugateSchedule`. -/

section Transport

variable {n m : Nat} [NeZero m] {α : Type*}
  (S : Shared.RootFlatSchedule
    (Shared.TorusColor (n + 1)) (Shared.TorusDirection (n + 1)) α m)
  (e : α ≃ RootState n m)

/-- The transported `dir`: read the packed state through `e.symm`. -/
def transportDir :
    ZMod m → RootState n m →
      Shared.TorusColor (n + 1) → Shared.TorusDirection (n + 1) :=
  fun t w c => S.dir t (e.symm w) c

omit [NeZero m] in
theorem transport_layerMap_conj
    (hStep : ∀ δ x, e (S.step δ x) = rootStep δ (e x))
    (t : ZMod m) (c : Shared.TorusColor (n + 1)) (x : α) :
    (schedule (transportDir S e)).layerMap t c (e x) =
      e (S.layerMap t c x) := by
  change rootStep (S.dir t (e.symm (e x)) c) (e x) =
    e (S.step (S.dir t x c) x)
  rw [Equiv.symm_apply_apply, hStep]

omit [NeZero m] in
theorem transport_layerBijective
    (hStep : ∀ δ x, e (S.step δ x) = rootStep δ (e x))
    (hLayer : S.layerBijective) :
    (schedule (transportDir S e)).layerBijective := by
  intro t c
  have hfun :
      (schedule (transportDir S e)).layerMap t c =
        fun w => e (S.layerMap t c (e.symm w)) := by
    funext w
    calc
      (schedule (transportDir S e)).layerMap t c w
          = (schedule (transportDir S e)).layerMap t c (e (e.symm w)) := by
            rw [Equiv.apply_symm_apply]
      _ = e (S.layerMap t c (e.symm w)) :=
            transport_layerMap_conj S e hStep t c (e.symm w)
  rw [hfun]
  exact e.bijective.comp ((hLayer t c).comp e.symm.bijective)

theorem transport_returnMap_conj
    (hStep : ∀ δ x, e (S.step δ x) = rootStep δ (e x))
    (c : Shared.TorusColor (n + 1)) (x : α) :
    (schedule (transportDir S e)).returnMap c (e x) =
      e (S.returnMap c x) := by
  have hFold :
      ∀ ts : List Nat, ∀ y : α,
        ts.foldl
            (fun z (t : Nat) =>
              (schedule (transportDir S e)).layerMap (t : ZMod m) c z)
            (e y) =
          e (ts.foldl
              (fun z (t : Nat) => S.layerMap (t : ZMod m) c z) y) := by
    intro ts
    induction ts with
    | nil =>
        intro y
        rfl
    | cons t ts ih =>
        intro y
        simp only [List.foldl_cons]
        rw [transport_layerMap_conj S e hStep (t : ZMod m) c y]
        exact ih (S.layerMap (t : ZMod m) c y)
  simpa [Shared.RootFlatSchedule.returnMap] using hFold (List.range m) x

/-- RF1/RF2/RF3 transport along a step-conjugating equivalence onto the
standard lift. -/
def cycleDataOfConjugateSchedule
    (hStep : ∀ δ x, e (S.step δ x) = rootStep δ (e x))
    (hRow : S.rowLatin) (hLayer : S.layerBijective)
    (hRet : S.returnsSingleCycle) :
    RootFlatCycleData n m where
  dir := transportDir S e
  rowLatin := fun t w => hRow t (e.symm w)
  layerBijective := transport_layerBijective S e hStep hLayer
  returnsSingleCycle := by
    intro c
    refine Shared.single_cycle_of_equiv_conj e _ (S.returnMap c) (hRet c) ?_
    intro x
    apply e.injective
    rw [Equiv.apply_symm_apply, transport_returnMap_conj S e hStep c x]

end Transport

/-! ## Decoding the certified folded data to standard-lift states

Radix-`m` codes are little-endian in the coordinate order
`(y0, y1, q0, q1, z0, z1)` — coordinate `i` is digit `i`, exactly as
`LowD7M4Finite.rootVecOfIndex` / `LowD7M6Finite.rootVecOfIndex` (and the
rewrite verifier's `dec`).  The closure-clause `native_decide`s below are the
machine cross-check that this is the schedule's state indexing. -/

/-- Decode a radix-`m` code to a six-coordinate standard-lift state. -/
def stateOfCode (m : Nat) [NeZero m] (code : Nat) : RootState 6 m :=
  fun i => ((code / m ^ (i : Nat)) % m : Nat)

/-- Decode a printed `FoldedCoord` (coordinate order `y0 y1 q0 q1 z0 z1`). -/
def stateOfFolded {m : Nat} [NeZero m] (fc : FoldedCoord m) : RootState 6 m :=
  ![fc.y.1, fc.y.2, fc.q.1, fc.q.2, fc.z.1, fc.z.2]

/-- The reserve fiber moves only in the two `y`-coordinates
(the printed `(y; m-1, m-1; 0, 0)` fixed-fiber form). -/
def reserveFreeCoords : List (Fin 6) := [0, 1]

/-! ## The `(7, 4)` base -/

/-- Selector point `c` (code `68`, coords `(0,1,0,1,0,0)`). -/
def selectorPoint4 : RootState 6 4 := stateOfCode 4 68

/-- Common image `I` (code `1352`, coords `(0,2,0,1,1,1)`). -/
def commonImage4 : RootState 6 4 := stateOfCode 4 1352

/-- Protected neighborhood `N(C)` (codes `68, 886, 1352, 3143`). -/
def protectedStates4 : List (RootState 6 4) :=
  (codedCoords protected4).map stateOfFolded

/-- Reserve singletons (codes `240`–`249`, shape `(y; 3, 3; 0, 0)`). -/
def reserveStates4 : List (RootState 6 4) :=
  (reserveCoords reserves4).map stateOfFolded

/-- Seven-site switching ledger (codes `[0, 16, 1092, 128, 144, 32, 96]`). -/
def usedTraces4 : List (RootState 6 4) :=
  (siteCoords foldedSites4).map stateOfFolded

/-- Decode anchors: the decoded states match the printed `FoldedCoord` code
lists (selector/image against `singletonCommonEdgeWitness4`, protected,
reserve and trace lists against their code columns). -/
theorem selectorPoint4_code :
    selectorPoint4 =
      stateOfCode 4 singletonCommonEdgeWitness4.selector.code ∧
    selectorPoint4 =
      stateOfFolded singletonCommonEdgeWitness4.selector.coord := by
  decide

theorem commonImage4_code :
    commonImage4 =
      stateOfCode 4 singletonCommonEdgeWitness4.commonImage.code ∧
    commonImage4 =
      stateOfFolded singletonCommonEdgeWitness4.commonImage.coord := by
  decide

theorem protectedStates4_codes :
    protectedStates4 = (codedCoordCodes protected4).map (stateOfCode 4) := by
  decide

theorem reserveStates4_codes :
    reserveStates4 = (reserveStateCodes reserves4).map (stateOfCode 4) := by
  decide

theorem usedTraces4_codes :
    usedTraces4 = (foldedSiteCodes foldedSites4).map (stateOfCode 4) := by
  decide

/-- The transported `(7, 4)` cycle data (RF1/RF2/RF3 over the standard lift),
conjugated from the inventoried `LowD7M4Finite` witness. -/
def cycleData74 : RootFlatCycleData 6 4 :=
  cycleDataOfConjugateSchedule LowD7M4Finite.schedule
    LowD7M4Finite.rootIndexEquiv LowD7M4Finite.step_rootStep
    LowD7M4Finite.schedule_rowLatin LowD7M4Finite.schedule_layerBijective
    LowD7M4Finite.schedule_returnsSingleCycle

/-- Selector clause audit at `(7, 4)`: marked colors `(0, 1)`, closure
`R_0(c) = R_1(c) = I` re-computed through the transported schedule (the
decode-indexing cross-check), membership and nodup of `N(C)`. -/
theorem selectorClauses4 :
    selectorClausesBool cycleData74.dir 0 1 selectorPoint4 commonImage4
      protectedStates4 = true := by
  native_decide

/-- Reserve clause audit at `(7, 4)`: ten pairwise-distinct singletons in one
`(Q, Z)`-fiber with only the `y`-coordinates free. -/
theorem reserveClauses4 :
    reserveClausesBool reserveStates4 reserveFreeCoords = true := by
  native_decide

/-- Witness-level separation audit at `(7, 4)`: the reserve is separated from
`N(C)` in the pinned coordinates and avoids the seven used traces. -/
theorem reserveSeparation4 :
    reserveSeparationBool protectedStates4 reserveStates4 reserveFreeCoords
      usedTraces4 = true := by
  native_decide

/-! ## The `(7, 6)` base -/

/-- Selector point `c` (code `2910`, coords `(0,5,2,1,2,0)`). -/
def selectorPoint6 : RootState 6 6 := stateOfCode 6 2910

/-- Common image `I` (code `10908`, coords `(0,0,3,2,2,1)`). -/
def commonImage6 : RootState 6 6 := stateOfCode 6 10908

/-- Protected neighborhood `N(C)` (codes `2910, 10908, 41532, 42623`). -/
def protectedStates6 : List (RootState 6 6) :=
  (codedCoords protected6).map stateOfFolded

/-- Reserve singletons (codes `1260`–`1269`, shape `(y; 5, 5; 0, 0)`). -/
def reserveStates6 : List (RootState 6 6) :=
  (reserveCoords reserves6).map stateOfFolded

/-- Seven-site switching ledger
(codes `[0, 36, 1014, 324, 1224, 792, 288]`). -/
def usedTraces6 : List (RootState 6 6) :=
  (siteCoords foldedSites6).map stateOfFolded

theorem selectorPoint6_code :
    selectorPoint6 =
      stateOfCode 6 singletonCommonEdgeWitness6.selector.code ∧
    selectorPoint6 =
      stateOfFolded singletonCommonEdgeWitness6.selector.coord := by
  decide

theorem commonImage6_code :
    commonImage6 =
      stateOfCode 6 singletonCommonEdgeWitness6.commonImage.code ∧
    commonImage6 =
      stateOfFolded singletonCommonEdgeWitness6.commonImage.coord := by
  decide

theorem protectedStates6_codes :
    protectedStates6 = (codedCoordCodes protected6).map (stateOfCode 6) := by
  decide

theorem reserveStates6_codes :
    reserveStates6 = (reserveStateCodes reserves6).map (stateOfCode 6) := by
  decide

theorem usedTraces6_codes :
    usedTraces6 = (foldedSiteCodes foldedSites6).map (stateOfCode 6) := by
  decide

/-- The transported `(7, 6)` cycle data, conjugated from the inventoried
`LowD7M6Finite` witness. -/
def cycleData76 : RootFlatCycleData 6 6 :=
  cycleDataOfConjugateSchedule LowD7M6Finite.schedule
    LowD7M6Finite.rootIndexEquiv LowD7M6Finite.step_rootStep
    LowD7M6Finite.schedule_rowLatin LowD7M6Finite.schedule_layerBijective
    LowD7M6Finite.schedule_returnsSingleCycle

/-- Selector clause audit at `(7, 6)`: marked colors `(2, 5)`, closure
`R_2(c) = R_5(c) = I` re-computed through the transported schedule. -/
theorem selectorClauses6 :
    selectorClausesBool cycleData76.dir 2 5 selectorPoint6 commonImage6
      protectedStates6 = true := by
  native_decide

theorem reserveClauses6 :
    reserveClausesBool reserveStates6 reserveFreeCoords = true := by
  native_decide

theorem reserveSeparation6 :
    reserveSeparationBool protectedStates6 reserveStates6 reserveFreeCoords
      usedTraces6 = true := by
  native_decide

/-! ## Chain fields: the certified chained `7 → 9` interface

The label chart and carrier are the gate report's chain-datum items 2 and 5
(`ZMod 9 \ {0, 1}`, carrier `{3, 4, 6}`); the two rows are `GuideLocality`'s
audited chained growth-row tables verbatim — including the certified
boundary-avoiding phases `ρ = 1, 5`
(`chainedHighEvenBoundaryAvoidingPhaseChoice_spec`) and the real quotient
generators `(7, 5)` / `(2, 8)` (`lem:growth-old-generator-invariant`:
`u_0 - u_8 = (u_0 - u_2) + (u_2 - u_8)`, so the second row's quotient
direction is `u_2 - u_8`, not the raw word edge).  Chart data is independent
of the modulus, so both bases share one `ChainFields 6`. -/

/-- One chained growth row read off `GuideLocality`'s audited tables. -/
def chainedGrowthRowInterface
    (row : GuideLocality.ChainedHighEvenRow) : GrowthRowInterface 6 where
  support := GuideLocality.chainedHighEvenRowSupport row
  leafLine := GuideLocality.chainedHighEvenRowLeafLine row
  quotientGen := GuideLocality.chainedHighEvenRowQuotientGenerator row
  oldGens := GuideLocality.chainedHighEvenRowNonzeroPairs row
  phase := GuideLocality.chainedHighEvenBoundaryAvoidingPhaseChoice row
  delta := GuideLocality.chainedHighEvenRowDelta row

/-- The certified chained `7 → 9` chain fields. -/
def chainedChainFields : ChainFields 6 :=
  ChainFields.ofBool
    (newLabels := (0, 1))
    (oldLabel := fun i => ((i : Nat) : ZMod 9) + 2)
    (rows := fun r =>
      chainedGrowthRowInterface
        (if r = 0 then GuideLocality.ChainedHighEvenRow.first
          else GuideLocality.ChainedHighEvenRow.second))
    (carrier := ![3, 4, 6])
    (by decide)

example : (chainedChainFields.rows 0).support = [0, 2, 7, 5] := by decide
example : (chainedChainFields.rows 1).support = [1, 2, 0, 8] := by decide
example : (chainedChainFields.rows 0).quotientGen = (7, 5) := by decide
example : (chainedChainFields.rows 1).quotientGen = (2, 8) := by decide
example : (chainedChainFields.rows 0).phase = 1 ∧
    (chainedChainFields.rows 1).phase = 5 := by decide

/-- Midpoint guide centers `{ρ - δ, ρ, ρ + δ}` at the certified phases:
`{-1, 1, 3}` and `{4, 5, 6}` (the sets
`chainedHighEvenBoundaryAvoidingPhaseChoice_spec` proves boundary-free). -/
example : chainedChainFields.guideCenters 0 = [8, 1, 3] := by decide
example : chainedChainFields.guideCenters 1 = [4, 5, 6] := by decide

/-! ## The two base witnesses -/

/-- `HED(7, 4)` — the `m = 4` chain-propagation base
(`prop:rank-three-chain-bases`). -/
def hedWitness74 : HEDWitness.HEDWitness 6 4 where
  cycleData := cycleData74
  selector :=
    MarkedSelector.ofBool cycleData74 0 1 selectorPoint4 commonImage4
      protectedStates4 selectorClauses4
  reserve := ReserveSites.ofBool reserveStates4 reserveFreeCoords reserveClauses4
  usedTraces := usedTraces4
  chain := chainedChainFields
  reserveSeparated := (reserveSeparationBool_holds reserveSeparation4).1
  reserveAvoidsTraces := (reserveSeparationBool_holds reserveSeparation4).2

/-- `HED(7, 6)` — the `m = 6` chain-propagation base
(`prop:rank-three-chain-bases`). -/
def hedWitness76 : HEDWitness.HEDWitness 6 6 where
  cycleData := cycleData76
  selector :=
    MarkedSelector.ofBool cycleData76 2 5 selectorPoint6 commonImage6
      protectedStates6 selectorClauses6
  reserve := ReserveSites.ofBool reserveStates6 reserveFreeCoords reserveClauses6
  usedTraces := usedTraces6
  chain := chainedChainFields
  reserveSeparated := (reserveSeparationBool_holds reserveSeparation6).1
  reserveAvoidsTraces := (reserveSeparationBool_holds reserveSeparation6).2

/-! ## Convenience projections and the cross-check against the H3/H4 route -/

/-- The bare `D₇(4)` marked target from the HED witness.  Note: this is an
independent second route to `FinalMarkedTarget 7 4` — the existing one goes
`assume_lowD7M4` → `finalLowD7M4Target_of_rootFlatCertificateFamily`. -/
theorem hedMarkedTarget74 : FinalMarkedTarget 7 4 :=
  hedWitness74.toMarkedTarget

/-- The bare `D₇(6)` marked target from the HED witness (second route next to
`finalLowD7M6Target_of_rootFlatCertificateFamily`). -/
theorem hedMarkedTarget76 : FinalMarkedTarget 7 6 :=
  hedWitness76.toMarkedTarget

/-- Cross-check: the HED route and the existing H3 certificate-family route
prove the same `Prop`, so the proofs agree definitionally. -/
theorem hedMarkedTarget74_eq_lowBaseRoute
    (input : FinalLowD7M4ClosedInputs) :
    hedMarkedTarget74 =
      finalLowD7M4Target_of_rootFlatCertificateFamily
        LowD7M4Finite.finalLowD7M4RootFlatCertificateFamily input :=
  rfl

/-- Cross-check for `(7, 6)` against the H4 route. -/
theorem hedMarkedTarget76_eq_lowBaseRoute
    (input : FinalLowD7M6ClosedInputs) :
    hedMarkedTarget76 =
      finalLowD7M6Target_of_rootFlatCertificateFamily
        LowD7M6Finite.finalLowD7M6RootFlatCertificateFamily input :=
  rfl

/-- Payload form (target + real-content selector/reserve evidence). -/
example : FinalMarkedPayload 7 4 := hedWitness74.toMarkedPayload
example : FinalMarkedPayload 7 6 := hedWitness76.toMarkedPayload

/-- BASE closed: with any G4/G5 step family the driver now reaches every odd
`d ≥ 7` at both low moduli from these witnesses alone. -/
example (step4 : ∀ k, 3 ≤ k → GrowthStep (2 * k) 4)
    (step6 : ∀ k, 3 ≤ k → GrowthStep (2 * k) 6) :
    FinalMarkedTarget 9 4 ∧ FinalMarkedTarget 11 6 :=
  ⟨propagate step4 hedWitness74 9 (by omega) (by omega),
    propagate step6 hedWitness76 11 (by omega) (by omega)⟩

end HEDBaseWitnesses
end V28Hard
end EvenV11
