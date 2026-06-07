import EvenV11.LowD5M4Seed
import EvenV11.LowD5M4Schedule
import EvenV11.FinalTargetLowBaseRootFlatCertificateBridge

/-!
# D5(4) structural certificate — engine-application reduction (H2, paper §11)

This file replaces the `native_decide` blob (`LowD5M4Finite.lean`) route for the
`D5(4)` base with a **structural** assembly that reuses the single-cycle facts
already proved (without `native_decide`) in `LowD5M4Seed.lean` via the unit-carry
engine (Bundle B = paper Lemma `unit-carry`).

## What is proved here (no `sorry`, no `native_decide`)

`finalLowD5M4RootFlatCertificateFamily_of_returnRealization`: given the standard
root-flat lift schedule (`LowD5M4Schedule`, `RootState = Fin 4 → ZMod 4`,
`step = rootStep`) for a direction table `dir`, **plus**

* `hRow`  — RF1, the rows are Latin (`schedule.rowLatin`);
* `hLayer` — RF2, the layer maps are bijective (`schedule.layerBijective`);
* `hReal` — the *layer-row realization*: each generator-move first return
  `schedule.returnMap c` is conjugate, via an explicit coordinate equivalence
  `e : Seed ≃ RootState`, to the abstract skew-tower return `LowD5M4.fullReturn c`,

this produces `FinalLowD5M4RootFlatCertificateFamily`. The proof:

* **RF3** (`returnsSingleCycle`) follows from `hReal` + the *already proved*
  `LowD5M4.fullReturn_singleCycle` by `single_cycle_of_equiv_conj` — this is the
  whole point: the 256-cycle content is structural, not enumerated.
* **stepConjugacy** is free (`LowD5M4Schedule.stepConjugacy_of_dir`, dir-independent).
* the final promotion is `finalRootFlatTorusCertificate_of_fields`.

## What is handed off (the genuine hard math)

The hypotheses `dir`, `e`, `hRow`, `hLayer`, `hReal` are **not** discharged here.
`stepConjugacy` forces `step = rootStep` (real generator moves), so
`schedule.returnMap c` is a 4-layer composition of generator moves on
`Fin 4 → ZMod 4`. The abstract `LowD5M4.fullReturn c` is built from the terminal
`A₂` carriers `F_i = terminalSymbolStep` (not single generator moves). Proving
they are conjugate (`hReal`) is exactly the paper's *"realize these return maps by
layer rows"* step (`D54_parity_reset.tex`, final paragraph): the terminal `A₂`
layer word × the `Y`-row × the neutral `Z`-row, with the five disjoint two-entry
substitutions of Table `D54-reset-ports`, realized by `switching-ribbons`. The
`dir` table and the equivalence `e` are co-designed with that realization; hence
they are supplied together by the user.

Note `hReal` is stated pointwise in the exact shape `single_cycle_of_equiv_conj`
consumes (`e.symm (returnMap c (e x)) = fullReturn c x`), which is the
conjugacy `returnMap c = e ∘ fullReturn c ∘ e.symm`.

The equivalence `e` is deliberately a parameter.  The paper's
`ribbon-realization` argument identifies return-section cycles by a run-collapse
reindexing, not by the tame coordinate chart `Q4 x Y x Z = (ZMod 4)^4`.
-/

namespace EvenV11
namespace LowD5M4Structural

open Shared

/-- The standard root-flat coordinate used by `LowD5M4Schedule` (height-`t`
section of `D5(4)`); 256 states. -/
abbrev RootState := LowD5M4Schedule.RootState

/-- The abstract skew-tower coordinate of `LowD5M4Seed` (`Q4 × Y × Z`); 256
states. The five `LowD5M4.fullReturn` returns are proved 256-cycles here. -/
abbrev Seed := (LowD5M4.Q4 × LowD5M4.Y) × LowD5M4.Z

/-- Build a direction table from explicit Latin rows.  This is the paper-facing
RF1 shape: the D54 row word and its local two-entry switches should produce a
color-direction equivalence at every layer/source. -/
def dirOfRowEquiv
    (row : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    ZMod 4 → RootState → TorusColor 5 → TorusDirection 5 :=
  fun t w c => row t w c

@[simp] theorem dirOfRowEquiv_apply
    (row : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (t : ZMod 4) (w : RootState) (c : TorusColor 5) :
    dirOfRowEquiv row t w c = row t w c :=
  rfl

theorem rowLatin_of_rowEquiv
    (row : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5) :
    (LowD5M4Schedule.schedule (dirOfRowEquiv row)).rowLatin := by
  intro t w
  exact (row t w).bijective

/-- **H2 structural reduction.** The `D5(4)` root-flat certificate family from the
standard lift `dir`, its Latin/bijective layer data, and the layer-row
realization `hReal` connecting the generator-move return to the (already proven
single-cycle) abstract skew return. No `sorry`, no `native_decide`. -/
theorem finalLowD5M4RootFlatCertificateFamily_of_returnRealization
    (dir : ZMod 4 → RootState → TorusColor 5 → TorusDirection 5)
    (e : Seed ≃ RootState)
    (hRow : (LowD5M4Schedule.schedule dir).rowLatin)
    (hLayer : (LowD5M4Schedule.schedule dir).layerBijective)
    (hReal : ∀ c : TorusColor 5, ∀ x : Seed,
        e.symm ((LowD5M4Schedule.schedule dir).returnMap c (e x))
          = LowD5M4.fullReturn c x) :
    FinalLowD5M4RootFlatCertificateFamily := by
  have hReturn : (LowD5M4Schedule.schedule dir).returnsSingleCycle := by
    intro c
    exact single_cycle_of_equiv_conj e
      ((LowD5M4Schedule.schedule dir).returnMap c)
      (LowD5M4.fullReturn c)
      (LowD5M4.fullReturn_singleCycle c)
      (hReal c)
  have cert : FinalRootFlatTorusCertificate 5 4 :=
    finalRootFlatTorusCertificate_of_fields
      (torusEquiv := LowD5M4Schedule.torusEquiv)
      hRow hLayer hReturn
      (fun c tw => LowD5M4Schedule.stepConjugacy_of_dir dir c tw)
  exact finalLowD5M4RootFlatCertificateFamily_of_certificate cert

/-- RF-level H2 data for `D5(4)`: a concrete root-flat direction table together
with RF1/RF2 and direct cyclicity of the five first-return maps. This is the
most general paper-compatible handoff: the cyclicity may come from
`ribbon-realization`, a wild reindexing, or another structural RF argument. -/
structure ResetPortH2RootFlatCycleData where
  dir : ZMod 4 → RootState → TorusColor 5 → TorusDirection 5
  rowLatin : (LowD5M4Schedule.schedule dir).rowLatin
  layerBijective : (LowD5M4Schedule.schedule dir).layerBijective
  returnsSingleCycle : (LowD5M4Schedule.schedule dir).returnsSingleCycle

/-- Build the `D5(4)` low-base family from direct RF-cycle data. -/
theorem finalLowD5M4RootFlatCertificateFamily_of_rootFlatCycleData
    (data : ResetPortH2RootFlatCycleData) :
    FinalLowD5M4RootFlatCertificateFamily := by
  have cert : FinalRootFlatTorusCertificate 5 4 :=
    finalRootFlatTorusCertificate_of_fields
      (torusEquiv := LowD5M4Schedule.torusEquiv)
      data.rowLatin data.layerBijective data.returnsSingleCycle
      (fun c tw => LowD5M4Schedule.stepConjugacy_of_dir data.dir c tw)
  exact finalLowD5M4RootFlatCertificateFamily_of_certificate cert

/-- Main-facing H2 data matching the paper's run-collapse/ribbon route. The
equivalence `e` is intentionally *wild*: it is the return-section reindexing
produced by the ribbon correspondence, not the coordinate chart used to define
the abstract seed. -/
structure ResetPortH2RibbonRealizationData where
  dir : ZMod 4 → RootState → TorusColor 5 → TorusDirection 5
  e : Seed ≃ RootState
  rowLatin : (LowD5M4Schedule.schedule dir).rowLatin
  layerBijective : (LowD5M4Schedule.schedule dir).layerBijective
  returnRealization : ∀ c : TorusColor 5, ∀ x : Seed,
    e.symm ((LowD5M4Schedule.schedule dir).returnMap c (e x))
      = LowD5M4.fullReturn c x

/-- Narrowed paper-facing H2 handoff.  Instead of accepting an arbitrary
direction table plus a separate RF1 proof, this takes explicit Latin rows.
The remaining H2 obligations are RF2 and the ribbon/run-collapse realization. -/
structure ResetPortH2RowEquivRibbonRealizationData where
  row : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5
  e : Seed ≃ RootState
  layerBijective :
    (LowD5M4Schedule.schedule (dirOfRowEquiv row)).layerBijective
  returnRealization : ∀ c : TorusColor 5, ∀ x : Seed,
    e.symm
        ((LowD5M4Schedule.schedule (dirOfRowEquiv row)).returnMap c (e x))
      = LowD5M4.fullReturn c x

/-- Convert the usual map-level conjugacy
`returnMap = e ∘ fullReturn ∘ e.symm` into the pointwise orientation consumed by
`single_cycle_of_equiv_conj` and the H2 handoff records. -/
theorem returnRealization_of_returnMap_conj
    {dir : ZMod 4 → RootState → TorusColor 5 → TorusDirection 5}
    (e : Seed ≃ RootState)
    (hReturn : ∀ c : TorusColor 5, ∀ w : RootState,
      (LowD5M4Schedule.schedule dir).returnMap c w =
        e (LowD5M4.fullReturn c (e.symm w))) :
    ∀ c : TorusColor 5, ∀ x : Seed,
      e.symm ((LowD5M4Schedule.schedule dir).returnMap c (e x))
        = LowD5M4.fullReturn c x := by
  intro c x
  rw [hReturn c (e x)]
  simp

def ribbonRealizationData_of_returnMap_conj
    (dir : ZMod 4 → RootState → TorusColor 5 → TorusDirection 5)
    (e : Seed ≃ RootState)
    (hRow : (LowD5M4Schedule.schedule dir).rowLatin)
    (hLayer : (LowD5M4Schedule.schedule dir).layerBijective)
    (hReturn : ∀ c : TorusColor 5, ∀ w : RootState,
      (LowD5M4Schedule.schedule dir).returnMap c w =
        e (LowD5M4.fullReturn c (e.symm w))) :
    ResetPortH2RibbonRealizationData where
  dir := dir
  e := e
  rowLatin := hRow
  layerBijective := hLayer
  returnRealization := returnRealization_of_returnMap_conj e hReturn

def rowEquivRibbonRealizationData_of_returnMap_conj
    (row : ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5)
    (e : Seed ≃ RootState)
    (hLayer :
      (LowD5M4Schedule.schedule (dirOfRowEquiv row)).layerBijective)
    (hReturn : ∀ c : TorusColor 5, ∀ w : RootState,
      (LowD5M4Schedule.schedule (dirOfRowEquiv row)).returnMap c w =
        e (LowD5M4.fullReturn c (e.symm w))) :
    ResetPortH2RowEquivRibbonRealizationData where
  row := row
  e := e
  layerBijective := hLayer
  returnRealization := returnRealization_of_returnMap_conj e hReturn

def ribbonRealizationData_of_rowEquivRibbonRealizationData
    (data : ResetPortH2RowEquivRibbonRealizationData) :
    ResetPortH2RibbonRealizationData where
  dir := dirOfRowEquiv data.row
  e := data.e
  rowLatin := rowLatin_of_rowEquiv data.row
  layerBijective := data.layerBijective
  returnRealization := data.returnRealization

/-- Strengthened H2 data for the paper-faithful marked route.  This extends the
root-flat ribbon realization with the marked selector and endpoint reserve
evidence that the paper preserves through the D5(4) reset. -/
structure ResetPortH2MarkedRibbonRealizationData extends
    ResetPortH2RibbonRealizationData where
  markedEvidence : FinalMarkedEvidence 5 4

/-- Marked version of the narrowed row-equivalence H2 handoff. -/
structure ResetPortH2MarkedRowEquivRibbonRealizationData extends
    ResetPortH2RowEquivRibbonRealizationData where
  markedEvidence : FinalMarkedEvidence 5 4

def rowEquivRibbonRealizationData_of_markedRowEquivRibbonRealizationData
    (data : ResetPortH2MarkedRowEquivRibbonRealizationData) :
    ResetPortH2RowEquivRibbonRealizationData where
  row := data.row
  e := data.e
  layerBijective := data.layerBijective
  returnRealization := data.returnRealization

def markedRibbonRealizationData_of_markedRowEquivRibbonRealizationData
    (data : ResetPortH2MarkedRowEquivRibbonRealizationData) :
    ResetPortH2MarkedRibbonRealizationData where
  toResetPortH2RibbonRealizationData :=
    ribbonRealizationData_of_rowEquivRibbonRealizationData
      (rowEquivRibbonRealizationData_of_markedRowEquivRibbonRealizationData
        data)
  markedEvidence := data.markedEvidence

def ribbonRealizationData_of_markedRibbonRealizationData
    (data : ResetPortH2MarkedRibbonRealizationData) :
    ResetPortH2RibbonRealizationData where
  dir := data.dir
  e := data.e
  rowLatin := data.rowLatin
  layerBijective := data.layerBijective
  returnRealization := data.returnRealization

/-- Convert the paper ribbon/reindexing data into direct RF-cycle data. -/
def rootFlatCycleData_of_ribbonRealizationData
    (data : ResetPortH2RibbonRealizationData) :
    ResetPortH2RootFlatCycleData where
  dir := data.dir
  rowLatin := data.rowLatin
  layerBijective := data.layerBijective
  returnsSingleCycle := by
    intro c
    exact single_cycle_of_equiv_conj data.e
      ((LowD5M4Schedule.schedule data.dir).returnMap c)
      (LowD5M4.fullReturn c)
      (LowD5M4.fullReturn_singleCycle c)
      (data.returnRealization c)

/-- Build the `D5(4)` low-base family from the paper ribbon/reindexing data. -/
theorem finalLowD5M4RootFlatCertificateFamily_of_ribbonRealizationData
    (data : ResetPortH2RibbonRealizationData) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_rootFlatCycleData
    (rootFlatCycleData_of_ribbonRealizationData data)

/-- Build the `D5(4)` low-base family from the narrowed row-equivalence ribbon
handoff.  RF1 is discharged by `rowLatin_of_rowEquiv`; the caller still supplies
RF2 and the wild return-section conjugacy. -/
theorem finalLowD5M4RootFlatCertificateFamily_of_rowEquivRibbonRealizationData
    (data : ResetPortH2RowEquivRibbonRealizationData) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_ribbonRealizationData
    (ribbonRealizationData_of_rowEquivRibbonRealizationData data)

/-- Paper-faithful marked H2 output.  The ordinary target is still obtained from
the RF certificate; the extra marked evidence is carried as a separate payload. -/
theorem finalLowD5M4MarkedPayload_of_markedRibbonRealizationData
    (data : ResetPortH2MarkedRibbonRealizationData) :
    FinalMarkedPayload 5 4 := by
  let baseData : ResetPortH2RibbonRealizationData :=
    ribbonRealizationData_of_markedRibbonRealizationData data
  let family : FinalLowD5M4RootFlatCertificateFamily :=
    finalLowD5M4RootFlatCertificateFamily_of_ribbonRealizationData baseData
  exact
    { target :=
        finalLowD5M4Target_of_rootFlatCertificateFamily
          family finalLowD5M4ClosedInputs_holds
      evidence := ⟨data.markedEvidence⟩ }

theorem finalLowD5M4Target_of_markedRibbonRealizationData
    (data : ResetPortH2MarkedRibbonRealizationData) :
    FinalMarkedTarget 5 4 :=
  finalMarkedPayload_forget
    (finalLowD5M4MarkedPayload_of_markedRibbonRealizationData data)

theorem finalLowD5M4MarkedPayload_of_nonemptyMarkedRibbonRealizationData
    (hData : Nonempty ResetPortH2MarkedRibbonRealizationData) :
    FinalMarkedPayload 5 4 :=
  finalLowD5M4MarkedPayload_of_markedRibbonRealizationData
    (Classical.choice hData)

theorem finalLowD5M4MarkedPayload_of_markedRowEquivRibbonRealizationData
    (data : ResetPortH2MarkedRowEquivRibbonRealizationData) :
    FinalMarkedPayload 5 4 :=
  finalLowD5M4MarkedPayload_of_markedRibbonRealizationData
    (markedRibbonRealizationData_of_markedRowEquivRibbonRealizationData data)

theorem finalLowD5M4MarkedPayload_of_nonemptyMarkedRowEquivRibbonRealizationData
    (hData : Nonempty ResetPortH2MarkedRowEquivRibbonRealizationData) :
    FinalMarkedPayload 5 4 :=
  finalLowD5M4MarkedPayload_of_markedRowEquivRibbonRealizationData
    (Classical.choice hData)

theorem finalLowD5M4RootFlatCertificateFamily_of_nonemptyRibbonRealizationData
    (hData : Nonempty ResetPortH2RibbonRealizationData) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_ribbonRealizationData
    (Classical.choice hData)

theorem finalLowD5M4RootFlatCertificateFamily_of_nonemptyRowEquivRibbonRealizationData
    (hData : Nonempty ResetPortH2RowEquivRibbonRealizationData) :
    FinalLowD5M4RootFlatCertificateFamily :=
  finalLowD5M4RootFlatCertificateFamily_of_rowEquivRibbonRealizationData
    (Classical.choice hData)

end LowD5M4Structural
end EvenV11
