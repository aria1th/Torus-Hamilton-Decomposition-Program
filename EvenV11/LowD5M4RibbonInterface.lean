import EvenV11.LowD5M4Structural
import EvenV11.Switching

/-!
# D5(4) ribbon-realization interface (paper §11)

This module is the active, archive-free H2 handoff for the manuscript sentence:

> Start with the terminal `A₂` layer word, the `Y` row word, and the neutral
> `Z` row; insert the five disjoint local substitutions.

It does not assert the row table itself.  Instead it gives the exact Lean target
for that remaining proof: a four-layer physical row table, RF2 for those layers,
and a return-section reindexing `e` proving that the actual root-flat returns are
conjugate to `LowD5M4.fullReturn`.
-/

namespace EvenV11
namespace LowD5M4RibbonInterface

open Shared
open LowD5M4Structural

/-- Four physical layer rows after the five reset substitutions have already
been inserted.  Each displayed row is Latin by construction. -/
structure PhysicalLayerRows where
  layer0 : RootState → TorusColor 5 ≃ TorusDirection 5
  layer1 : RootState → TorusColor 5 ≃ TorusDirection 5
  layer2 : RootState → TorusColor 5 ≃ TorusDirection 5
  layer3 : RootState → TorusColor 5 ≃ TorusDirection 5

/-- Convert four displayed rows into the row-equivalence API used by
`LowD5M4Structural`. -/
def PhysicalLayerRows.row
    (rows : PhysicalLayerRows) :
    ZMod 4 → RootState → TorusColor 5 ≃ TorusDirection 5 :=
  fun t w =>
    if t = (0 : ZMod 4) then rows.layer0 w
    else if t = (1 : ZMod 4) then rows.layer1 w
    else if t = (2 : ZMod 4) then rows.layer2 w
    else rows.layer3 w

/-- The root-flat schedule induced by the physical paper rows. -/
abbrev schedule (rows : PhysicalLayerRows) :=
  LowD5M4Schedule.schedule (dirOfRowEquiv rows.row)

/-- RF2 for the physical row schedule. -/
abbrev PhysicalRowsLayerBijectiveGoal (rows : PhysicalLayerRows) : Prop :=
  (schedule rows).layerBijective

/-- Return realization in the orientation used by
`ResetPortH2RowEquivRibbonRealizationData`. -/
abbrev PhysicalRowsReturnRealizationGoal
    (rows : PhysicalLayerRows) (e : Seed ≃ RootState) : Prop :=
  ∀ c : TorusColor 5, ∀ x : Seed,
    e.symm ((schedule rows).returnMap c (e x)) = LowD5M4.fullReturn c x

/-- Equivalent map-level form of the return-section conjugacy.  This is often
the easier shape when proving the row-word/ribbon calculation directly. -/
abbrev PhysicalRowsReturnMapConjGoal
    (rows : PhysicalLayerRows) (e : Seed ≃ RootState) : Prop :=
  ∀ c : TorusColor 5, ∀ w : RootState,
    (schedule rows).returnMap c w =
      e (LowD5M4.fullReturn c (e.symm w))

/-- Map-level conjugacy implies the pointwise H2 realization field. -/
theorem returnRealization_of_returnMap_conj
    {rows : PhysicalLayerRows} {e : Seed ≃ RootState}
    (hReturn : PhysicalRowsReturnMapConjGoal rows e) :
    PhysicalRowsReturnRealizationGoal rows e := by
  simpa [schedule, PhysicalRowsReturnMapConjGoal,
    PhysicalRowsReturnRealizationGoal] using
    LowD5M4Structural.returnRealization_of_returnMap_conj
      (dir := dirOfRowEquiv rows.row) e hReturn

/-- Main H2 input after the paper rows have been transcribed.  This is the
preferred replacement target for `EvenV11.assume_lowD5M4RibbonData`. -/
structure PhysicalRowsRibbonCollapseInput where
  rows : PhysicalLayerRows
  e : Seed ≃ RootState
  layerBijective : PhysicalRowsLayerBijectiveGoal rows
  returnRealization : PhysicalRowsReturnRealizationGoal rows e

def PhysicalRowsRibbonCollapseInput.toRowEquivRibbonRealizationData
    (input : PhysicalRowsRibbonCollapseInput) :
    ResetPortH2RowEquivRibbonRealizationData where
  row := input.rows.row
  e := input.e
  layerBijective := input.layerBijective
  returnRealization := input.returnRealization

theorem PhysicalRowsRibbonCollapseInput.nonemptyRibbonData
    (input : PhysicalRowsRibbonCollapseInput) :
    Nonempty ResetPortH2RowEquivRibbonRealizationData :=
  ⟨input.toRowEquivRibbonRealizationData⟩

theorem PhysicalRowsRibbonCollapseInput.lowBaseFamily
    (input : PhysicalRowsRibbonCollapseInput) :
    FinalLowD5M4RootFlatCertificateFamily :=
  LowD5M4Structural.finalLowD5M4RootFlatCertificateFamily_of_rowEquivRibbonRealizationData
    input.toRowEquivRibbonRealizationData

/-- Same H2 input, with RF3 supplied in map-level conjugacy form. -/
structure PhysicalRowsMapConjRibbonCollapseInput where
  rows : PhysicalLayerRows
  e : Seed ≃ RootState
  layerBijective : PhysicalRowsLayerBijectiveGoal rows
  returnMapConj : PhysicalRowsReturnMapConjGoal rows e

def PhysicalRowsMapConjRibbonCollapseInput.toRibbonCollapseInput
    (input : PhysicalRowsMapConjRibbonCollapseInput) :
    PhysicalRowsRibbonCollapseInput where
  rows := input.rows
  e := input.e
  layerBijective := input.layerBijective
  returnRealization :=
    returnRealization_of_returnMap_conj input.returnMapConj

theorem PhysicalRowsMapConjRibbonCollapseInput.nonemptyRibbonData
    (input : PhysicalRowsMapConjRibbonCollapseInput) :
    Nonempty ResetPortH2RowEquivRibbonRealizationData :=
  input.toRibbonCollapseInput.nonemptyRibbonData

theorem PhysicalRowsMapConjRibbonCollapseInput.lowBaseFamily
    (input : PhysicalRowsMapConjRibbonCollapseInput) :
    FinalLowD5M4RootFlatCertificateFamily :=
  input.toRibbonCollapseInput.lowBaseFamily

/-! ## RF2 helpers for the local two-entry exchange route -/

/-- RF2 data for a physical row table expressed layer/color-wise as a partial
exchange between two bijections.  This is the abstract form of the paper's local
switching-ribbon substitutions. -/
structure PhysicalPartialExchangeLayerData
    (rows : PhysicalLayerRows) where
  T : ZMod 4 → TorusColor 5 → RootState ≃ RootState
  R : ZMod 4 → TorusColor 5 → RootState ≃ RootState
  U : ZMod 4 → TorusColor 5 → Set RootState
  chooseLeft : ZMod 4 → TorusColor 5 → Bool
  [decidableMem : ∀ t c w, Decidable (w ∈ U t c)]
  invariant : ∀ t c, ComparisonSetInvariant (T t c) (R t c) (U t c)
  layerMap_eq :
    ∀ t c w,
      (schedule rows).layerMap t c w =
        (if chooseLeft t c then
          partialExchangeLeft (T t c) (R t c) (U t c)
        else
          partialExchangeRight (T t c) (R t c) (U t c)) w

theorem physicalRowsLayerBijective_of_partialExchangeLayerData
    {rows : PhysicalLayerRows}
    (data : PhysicalPartialExchangeLayerData rows) :
    PhysicalRowsLayerBijectiveGoal rows := by
  letI := data.decidableMem
  exact rootFlatLayerBijective_of_partialExchangeChoice_eq
    (schedule rows)
    data.T data.R data.U data.chooseLeft data.invariant data.layerMap_eq

/-- Singleton-switch specialization of RF2.  This is the expected shape for the
five local substitutions in Table D54-reset-ports. -/
structure PhysicalSingletonSwitchLayerData
    (rows : PhysicalLayerRows) where
  T : ZMod 4 → TorusColor 5 → RootState ≃ RootState
  R : ZMod 4 → TorusColor 5 → RootState ≃ RootState
  site : ZMod 4 → TorusColor 5 → RootState
  chooseLeft : ZMod 4 → TorusColor 5 → Bool
  commonImage : ∀ t c, T t c (site t c) = R t c (site t c)
  layerMap_eq :
    ∀ t c w,
      (schedule rows).layerMap t c w =
        (if chooseLeft t c then
          partialExchangeLeft (T t c) (R t c)
            ({site t c} : Set RootState)
        else
          partialExchangeRight (T t c) (R t c)
            ({site t c} : Set RootState)) w

def partialExchangeLayerData_of_singletonSwitchLayerData
    {rows : PhysicalLayerRows}
    (data : PhysicalSingletonSwitchLayerData rows) :
    PhysicalPartialExchangeLayerData rows where
  T := data.T
  R := data.R
  U := fun t c => ({data.site t c} : Set RootState)
  chooseLeft := data.chooseLeft
  decidableMem := fun _ _ _ => inferInstance
  invariant := fun t c =>
    comparisonSetInvariant_singleton_of_common_image
      (data.commonImage t c)
  layerMap_eq := data.layerMap_eq

theorem physicalRowsLayerBijective_of_singletonSwitchLayerData
    {rows : PhysicalLayerRows}
    (data : PhysicalSingletonSwitchLayerData rows) :
    PhysicalRowsLayerBijectiveGoal rows :=
  physicalRowsLayerBijective_of_partialExchangeLayerData
    (partialExchangeLayerData_of_singletonSwitchLayerData data)

/-- Full preferred H2 target with RF2 in singleton-switch form. -/
structure PhysicalRowsSingletonSwitchRibbonCollapseInput where
  rows : PhysicalLayerRows
  rf2 : PhysicalSingletonSwitchLayerData rows
  e : Seed ≃ RootState
  returnRealization : PhysicalRowsReturnRealizationGoal rows e

def PhysicalRowsSingletonSwitchRibbonCollapseInput.toRibbonCollapseInput
    (input : PhysicalRowsSingletonSwitchRibbonCollapseInput) :
    PhysicalRowsRibbonCollapseInput where
  rows := input.rows
  e := input.e
  layerBijective :=
    physicalRowsLayerBijective_of_singletonSwitchLayerData input.rf2
  returnRealization := input.returnRealization

theorem PhysicalRowsSingletonSwitchRibbonCollapseInput.nonemptyRibbonData
    (input : PhysicalRowsSingletonSwitchRibbonCollapseInput) :
    Nonempty ResetPortH2RowEquivRibbonRealizationData :=
  input.toRibbonCollapseInput.nonemptyRibbonData

theorem PhysicalRowsSingletonSwitchRibbonCollapseInput.lowBaseFamily
    (input : PhysicalRowsSingletonSwitchRibbonCollapseInput) :
    FinalLowD5M4RootFlatCertificateFamily :=
  input.toRibbonCollapseInput.lowBaseFamily

/-- Singleton-switch RF2 plus map-level return conjugacy. -/
structure PhysicalRowsSingletonSwitchMapConjInput where
  rows : PhysicalLayerRows
  rf2 : PhysicalSingletonSwitchLayerData rows
  e : Seed ≃ RootState
  returnMapConj : PhysicalRowsReturnMapConjGoal rows e

def PhysicalRowsSingletonSwitchMapConjInput.toSingletonSwitchInput
    (input : PhysicalRowsSingletonSwitchMapConjInput) :
    PhysicalRowsSingletonSwitchRibbonCollapseInput where
  rows := input.rows
  rf2 := input.rf2
  e := input.e
  returnRealization :=
    returnRealization_of_returnMap_conj input.returnMapConj

theorem PhysicalRowsSingletonSwitchMapConjInput.nonemptyRibbonData
    (input : PhysicalRowsSingletonSwitchMapConjInput) :
    Nonempty ResetPortH2RowEquivRibbonRealizationData :=
  input.toSingletonSwitchInput.nonemptyRibbonData

theorem PhysicalRowsSingletonSwitchMapConjInput.lowBaseFamily
    (input : PhysicalRowsSingletonSwitchMapConjInput) :
    FinalLowD5M4RootFlatCertificateFamily :=
  input.toSingletonSwitchInput.lowBaseFamily

end LowD5M4RibbonInterface
end EvenV11
