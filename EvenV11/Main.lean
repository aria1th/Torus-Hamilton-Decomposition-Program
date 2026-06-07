import EvenV11.FinalTargetLowBaseRootFlatCertificateBridge
import EvenV11.LowD5M4RibbonInterface
import EvenV11.LowD5M4Structural
import EvenV11.D54DirectRF
import EvenV11.RootFlatCycleData

/-!
# Even-modulus directed tori: unconditional main theorem (paper-faithful skeleton)

The main theorem is stated **unconditionally** as a `Goal` predicate.  Most
remaining mathematical content is exposed as a small, uniform set of
`sorry`-backed obligations, one per still-open paper case.

**Uniform interface.** Every even-modulus *root-flat base* (`D₃` parametric,
`D₅(4)`, `D₇(4)`, `D₇(6)`) reduces to supplying a root-flat schedule satisfying
the paper's return criterion RF1/RF2/RF3 over the standard lift
(`StandardRootFlatLift`, `step = rootStep`); `stepConjugacy` is then free. The
single-cycle content RF3 comes from the unit-carry engine (`LowD5M4Seed`,
Bundle B), terminal-cyclicity, the ribbon run-collapse, or an explicit finite
root-flat certificate.

* H1/H3/H4 use `RootFlatCycle.RootFlatCycleData` (`dir` + RF1/RF2/RF3) directly.
* H2 is closed for the low-base checklist by the active finite root-flat
  certificate `LowD5M4Finite.finalLowD5M4RootFlatCertificateFamily`.  The
  paper-faithful ribbon handoff `ResetPortH2RowEquivRibbonRealizationData`
  remains exposed below as a stronger realization target, but it is no longer
  an axiom of the main theorem.
* H5/H6 are the parametric odd-branch promotions.

The retired Route E, the tame `paperReturn` / `resetPortRowOfBase` H2
scaffolding, and `Status` live under `archive/EvenV11/`;
see `docs/ROUTE_E_AND_DEADCODE_AUDIT_20260607.md` and
`docs/H2_REALIZATION_BLOCKER_20260605.md` (§8: the t-independent `resetPortRowOfBase`
is RF2-unsatisfiable, hence H2 requires a t-dependent `dir`).

Progress is measured by `#print axioms evenModulusToriAllDimensions`: each open
obligation appears as `sorryAx`.
-/

namespace EvenV11

/-- The unconditional target: every positive-basis directed torus `D_d(m)` with
`d ≥ 2` and even `m ≥ 4` decomposes into `d` directed Hamilton cycles. -/
def EvenModulusToriAllDimensionsGoal : Prop :=
  ∀ {d m : Nat}, 2 ≤ d → Even m → 4 ≤ m → Shared.CayleyHamiltonDecomposition d m

/-! ## Open obligations (uniform paper-faithful root-flat handoffs) -/

/-- H1 — `D₃` even base, **all even `m ≥ 4`** (paper §5 terminal `A₂`).
Parametric root-flat cycle-data: a `dir` on `Fin 2 → ZMod m` with RF1/RF2/RF3
for every even `m ≥ 4` (RF3 = terminal cyclicity, unit-carry). -/
theorem assume_d3CycleData : RootFlatCycle.D3EvenCycleDataFamily := sorry

theorem assume_d3EvenRootFlat : FinalD3EvenRootFlatCertificateFamily :=
  RootFlatCycle.finalD3EvenRootFlatCertificateFamily_of_d3EvenCycleDataFamily
    assume_d3CycleData

/-- H2 — `D₅(4)` (paper §11 parity reset) via the ribbon run-collapse.
The `dir` is a **t-dependent** colour-direction row (RF1 automatic); RF2 holds
because the `Y`- and `Z`-carry substitutions sit on **different layers**; RF3 is
transported from the proved `LowD5M4.fullReturn` 256-cycles by the wild
return-section reindexing `e`. -/
abbrev LowD5M4RibbonData :=
  LowD5M4Structural.ResetPortH2RowEquivRibbonRealizationData

abbrev LowD5M4DirectRFData :=
  LowD5M4Structural.ResetPortH2RootFlatCycleData

abbrev LowD5M4ConjugateDirectRFInput :=
  H2.D54.D54ConjugateDirectRFInput

abbrev LowD5M4PhysicalRibbonInput :=
  LowD5M4RibbonInterface.PhysicalRowsSingletonSwitchMapConjInput

abbrev LowD5M4PaperRealization :=
  H2.D54.D54PaperRealization

abbrev LowD5M4PaperRealizationLadder :=
  H2.D54.D54PaperRealizationLadder

abbrev LowD5M4FiveSwitchRealization :=
  H2.D54.D54FiveSwitchRealization

abbrev LowD5M4TwoStageLayerModelRealization :=
  H2.D54.D54TwoStageLayerModelRealization

abbrev LowD5M4TwoStageSingletonSwitchRealization :=
  H2.D54.D54TwoStageSingletonSwitchRealization

abbrev LowD5M4FiveSwitchLayerModelRealization :=
  H2.D54.D54FiveSwitchLayerModelRealization

abbrev LowD5M4FiveSwitchSeedSwitchRealization :=
  H2.D54.D54FiveSwitchSeedSwitchRealization

theorem lowD5M4RibbonData_of_physicalRibbonInput
    (input : LowD5M4PhysicalRibbonInput) :
    Nonempty LowD5M4RibbonData :=
  input.nonemptyRibbonData

theorem lowD5M4_of_directRFData
    (input : LowD5M4DirectRFData) :
    FinalLowD5M4RootFlatCertificateFamily :=
  LowD5M4Structural.finalLowD5M4RootFlatCertificateFamily_of_rootFlatCycleData
    input

theorem lowD5M4_of_conjugateDirectRFInput
    (input : LowD5M4ConjugateDirectRFInput) :
    FinalLowD5M4RootFlatCertificateFamily :=
  input.lowBaseFamily

theorem lowD5M4RibbonData_of_fiveSwitchRealization
    (input : LowD5M4FiveSwitchRealization) :
    Nonempty LowD5M4RibbonData :=
  input.nonemptyRibbonData

theorem lowD5M4_of_fiveSwitchRealization
    (input : LowD5M4FiveSwitchRealization) :
    FinalLowD5M4RootFlatCertificateFamily :=
  input.lowBaseFamily

theorem lowD5M4RibbonData_of_twoStageLayerModelRealization
    (input : LowD5M4TwoStageLayerModelRealization) :
    Nonempty LowD5M4RibbonData :=
  input.nonemptyRibbonData

theorem lowD5M4_of_twoStageLayerModelRealization
    (input : LowD5M4TwoStageLayerModelRealization) :
    FinalLowD5M4RootFlatCertificateFamily :=
  input.lowBaseFamily

theorem lowD5M4RibbonData_of_twoStageSingletonSwitchRealization
    (input : LowD5M4TwoStageSingletonSwitchRealization) :
    Nonempty LowD5M4RibbonData :=
  input.nonemptyRibbonData

theorem lowD5M4_of_twoStageSingletonSwitchRealization
    (input : LowD5M4TwoStageSingletonSwitchRealization) :
    FinalLowD5M4RootFlatCertificateFamily :=
  input.lowBaseFamily

theorem lowD5M4RibbonData_of_fiveSwitchLayerModelRealization
    (input : LowD5M4FiveSwitchLayerModelRealization) :
    Nonempty LowD5M4RibbonData :=
  input.toFiveSwitchRealization.nonemptyRibbonData

theorem lowD5M4_of_fiveSwitchLayerModelRealization
    (input : LowD5M4FiveSwitchLayerModelRealization) :
    FinalLowD5M4RootFlatCertificateFamily :=
  input.toFiveSwitchRealization.lowBaseFamily

theorem lowD5M4RibbonData_of_fiveSwitchSeedSwitchRealization
    (input : LowD5M4FiveSwitchSeedSwitchRealization) :
    Nonempty LowD5M4RibbonData :=
  input.nonemptyRibbonData

theorem lowD5M4_of_fiveSwitchSeedSwitchRealization
    (input : LowD5M4FiveSwitchSeedSwitchRealization) :
    FinalLowD5M4RootFlatCertificateFamily :=
  input.lowBaseFamily

theorem lowD5M4RibbonData_of_paperRealization
    (input : LowD5M4PaperRealization) :
    Nonempty LowD5M4RibbonData :=
  input.nonemptyRibbonData

theorem lowD5M4RibbonData_of_paperRealizationLadder
    (input : LowD5M4PaperRealizationLadder) :
    Nonempty LowD5M4RibbonData :=
  input.toPaperRealization.nonemptyRibbonData

/-- H2 direct RF certificate.  This closes the `D5(4)` low-base obligation via
`D54ConjugateDirectRFInput`, without using the still-open paper ribbon
realization interface above. -/
theorem lowD5M4_of_finiteRF :
    FinalLowD5M4RootFlatCertificateFamily :=
  H2.D54.finalLowD5M4RootFlatCertificateFamily_of_lowD5M4Finite

theorem assume_lowD5M4 : FinalLowD5M4RootFlatCertificateFamily :=
  lowD5M4_of_finiteRF

/-- H3 — `D₇(4)` (paper App A/B two-rail relay): a `dir` on `Fin 6 → ZMod 4`
with RF1/RF2/RF3. -/
abbrev LowD7M4RootFlatCycleData := RootFlatCycle.RootFlatCycleData 6 4

theorem assume_lowD7M4CycleData : Nonempty LowD7M4RootFlatCycleData := sorry

theorem assume_lowD7M4 : FinalLowD7M4RootFlatCertificateFamily :=
  RootFlatCycle.finalLowD7M4RootFlatCertificateFamily_of_nonemptyCycleData
    assume_lowD7M4CycleData

/-- H4 — `D₇(6)`: a `dir` on `Fin 6 → ZMod 6` with RF1/RF2/RF3. -/
abbrev LowD7M6RootFlatCycleData := RootFlatCycle.RootFlatCycleData 6 6

theorem assume_lowD7M6CycleData : Nonempty LowD7M6RootFlatCycleData := sorry

theorem assume_lowD7M6 : FinalLowD7M6RootFlatCertificateFamily :=
  RootFlatCycle.finalLowD7M6RootFlatCertificateFamily_of_nonemptyCycleData
    assume_lowD7M6CycleData

/-- H5 — odd-dimension high-modulus branch (paper §6 coforest splice + §8 growth). -/
theorem assume_oddHighModulus : FinalOddHighModulusTargetPromotion := sorry

/-- H6 — odd-dimension endpoint branch (paper §9–§10 endpoint successor). -/
theorem assume_oddEndpoint : FinalOddEndpointPhaseProductTargetPromotion := sorry

/-! ## Assembly -/

/-- The full certificate checklist, assembled from the open obligations. -/
theorem evenCertificateChecklist :
    FinalTargetCertificateChecklistWithD3AndLowRootFlat where
  d3RootFlatFamily := assume_d3EvenRootFlat
  lowRootFlatFamilies :=
    { d5m4 := assume_lowD5M4
      d7m4 := assume_lowD7M4
      d7m6 := assume_lowD7M6 }
  oddHighModulusPromotion := assume_oddHighModulus
  oddEndpointPromotion := assume_oddEndpoint

/-- **Main theorem.** Every positive-basis directed torus `D_d(m)` with `d ≥ 2`
and even `m ≥ 4` arc-decomposes into `d` directed Hamilton cycles. -/
theorem evenModulusToriAllDimensions : EvenModulusToriAllDimensionsGoal := by
  intro d m hd hm hm4
  obtain ⟨r, hr⟩ := hm
  exact finalTargetCayley_from_d3AndLowRootFlatChecklist evenCertificateChecklist
    ⟨hd, hm4, r, by omega⟩

end EvenV11
