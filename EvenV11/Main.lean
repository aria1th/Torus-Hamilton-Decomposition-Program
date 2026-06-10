import EvenV11.FinalTargetLowBaseRootFlatCertificateBridge
import EvenV11.LowD5M4RibbonInterface
import EvenV11.LowD5M4Structural
import EvenV11.D54DirectRF
import EvenV11.RootFlatCycleData
import EvenV11.V28Hard.PaperExactStructure
import EvenV11.V28Hard.TerminalA2IntervalSplice
import EvenV11.V28Hard.D3TerminalA2PerColor
import EvenV11.V28Hard.D3EvenRailWiring
import EvenV11.V28Hard.OddLowClosureBridge
import EvenV11.LowD7M4Finite
import EvenV11.LowD7M6Finite

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
* H5 is the parametric odd high-modulus promotion; it now also powers the
  modulus-free restart of H6′ below.
* H6 follows the REWRITTEN paper architecture
  (`/data/angel/repos/etc/even_modulus_rewrite_20260610/`,
  `subtex/high_even_growth.tex` + `subtex/final_induction_framework.tex`):
  the odd low-modulus range is closed by chain propagation from the certified
  dimension-7 bases (`cor:odd-chain-propagation`, `m ∈ {4, 6}`) plus the
  modulus-free restart of the high-even closure at `D₀ = m − 1`
  (`cor:modulus-free-restart`, even `8 ≤ m ≤ d`).  The single hole is
  `V28Hard.OddLowClosureBridge.OddLowClosure`; the old endpoint interface is
  derived from it sorry-free (`oddEndpointPromotion_of_oddLowClosure`), so the
  checklist below is unchanged.  The endpoint-successor scaffolding of the
  earlier manuscript (EndpointChart/PortRoom/RowSchedule/SeedReturns/
  ParentCycle/Realization, E6) stays off-spine under `EvenV11.V28Hard`.

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

/-- H1a — terminal carrier cyclicity (paper `lem:terminal-cyclicity`).  For every
even `m ≥ 4` the three collapsed terminal `A₂` carriers `Fᵢ = terminalReturn i`
are single `m²`-cycles on `Qₘ = (ℤ/m)²`.  CLOSED: the generic even `m ≥ 6` case
is the interval-splice argument (`V28Hard.TerminalA2IntervalSplice`), splicing
the straight fiber intervals along the endpoint recurrence `Aʳ/Bʳ` rank list;
`m = 4` is the finite orbit certificate (`terminalA2M4FiniteCyclicity`). -/
theorem assume_d3TerminalCarrierCyclicity :
    V28Hard.D3TerminalA2Parametric.TerminalA2CarrierCyclicityFamily :=
  V28Hard.TerminalA2IntervalSplice.terminalA2CarrierCyclicityFamily

/-- H1b — terminal `A₂` root-flat realization (paper terminal row expansion),
**per-color form**.  CLOSED via the rail-seam schedule
(`docs/WILDE_SEARCH_20260610.md`): module 1 (`V28Hard.D3EvenRailSeam`) builds
the wild seam layer, module 2 (`V28Hard.D3EvenRailSchedule`) installs it into
a standard root-flat schedule with RF1/RF2 and reduces the first return to a
conjugated core map, and module 3 closes RF3 for both drift cases —
`V28Hard.D3EvenRailCore3Free` (`3 ∤ m`) and `V28Hard.D3EvenRailCore3Dvd`
(`3 ∣ m`) — by two-level interval splices (numeric ground truth:
`scripts/search_d3_even_dir.py core3free` / `core3dvd`).  The per-color wild
run-collapse `sectionEquiv` demanded here (the plain chart `rootPairEquiv` is
too rigid, `docs/H1B_REALIZATION_OBSTRUCTION_20260609.md`) is CONSTRUCTED in
`V28Hard.D3EvenRailWiring.perColorRealization_of_cycleData` by composing the
orbit-rank enumerations of the schedule first returns (RF3) and of the proven
terminal carriers (H1a). -/
theorem assume_d3TerminalRealization :
    Nonempty V28Hard.D3TerminalA2PerColor.TerminalA2PerColorRealizationFamily :=
  V28Hard.D3EvenRailWiring.perColorRealization_of_cycleData
    V28Hard.D3EvenRailWiring.railCycleDataFamily
    assume_d3TerminalCarrierCyclicity

/-- H1 — `D₃` even base, **all even `m ≥ 4`** (paper §5 terminal `A₂`).  Assembled
from the two separated obligations above by the closed conjugacy adapter
`cycleDataFamily_of_carrierCyclicity_and_perColorRealization`: carrier cyclicity
supplies RF3 and the realization supplies RF1/RF2 + the per-color conjugacy. -/
theorem assume_d3CycleData : RootFlatCycle.D3EvenCycleDataFamily :=
  V28Hard.D3TerminalA2PerColor.cycleDataFamily_of_carrierCyclicity_and_perColorRealization
    assume_d3TerminalCarrierCyclicity
    (Classical.choice assume_d3TerminalRealization)

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

abbrev LowD5M4TerminalRealization :=
  H2.D54.TerminalA2M4PhysicalRealization

abbrev LowD5M4TerminalSeedRowRealization :=
  H2.D54.TerminalA2M4SeedRowRealization

abbrev LowD5M4TerminalTransportedSeedRowRealization :=
  H2.D54.TerminalA2M4TransportedSeedRowRealization

abbrev LowD5M4ProductBaseRealization :=
  H2.D54.D54ProductBaseRealization

abbrev LowD5M4ProductBaseLayerConjRealization :=
  H2.D54.D54ProductBaseLayerConjRealization

abbrev LowD5M4ProductBaseSeedRowRealization :=
  H2.D54.D54ProductBaseSeedRowRealization

abbrev LowD5M4ProductBaseTransportedSeedRowRealization :=
  H2.D54.D54ProductBaseTransportedSeedRowRealization

abbrev LowD5M4TwoStageLayerModelRealization :=
  H2.D54.D54TwoStageLayerModelRealization

abbrev LowD5M4TwoStageLayerConjRealization :=
  H2.D54.D54TwoStageLayerConjRealization

abbrev LowD5M4TwoStageSeedRowRealization :=
  H2.D54.D54TwoStageSeedRowRealization

abbrev LowD5M4TwoStageTransportedSeedRowRealization :=
  H2.D54.D54TwoStageTransportedSeedRowRealization

abbrev LowD5M4TwoStageSingletonSwitchRealization :=
  H2.D54.D54TwoStageSingletonSwitchRealization

abbrev LowD5M4TwoStageLayerConjSingletonSwitchRealization :=
  H2.D54.D54TwoStageLayerConjSingletonSwitchRealization

abbrev LowD5M4TwoStageSeedRowSingletonSwitchRealization :=
  H2.D54.D54TwoStageSeedRowSingletonSwitchRealization

abbrev LowD5M4TwoStageTransportedSeedRowSingletonSwitchRealization :=
  H2.D54.D54TwoStageTransportedSeedRowSingletonSwitchRealization

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

def lowD5M4TerminalRealization_of_terminalSeedRowRealization
    (input : LowD5M4TerminalSeedRowRealization) :
    LowD5M4TerminalRealization :=
  input.toPhysicalRealization

def lowD5M4TerminalSeedRowRealization_of_terminalTransportedSeedRowRealization
    (input : LowD5M4TerminalTransportedSeedRowRealization) :
    LowD5M4TerminalSeedRowRealization :=
  input.toSeedRowRealization

def lowD5M4ProductBaseRealization_of_productBaseLayerConjRealization
    (input : LowD5M4ProductBaseLayerConjRealization) :
    LowD5M4ProductBaseRealization :=
  input.toProductBaseRealization

def lowD5M4ProductBaseLayerConjRealization_of_productBaseSeedRowRealization
    (input : LowD5M4ProductBaseSeedRowRealization) :
    LowD5M4ProductBaseLayerConjRealization :=
  input.toLayerConjRealization

def lowD5M4ProductBaseSeedRowRealization_of_productBaseTransportedSeedRowRealization
    (input : LowD5M4ProductBaseTransportedSeedRowRealization) :
    LowD5M4ProductBaseSeedRowRealization :=
  input.toSeedRowRealization

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

theorem lowD5M4RibbonData_of_twoStageLayerConjRealization
    (input : LowD5M4TwoStageLayerConjRealization) :
    Nonempty LowD5M4RibbonData :=
  input.nonemptyRibbonData

theorem lowD5M4_of_twoStageLayerConjRealization
    (input : LowD5M4TwoStageLayerConjRealization) :
    FinalLowD5M4RootFlatCertificateFamily :=
  input.lowBaseFamily

def lowD5M4TwoStageLayerConjRealization_of_seedRowRealization
    (input : LowD5M4TwoStageSeedRowRealization) :
    LowD5M4TwoStageLayerConjRealization :=
  input.toLayerConjRealization

def lowD5M4TwoStageSeedRowRealization_of_transportedSeedRowRealization
    (input : LowD5M4TwoStageTransportedSeedRowRealization) :
    LowD5M4TwoStageSeedRowRealization :=
  input.toSeedRowRealization

theorem lowD5M4RibbonData_of_twoStageSingletonSwitchRealization
    (input : LowD5M4TwoStageSingletonSwitchRealization) :
    Nonempty LowD5M4RibbonData :=
  input.nonemptyRibbonData

theorem lowD5M4_of_twoStageSingletonSwitchRealization
    (input : LowD5M4TwoStageSingletonSwitchRealization) :
    FinalLowD5M4RootFlatCertificateFamily :=
  input.lowBaseFamily

theorem lowD5M4RibbonData_of_twoStageLayerConjSingletonSwitchRealization
    (input : LowD5M4TwoStageLayerConjSingletonSwitchRealization) :
    Nonempty LowD5M4RibbonData :=
  input.nonemptyRibbonData

theorem lowD5M4_of_twoStageLayerConjSingletonSwitchRealization
    (input : LowD5M4TwoStageLayerConjSingletonSwitchRealization) :
    FinalLowD5M4RootFlatCertificateFamily :=
  input.lowBaseFamily

theorem lowD5M4RibbonData_of_twoStageSeedRowSingletonSwitchRealization
    (input : LowD5M4TwoStageSeedRowSingletonSwitchRealization) :
    Nonempty LowD5M4RibbonData :=
  input.nonemptyRibbonData

theorem lowD5M4_of_twoStageSeedRowSingletonSwitchRealization
    (input : LowD5M4TwoStageSeedRowSingletonSwitchRealization) :
    FinalLowD5M4RootFlatCertificateFamily :=
  input.lowBaseFamily

def lowD5M4TwoStageSingletonSwitchRealization_of_layerConjSingletonSwitchRealization
    (input : LowD5M4TwoStageLayerConjSingletonSwitchRealization) :
    LowD5M4TwoStageSingletonSwitchRealization :=
  input.toTwoStageSingletonSwitchRealization

def lowD5M4TwoStageLayerConjSingletonSwitchRealization_of_seedRowSingletonSwitchRealization
    (input : LowD5M4TwoStageSeedRowSingletonSwitchRealization) :
    LowD5M4TwoStageLayerConjSingletonSwitchRealization :=
  input.toLayerConjSingletonSwitchRealization

def lowD5M4TwoStageSeedRowSingletonSwitchRealization_of_transportedSeedRowSingletonSwitchRealization
    (input : LowD5M4TwoStageTransportedSeedRowSingletonSwitchRealization) :
    LowD5M4TwoStageSeedRowSingletonSwitchRealization :=
  input.toSeedRowSingletonSwitchRealization

def lowD5M4PaperRealization_of_twoStageSingletonSwitchRealization
    (input : LowD5M4TwoStageSingletonSwitchRealization) :
    LowD5M4PaperRealization :=
  H2.D54.D54PaperRealization.ofTwoStageSingletonSwitchRealization input

def lowD5M4PaperRealization_of_twoStageLayerConjSingletonSwitchRealization
    (input : LowD5M4TwoStageLayerConjSingletonSwitchRealization) :
    LowD5M4PaperRealization :=
  H2.D54.D54PaperRealization.ofTwoStageLayerConjSingletonSwitchRealization input

def lowD5M4PaperRealization_of_twoStageSeedRowSingletonSwitchRealization
    (input : LowD5M4TwoStageSeedRowSingletonSwitchRealization) :
    LowD5M4PaperRealization :=
  H2.D54.D54PaperRealization.ofTwoStageSeedRowSingletonSwitchRealization input

def lowD5M4PaperRealization_of_twoStageTransportedSeedRowSingletonSwitchRealization
    (input : LowD5M4TwoStageTransportedSeedRowSingletonSwitchRealization) :
    LowD5M4PaperRealization :=
  H2.D54.D54PaperRealization.ofTwoStageTransportedSeedRowSingletonSwitchRealization input

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

theorem lowD5M4_of_paperRealization
    (input : LowD5M4PaperRealization) :
    FinalLowD5M4RootFlatCertificateFamily :=
  input.lowBaseFamily

theorem lowD5M4RibbonData_of_paperRealizationLadder
    (input : LowD5M4PaperRealizationLadder) :
    Nonempty LowD5M4RibbonData :=
  input.toPaperRealization.nonemptyRibbonData

theorem lowD5M4_of_paperRealizationLadder
    (input : LowD5M4PaperRealizationLadder) :
    FinalLowD5M4RootFlatCertificateFamily :=
  input.lowBaseFamily

theorem lowD5M4_of_paperStagesTwoStageSingleton
    (terminal : LowD5M4TerminalRealization)
    (productBase : LowD5M4ProductBaseRealization)
    (twoStageSwitch : LowD5M4TwoStageSingletonSwitchRealization) :
    FinalLowD5M4RootFlatCertificateFamily :=
  H2.D54.finalLowD5M4RootFlatCertificateFamily_of_paperStagesTwoStageSingleton
    terminal productBase twoStageSwitch

theorem lowD5M4_of_paperStagesTwoStageLayerConjSingleton
    (terminal : LowD5M4TerminalRealization)
    (productBase : LowD5M4ProductBaseRealization)
    (twoStageSwitch : LowD5M4TwoStageLayerConjSingletonSwitchRealization) :
    FinalLowD5M4RootFlatCertificateFamily :=
  H2.D54.finalLowD5M4RootFlatCertificateFamily_of_paperStagesTwoStageLayerConjSingleton
    terminal productBase twoStageSwitch

theorem lowD5M4_of_paperLayerConjStages
    (terminal : LowD5M4TerminalRealization)
    (productBase : LowD5M4ProductBaseLayerConjRealization)
    (twoStageSwitch : LowD5M4TwoStageLayerConjSingletonSwitchRealization) :
    FinalLowD5M4RootFlatCertificateFamily :=
  H2.D54.finalLowD5M4RootFlatCertificateFamily_of_paperLayerConjStages
    terminal productBase twoStageSwitch

theorem lowD5M4_of_paperSeedRowStages
    (terminal : LowD5M4TerminalRealization)
    (productBase : LowD5M4ProductBaseSeedRowRealization)
    (twoStageSwitch : LowD5M4TwoStageSeedRowSingletonSwitchRealization) :
    FinalLowD5M4RootFlatCertificateFamily :=
  H2.D54.finalLowD5M4RootFlatCertificateFamily_of_paperSeedRowStages
    terminal productBase twoStageSwitch

theorem lowD5M4_of_paperAllSeedRowStages
    (terminal : LowD5M4TerminalSeedRowRealization)
    (productBase : LowD5M4ProductBaseSeedRowRealization)
    (twoStageSwitch : LowD5M4TwoStageSeedRowSingletonSwitchRealization) :
    FinalLowD5M4RootFlatCertificateFamily :=
  H2.D54.finalLowD5M4RootFlatCertificateFamily_of_paperAllSeedRowStages
    terminal productBase twoStageSwitch

theorem lowD5M4_of_paperTransportedSeedRowStages
    (terminal : LowD5M4TerminalTransportedSeedRowRealization)
    (productBase : LowD5M4ProductBaseTransportedSeedRowRealization)
    (twoStageSwitch : LowD5M4TwoStageTransportedSeedRowSingletonSwitchRealization) :
    FinalLowD5M4RootFlatCertificateFamily :=
  H2.D54.finalLowD5M4RootFlatCertificateFamily_of_paperTransportedSeedRowStages
    terminal productBase twoStageSwitch

/-- H2 direct RF certificate.  This closes the `D5(4)` low-base obligation via
`D54ConjugateDirectRFInput`, without using the still-open paper ribbon
realization interface above. -/
theorem lowD5M4_of_finiteRF :
    FinalLowD5M4RootFlatCertificateFamily :=
  H2.D54.finalLowD5M4RootFlatCertificateFamily_of_lowD5M4Finite

theorem assume_lowD5M4 : FinalLowD5M4RootFlatCertificateFamily :=
  lowD5M4_of_finiteRF

/-- H3 — `D₇(4)` (paper App A/B two-rail relay).  Closed by the finite root-flat
**existence witness** `LowD7M4Finite`: a concrete `dir` on `Fin 4096` whose
RF1/RF2/RF3 (`rowLatin`/`layerBijective`/`returnsSingleCycle`) are verified by
`native_decide`.  This exhibits one valid schedule, i.e. settles the existence
question for `D₇(4)`.  The structural cycle-data target is kept exposed for a
future `native_decide`-free realization. -/
abbrev LowD7M4RootFlatCycleData := RootFlatCycle.RootFlatCycleData 6 4

theorem assume_lowD7M4 : FinalLowD7M4RootFlatCertificateFamily :=
  LowD7M4Finite.finalLowD7M4RootFlatCertificateFamily

/-- H4 — `D₇(6)`.  Closed by the finite root-flat **existence witness**
`LowD7M6Finite`: a concrete `dir` on `Fin 46656` with RF1/RF2/RF3 verified by
`native_decide`. -/
abbrev LowD7M6RootFlatCycleData := RootFlatCycle.RootFlatCycleData 6 6

theorem assume_lowD7M6 : FinalLowD7M6RootFlatCertificateFamily :=
  LowD7M6Finite.finalLowD7M6RootFlatCertificateFamily

/-- H5 — odd-dimension high-modulus branch (paper §6 coforest splice + §8
growth).  In the rewritten architecture this promotion also feeds the
modulus-free restart route of H6′: the odd low-modulus pair `(d, m)` with even
`8 ≤ m ≤ d` is closed by restarting the high-even closure at `D₀ = m − 1` and
growing past `D = m` (`cor:modulus-free-restart`). -/
theorem assume_oddHighModulus : FinalOddHighModulusTargetPromotion := sorry

/-- H6′ — odd low-modulus closure of the REWRITTEN paper
(`/data/angel/repos/etc/even_modulus_rewrite_20260610/subtex/high_even_growth.tex`):
chain propagation from the certified dimension-7 bases
(`cor:odd-chain-propagation`) plus the modulus-free restart
(`cor:modulus-free-restart`).  The endpoint-successor route of the earlier
manuscript is retired: its Lean scaffolding
(EndpointChart/PortRoom/RowSchedule/SeedReturns/ParentCycle/Realization and
the E6d obstruction theorems) is preserved off-spine as supporting material
and as machine-checked errata anchors. -/
theorem assume_oddLowClosure : V28Hard.OddLowClosureBridge.OddLowClosure :=
  sorry

/-- H6 interface discharged from the new architecture (closed adapter):
the old endpoint promotion is derivable because `MarkedDimensionRange b m`
forces even `4 ≤ m ≤ 2b + 1`, so `m ∈ {4, 6}` (chain propagation from the H3/H4
finite witnesses) or `8 ≤ m ≤ 2b + 1` (restart via H5). -/
theorem assume_oddEndpoint : FinalOddEndpointPhaseProductTargetPromotion :=
  V28Hard.OddLowClosureBridge.oddEndpointPromotion_of_oddLowClosure
    assume_oddLowClosure assume_oddHighModulus
    (finalLowD7M4Target_of_rootFlatCertificateFamily assume_lowD7M4
      finalLowD7M4ClosedInputs_holds)
    (finalLowD7M6Target_of_rootFlatCertificateFamily assume_lowD7M6
      finalLowD7M6ClosedInputs_holds)

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

/-! ## Paper-exact constructive adapter -/

abbrev ConstructiveV28Solution :=
  V28Hard.PaperExactStructure.ConstructiveV28Solution

/-- Conditional version of the main theorem whose assumptions are the explicit
H1--H6 manuscript handoffs from `V28Hard.PaperExactStructure`.  The existing
unconditional theorem above is left unchanged; this adapter exposes the
paper-facing record package imported from the JSON-proof bundle. -/
theorem evenModulusToriAllDimensions_of_constructiveSolution
    (solution : ConstructiveV28Solution) :
    EvenModulusToriAllDimensionsGoal :=
  V28Hard.PaperExactStructure.evenModulusToriAllDimensions_of_constructiveSolution
    solution

end EvenV11
