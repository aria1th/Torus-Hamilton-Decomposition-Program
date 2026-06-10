import EvenV11.V28Hard.D3TerminalA2Parametric

/-!
# Hard slot H1b: per-color terminal `A₂` root-flat realization

Per-color weakening of `D3TerminalA2Parametric.TerminalA2RootFlatRealizationFamily`,
aligned with the H6 interface shape (`EndpointRealization.EndpointRunCollapseRealization`,
whose `collapse` reindexing is already per color).

The common-section family demands ONE `sectionEquiv : TerminalQ m ≃ RootState m`
conjugating the schedule's first return to the carrier `terminalReturn c` for all
three colors **simultaneously**.  That simultaneous-conjugacy constraint is
potentially unsatisfiable-shaped for any constructible `dir`
(cf. `docs/H2_REALIZATION_BLOCKER_20260605.md`, where a too-rigid interface was
proven unsatisfiable, and `docs/H1B_REALIZATION_OBSTRUCTION_20260609.md` for the
wild-`e` obstruction).  Per-color equivalences suffice for the only mathematical
payoff — RF3, each return single-cyclic by per-color transport — and give the
eventual wild run-collapse construction maximal freedom.

* `TerminalA2PerColorRealizationFamily` — the weakened realization record.
* `perColor_of_common` (sorry-free) — forgetful adapter from the common-section
  family (use the same equivalence for every color).
* `cycleDataFamily_of_carrierCyclicity_and_perColorRealization` (sorry-free) —
  the H1 conjugacy adapter, mirroring
  `cycleDataFamily_of_carrierCyclicity_and_realization` with the per-color
  transport.

No `sorry`, no `native_decide`.
-/

namespace EvenV11
namespace V28Hard
namespace D3TerminalA2PerColor

open Shared

/-- Per-color root-flat realization of the terminal A₂ carriers.  Weaker than
`TerminalA2RootFlatRealizationFamily`: each color may use its own run-collapse
section equivalence (no simultaneous conjugacy).

Why per-color: the only consumer of the conjugacy is RF3 (each first return
single-cyclic), and RF3 is transported color by color through
`Shared.single_cycle_of_equiv_conj`, so a common section is mathematically
unnecessary.  Demanding a single simultaneous conjugator is exactly the kind of
over-rigid interface shape that was proven unsatisfiable for H2
(`docs/H2_REALIZATION_BLOCKER_20260605.md`); the H1b wild-`e` analysis
(`docs/H1B_REALIZATION_OBSTRUCTION_20260609.md`) shows tame charts are already
blocked, so the wild run-collapse construction should be left maximally free.
This matches the H6 interface (`EndpointRunCollapseRealization.collapse` is per
color).

Inter-derivability (intended proof route): given RF1/RF2 and the per-color
conjugacies, the cycle data follows (the adapter below); conversely any cycle
data yields per-color equivalences through the rank enumerations of the single
cycles (`CompletionTower.rankEquiv_of_singleCycle`), so this structure records
the obligation without strengthening it. -/
structure TerminalA2PerColorRealizationFamily where
  dir : ∀ {m : Nat} (_hm : EvenModulusRange m),
      ZMod m → D3TerminalA2Parametric.RootState m → TorusColor 3 → TorusDirection 3
  sectionEquiv : ∀ {m : Nat} (_hm : EvenModulusRange m) (_c : TorusColor 3),
      TerminalA2LowMod.TerminalQ m ≃ D3TerminalA2Parametric.RootState m
  rowLatin : ∀ {m : Nat} (hm : EvenModulusRange m),
      (D3TerminalA2Parametric.terminalA2ScheduleOfDir hm (dir hm)).rowLatin
  layerBijective : ∀ {m : Nat} (hm : EvenModulusRange m),
      (D3TerminalA2Parametric.terminalA2ScheduleOfDir hm (dir hm)).layerBijective
  return_eq_terminal : ∀ {m : Nat} (hm : EvenModulusRange m)
      (c : TorusColor 3) (q : TerminalA2LowMod.TerminalQ m),
      (sectionEquiv hm c).symm
          (D3TerminalA2Parametric.terminalA2ReturnMapOfDir hm (dir hm) c
            ((sectionEquiv hm c) q)) =
        D3TerminalA2Parametric.terminalReturnOfRange hm c q

/-- Forgetful adapter: a common-section realization is in particular a per-color
one (use the same equivalence for every color). -/
def perColor_of_common
    (realization : D3TerminalA2Parametric.TerminalA2RootFlatRealizationFamily) :
    TerminalA2PerColorRealizationFamily where
  dir := realization.dir
  sectionEquiv := fun hm _c => realization.sectionEquiv hm
  rowLatin := realization.rowLatin
  layerBijective := realization.layerBijective
  return_eq_terminal := fun hm c q => realization.return_eq_terminal hm c q

/-- Closed A₂ adapter (per-color form): carrier cyclicity plus a per-color
root-flat realization gives the cycle-data family consumed by H1.  Mirrors
`cycleDataFamily_of_carrierCyclicity_and_realization`; the RF3 transport was
already per color, so only `sectionEquiv hm c` changes. -/
theorem cycleDataFamily_of_carrierCyclicity_and_perColorRealization
    (carrier : D3TerminalA2Parametric.TerminalA2CarrierCyclicityFamily)
    (realization : TerminalA2PerColorRealizationFamily) :
    RootFlatCycle.D3EvenCycleDataFamily := by
  intro m hm
  letI := RootFlatCycle.neZero_of_evenModulusRange hm
  let a2Dir := realization.dir hm
  refine ⟨⟨a2Dir, ?_, ?_, ?_⟩⟩
  · simpa [D3TerminalA2Parametric.terminalA2ScheduleOfDir] using
      realization.rowLatin hm
  · simpa [D3TerminalA2Parametric.terminalA2ScheduleOfDir] using
      realization.layerBijective hm
  · intro c
    exact Shared.single_cycle_of_equiv_conj
      (realization.sectionEquiv hm c)
      ((RootFlatCycle.schedule (realization.dir hm)).returnMap c)
      (D3TerminalA2Parametric.terminalReturnOfRange hm c)
      (carrier hm c)
      (by
        intro q
        simpa [D3TerminalA2Parametric.terminalA2ReturnMapOfDir] using
          realization.return_eq_terminal hm c q)

end D3TerminalA2PerColor
end V28Hard
end EvenV11
