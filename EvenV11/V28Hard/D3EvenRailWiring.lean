import EvenV11.V28Hard.D3EvenRailCore3Free
import EvenV11.V28Hard.D3EvenRailCore3Dvd
import EvenV11.V28Hard.CompletionTower
import EvenV11.V28Hard.D3TerminalA2PerColor

/-!
# D3-even rail seam: the H1b wiring (modules 1–3 → per-color realization)

This file closes hole H1b from the completed rail-seam stack:

* **`railCycleDataFamily`** combines the two core modules — `3 ∤ m`
  (`D3EvenRailCore3Free.railCycleData_of_not_dvd`) and `3 ∣ m`
  (`D3EvenRailCore3Dvd.railCycleData_of_dvd`) — into the parametric H1
  cycle-data family `RootFlatCycle.D3EvenCycleDataFamily`: for every even
  `m ≥ 4` a concrete root-flat `dir` (the rail-seam schedule of module 2)
  with RF1/RF2/RF3.

* **`perColorRealization_of_cycleData`** *constructs* the per-color
  run-collapse realization demanded by H1b
  (`D3TerminalA2PerColor.TerminalA2PerColorRealizationFamily`) from any
  cycle-data family plus the proven carrier cyclicity (H1a).  The wild
  return-section reindexing `sectionEquiv c` is the composite of the two
  orbit rank enumerations supplied by the converse rank lemma
  `CompletionTower.rankEquiv_of_singleCycle`: both the schedule's first
  return `R_c` (RF3) and the collapsed terminal carrier `F_c` (H1a) are
  single `m²`-cycles, hence each is conjugate to `+1` on `ZMod (m·m)`
  through its rank equivalence (`r_R`, `r_F`), and
  `sectionEquiv c := r_F.trans r_R.symm` satisfies the realization
  equation `(sectionEquiv c).symm ∘ R_c ∘ sectionEquiv c = F_c`
  pointwise: under `r_F`, both sides advance the rank by `+1`.  This is
  exactly the wild run-collapse reindexing whose tame (coordinate-chart)
  versions were ruled out in
  `docs/H1B_REALIZATION_OBSTRUCTION_20260609.md` — built here from the
  orbit ranks instead of a chart.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace EvenV11
namespace V28Hard
namespace D3EvenRailWiring

open Shared
open TerminalA2LowMod
open D3TerminalA2Parametric

set_option linter.unusedSectionVars false

/-- The rail-seam cycle-data family: H1's parametric RF1/RF2/RF3 payload,
for every even `m ≥ 4`, split on `m % 3` (the rail-seam schedule of
`docs/WILDE_SEARCH_20260610.md`, modules 1–3). -/
theorem railCycleDataFamily : RootFlatCycle.D3EvenCycleDataFamily := by
  intro m hm
  letI := RootFlatCycle.neZero_of_evenModulusRange hm
  have hm4 : 4 ≤ m := hm.1
  have hEven : Even m := by
    rcases hm.2 with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  by_cases h3 : m % 3 = 0
  · exact ⟨D3EvenRailCore3Dvd.railCycleData_of_dvd m hm4 hEven h3⟩
  · exact ⟨D3EvenRailCore3Free.railCycleData_of_not_dvd m hm4 hEven h3⟩

/-! ## Rank-transport construction of the per-color realization -/

section RankTransport

/-- A choice of cycle data per modulus. -/
private noncomputable def chosenData
    (data : RootFlatCycle.D3EvenCycleDataFamily)
    (m : Nat) (hm : EvenModulusRange m) :
    @RootFlatCycle.RootFlatCycleData 2 m
      (RootFlatCycle.neZero_of_evenModulusRange hm) :=
  Classical.choice (data hm)

/-- The chosen schedule `dir`. -/
private noncomputable def chosenDir
    (data : RootFlatCycle.D3EvenCycleDataFamily)
    {m : Nat} (hm : EvenModulusRange m) :
    ZMod m → RootState m → TorusColor 3 → TorusDirection 3 :=
  letI := RootFlatCycle.neZero_of_evenModulusRange hm
  (chosenData data m hm).dir

variable (m : Nat) [NeZero m]

/-- `Nat.card` of the root section is `m * m`. -/
private theorem card_rootState : Nat.card (RootState m) = m * m := by
  rw [Nat.card_congr (rootPairEquiv m), Nat.card_prod, Nat.card_zmod]

/-- `Nat.card` of the manuscript pair space is `m * m`. -/
private theorem card_terminalQ : Nat.card (TerminalQ m) = m * m := by
  rw [Nat.card_prod, Nat.card_zmod]

end RankTransport

/-- **The per-color realization, constructed.**  Any `D₃`-even cycle-data
family (RF1/RF2/RF3 — e.g. the rail-seam family above) together with the
carrier cyclicity (H1a) yields the per-color terminal `A₂` realization:
the section equivalences are the composites of the orbit rank enumerations
of the two single `m²`-cycles, and the realization equation holds because
both sides step the carrier rank by `+1`. -/
theorem perColorRealization_of_cycleData
    (data : RootFlatCycle.D3EvenCycleDataFamily)
    (carrier : D3TerminalA2Parametric.TerminalA2CarrierCyclicityFamily) :
    Nonempty D3TerminalA2PerColor.TerminalA2PerColorRealizationFamily := by
  -- per-color rank enumerations of the schedule first returns (RF3)
  have hR : ∀ (m : Nat) (hm : EvenModulusRange m) (c : TorusColor 3),
      ∃ rank : RootState m ≃ ZMod (m * m),
        ∀ w, rank (terminalA2ReturnMapOfDir hm (chosenDir data hm) c w)
          = rank w + 1 := by
    intro m hm c
    letI := RootFlatCycle.neZero_of_evenModulusRange hm
    haveI : NeZero (m * m) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne m)⟩
    obtain ⟨rank, hrank⟩ := CompletionTower.rankEquiv_of_singleCycle
      ((RootFlatCycle.schedule (chosenDir data hm)).returnMap c)
      ((chosenData data m hm).returnsSingleCycle c) (card_rootState m)
    exact ⟨rank, fun w => by
      simpa [terminalA2ReturnMapOfDir] using hrank w⟩
  -- per-color rank enumerations of the terminal carriers (H1a)
  have hF : ∀ (m : Nat) (hm : EvenModulusRange m) (c : TorusColor 3),
      ∃ rank : TerminalQ m ≃ ZMod (m * m),
        ∀ q, rank (terminalReturnOfRange hm c q) = rank q + 1 := by
    intro m hm c
    letI := RootFlatCycle.neZero_of_evenModulusRange hm
    haveI : NeZero (m * m) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne m)⟩
    exact CompletionTower.rankEquiv_of_singleCycle _
      (carrier hm c) (card_terminalQ m)
  choose rR hrR using hR
  choose rF hrF using hF
  refine ⟨⟨fun {m} hm => chosenDir data hm,
    fun {m} hm c => (rF m hm c).trans (rR m hm c).symm,
    fun {m} hm =>
      letI := RootFlatCycle.neZero_of_evenModulusRange hm
      (chosenData data m hm).rowLatin,
    fun {m} hm =>
      letI := RootFlatCycle.neZero_of_evenModulusRange hm
      (chosenData data m hm).layerBijective,
    ?_⟩⟩
  intro m hm c q
  have hstep := hrR m hm c ((rR m hm c).symm (rF m hm c q))
  rw [Equiv.apply_symm_apply] at hstep
  simp only [Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.symm_symm]
  rw [hstep, ← hrF m hm c q, Equiv.symm_apply_apply]

end D3EvenRailWiring
end V28Hard
end EvenV11
