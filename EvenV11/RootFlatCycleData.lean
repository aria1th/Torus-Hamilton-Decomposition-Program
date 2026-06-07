import EvenV11.StandardRootFlatLift
import EvenV11.FinalTargetLowBaseRootFlatCertificateBridge
import EvenV11.FinalRangeBookkeepingBridge

/-!
# Generic root-flat cycle-data → certificate reduction (connective glue)

This is the dimension-agnostic version of the `D5(4)` reduction in
`LowD5M4Structural`: it packages the *dir-independent* assembly so that any
low-base hole `D_{n+1}(m)` is reduced to a single clean handoff —

> supply a concrete root-flat `dir` on `Fin n → ZMod m` together with RF1/RF2/RF3
> (`rowLatin`, `layerBijective`, `returnsSingleCycle`).

`stepConjugacy` is **free** for the standard lift (`StandardRootFlatLift`,
`step = rootStep`), exactly as in the `D5(4)` case. The genuine mathematical
content — constructing the paper `dir` and proving its first returns are single
cycles — is intentionally left as the open obligation.

No `sorry`, no `native_decide`.
-/

namespace EvenV11
namespace RootFlatCycle

open Shared StandardRootFlatLift

/-- The standard root-flat schedule on `Fin n → ZMod m` whose generator step is
the standard lift `rootStep`. -/
def schedule {n m : Nat}
    (dir : ZMod m → RootState n m → TorusColor (n + 1) → TorusDirection (n + 1)) :
    RootFlatSchedule (TorusColor (n + 1)) (TorusDirection (n + 1)) (RootState n m) m where
  dir := dir
  step := rootStep

/-- `stepConjugacy` for the standard lift is independent of `dir`: it is exactly
`StandardRootFlatLift.torusEquiv_step` instantiated at `dir tw.1 tw.2 c`. -/
theorem stepConjugacy_of_dir {n m : Nat} [NeZero m]
    (dir : ZMod m → RootState n m → TorusColor (n + 1) → TorusDirection (n + 1))
    (c : TorusColor (n + 1)) (tw : ZMod m × RootState n m) :
    cayleyColorStep
        (finalRootFlatModelColorDir (schedule dir) (torusEquiv n m)) c
        (torusEquiv n m tw) =
      torusEquiv n m ((schedule dir).fullStep c tw) := by
  simpa [cayleyColorStep, finalRootFlatModelColorDir, schedule,
    Shared.RootFlatSchedule.fullStep, Shared.RootFlatSchedule.layerMap]
    using torusEquiv_step (dir tw.1 tw.2 c) tw

/-- Root-flat RF1/RF2/RF3 data for `D_{n+1}(m)` over the standard lift. This is
the minimal paper-faithful handoff for a low-base hole: a concrete `dir` plus the
three return-criterion facts. -/
structure RootFlatCycleData (n m : Nat) [NeZero m] where
  dir : ZMod m → RootState n m → TorusColor (n + 1) → TorusDirection (n + 1)
  rowLatin : (schedule dir).rowLatin
  layerBijective : (schedule dir).layerBijective
  returnsSingleCycle : (schedule dir).returnsSingleCycle

/-- The whole point: RF1/RF2/RF3 over the standard lift assemble into the final
root-flat certificate, with `stepConjugacy` supplied for free. -/
theorem finalRootFlatTorusCertificate_of_cycleData {n m : Nat} [NeZero m]
    (data : RootFlatCycleData n m) :
    FinalRootFlatTorusCertificate (n + 1) m :=
  finalRootFlatTorusCertificate_of_fields
    (torusEquiv := torusEquiv n m)
    data.rowLatin data.layerBijective data.returnsSingleCycle
    (fun c tw => stepConjugacy_of_dir data.dir c tw)

/-! ## H4 wiring: `D₇(6)` -/

/-- `D₇(6)` low-base family from a standard-lift root-flat schedule with
RF1/RF2/RF3. (`n = 6`, `m = 6`, so `n + 1 = 7`.) -/
theorem finalLowD7M6RootFlatCertificateFamily_of_cycleData
    (data : RootFlatCycleData 6 6) :
    FinalLowD7M6RootFlatCertificateFamily :=
  finalLowD7M6RootFlatCertificateFamily_of_certificate
    (finalRootFlatTorusCertificate_of_cycleData data)

theorem finalLowD7M6RootFlatCertificateFamily_of_nonemptyCycleData
    (hData : Nonempty (RootFlatCycleData 6 6)) :
    FinalLowD7M6RootFlatCertificateFamily :=
  finalLowD7M6RootFlatCertificateFamily_of_cycleData (Classical.choice hData)

/-! ## H3 wiring: `D₇(4)` (available for a later structural replacement of the blob) -/

/-- `D₇(4)` low-base family from a standard-lift root-flat schedule with
RF1/RF2/RF3. (`n = 6`, `m = 4`.) -/
theorem finalLowD7M4RootFlatCertificateFamily_of_cycleData
    (data : RootFlatCycleData 6 4) :
    FinalLowD7M4RootFlatCertificateFamily :=
  finalLowD7M4RootFlatCertificateFamily_of_certificate
    (finalRootFlatTorusCertificate_of_cycleData data)

theorem finalLowD7M4RootFlatCertificateFamily_of_nonemptyCycleData
    (hData : Nonempty (RootFlatCycleData 6 4)) :
    FinalLowD7M4RootFlatCertificateFamily :=
  finalLowD7M4RootFlatCertificateFamily_of_cycleData (Classical.choice hData)

/-! ## H1 wiring: `D₃(m)`, parametric over all even `m ≥ 4` -/

/-- `EvenModulusRange m` (which contains `4 ≤ m`) gives `NeZero m`. -/
theorem neZero_of_evenModulusRange {m : Nat} (hm : EvenModulusRange m) :
    NeZero m :=
  ⟨by have := hm.1; omega⟩

/-- Parametric H1 obligation: a standard-lift root-flat cycle-data
(`dir` on `Fin 2 → ZMod m` with RF1/RF2/RF3) for **every** even `m ≥ 4`.
This is the paper §5 terminal-`A₂` content in the uniform RF interface. -/
abbrev D3EvenCycleDataFamily : Prop :=
  ∀ {m : Nat} (hm : EvenModulusRange m),
    Nonempty (@RootFlatCycleData 2 m (neZero_of_evenModulusRange hm))

/-- The `D₃`-even root-flat family from parametric cycle-data. (`n = 2`,
`n + 1 = 3`.) -/
theorem finalD3EvenRootFlatCertificateFamily_of_d3EvenCycleDataFamily
    (h : D3EvenCycleDataFamily) :
    FinalD3EvenRootFlatCertificateFamily where
  rootFlatCertificate := fun {m} hm =>
    @finalRootFlatTorusCertificate_of_cycleData 2 m
      (neZero_of_evenModulusRange hm) (Classical.choice (h hm))

end RootFlatCycle
end EvenV11
