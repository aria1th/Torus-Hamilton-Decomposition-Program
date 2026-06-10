import EvenV11.RootFlatCycleData
import EvenV11.V28Hard.HighEvenEndpointPromotions
import EvenV11.V28Hard.EndpointPortRoom

/-!
# Hard slot H6 (E6c): endpoint run-collapse realization interface

`E6_DESIGN_20260610.md` §6.  The endpoint child `D_{2b+1}(m)` is reduced to
the narrowest precisely-shaped open input: per child color, a §5 seed model
(`EndpointSeedReturns`) together with a **wild run-collapse reindexing**
`collapse c` conjugating the physical child schedule's first return to that
seed.  This is the family version of the H1b wild-`e` problem
(`H1B_REALIZATION_OBSTRUCTION_20260609.md` §3), but strictly weaker: the
reindexing is allowed to vary per color and the seed models are not externally
fixed.  The walls of design §4 (firing-fiber budget, localized full-row RF2
violation, partner/donation deadlock) say exactly why the tame charts cannot
fill it.

* `EndpointRunCollapseRealization` — the realization record (design §6).
* **E6c-1** `cycleData_of_realization` (sorry-free) — RF3 from `conj` +
  `seedSingleCycle` via `Shared.single_cycle_of_equiv_conj`, yielding the
  standard-lift `RootFlatCycle.RootFlatCycleData (2*b) m`.
* `EndpointRealizationFamily` — the open family input, stated over exactly the
  range hypotheses of `OddEndpointPayloadEngine.run` and **from** the parent
  marked payload (so E6a's parent-cycle extraction is available to the
  eventual construction).
* **E6c-2** `oddEndpointPayloadEngine_of_realizationFamily` (sorry-free) —
  engine assembly: E6c-1 → `finalRootFlatTorusCertificate_of_cycleData`
  (`n := 2*b`, so `n + 1` is literally `2*b + 1`) →
  `finalRootFlatMarkedTarget_of_certificate` → `finalMarkedPayload_weakOfTarget`.
  The `FinalOddEndpointPhaseProductCertificateInputs` argument is threaded
  through unchanged (its fields are closed per the audit; true marked fidelity
  is a later work item).
* `oddEndpointTargetPromotion_of_realizationFamily` — the convenience adapter
  consumed by `Main`.

No `sorry`, no `native_decide`.
-/

namespace EvenV11
namespace V28Hard
namespace EndpointRealization

/-- **E6c interface** (design §6): per-color run-collapse realization of the
child schedule for the endpoint successor `b ↦ 2b + 1`.

The fields `qData` and `P`/`hP` pin the intended inputs of the eventual
constructor — the D3 terminal `A₂` cycle-data consumed on the `Q`-sector and
the E6a parent cycle on the `Y`-sector (`EndpointParentCycle`, transported to
the lane chart) — even though the sorry-free reductions below do not consume
them: they are carried so the realization record states the *whole* obligation,
not just its RF3 shadow.

The range hypotheses (`4 ≤ b`, `MarkedDimensionRange b m`) are deliberately
NOT parameters of this structure; they live on `EndpointRealizationFamily`. -/
structure EndpointRunCollapseRealization (b m : Nat) [NeZero m] : Type where
  /-- D3 input consumed (`Q`-sector): the terminal `A₂` cycle-data. -/
  qData : RootFlatCycle.RootFlatCycleData 2 m
  /-- Parent cycle input (`Y`-sector): the E6a cycle transported to the lane
  chart `LaneZ b m` (`EndpointParentCycle.parentSectionEquiv`). -/
  P : EndpointPortRoom.LaneZ b m ≃ EndpointPortRoom.LaneZ b m
  hP : Shared.IsSingleCycleMap ⇑P
  /-- The physical child schedule. -/
  dir : ZMod m → StandardRootFlatLift.RootState (2 * b) m →
      Shared.TorusColor (2 * b + 1) → Shared.TorusDirection (2 * b + 1)
  rowLatin : (RootFlatCycle.schedule dir).rowLatin
  layerBijective : (RootFlatCycle.schedule dir).layerBijective
  /-- Per-color seed model selector (which §5 ledger model the color realizes;
  `EndpointSeedReturns` provides the active cores, tower attachments and the
  μ-class as default instantiations). -/
  seed : Shared.TorusColor (2 * b + 1) →
      (StandardRootFlatLift.RootState (2 * b) m →
        StandardRootFlatLift.RootState (2 * b) m)
  seedSingleCycle : ∀ c, Shared.IsSingleCycleMap (seed c)
  /-- The wild run-collapse reindexings, PER COLOR (no common-`e` requirement —
  strictly weaker than H1b's interface). -/
  collapse : Shared.TorusColor (2 * b + 1) →
      (StandardRootFlatLift.RootState (2 * b) m ≃
        StandardRootFlatLift.RootState (2 * b) m)
  /-- The child's first return is the collapse-conjugate of the seed model. -/
  conj : ∀ c w, (RootFlatCycle.schedule dir).returnMap c w
      = collapse c (seed c ((collapse c).symm w))

/-- **E6c-1 (sorry-free).**  A run-collapse realization yields the standard-lift
root-flat cycle-data for the child: RF1/RF2 are carried verbatim, and RF3 is the
seed single-cycle property transported through the per-color collapse via
`Shared.single_cycle_of_equiv_conj` (orientation
`e.symm (f (e x)) = g x` with `e := collapse c`, `f := returnMap c`,
`g := seed c`, obtained from `conj` at `w := collapse c x`). -/
def cycleData_of_realization {b m : Nat} [NeZero m]
    (R : EndpointRunCollapseRealization b m) :
    RootFlatCycle.RootFlatCycleData (2 * b) m where
  dir := R.dir
  rowLatin := R.rowLatin
  layerBijective := R.layerBijective
  returnsSingleCycle := fun c =>
    Shared.single_cycle_of_equiv_conj
      (R.collapse c)
      ((RootFlatCycle.schedule R.dir).returnMap c)
      (R.seed c)
      (R.seedSingleCycle c)
      (fun w => by rw [R.conj c]; simp)

/-- **The open family input** (the precisely-shaped H6 hole): for every endpoint
range instance, a run-collapse realization built *from* the parent marked
payload.  The hypotheses match `OddEndpointPayloadEngine.run` exactly;
`NeZero m` is derived from the modulus range as in
`RootFlatCycle.D3EvenCycleDataFamily`. -/
def EndpointRealizationFamily : Prop :=
  ∀ {b m : Nat}, 4 ≤ b → ∀ hrange : MarkedDimensionRange b m,
    FinalMarkedPayload b m →
    Nonempty
      (@EndpointRunCollapseRealization b m
        (RootFlatCycle.neZero_of_evenModulusRange hrange.2.1))

/-- **E6c-2 (sorry-free).**  Engine assembly: the realization family closes the
endpoint payload engine.  The child cycle-data (E6c-1) feeds
`finalRootFlatTorusCertificate_of_cycleData` at `n := 2 * b` (so the certificate
dimension `n + 1` is literally `2 * b + 1`), the certificate is forgotten to the
marked target by `finalRootFlatMarkedTarget_of_certificate`, and the child
payload is rebuilt by `finalMarkedPayload_weakOfTarget` (PUnit evidence; true
marked fidelity is a separate, later work item).  The certificate inputs are
threaded through unchanged. -/
theorem oddEndpointPayloadEngine_of_realizationFamily
    (h : EndpointRealizationFamily) :
    HighEvenEndpointPromotions.OddEndpointPayloadEngine where
  run := fun {_b m} hb hrange payload _inputs =>
    letI : NeZero m := RootFlatCycle.neZero_of_evenModulusRange hrange.2.1
    let R := Classical.choice (h hb hrange payload)
    finalMarkedPayload_weakOfTarget
      (finalRootFlatMarkedTarget_of_certificate
        (RootFlatCycle.finalRootFlatTorusCertificate_of_cycleData
          (cycleData_of_realization R)))

/-- Convenience adapter: the realization family closes H6's target-only
promotion interface (the shape consumed by `Main`). -/
theorem oddEndpointTargetPromotion_of_realizationFamily
    (h : EndpointRealizationFamily) :
    FinalOddEndpointPhaseProductTargetPromotion :=
  HighEvenEndpointPromotions.endpointTargetPromotion_of_engine
    (oddEndpointPayloadEngine_of_realizationFamily h)

end EndpointRealization
end V28Hard
end EvenV11
