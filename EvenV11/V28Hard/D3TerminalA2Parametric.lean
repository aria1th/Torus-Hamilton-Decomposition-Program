import EvenV11.TerminalA2LowMod
import EvenV11.TerminalFiniteCyclicity
import EvenV11.FinalTargetD3RootFlatCertificateBridge
import EvenV11.StandardRootFlatLift
import EvenV11.RootFlatCycleData

/-!
# Hard slot H1: parametric terminal `A₂` root-flat base

This file keeps the manuscript terminal `A₂` block in an explicit, constructive
handoff form.  It defines the paper row word in the standard root-flat section
and exposes the exact proof object that downstream code consumes: a family of
RF1/RF2/RF3 cycle data for all even moduli `m ≥ 4`.

The source-anchored diagnostic row below is retained only as local arithmetic
support.  The final theorem in this file is conditional on a supplied
`TerminalA2ParametricSolution`, so the file contains no hidden global proof
constants.
-/

namespace EvenV11
namespace V28Hard
namespace D3TerminalA2Parametric

open Shared
open TerminalA2LowMod
open StandardRootFlatLift

/-- Standard D3 root section, definitionally close to
`StandardRootFlatLift.RootState 2 m`. -/
abbrev RootState (m : Nat) := Fin 2 → ZMod m

/-- Pair coordinates used by the manuscript terminal block. -/
def rootPair {m : Nat} (w : RootState m) : TerminalQ m :=
  (w 0, w 1)

/-- Convert a manuscript terminal pair back to the standard root section. -/
def pairRoot {m : Nat} (q : TerminalQ m) : RootState m :=
  fun j => if j = (0 : Fin 2) then q.1 else q.2

@[simp] theorem rootPair_pairRoot {m : Nat} (q : TerminalQ m) :
    rootPair (pairRoot q) = q := by
  ext <;> simp [rootPair, pairRoot]

@[simp] theorem pairRoot_rootPair {m : Nat} (w : RootState m) :
    pairRoot (rootPair w) = w := by
  funext j
  fin_cases j <;> simp [rootPair, pairRoot]

/-- Equivalence between the Lean standard section and the paper's `Q_m`. -/
def rootPairEquiv (m : Nat) : RootState m ≃ TerminalQ m where
  toFun := rootPair
  invFun := pairRoot
  left_inv := pairRoot_rootPair
  right_inv := rootPair_pairRoot

/-- The terminal row word seen by color `c` at root point `w`.  The local row is
anchored at `z-a_c`, exactly as in the paper's definition of `η_i`. -/
def terminalTargetIndex {m : Nat} [NeZero m]
    (w : RootState m) (c : TorusColor 3) : TorusDirection 3 :=
  terminalRowEquiv
    (terminalOmega ((rootPair w) - terminalVertex (m := m) c)) c

/-- Candidate paper direction table for the terminal `A₂` block.  It is
independent of the layer `t`; the layer variable records the standard root-flat
lift period. -/
def terminalDir (m : Nat) [NeZero m] :
    ZMod m → RootState m → TorusColor 3 → TorusDirection 3 :=
  fun _t w c => terminalTargetIndex w c

/-- The root-flat schedule obtained by installing the terminal word in every
layer of the standard D3 lift. -/
def schedule (m : Nat) [NeZero m] :
    RootFlatSchedule (TorusColor 3) (TorusDirection 3) (RootState m) m :=
  RootFlatCycle.schedule (terminalDir m)

/-- Diagnostic obstruction: the collapsed terminal word cannot be read directly
as a standard root-flat row in the plain coordinate chart.  Already at `m = 4`,
layer `0`, root point `(0,0)`, two colours choose the same direction, so RF1
fails.  The paper realization therefore has to pass through the physical
triangle row expansion and a return-section equivalence, not this naive
`terminalDir`. -/
theorem terminalDir_m4_plainChart_not_rowLatin :
    ¬ (schedule (m := 4)).rowLatin := by
  intro h
  have hinj :=
    (h (0 : ZMod 4)
      (pairRoot (m := 4) ((0 : ZMod 4), (0 : ZMod 4)))).1
  have hdup :
      (fun c : TorusColor 3 =>
          (schedule (m := 4)).dir (0 : ZMod 4)
            (pairRoot (m := 4) ((0 : ZMod 4), (0 : ZMod 4))) c)
          (1 : TorusColor 3) =
        (fun c : TorusColor 3 =>
          (schedule (m := 4)).dir (0 : ZMod 4)
            (pairRoot (m := 4) ((0 : ZMod 4), (0 : ZMod 4))) c)
          (2 : TorusColor 3) := by
    decide
  exact (by decide : (1 : TorusColor 3) ≠ (2 : TorusColor 3)) (hinj hdup)

/-- Local-triangle RF1 in the exact form needed to repair `rowLatin`.  For a
fixed physical elementary triangle anchored at `q`, the map from source color to
head direction is the row equivalence `terminalRowEquiv (ω_m q)`. -/
theorem localTriangle_rowLatin {m : Nat} [NeZero m] (q : TerminalQ m) :
    Function.Bijective
      (fun c : TorusColor 3 =>
        (terminalRowEquiv (terminalOmega q) c : TorusDirection 3)) :=
  (terminalRowEquiv (terminalOmega q)).bijective

/-- Paper fiber labels `ℓ₀=x`, `ℓ₁=y`, and `ℓ₂=x+y`. -/
def terminalFiberLabel {m : Nat} : TorusColor 3 → TerminalQ m → ZMod m
  | 0, z => z.1
  | 1, z => z.2
  | 2, z => z.1 + z.2

/-- Active endpoint `A_i(r)` from the terminal `A₂` recurrence. -/
def terminalEndpointA {m : Nat} : TorusColor 3 → ZMod m → TerminalQ m
  | 0, r => (r, 2)
  | 1, r => (1, r)
  | 2, r => (1, r - 1)

/-- Active endpoint `B_i(r)` from the terminal `A₂` recurrence. -/
def terminalEndpointB {m : Nat} : TorusColor 3 → ZMod m → TerminalQ m
  | 0, r => (r, 4 - r)
  | 1, r => (4 - r, r)
  | 2, r => (r - 2, 2)

/-- Positive puncture endpoint `E⁺_i` in the terminal `A₂` recurrence. -/
def terminalEndpointEplus {m : Nat} : TorusColor 3 → TerminalQ m
  | 0 => ((2 : ZMod m), (3 : ZMod m))
  | 1 => ((0 : ZMod m), (3 : ZMod m))
  | 2 => ((2 : ZMod m), (1 : ZMod m))

/-- Negative puncture endpoint `E⁻_i` in the terminal `A₂` recurrence. -/
def terminalEndpointEminus {m : Nat} : TorusColor 3 → TerminalQ m
  | 0 => ((2 : ZMod m), (1 : ZMod m))
  | 1 => ((2 : ZMod m), (3 : ZMod m))
  | 2 => ((0 : ZMod m), (3 : ZMod m))

/-- The next fiber index in the collapsed endpoint recurrence. -/
def terminalEndpointNext {m : Nat} : TorusColor 3 → ZMod m → ZMod m
  | 0, r => r - 1
  | 1, r => r - 1
  | 2, r => r + 1

/-- Exceptional fibers where the generic endpoint string is replaced by a
boundary turn. -/
def terminalEndpointException {m : Nat} : TorusColor 3 → ZMod m → Prop
  | 0, r => r = 2 ∨ r = 3
  | 1, r => r = 3 ∨ r = 4
  | 2, r => r = 2 ∨ r = 3

/-- Endpoint exchange followed by the paper jump `η_i`.  This is the compressed
map `h_i = n_i η_i` used in the manuscript proof. -/
def terminalCompressedEndpointReturn {m : Nat} [NeZero m]
    (exchange : TorusColor 3 → TerminalQ m → TerminalQ m)
    (c : TorusColor 3) (z : TerminalQ m) : TerminalQ m :=
  exchange c (terminalEta (m := m) c z)

/-- Exact active-endpoint recurrence stated in the coordinates of the paper.
The generic fields cover every non-boundary fiber.  The boundary bridges keep
the two puncture endpoints `E⁺_i` and `E⁻_i` as separate rank vertices, matching
the paper lists `B₃ → E⁺₀ → A₁`, `A₃ → E⁻₀ → B₁`, and their color-1/color-2
analogues. -/
structure TerminalA2EndpointRecurrence (m : Nat) [NeZero m] where
  exchange : TorusColor 3 → TerminalQ m → TerminalQ m
  exchange_A :
    ∀ c r, exchange c (terminalEndpointA (m := m) c r) =
      terminalEndpointB (m := m) c r
  exchange_B :
    ∀ c r, exchange c (terminalEndpointB (m := m) c r) =
      terminalEndpointA (m := m) c r
  generic_A :
    ∀ c r, ¬ terminalEndpointException (m := m) c r →
      terminalCompressedEndpointReturn (m := m) exchange c
        (terminalEndpointA (m := m) c r) =
      terminalEndpointB (m := m) c (terminalEndpointNext (m := m) c r)
  generic_B :
    ∀ c r, ¬ terminalEndpointException (m := m) c r →
      terminalCompressedEndpointReturn (m := m) exchange c
        (terminalEndpointB (m := m) c r) =
      terminalEndpointA (m := m) c (terminalEndpointNext (m := m) c r)
  boundary0_B3 :
    terminalCompressedEndpointReturn (m := m) exchange 0
      (terminalEndpointB (m := m) 0 3) = terminalEndpointEplus (m := m) 0
  boundary0_Eplus :
    terminalCompressedEndpointReturn (m := m) exchange 0
      (terminalEndpointEplus (m := m) 0) = terminalEndpointA (m := m) 0 1
  boundary0_A3 :
    terminalCompressedEndpointReturn (m := m) exchange 0
      (terminalEndpointA (m := m) 0 3) = terminalEndpointEminus (m := m) 0
  boundary0_Eminus :
    terminalCompressedEndpointReturn (m := m) exchange 0
      (terminalEndpointEminus (m := m) 0) = terminalEndpointB (m := m) 0 1
  boundary1_A4 :
    terminalCompressedEndpointReturn (m := m) exchange 1
      (terminalEndpointA (m := m) 1 4) = terminalEndpointEplus (m := m) 1
  boundary1_Eplus :
    terminalCompressedEndpointReturn (m := m) exchange 1
      (terminalEndpointEplus (m := m) 1) = terminalEndpointB (m := m) 1 2
  boundary1_B4 :
    terminalCompressedEndpointReturn (m := m) exchange 1
      (terminalEndpointB (m := m) 1 4) = terminalEndpointEminus (m := m) 1
  boundary1_Eminus :
    terminalCompressedEndpointReturn (m := m) exchange 1
      (terminalEndpointEminus (m := m) 1) = terminalEndpointA (m := m) 1 2
  boundary2_A2 :
    terminalCompressedEndpointReturn (m := m) exchange 2
      (terminalEndpointA (m := m) 2 2) = terminalEndpointEminus (m := m) 2
  boundary2_Eminus :
    terminalCompressedEndpointReturn (m := m) exchange 2
      (terminalEndpointEminus (m := m) 2) = terminalEndpointB (m := m) 2 4
  boundary2_B2 :
    terminalCompressedEndpointReturn (m := m) exchange 2
      (terminalEndpointB (m := m) 2 2) = terminalEndpointEplus (m := m) 2
  boundary2_Eplus :
    terminalCompressedEndpointReturn (m := m) exchange 2
      (terminalEndpointEplus (m := m) 2) = terminalEndpointA (m := m) 2 4

/-- Exact selector used for the terminal interlacing step.  For `m ≥ 6`, the
manuscript selects `m-1` bridge points `c_j`; the final field records the
successor relation `F₁⁻¹ F₀(c_j)=c_{j+1}`. -/
structure TerminalA2InterlacingSelector (m : Nat) [NeZero m] where
  six_le : 6 ≤ m
  L : Nat
  L_eq : L = m - 1
  point : Fin L → TerminalQ m
  inverseF1 : TerminalQ m → TerminalQ m
  inverseF1_left : Function.LeftInverse inverseF1 (terminalReturn (m := m) 1)
  selectorSucc : Fin L → Fin L
  selectorStep :
    ∀ j : Fin L,
      inverseF1 (terminalReturn (m := m) 0 (point j)) = point (selectorSucc j)
  selectorSucc_singleCycle : IsSingleCycleMap selectorSucc
  odd_length : Odd L

/-- Finite terminal-carrier cyclicity for a fixed modulus.  This is the
part of the terminal `A₂` argument that is literally finite and should be closed
by explicit orbits. -/
structure TerminalA2FiniteCyclicity (m : Nat) [NeZero m] where
  even : Even m
  four_le : 4 ≤ m
  terminalReturn_singleCycle :
    ∀ c : TorusColor 3, IsSingleCycleMap (terminalReturn (m := m) c)

/-- Paper proof payload for parametric terminal `A₂` cyclicity.  The endpoint
recurrence is recorded separately from the final single-cycle conclusion so that
the remaining formalization has a concrete target rather than an opaque theorem
statement. -/
structure TerminalA2ParametricCyclicity (m : Nat) [NeZero m]
    extends TerminalA2FiniteCyclicity m where
  endpointRecurrence : TerminalA2EndpointRecurrence m

/-- Closed `m = 4` terminal-carrier cyclicity, using the three explicit orbit
certificates ported from the terminal `A₂` appendix table. -/
noncomputable def terminalA2M4FiniteCyclicity :
    TerminalA2FiniteCyclicity 4 where
  even := ⟨2, by omega⟩
  four_le := by omega
  terminalReturn_singleCycle := by
    intro c
    simpa [TerminalFiniteCyclicity.F4] using
      TerminalFiniteCyclicity.f4_all_singleCycle c

/-- Closed `m = 6` terminal-carrier cyclicity, using the three explicit orbit
certificates from the small-terminal parent check. -/
noncomputable def terminalA2M6FiniteCyclicity :
    TerminalA2FiniteCyclicity 6 where
  even := ⟨3, by omega⟩
  four_le := by omega
  terminalReturn_singleCycle := by
    intro c
    simpa [TerminalFiniteCyclicity.F6] using
      TerminalFiniteCyclicity.f6_all_singleCycle c

/-! ## A₂ proof payload split

The paper proof has two logically separate layers.

* `TerminalA2CarrierCyclicityFamily` is the parametric statement that the
  collapsed terminal carriers `Fᵢ = terminalReturn i` are single cycles on
  `Q_m`.
* `TerminalA2RootFlatRealizationFamily` is the section/row-expansion statement
  that a standard root-flat schedule has first return conjugate to those
  carriers through an explicit return-section equivalence.

The adapter below is closed: once these two pieces are supplied, the H1
`RootFlatCycle.D3EvenCycleDataFamily` follows by conjugacy.
-/

/-- The two closed low-modulus terminal A₂ checks currently available in Lean. -/
structure TerminalA2LowModFiniteBundle where
  m4 : TerminalA2FiniteCyclicity 4
  m6 : TerminalA2FiniteCyclicity 6

/-- Closed `m=4` and `m=6` terminal-carrier evidence, bundled at the A₂ layer. -/
noncomputable def terminalA2LowModFiniteBundle :
    TerminalA2LowModFiniteBundle where
  m4 := terminalA2M4FiniteCyclicity
  m6 := terminalA2M6FiniteCyclicity

/-- Evaluate `terminalReturn` under the `EvenModulusRange` instance package. -/
def terminalReturnOfRange {m : Nat} (hm : EvenModulusRange m)
    (c : TorusColor 3) : TerminalQ m → TerminalQ m := by
  letI := RootFlatCycle.neZero_of_evenModulusRange hm
  exact terminalReturn (m := m) c

/-- Parametric terminal-carrier cyclicity, isolated from root-flat realization. -/
abbrev TerminalA2CarrierCyclicityFamily : Prop :=
  ∀ {m : Nat} (hm : EvenModulusRange m),
    ∀ c : TorusColor 3,
      IsSingleCycleMap (terminalReturnOfRange hm c)

/-- Package a candidate root-flat direction table under `EvenModulusRange`. -/
def terminalA2ScheduleOfDir {m : Nat} (_hm : EvenModulusRange m)
    (dir : ZMod m → RootState m → TorusColor 3 → TorusDirection 3) :
    RootFlatSchedule (TorusColor 3) (TorusDirection 3) (RootState m) m :=
  RootFlatCycle.schedule dir

/-- First return of an A₂ root-flat direction table under `EvenModulusRange`. -/
def terminalA2ReturnMapOfDir {m : Nat} (hm : EvenModulusRange m)
    (dir : ZMod m → RootState m → TorusColor 3 → TorusDirection 3)
    (c : TorusColor 3) : RootState m → RootState m := by
  letI := RootFlatCycle.neZero_of_evenModulusRange hm
  exact (RootFlatCycle.schedule dir).returnMap c

/-- Single-modulus root-flat realization layer for the terminal A₂ block.  This
is the pointwise form used by low-modulus bridges such as the `m=4` H2 terminal
realization. -/
structure TerminalA2RootFlatRealizationAt (m : Nat) [NeZero m] where
  dir : ZMod m → RootState m → TorusColor 3 → TorusDirection 3
  sectionEquiv : TerminalQ m ≃ RootState m
  rowLatin : (RootFlatCycle.schedule dir).rowLatin
  layerBijective : (RootFlatCycle.schedule dir).layerBijective
  return_eq_terminal :
    ∀ c : TorusColor 3, ∀ q : TerminalQ m,
      sectionEquiv.symm ((RootFlatCycle.schedule dir).returnMap c (sectionEquiv q)) =
        terminalReturn (m := m) c q

/-- A single-modulus A₂ realization plus finite carrier cyclicity gives the
standard root-flat cycle-data for `D₃(m)`. -/
def cycleData_of_finiteCyclicity_and_realizationAt
    {m : Nat} [NeZero m]
    (cyclicity : TerminalA2FiniteCyclicity m)
    (realization : TerminalA2RootFlatRealizationAt m) :
    RootFlatCycle.RootFlatCycleData 2 m := by
  refine ⟨realization.dir, realization.rowLatin,
    realization.layerBijective, ?_⟩
  intro c
  exact Shared.single_cycle_of_equiv_conj
    realization.sectionEquiv
    ((RootFlatCycle.schedule realization.dir).returnMap c)
    (terminalReturn (m := m) c)
    (cyclicity.terminalReturn_singleCycle c)
    (realization.return_eq_terminal c)

/-- Root-flat realization layer for the terminal A₂ block.  The return equality
is stated through an explicit return-section equivalence.  This field is
essential: the plain chart `rootPairEquiv` is too rigid for the paper's
run-collapse correspondence. -/
structure TerminalA2RootFlatRealizationFamily where
  dir :
    ∀ {m : Nat} (_hm : EvenModulusRange m),
      ZMod m → RootState m → TorusColor 3 → TorusDirection 3
  sectionEquiv :
    ∀ {m : Nat} (_hm : EvenModulusRange m), TerminalQ m ≃ RootState m
  rowLatin :
    ∀ {m : Nat} (hm : EvenModulusRange m),
      (terminalA2ScheduleOfDir hm (dir hm)).rowLatin
  layerBijective :
    ∀ {m : Nat} (hm : EvenModulusRange m),
      (terminalA2ScheduleOfDir hm (dir hm)).layerBijective
  return_eq_terminal :
    ∀ {m : Nat} (hm : EvenModulusRange m)
      (c : TorusColor 3) (q : TerminalQ m),
      (sectionEquiv hm).symm
          (terminalA2ReturnMapOfDir hm (dir hm) c ((sectionEquiv hm) q)) =
        terminalReturnOfRange hm c q

/-- Derive terminal-carrier cyclicity from the stronger parametric cyclicity
payload used by `TerminalA2ParametricSolution`. -/
theorem carrierCyclicityFamily_of_parametricCyclicity
    (h :
      ∀ {m : Nat} [NeZero m], Even m → 4 ≤ m →
        TerminalA2ParametricCyclicity m) :
    TerminalA2CarrierCyclicityFamily := by
  intro m hm c
  letI := RootFlatCycle.neZero_of_evenModulusRange hm
  have hmEven : Even m := by
    rcases hm.2 with ⟨k, rfl⟩
    exact ⟨k, by omega⟩
  simpa [terminalReturnOfRange] using
    (h hmEven hm.1).terminalReturn_singleCycle c

/-- Closed A₂ adapter: carrier cyclicity plus a root-flat realization gives the
cycle-data family consumed by H1. -/
theorem cycleDataFamily_of_carrierCyclicity_and_realization
    (carrier : TerminalA2CarrierCyclicityFamily)
    (realization : TerminalA2RootFlatRealizationFamily) :
    RootFlatCycle.D3EvenCycleDataFamily := by
  intro m hm
  letI := RootFlatCycle.neZero_of_evenModulusRange hm
  let a2Dir := realization.dir hm
  refine ⟨⟨a2Dir, ?_, ?_, ?_⟩⟩
  · simpa [terminalA2ScheduleOfDir] using realization.rowLatin hm
  · simpa [terminalA2ScheduleOfDir] using realization.layerBijective hm
  · intro c
    exact Shared.single_cycle_of_equiv_conj
      (realization.sectionEquiv hm)
      ((RootFlatCycle.schedule (realization.dir hm)).returnMap c)
      (terminalReturnOfRange hm c)
      (carrier hm c)
      (by
        intro q
        simpa [terminalA2ReturnMapOfDir] using
          realization.return_eq_terminal hm c q)

/-- Convenience adapter when the paper recurrence package supplies carrier
cyclicity and the separate row/section theorem supplies realization. -/
theorem cycleDataFamily_of_parametricCyclicity_and_realization
    (cyclicity :
      ∀ {m : Nat} [NeZero m], Even m → 4 ≤ m →
        TerminalA2ParametricCyclicity m)
    (realization : TerminalA2RootFlatRealizationFamily) :
    RootFlatCycle.D3EvenCycleDataFamily :=
  cycleDataFamily_of_carrierCyclicity_and_realization
    (carrierCyclicityFamily_of_parametricCyclicity cyclicity)
    realization

/-- The constructive H1 handoff required by the final induction.  The first
field is the paper recurrence statement for the collapsed terminal returns; the
second is the standard-lift RF1/RF2/RF3 family consumed by `RootFlatCycle`. -/
structure TerminalA2ParametricSolution where
  cyclicity :
    ∀ {m : Nat} [NeZero m], Even m → 4 ≤ m →
      TerminalA2ParametricCyclicity m
  interlacing :
    ∀ {m : Nat} [NeZero m], Even m → 6 ≤ m →
      TerminalA2InterlacingSelector m
  m4FiniteCyclicity : TerminalA2FiniteCyclicity 4
  cycleDataFamily : RootFlatCycle.D3EvenCycleDataFamily

/-- Build the full H1 solution package from the separated paper ingredients:
parametric carrier cyclicity, the odd selector/interlacing data, and the
root-flat realization theorem. -/
noncomputable def terminalA2ParametricSolution_of_realization
    (cyclicity :
      ∀ {m : Nat} [NeZero m], Even m → 4 ≤ m →
        TerminalA2ParametricCyclicity m)
    (interlacing :
      ∀ {m : Nat} [NeZero m], Even m → 6 ≤ m →
        TerminalA2InterlacingSelector m)
    (realization : TerminalA2RootFlatRealizationFamily) :
    TerminalA2ParametricSolution where
  cyclicity := cyclicity
  interlacing := interlacing
  m4FiniteCyclicity := terminalA2M4FiniteCyclicity
  cycleDataFamily :=
    cycleDataFamily_of_parametricCyclicity_and_realization
      cyclicity realization

/-- Assemble a final D3 root-flat certificate family from supplied H1 cycle
data.  The RF1/RF2/RF3-to-certificate step is closed here. -/
theorem rootFlatCertificateFamily_of_cycleDataFamily
    (cycleDataFamily : RootFlatCycle.D3EvenCycleDataFamily) :
    FinalD3EvenRootFlatCertificateFamily :=
  RootFlatCycle.finalD3EvenRootFlatCertificateFamily_of_d3EvenCycleDataFamily
    cycleDataFamily

/-- Assemble the final D3 root-flat certificate family from the full terminal
`A₂` solution package. -/
theorem rootFlatCertificateFamily_of_solution
    (solution : TerminalA2ParametricSolution) :
    FinalD3EvenRootFlatCertificateFamily :=
  rootFlatCertificateFamily_of_cycleDataFamily solution.cycleDataFamily

/-- Direct H1 handoff from the separated A₂ proof ingredients. -/
theorem rootFlatCertificateFamily_of_realization
    (cyclicity :
      ∀ {m : Nat} [NeZero m], Even m → 4 ≤ m →
        TerminalA2ParametricCyclicity m)
    (interlacing :
      ∀ {m : Nat} [NeZero m], Even m → 6 ≤ m →
        TerminalA2InterlacingSelector m)
    (realization : TerminalA2RootFlatRealizationFamily) :
    FinalD3EvenRootFlatCertificateFamily :=
  rootFlatCertificateFamily_of_solution
    (terminalA2ParametricSolution_of_realization
      cyclicity interlacing realization)

/-- D3 root-flat certificate for one even modulus, obtained from a supplied H1
solution package. -/
theorem rootFlatCertificate_of_evenModulusRange
    (solution : TerminalA2ParametricSolution)
    {m : Nat} (hm : EvenModulusRange m) :
    FinalD3EvenRootFlatCertificate m :=
  (rootFlatCertificateFamily_of_solution solution).rootFlatCertificate hm

end D3TerminalA2Parametric
end V28Hard
end EvenV11
