import EvenV11.TerminalA2LowMod
import EvenV11.FinalTargetD3RootFlatCertificateBridge
import EvenV11.StandardRootFlatLift
import EvenV11.RootFlatCycleData

/-!
# Hard slot H1: parametric terminal `A₂` root-flat base

This file is a proof-oriented implementation of the manuscript's terminal
`A₂` block.  It intentionally avoids the old Route-E finite-tail strategy and
instead states the exact RF1/RF2/RF3 facts needed to turn the paper's terminal
word into a `FinalD3EvenRootFlatCertificateFamily`.

The delicate point is the identification between a physical terminal row
`q + {a₀,a₁,a₂}` and the standard root-flat lift.  The definitions below make
that identification explicit:

* the root section is `Fin 2 → ZMod m`, transported to `TerminalQ m`;
* `terminalDir` reads the row word `ω_m(z-a_i)` at the current terminal tail;
* `returnMap_eq_terminalReturn` is the run-collapse lemma saying that the
  physical first return of this schedule is exactly the paper's `F_i`;
* `TerminalA2ParametricCyclicity` is the active-endpoint recurrence proof from
  the paper, packaged as single-cycle evidence for all even `m ≥ 4`.

Most fields are closed reductions.  The remaining `sorry`s are the genuine
mathematical checks from the terminal section: run-collapse, layer bijectivity
for the localized terminal rows, and the active-endpoint cyclicity proof.
-/

namespace EvenV11
namespace V28Hard
namespace D3TerminalA2Parametric

open Shared
open TerminalA2LowMod
open StandardRootFlatLift

/-- Standard D3 root section, but kept definitionally close to
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
independent of the layer `t`; the layer variable only records the standard
root-flat lift period. -/
def terminalDir (m : Nat) [NeZero m] :
    ZMod m → RootState m → TorusColor 3 → TorusDirection 3 :=
  fun _t w c => terminalTargetIndex w c

/-- The root-flat schedule obtained by installing the terminal word in every
layer of the standard D3 lift. -/
def schedule (m : Nat) [NeZero m] :
    RootFlatSchedule (TorusColor 3) (TorusDirection 3) (RootState m) m :=
  RootFlatCycle.schedule (terminalDir m)

/-- Local-triangle RF1 in the exact form needed to repair `rowLatin`.  For a
fixed physical elementary triangle anchored at `q`, the map from source color to
head direction is the row equivalence `terminalRowEquiv (ω_m q)`. -/
theorem localTriangle_rowLatin {m : Nat} [NeZero m] (q : TerminalQ m) :
    Function.Bijective
      (fun c : TorusColor 3 =>
        (terminalRowEquiv (terminalOmega q) c : TorusDirection 3)) :=
  (terminalRowEquiv (terminalOmega q)).bijective

/-- RF1.  Each terminal row is Latin because it is one of the six row
permutations `012, 210, 021, 102, 120, 201`. -/
theorem rowLatin {m : Nat} [NeZero m] :
    (schedule m).rowLatin := by
  intro t w
  -- Delicate repair point: `terminalDir` currently lets the anchor depend on the
  -- source color (`z-a_i`).  The paper proof views all three sources inside one
  -- physical triangle `q + {a₀,a₁,a₂}` before transporting to root coordinates.
  -- Prove `terminalDir` is definitionally/extensionally equal to that fixed-row
  -- interpretation, then apply `localTriangle_rowLatin`.
  sorry

/-- RF2 for the terminal schedule.  The intended proof is a finite composition
of local Latin rows in the standard lift.  A useful repair is to prove the
stronger pointwise inverse obtained by replacing each row word by
`terminalRowSourceIndex`. -/
theorem layerBijective {m : Nat} [NeZero m] :
    (schedule m).layerBijective := by
  intro t c
  -- Suggested proof after repair:
  --   1. unfold `schedule`, `RootFlatCycle.schedule`, `terminalDir`,
  --      `RootFlatSchedule.layerMap`, `StandardRootFlatLift.rootStep`;
  --   2. split on `c = 0,1,2`;
  --   3. use the inverse row word `terminalRowSourceIndex` to build the inverse
  --      layer map.
  sorry

/-- Run-collapse: the `m`-layer first return of the standard root-flat schedule
is the paper's terminal return `F_i` on `Q_m`, up to the `RootState ↔ Q_m`
coordinate equivalence.

This is the formal version of Lemma `Terminal rows are Latin`: default layers
contribute the straight fiber advance `Δ_i`, and the non-default terminal rows
insert the local jumps `η_i`. -/
theorem returnMap_eq_terminalReturn {m : Nat} [NeZero m]
    (c : TorusColor 3) (w : RootState m) :
    rootPair ((schedule m).returnMap c w) =
      terminalReturn (m := m) c (rootPair w) := by
  -- Repair route: prove by rewriting `returnMap` as `prefixMap m`; classify the
  -- visited roots on the default fiber; collect the unique non-default rows; the
  -- resulting product is exactly `terminalEta c (z + terminalDelta c)`.
  sorry

/-- Paper proof payload for Terminal `A₂` cyclicity.  The manuscript proves this
by the active-endpoint recurrence; this structure isolates exactly that proof
from the root-flat bookkeeping. -/
structure TerminalA2ParametricCyclicity (m : Nat) [NeZero m] : Prop where
  even : Even m
  four_le : 4 ≤ m
  terminalReturn_singleCycle :
    ∀ c : TorusColor 3, IsSingleCycleMap (terminalReturn (m := m) c)

/-- The active-endpoint theorem from the paper, as a Lean target.  For `m=4` it
may reuse the displayed 16-cycles; for `m≥6` it should instantiate the two
endpoint strings `A^i_r,B^i_r`, prove the boundary blocks, and invoke the
interval-splicing lemma. -/
theorem terminalA2ParametricCyclicity
    {m : Nat} [NeZero m] (hmEven : Even m) (hm4 : 4 ≤ m) :
    TerminalA2ParametricCyclicity m := by
  refine ⟨hmEven, hm4, ?_⟩
  intro c
  -- Suggested split:
  --   * `m = 4`: use the three explicit orbits printed in the manuscript; these
  --     are already present for low-mod terminal words and can be mirrored for
  --     `terminalReturn 0/1/2`.
  --   * `m ≥ 6`: define the active endpoint set `S_i`, the endpoint swap `n_i`,
  --     and `h_i = n_i ∘ η_i`; prove the generic recurrences plus the two
  --     boundary blocks.  Then expand intervals along the default fibers.
  sorry

/-- Transfer terminal cyclicity through `returnMap_eq_terminalReturn`. -/
theorem returnsSingleCycle_of_terminalCyclicity
    {m : Nat} [NeZero m]
    (cyc : TerminalA2ParametricCyclicity m) :
    (schedule m).returnsSingleCycle := by
  intro c
  exact single_cycle_of_equiv_conj (rootPairEquiv m).symm
    ((schedule m).returnMap c)
    (terminalReturn (m := m) c)
    (cyc.terminalReturn_singleCycle c)
    (by
      intro q
      simpa using returnMap_eq_terminalReturn (m := m) c ((rootPairEquiv m).symm q))

/-- D3 root-flat certificate for one even modulus from the paper terminal block. -/
theorem rootFlatCertificate_of_terminalA2
    {m : Nat} [NeZero m] (hmEven : Even m) (hm4 : 4 ≤ m) :
    FinalD3EvenRootFlatCertificate m := by
  let cyc := terminalA2ParametricCyclicity (m := m) hmEven hm4
  let cert : FinalRootFlatTorusCertificate 3 m :=
    RootFlatCycle.finalRootFlatTorusCertificate_of_cycleData
      { dir := terminalDir m
        rowLatin := rowLatin
        layerBijective := layerBijective
        returnsSingleCycle := returnsSingleCycle_of_terminalCyclicity cyc }
  exact cert

/-- H1 candidate family.  Once `rootFlatCertificate_of_terminalA2` is repaired,
this theorem replaces `assume_d3EvenRootFlat` in `Main.lean`. -/
theorem rootFlatCertificateFamily :
    FinalD3EvenRootFlatCertificateFamily where
  rootFlatCertificate := by
    intro m hm
    rcases hm with ⟨hm4, k, rfl⟩
    haveI : NeZero (2 * k) := ⟨by omega⟩
    exact rootFlatCertificate_of_terminalA2
      (m := 2 * k) ⟨k, by omega⟩ hm4

/-- Drop-in replacement for `EvenV11.assume_d3EvenRootFlat` after local repair. -/
theorem candidate_assume_d3EvenRootFlat :
    FinalD3EvenRootFlatCertificateFamily :=
  rootFlatCertificateFamily

end D3TerminalA2Parametric
end V28Hard
end EvenV11
