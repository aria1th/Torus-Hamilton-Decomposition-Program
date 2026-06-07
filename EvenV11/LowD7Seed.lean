import EvenV11.TerminalFiniteCyclicity
import EvenV11.UnitCarry

/-!
# D7(4)/D7(6) reused-plus-lane returns are single cycles (rank-three folded base)

Paper: `subtex/rank_three_*`, `subtex/appendix/low_modulus_witnesses.tex`.
The folded rank-three endpoint (H3/H4) has exactly one new cyclicity issue — the
reused plus-lane `p₁⁺` return, which over one terminal period reads the odd
terminal word `W₄ = F₁F₀²` (m=4) / `W₆ = F₁²F₀³` (m=6).
`lem:rank-three-folded-word-verification` + `lem:word-skew-product` make this
return cyclic; the remaining coordinates are appended by unit-carry completions.

This file builds that reused-plus-lane return **exactly like `LowD5M4Seed.P1`**
(a word-skew product whose monodromy is the reset word) and proves it is a single
cycle, reusing the already-ported word cyclicity
(`TerminalFiniteCyclicity.w4/w6_singleCycle`) and the word-skew engine
(`single_cycle_of_skewProduct_base_orbit_monodromy`, Bundle B).

No `sorry`, no `native_decide`. This brings H3/H4 to the same state as H2: the
abstract return single cycles are done; only the ribbon realization remains.
-/

set_option maxRecDepth 8000
set_option maxHeartbeats 8000000

namespace EvenV11
namespace LowD7Seed

open Shared
open EvenV11.TerminalFiniteCyclicity

/-! ## D7(4): monodromy `W₄ = F₁F₀²` over the 4-circuit -/

/-- Fiber kicks placing the reused-return trace `F₀,F₀,F₁` at `y = 1,2,3`
(identity at `y = 0`); the period monodromy is `F₁∘F₀∘F₀ = W₄`. -/
def fiberW4 : ZMod 4 → TerminalQ 4 → TerminalQ 4 := fun y q =>
  if y = 1 then F4 0 q else if y = 2 then F4 0 q else if y = 3 then F4 1 q else q

/-- The reused-plus-lane return on `ZMod 4 × Q₄` (word-skew over `W₄`). -/
def reusedReturn4 : ZMod 4 × TerminalQ 4 → ZMod 4 × TerminalQ 4 :=
  skewProductMap (fun y : ZMod 4 => y + 1) fiberW4

theorem F4_bijective (i : Fin 3) : Function.Bijective (F4 i) := by
  fin_cases i <;> decide

private theorem base4_bij : Function.Bijective (fun y : ZMod 4 => y + 1) :=
  (Equiv.addRight (1 : ZMod 4)).bijective

private theorem fiberW4_bij : ∀ y, Function.Bijective (fiberW4 y) := by
  intro y
  by_cases h1 : y = 1
  · simpa [fiberW4, h1] using F4_bijective 0
  · by_cases h2 : y = 2
    · simpa [fiberW4, h1, h2] using F4_bijective 0
    · by_cases h3 : y = 3
      · simpa [fiberW4, h1, h2, h3] using F4_bijective 1
      · simpa [fiberW4, h1, h2, h3] using Function.bijective_id

private theorem base4_return : (fun y : ZMod 4 => y + 1)^[4] 0 = 0 := by decide
private theorem base4_cover :
    ∀ b : ZMod 4, ∃ k : Nat, k < 4 ∧ (fun y : ZMod 4 => y + 1)^[k] 0 = b := by decide

theorem reusedReturn4_monodromy : Shared.sectionReturn reusedReturn4 0 4 = W4 := by
  decide

theorem reusedReturn4_singleCycle : Shared.IsSingleCycleMap reusedReturn4 :=
  Shared.single_cycle_of_skewProduct_base_orbit_monodromy
    (fun y : ZMod 4 => y + 1) fiberW4 0 4 base4_bij fiberW4_bij base4_return base4_cover
    (by change Shared.IsSingleCycleMap (Shared.sectionReturn reusedReturn4 0 4)
        rw [reusedReturn4_monodromy]; exact w4_singleCycle)

/-! ## D7(6): monodromy `W₆ = F₁²F₀³` over the 6-circuit -/

/-- Fiber kicks placing the reused-return trace `F₀,F₀,F₀,F₁,F₁` at `y = 1..5`
(identity at `y = 0`); the period monodromy is `F₁∘F₁∘F₀∘F₀∘F₀ = W₆`. -/
def fiberW6 : ZMod 6 → TerminalQ 6 → TerminalQ 6 := fun y q =>
  if y = 1 then F6 0 q else if y = 2 then F6 0 q else if y = 3 then F6 0 q
  else if y = 4 then F6 1 q else if y = 5 then F6 1 q else q

/-- The reused-plus-lane return on `ZMod 6 × Q₆` (word-skew over `W₆`). -/
def reusedReturn6 : ZMod 6 × TerminalQ 6 → ZMod 6 × TerminalQ 6 :=
  skewProductMap (fun y : ZMod 6 => y + 1) fiberW6

theorem F6_bijective (i : Fin 3) : Function.Bijective (F6 i) := by
  fin_cases i
  · exact f6c0_singleCycle.1
  · exact f6c1_singleCycle.1
  · exact f6c2_singleCycle.1

private theorem base6_bij : Function.Bijective (fun y : ZMod 6 => y + 1) :=
  (Equiv.addRight (1 : ZMod 6)).bijective

private theorem fiberW6_bij : ∀ y, Function.Bijective (fiberW6 y) := by
  intro y
  by_cases h1 : y = 1
  · simpa [fiberW6, h1] using F6_bijective 0
  · by_cases h2 : y = 2
    · simpa [fiberW6, h1, h2] using F6_bijective 0
    · by_cases h3 : y = 3
      · simpa [fiberW6, h1, h2, h3] using F6_bijective 0
      · by_cases h4 : y = 4
        · simpa [fiberW6, h1, h2, h3, h4] using F6_bijective 1
        · by_cases h5 : y = 5
          · simpa [fiberW6, h1, h2, h3, h4, h5] using F6_bijective 1
          · simpa [fiberW6, h1, h2, h3, h4, h5] using Function.bijective_id

private theorem base6_return : (fun y : ZMod 6 => y + 1)^[6] 0 = 0 := by decide
private theorem base6_cover :
    ∀ b : ZMod 6, ∃ k : Nat, k < 6 ∧ (fun y : ZMod 6 => y + 1)^[k] 0 = b := by decide

theorem reusedReturn6_monodromy : Shared.sectionReturn reusedReturn6 0 6 = W6 := by
  decide

theorem reusedReturn6_singleCycle : Shared.IsSingleCycleMap reusedReturn6 :=
  Shared.single_cycle_of_skewProduct_base_orbit_monodromy
    (fun y : ZMod 6 => y + 1) fiberW6 0 6 base6_bij fiberW6_bij base6_return base6_cover
    (by change Shared.IsSingleCycleMap (Shared.sectionReturn reusedReturn6 0 6)
        rw [reusedReturn6_monodromy]; exact w6_singleCycle)

end LowD7Seed
end EvenV11
