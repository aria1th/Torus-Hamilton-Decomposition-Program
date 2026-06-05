import Shared.RootFlat
import Shared.TorusCayley

/-!
# D5(4) standard root-flat lift (dir-independent infrastructure)

**Key insight:** `stepConjugacy` is *independent of `dir`*. It is exactly the
standard lift relation `torusEquiv (t,w) + e_δ = torusEquiv (t+1, step δ w)`
instantiated at `δ = dir t w c`. So this relation (`torusEquiv_step`) holds for
every direction, and hence `stepConjugacy` holds for **any** Latin `dir`.

This isolates the remaining D5(4) obligation to: build a `dir` whose five colour
returns are single cycles (the single-cycle facts are already proved in
`LowD5M4Seed.lean`) plus `rowLatin`/`layerBijective`.

The `Equiv`/relation proofs below are mechanical `Fin`-index bookkeeping
and are now closed without `sorry`.
-/

namespace EvenV11
namespace LowD5M4Schedule

open Shared

abbrev RootState := Fin 4 → ZMod 4

/-- Generator step in root-flat coordinates: direction `δ < 4` increments
coordinate `δ`; the last direction (`δ = 4`) acts trivially. -/
def rootStep (δ : TorusDirection 5) (w : RootState) : RootState :=
  if h : (δ : ℕ) < 4 then Function.update w ⟨δ, h⟩ (w ⟨δ, h⟩ + 1) else w

/-- Standard layer identification `ZMod 4 × RootState ≃ TorusVertex 5 4`:
coordinate `i < 4` is `w i`; the last coordinate is `t - ∑ w`. -/
def torusEquiv : ZMod 4 × RootState ≃ TorusVertex 5 4 where
  toFun tw := Fin.snoc tw.2 (tw.1 - ∑ j : Fin 4, tw.2 j)
  invFun x := (∑ i : Fin 5, x i, fun j : Fin 4 => x j.castSucc)
  left_inv := by
    intro tw
    ext
    · simp [Fin.sum_snoc]
    · simp
  right_inv := by
    intro x
    funext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simp
    · simp only [Fin.snoc_last]
      rw [Fin.sum_univ_castSucc]
      abel

/-- The standard lift relation: a generator move on the torus equals
`(layer+1, rootStep)` on the lift. This is the entire content of
`stepConjugacy`, and it is independent of `dir`. -/
theorem torusEquiv_step (δ : TorusDirection 5) (tw : ZMod 4 × RootState) :
    torusEquiv tw + torusBasis 5 4 δ = torusEquiv (tw.1 + 1, rootStep δ tw.2) := by
  classical
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · by_cases hδ : (δ : ℕ) < 4
    · let δ4 : Fin 4 := ⟨δ, hδ⟩
      have hcast : δ = δ4.castSucc := by
        ext
        rfl
      by_cases h : δ4 = j
      · subst j
        simp [torusEquiv, rootStep, torusBasis, hcast]
      · have hne : δ4.castSucc ≠ j.castSucc := by
          intro hc
          exact h (Fin.castSucc_injective 4 hc)
        have h' : j ≠ δ4 := h ∘ Eq.symm
        simp [torusEquiv, rootStep, torusBasis, hcast, h']
    · have hne : δ ≠ j.castSucc := by
        intro hEq
        rw [hEq] at hδ
        exact hδ j.isLt
      have hne' : j.castSucc ≠ δ := hne ∘ Eq.symm
      simp [torusEquiv, rootStep, torusBasis, hδ, hne']
  · fin_cases δ <;>
      simp [torusEquiv, rootStep, torusBasis, Fin.sum_univ_four, Fin.snoc] <;>
      ring_nf

/-- Root-flat schedule determined by a D5(4) direction table. -/
def schedule
    (dir : ZMod 4 → RootState → TorusColor 5 → TorusDirection 5) :
    Shared.RootFlatSchedule (TorusColor 5) (TorusDirection 5) RootState 4 where
  dir := dir
  step := rootStep

/-- The induced Cayley color-direction table on torus coordinates. -/
def liftedColorDir
    (dir : ZMod 4 → RootState → TorusColor 5 → TorusDirection 5) :
    TorusColor 5 → TorusVertex 5 4 → TorusDirection 5 :=
  fun c x => dir (torusEquiv.symm x).1 (torusEquiv.symm x).2 c

/-- `stepConjugacy` for the standard D5(4) lift is independent of the chosen
direction table. The actual H2 work is therefore `rowLatin`,
`layerBijective`, and `returnsSingleCycle` for the concrete `dir`. -/
theorem stepConjugacy_of_dir
    (dir : ZMod 4 → RootState → TorusColor 5 → TorusDirection 5)
    (c : TorusColor 5) (tw : ZMod 4 × RootState) :
    Shared.cayleyColorStep (liftedColorDir dir) c (torusEquiv tw) =
      torusEquiv ((schedule dir).fullStep c tw) := by
  simpa [Shared.cayleyColorStep, liftedColorDir, schedule,
    Shared.RootFlatSchedule.fullStep, Shared.RootFlatSchedule.layerMap]
    using torusEquiv_step (dir tw.1 tw.2 c) tw

end LowD5M4Schedule
end EvenV11
