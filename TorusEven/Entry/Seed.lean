-- STATUS: main-path
import TorusEven.Collar.Superposition
import TorusEven.Entry.Shell
import TorusEven.Entry.Star

namespace TorusEven.Entry.Seed

open Collar Surgery

abbrev Color (p : ℕ) := Fin 3 ⊕ Shell.Color p

variable (p : ℕ) (hp : 2 ≤ p) {m : ℕ}

def factorization : MultitorusFactorization (Color p) (Fin 3) m :=
  NearCore.factorization.superpose (Shell.factorization p hp)

def active : Finset (Color p) := Finset.univ.map Function.Embedding.inl

theorem width (j : Fin 3) : (factorization (m := m) p hp).width j =
    ![p - p / 2 + 1, p / 2 + 1, p + 1] j := by
  fin_cases j <;> simp [factorization, MultitorusFactorization.superpose,
    NearCore.factorization, Shell.factorization, Nat.add_comm]

theorem activeSeparated : (factorization (m := m) p hp).ActiveSeparated (active p) := by
  intro v c hc d hd he
  obtain ⟨c, _, rfl⟩ := Finset.mem_map.mp hc
  obtain ⟨d, _, rfl⟩ := Finset.mem_map.mp hd
  exact congrArg Sum.inl ((nearRow (height v) (v 2)).injective he)

variable [NeZero m] (hm : 4 ≤ m) (heven : Even m)
include hm heven

theorem circuitCount_left (c : Fin 3) :
    circuitCount ((factorization (m := m) p hp).step (.inl c)) = if c = 2 then 2 else 1 :=
  NearCore.circuitCount hm heven c

omit heven in
theorem circuitCount_right (c : Shell.Color p) :
    circuitCount ((factorization (m := m) p hp).step (.inr c)) = 1 := Shell.circuitCount p hp hm c

theorem xChart_consistent : CircuitConsistent (factorization (m := m) p hp) xChart :=
  CircuitConsistent.superpose NearCore.factorization (Shell.factorization p hp) xChart
    (Entry.xChart_consistent hm heven) (Shell.xChart_consistent p hp hm)

noncomputable def labels : (factorization (m := m) p hp).CircuitLabel ≃ Fin 4 ⊕ Shell.Color p :=
  (NearCore.factorization.superposeLabels (Shell.factorization p hp)).trans
    (Equiv.sumCongr (anchorEquiv hm heven).symm (Shell.labelEquiv p hp hm))

theorem circuitLabel_card :
    Fintype.card (factorization (m := m) p hp).CircuitLabel = 2 * p + 4 := by
  rw [Fintype.card_congr (labels p hp hm heven)]
  simp [Shell.Color, Nat.add_comm]

omit heven in
noncomputable def replacement : Recolouring (factorization (m := m) p hp)
    (active p) (replacementSupport m) :=
  Recolouring.superpose NearCore.factorization (Shell.factorization p hp) (Star.replacement hm)

theorem replacement_hamilton (c : Color p) :
    Shared.IsSingleCycleMap ((replacement p hp hm).factorization.step c) := by
  cases c with
  | inl c =>
    change Shared.IsSingleCycleMap ((Star.replacement hm).factorization.step c)
    exact Star.replacement_hamilton hm heven c
  | inr c =>
    have hs : (replacement p hp hm).factorization.step (.inr c) =
        (Shell.factorization p hp).step c :=
      Recolouring.superpose_step_right NearCore.factorization
        (Shell.factorization p hp) (Star.replacement hm) c
    rw [hs]
    exact Shell.hamilton p hp hm c

end TorusEven.Entry.Seed
