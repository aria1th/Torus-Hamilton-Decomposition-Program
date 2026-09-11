-- STATUS: main-path
import TorusEven.Entry.Seed.Residual

namespace TorusEven.Entry.Seed

def residualWitness (p h w c : ℕ) : Prop :=
  if p % 2 = 0 then
    (h = 1 ∧ c < p ∧
      ((w = 0 ∧ (c = 3 ∨ (4 ≤ c ∧ c % 2 = 0))) ∨
       (w = 1 ∧ (c = 1 ∨ c = 2 ∨ (5 ≤ c ∧ c % 2 = 1))) ∨
       (w = 2 ∧ 1 ≤ c ∧ c % 2 = 1))) ∨
    (h = 2 ∧
      ((w = 0 ∧ (c = p + 2 ∨ c = p + 5 ∨ (p + 6 ≤ c ∧ c % 2 = 0))) ∨
       (w = 1 ∧ (c = p + 1 ∨ c = p + 3 ∨ c = p + 4 ∨ (p + 7 ≤ c ∧ c % 2 = 1))) ∨
       (w = 2 ∧ p + 1 ≤ c ∧ c % 2 = 1))) ∨
    (p = 4 ∧ h = 3 ∧ w = 0 ∧ p + 2 ≤ c)
  else
    (h = 1 ∧
      ((w = 0 ∧ c < p ∧ (c = 1 ∨ c = 4 ∨ (5 ≤ c ∧ c % 2 = 1))) ∨
       (w = 1 ∧ (c = p ∨ (c < p ∧ (c = 2 ∨ c = 3 ∨ (6 ≤ c ∧ c % 2 = 0))))) ∨
       (w = 2 ∧ (c = p ∨ (2 ≤ c ∧ c < p ∧ c % 2 = 0))))) ∨
    (h = 2 ∧
      ((w = 0 ∧ (c = p ∨ c = p + 4 ∨ (p + 5 ≤ c ∧ c % 2 = 0))) ∨
       (w = 1 ∧ (c = p + 1 ∨ c = p + 2 ∨ c = p + 3 ∨ (p + 6 ≤ c ∧ c % 2 = 1))) ∨
       (w = 2 ∧ (c = p + 1 ∨ (p + 2 ≤ c ∧ c % 2 = 1)))))

theorem mem_residualNat_of_witness (p : ℕ) (hp : 2 ≤ p) (hp4 : 4 ≤ p)
    (hw : Fin 4 × Fin 4) (c : Shell.Color p)
    (hc : residualWitness p hw.1.val hw.2.val c.val) : c ∈ residualNat p hp hw := by
  have h3 : p ≠ 3 := by omega
  have hclt := c.isLt
  obtain ⟨h, w⟩ := hw
  by_cases he : p % 2 = 0
  all_goals fin_cases h <;> fin_cases w <;> simp [residualWitness, he] at hc
  all_goals
    rw [residualNat, Finset.mem_filter, auxiliaryNat, Finset.mem_sdiff,
      Shell.mem_aUsers, Shell.mem_selectedNat]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp [Shell.aUser]
      omega
    · rintro (⟨i, hi, hi'⟩ | ⟨i, hi, hi'⟩)
      · simp [Shell.pairCount, Shell.fillerIndex, he] at hi hi' <;> omega
      · by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;>
          simp [Shell.pairCount, Shell.endpointIndex, he, hi0, hi1] at hi hi' <;> omega
    · intro q hq hmate
      have hv := congrArg Fin.val hmate
      change c.val = mateIndex p q at hv
      fin_cases q <;> simp [anchorBlockNat] at hq
      all_goals simp [mateIndex, h3, he] at hv; omega

end TorusEven.Entry.Seed
