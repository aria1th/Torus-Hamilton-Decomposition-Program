-- STATUS: main-path
import TorusEven.Entry.Seed.Selection
import TorusEven.Entry.Seed.Parity
import TorusEven.Entry.FirstSplit

namespace TorusEven.Entry.Seed

open Collar

variable (p : ℕ) (hp : 2 ≤ p) {m : ℕ} [NeZero m] (hm : 4 ≤ m) (heven : Even m)

include hp hm heven in
theorem hamilton_decomposition : Nonempty (Shared.CayleyDecomposition (2 * p + 3) m) := by
  obtain ⟨S, hS⟩ := exists_blockSelection p hp hm heven
  have hgap : ∀ c ∈ active p, GapSupport ((factorization p hp).step c)
      (replacementSupport m) (splitVoltage S.sources c) := by
    intro c hc
    obtain ⟨c, _, rfl⟩ := Finset.mem_map.mp hc
    change GapSupport (NearCore.step c) (replacementSupport m) (splitVoltage S.sources (.inl c))
    rw [hS c]
    exact anchorVoltage_gapSupport hm heven c
  have hi : 2 ≤ (factorization (m := m) p hp).width 0 := by
    rw [width]
    change 2 ≤ p - p / 2 + 1
    omega
  have h := hamilton_decomposition_of_entry_palette (xChart_consistent p hp hm heven)
    hm heven (activeSeparated p hp) (fun j _ => incidence_even p hp heven hm j)
    S hi hgap (replacement p hp hm) (replacement_hamilton p hp hm heven)
  simpa only [Fintype.card_sum, Fintype.card_fin, Nat.add_comm 3] using h

end TorusEven.Entry.Seed
