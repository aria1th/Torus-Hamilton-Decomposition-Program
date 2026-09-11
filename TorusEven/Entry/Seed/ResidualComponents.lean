-- STATUS: main-path
import TorusEven.Entry.Seed.ResidualRows

namespace TorusEven.Entry.Seed

open Collar Incidence

variable (p : ℕ) (hp : 2 ≤ p) {m : ℕ} [NeZero m] (hm : 4 ≤ m) (heven : Even m)
variable (hp4 : 4 ≤ p)
include hp4

theorem residual_same_witness (hw : Fin 4 × Fin 4) {c d : Shell.Color p}
    (hc : residualWitness p hw.1.val hw.2.val c.val)
    (hd : residualWitness p hw.1.val hw.2.val d.val) :
    residualComponent p hp hm heven c = residualComponent p hp hm heven d :=
  residual_same_nat p hp hm heven hw (mem_residualNat_of_witness p hp hp4 hw c hc)
    (mem_residualNat_of_witness p hp hp4 hw d hd)

theorem residual_even_A (he : p % 2 = 0) (c : Shell.Color p) (hlo : 1 ≤ c.val)
    (hhi : c.val < p) :
    residualComponent p hp hm heven c = residualComponent p hp hm heven ⟨1, by omega⟩ := by
  by_cases hc2 : c.val = 2
  · apply residual_same_witness p hp hm heven hp4 (1, 1)
    all_goals simp [residualWitness, he] ; omega
  · by_cases ho : c.val % 2 = 1
    · apply residual_same_witness p hp hm heven hp4 (1, 2)
      all_goals simp [residualWitness, he] ; omega
    · trans residualComponent p hp hm heven ⟨3, by omega⟩
      · apply residual_same_witness p hp hm heven hp4 (1, 0)
        all_goals simp [residualWitness, he] ; omega
      · apply residual_same_witness p hp hm heven hp4 (1, 2)
        all_goals simp [residualWitness, he] ; omega

theorem residual_even_B (he : p % 2 = 0) (c : Shell.Color p) (hlo : p + 1 ≤ c.val) :
    residualComponent p hp hm heven c = residualComponent p hp hm heven ⟨p + 1, by omega⟩ := by
  have hhi := c.isLt
  by_cases ho : c.val % 2 = 1
  · apply residual_same_witness p hp hm heven hp4 (2, 2)
    all_goals simp [residualWitness, he] ; omega
  · by_cases hc4 : c.val = p + 4
    · apply residual_same_witness p hp hm heven hp4 (2, 1)
      all_goals simp [residualWitness, he] <;> omega
    · by_cases hp_eq : p = 4
      · trans residualComponent p hp hm heven ⟨p + 3, by omega⟩
        · apply residual_same_witness p hp hm heven hp4 (3, 0)
          all_goals simp [residualWitness, he] ; omega
        · apply residual_same_witness p hp hm heven hp4 (2, 2)
          all_goals simp [residualWitness, he] ; omega
      · trans residualComponent p hp hm heven ⟨p + 5, by omega⟩
        · apply residual_same_witness p hp hm heven hp4 (2, 0)
          all_goals simp [residualWitness, he] <;> omega
        · apply residual_same_witness p hp hm heven hp4 (2, 2)
          all_goals simp [residualWitness, he] ; omega

theorem residual_odd_A (he : p % 2 ≠ 0) (c : Shell.Color p) (hlo : 1 ≤ c.val)
    (hhi : c.val < p) :
    residualComponent p hp hm heven c = residualComponent p hp hm heven ⟨p, by omega⟩ := by
  by_cases ho : c.val % 2 = 0
  · apply residual_same_witness p hp hm heven hp4 (1, 2)
    all_goals simp [residualWitness, he] <;> omega
  · by_cases hc3 : c.val = 3
    · apply residual_same_witness p hp hm heven hp4 (1, 1)
      all_goals simp [residualWitness, he] <;> omega
    · trans residualComponent p hp hm heven ⟨4, by omega⟩
      · apply residual_same_witness p hp hm heven hp4 (1, 0)
        all_goals simp [residualWitness, he] ; omega
      · apply residual_same_witness p hp hm heven hp4 (1, 2)
        all_goals simp [residualWitness, he] <;> omega

theorem residual_odd_B (he : p % 2 ≠ 0) (c : Shell.Color p) (hlo : p ≤ c.val) :
    residualComponent p hp hm heven c = residualComponent p hp hm heven ⟨p, by omega⟩ := by
  have hroot : residualComponent p hp hm heven ⟨p + 1, by omega⟩ =
      residualComponent p hp hm heven ⟨p, by omega⟩ := by
    trans residualComponent p hp hm heven ⟨p + 4, by omega⟩
    · apply residual_same_witness p hp hm heven hp4 (2, 2)
      all_goals simp [residualWitness, he] <;> omega
    · apply residual_same_witness p hp hm heven hp4 (2, 0)
      all_goals simp [residualWitness, he]
  by_cases hz : c.val = p ∨ (p + 5 ≤ c.val ∧ c.val % 2 = 0)
  · apply residual_same_witness p hp hm heven hp4 (2, 0)
    all_goals simp [residualWitness, he] <;> omega
  · apply Eq.trans _ hroot
    by_cases hc3 : c.val = p + 3
    · apply residual_same_witness p hp hm heven hp4 (2, 1)
      all_goals simp [residualWitness, he] <;> omega
    · apply residual_same_witness p hp hm heven hp4 (2, 2)
      all_goals simp [residualWitness, he] <;> omega

theorem residual_odd_connected (he : p % 2 ≠ 0) (c : Shell.Color p) (hc : 1 ≤ c.val) :
    residualComponent p hp hm heven c = residualComponent p hp hm heven ⟨p, by omega⟩ := by
  by_cases ha : c.val < p
  · exact residual_odd_A p hp hm heven hp4 he c hc ha
  · exact residual_odd_B p hp hm heven hp4 he c (by omega)

end TorusEven.Entry.Seed
