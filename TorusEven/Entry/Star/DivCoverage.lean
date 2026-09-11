-- STATUS: main-path
import TorusEven.Entry.Star.DivTable

namespace TorusEven.Entry.Star.Divisible

open Surgery

variable (q : ℕ) [NeZero (6 * q)] (hq : 2 ≤ q)

def MeetsX (u : ZMod (6 * q) × ZMod 2) : Prop :=
  ∃ s, 0 < s ∧ s < 6 * q ∧ x q s ∈ orbitSet (phi q hq) u

theorem meets_x (s : ℕ) (hs : 0 < s) (hsm : s < 6 * q) : MeetsX q hq (x q s) :=
  ⟨s, hs, hsm, 0, rfl⟩

theorem meets_of_step {u v : ZMod (6 * q) × ZMod 2}
    (he : phi q hq u = v) (hv : MeetsX q hq v) : MeetsX q hq u := by
  obtain ⟨s, hs, hsm, hsu⟩ := hv
  refine ⟨s, hs, hsm, ?_⟩
  rwa [orbitSet_eq_of_mem (phi q hq).injective (show v ∈ orbitSet (phi q hq) u from ⟨1, he⟩)] at hsu

theorem plus_meets_x : MeetsX q hq (x q 0) :=
  meets_of_step q hq (phi_plus q hq) (meets_x q hq _ (by omega) (by omega))

theorem minus_meets_x : MeetsX q hq (y q 0) := by
  have h1 := phi_y_fixed q hq 1 (by omega) (by omega) (by decide) (by decide) (by omega)
  have h2 : phi q hq (y q 2) = x q (2 * q - 1) := by
    simpa using phi_y_axis q hq 1 (by omega) (by omega)
  exact meets_of_step q hq (phi_minus q hq) (meets_of_step q hq h1
    (meets_of_step q hq h2 (meets_x q hq _ (by omega) (by omega))))

theorem last_y_meets_x : MeetsX q hq (y q (6 * q - 1)) := by
  have he : phi q hq (y q (6 * q - 4)) = x q 1 := by
    simpa only [show 3 * (2 * q - 1) - 1 = 6 * q - 4 by omega,
      show 2 * q - (2 * q - 1) = 1 by omega] using
      phi_y_axis q hq (2 * q - 1) (by omega) (by omega)
  exact meets_of_step q hq (phi_y_last q hq)
    (meets_of_step q hq he (meets_x q hq _ (by omega) (by omega)))

theorem y_meets_x (s : ℕ) (hsm : s < 6 * q) : MeetsX q hq (y q s) := by
  suffices ∀ n s, 6 * q - s = n → s < 6 * q → MeetsX q hq (y q s) from this _ s rfl hsm
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro s hn hs
    by_cases h0 : s = 0
    · subst s; exact minus_meets_x q hq
    by_cases h3 : s = 3
    · subst s; exact meets_of_step q hq (phi_y_three q hq) (minus_meets_x q hq)
    by_cases hl : s = 6 * q - 1
    · subst s; exact last_y_meets_x q hq
    by_cases he : s = 6 * q - 5
    · subst s; exact meets_of_step q hq (phi_y_end q hq) (plus_meets_x q hq)
    by_cases hd : (s + 1) % 3 = 0
    · let r := (s + 1) / 3
      have hr : 3 * r = s + 1 := by dsimp [r]; omega
      have hr0 : 0 < r := by omega
      have hrm : r < 2 * q := by omega
      have hp : phi q hq (y q s) = x q (2 * q - r) := by
        simpa only [hr, Nat.add_sub_cancel] using phi_y_axis q hq r hr0 hrm
      exact meets_of_step q hq hp (meets_x q hq _ (by omega) (by omega))
    · exact meets_of_step q hq (phi_y_fixed q hq s (by omega) (by omega) hd h3 he)
        (ih (6 * q - (s + 1)) (by omega) (s + 1) rfl (by omega))

theorem phi_meets_x (u : ZMod (6 * q) × ZMod 2) : MeetsX q hq u := by
  obtain ⟨s, z⟩ := u
  have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hz z with rfl | rfl
  · by_cases hs : s = 0
    · subst s; simpa [x] using plus_meets_x q hq
    · have hv : 0 < s.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero s).mpr hs)
      simpa [x] using meets_x q hq s.val hv s.val_lt
  · simpa [y] using y_meets_x q hq s.val s.val_lt

theorem phi_hamilton : Shared.IsSingleCycleMap (phi q hq) := by
  apply singleCycle_of_induced_orbits (phi q hq) (xEmbedding q) (psi q hq) (psi_hamilton q hq)
  · intro i
    exact ⟨retTime (phi q hq) (horizontal q) (xEmbedding q i), phi_ret_x q hq i⟩
  · intro u
    obtain ⟨s, hs, hsm, hsu⟩ := phi_meets_x q hq u
    refine ⟨⟨s - 1, by omega⟩, ?_⟩
    simpa only [xEmbedding, Nat.sub_add_cancel hs] using hsu

theorem sum_return_times :
    (∑ u : horizontal q, retTime (phi q hq) (horizontal q) u) = 12 * q := by
  have hm (u : ZMod (6 * q) × ZMod 2) :
      ∃ v ∈ horizontal q, v ∈ orbitSet (phi q hq) u := by
    obtain ⟨s, hs, hsm, hsu⟩ := phi_meets_x q hq u
    exact ⟨x q s, x_mem q s hs hsm, hsu⟩
  rw [sum_retTime (phi q hq) (horizontal q) hm]
  simp only [Fintype.card_prod, ZMod.card]
  omega

end TorusEven.Entry.Star.Divisible
