-- STATUS: main-path
import TorusEven.Entry.Star.NondivTable

namespace TorusEven.Entry.Star.Nondivisible

open Surgery

variable (k : ℕ) [NeZero (2 * k)] (hk : 4 ≤ k)

def MeetsX (u : ZMod (2 * k) × ZMod 2) : Prop :=
  ∃ s, 0 < s ∧ s < 2 * k ∧ x k s ∈ orbitSet (phi k hk) u

theorem meets_x (s : ℕ) (hs : 0 < s) (hsm : s < 2 * k) : MeetsX k hk (x k s) :=
  ⟨s, hs, hsm, 0, rfl⟩

theorem meets_of_step {u v : ZMod (2 * k) × ZMod 2}
    (he : phi k hk u = v) (hv : MeetsX k hk v) : MeetsX k hk u := by
  obtain ⟨s, hs, hsm, hsu⟩ := hv
  refine ⟨s, hs, hsm, ?_⟩
  rwa [orbitSet_eq_of_mem (phi k hk).injective (show v ∈ orbitSet (phi k hk) u from ⟨1, he⟩)] at hsu

variable (hd : ¬ 3 ∣ 2 * k)
include hd

theorem plus_meets_x : MeetsX k hk (x k 0) :=
  meets_of_step k hk (phi_plus k hk hd) (meets_x k hk _ (by omega) (by omega))

theorem minus_meets_x : MeetsX k hk (y k 0) :=
  meets_of_step k hk (phi_minus k hk hd) (plus_meets_x k hk hd)

theorem odd_y_meets_x (s : ℕ) (hsm : s < 2 * k - 1) (hs2 : s % 2 ≠ 0) :
    MeetsX k hk (y k s) := by
  have he : 2 * ((s + 1) / 2) - 1 = s := by omega
  have hp : phi k hk (y k s) = x k ((s + 1) / 2) := by
    simpa only [he] using phi_y_axis k hk hd ((s + 1) / 2) (by omega) (by omega)
  exact meets_of_step k hk hp (meets_x k hk _ (by omega) (by omega))

theorem y_meets_x (s : ℕ) (hsm : s < 2 * k) : MeetsX k hk (y k s) := by
  by_cases h0 : s = 0
  · subst s; exact minus_meets_x k hk hd
  by_cases hl : s = 2 * k - 1
  · subst s
    exact meets_of_step k hk (phi_y_last k hk hd) (odd_y_meets_x k hk hd 1 (by omega) (by decide))
  by_cases hp : s = 2 * k - 2
  · subst s
    exact meets_of_step k hk (phi_y_penultimate k hk hd) (minus_meets_x k hk hd)
  by_cases hs2 : s % 2 = 0
  · exact meets_of_step k hk (phi_y_fixed k hk hd s (by omega) (by omega) hs2)
      (odd_y_meets_x k hk hd (s + 1) (by omega) (by omega))
  · exact odd_y_meets_x k hk hd s (by omega) hs2

theorem phi_meets_x (u : ZMod (2 * k) × ZMod 2) : MeetsX k hk u := by
  obtain ⟨s, z⟩ := u
  have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hz z with rfl | rfl
  · by_cases hs : s = 0
    · subst s; simpa [x] using plus_meets_x k hk hd
    · have hv : 0 < s.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero s).mpr hs)
      simpa [x] using meets_x k hk s.val hv s.val_lt
  · simpa [y] using y_meets_x k hk hd s.val s.val_lt

theorem phi_hamilton : Shared.IsSingleCycleMap (phi k hk) := by
  have hk3 : ¬ 3 ∣ k := by
    rintro ⟨r, hr⟩
    exact hd ⟨2 * r, by omega⟩
  apply singleCycle_of_induced_orbits (phi k hk) (xEmbedding k) (psi k hk) (psi_hamilton k hk hk3)
  · intro i
    exact ⟨retTime (phi k hk) (horizontal k) (xEmbedding k i), phi_ret_x k hk hd i⟩
  · intro u
    obtain ⟨s, hs, hsm, hsu⟩ := phi_meets_x k hk hd u
    refine ⟨⟨s - 1, by omega⟩, ?_⟩
    simpa only [xEmbedding, Nat.sub_add_cancel hs] using hsu

theorem sum_return_times :
    (∑ u : horizontal k, retTime (phi k hk) (horizontal k) u) = 4 * k := by
  have hm (u : ZMod (2 * k) × ZMod 2) :
      ∃ v ∈ horizontal k, v ∈ orbitSet (phi k hk) u := by
    obtain ⟨s, hs, hsm, hsu⟩ := phi_meets_x k hk hd u
    exact ⟨x k s, x_mem k s hs hsm, hsu⟩
  rw [sum_retTime (phi k hk) (horizontal k) hm]
  simp only [Fintype.card_prod, ZMod.card]
  omega

end TorusEven.Entry.Star.Nondivisible
