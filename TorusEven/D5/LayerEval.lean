-- STATUS: main-path (closed forms of the schedule's layer maps, colour by colour)
import TorusEven.D5.Lattice

/-!
# Layer maps in closed form

For colour `c` and height `t < m`, the schedule's layer map is
`x ↦ x + u_{ρ_t(c)} + [x ∈ C_P] e` where `(P, e)` is the row of colour `c` at height `t`
(if any), except for the terminal plane rule at height `2` for colours `1, 3, 4`, which is
recorded separately as a composition with the plane permutation.
-/

namespace TorusEven
namespace D5

open Cert D5Data Chart

variable {m : ℕ} [NeZero m]

/-- The unit root vector of direction `j` (`0` for `j = 4`). -/
def uvec (j : Fin 5) : Root m := fun i => if (i.castSucc : Fin 5) = j then 1 else 0

theorem rootStep_eq_add_uvec (j : Fin 5) (w : Root m) : rootStep 4 m j w = w + uvec j := by
  funext i
  simp [rootStep, uvec]

theorem layerMap_eq_uvec (t : ZMod m) (c : Fin 5) (x : Root m) :
    (schedule m).layerMap t c x = x + uvec (dir t x c) := by
  simp [Shared.RootFlatSchedule.layerMap, schedule, rootStep_eq_add_uvec]

theorem val_natCast_of_lt {t : ℕ} (ht : t < m) : ((t : ℕ) : ZMod m).val = t := by
  rw [ZMod.val_natCast]
  exact Nat.mod_eq_of_lt ht

/-- The neutral direction of colour `c` at height `t`. -/
def neut (c : Fin 5) (t : ℕ) : Fin 5 :=
  if t ≤ 4 then c + ⟨t % 5, Nat.mod_lt _ (by decide)⟩ else c

theorem rhoPerm_natCast {t : ℕ} (ht : t < m) (c : Fin 5) :
    rhoPerm ((t : ℕ) : ZMod m) c = neut c t := by
  simp only [rhoPerm, neut, val_natCast_of_lt ht]
  split_ifs <;> rfl

/-- The (component, displacement) row of colour `c` at height `t`, if any. -/
def rowOf : Fin 5 → ℕ → Option (Fin 5 × (Fin 4 → ℤ))
  | 0, 0 => some (0, e_c0p0)
  | 0, 1 => some (2, e_c0p2)
  | 0, 2 => some (4, e_c0p4)
  | 1, 0 => some (0, e_c1p0)
  | 1, 1 => some (3, e_c1p3)
  | 2, 0 => some (0, e_c2p0)
  | 2, 1 => some (3, e_c2p3)
  | 2, 2 => some (4, e_c2p4)
  | 3, 0 => some (1, e_c3p1)
  | 3, 1 => some (2, e_c3p2)
  | 4, 0 => some (1, e_c4p1)
  | 4, 1 => some (2, e_c4p2)
  | _, _ => none

/-- The preterminal layer of colour `c` at height `t`. -/
def preLayer (c : Fin 5) (t : ℕ) (x : Root m) : Root m :=
  x + uvec (neut c t) +
    (match rowOf c t with
      | some (P, e) => if maskP P x then castV e else 0
      | none => 0)

/-! ### Heights at least three: pure translations -/

theorem dir_ge3 (hm : 6 ≤ m) {t : ℕ} (ht3 : 3 ≤ t) (ht : t < m) (x : Root m) (c : Fin 5) :
    dir ((t : ℕ) : ZMod m) x c = neut c t := by
  have hv := val_natCast_of_lt (m := m) ht
  have h0 : t ≠ 0 := by omega
  have h1 : t ≠ 1 := by omega
  have h2 : t ≠ 2 := by omega
  simp [dir, rowPerm, hv, h0, h1, h2, rhoPerm_natCast ht]

theorem layer_ge3 (hm : 6 ≤ m) {t : ℕ} (ht3 : 3 ≤ t) (ht : t < m) (c : Fin 5) (x : Root m) :
    (schedule m).layerMap ((t : ℕ) : ZMod m) c x = preLayer c t x := by
  rw [layerMap_eq_uvec, dir_ge3 hm ht3 ht, preLayer]
  have hrow : rowOf c t = none := by
    fin_cases c <;> (rcases t with _ | _ | _ | t <;> simp [rowOf] <;> omega)
  rw [hrow]
  simp

/-! ### Heights `0, 1, 2` -/

theorem dir_c0_t0 (hm : 6 ≤ m) (x : Root m) :
    dir (((0 : ℕ) : ℕ) : ZMod m) x 0 = if mask0 x then (2 : Fin 5) else 0 := by
  have hv : (((0 : ℕ) : ℕ) : ZMod m).val = 0 := val_natCast_of_lt (by omega)
  simp only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero] at hv ⊢
  by_cases h : mask0 x <;> by_cases h' : mask1 x <;>
    simp [dir, rowPerm, rhoPerm, hv, h, h'] <;> first | rfl | decide

theorem uvec_e_c0p0 : uvec (2 : Fin 5) = uvec 0 + castV (m := m) e_c0p0 := by
  ext i
  fin_cases i <;> simp [uvec, castV, e_c0p0]

theorem layer_c0_t0 (hm : 6 ≤ m) (x : Root m) :
    (schedule m).layerMap (((0 : ℕ) : ℕ) : ZMod m) 0 x = preLayer 0 0 x := by
  rw [layerMap_eq_uvec, dir_c0_t0 hm, preLayer, show neut 0 0 = (0 : Fin 5) by rfl]
  simp only [rowOf, maskP]
  split_ifs with h
  · rw [uvec_e_c0p0]
    abel
  · abel

theorem dir_c1_t0 (hm : 6 ≤ m) (x : Root m) :
    dir (((0 : ℕ) : ℕ) : ZMod m) x 1 = if mask0 x then (0 : Fin 5) else 1 := by
  have hv : (((0 : ℕ) : ℕ) : ZMod m).val = 0 := val_natCast_of_lt (by omega)
  simp only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero] at hv ⊢
  by_cases h : mask0 x <;> by_cases h' : mask1 x <;>
    simp [dir, rowPerm, rhoPerm, hv, h, h'] <;> first | rfl | decide

theorem uvec_e_c1p0 : uvec (0 : Fin 5) = uvec 1 + castV (m := m) e_c1p0 := by
  ext i
  fin_cases i <;> simp [uvec, castV, e_c1p0]

theorem layer_c1_t0 (hm : 6 ≤ m) (x : Root m) :
    (schedule m).layerMap (((0 : ℕ) : ℕ) : ZMod m) 1 x = preLayer 1 0 x := by
  rw [layerMap_eq_uvec, dir_c1_t0 hm, preLayer, show neut 1 0 = (1 : Fin 5) by rfl]
  simp only [rowOf, maskP]
  split_ifs with h
  · rw [uvec_e_c1p0]
    abel
  · abel

theorem dir_c2_t0 (hm : 6 ≤ m) (x : Root m) :
    dir (((0 : ℕ) : ℕ) : ZMod m) x 2 = if mask0 x then (1 : Fin 5) else 2 := by
  have hv : (((0 : ℕ) : ℕ) : ZMod m).val = 0 := val_natCast_of_lt (by omega)
  simp only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero] at hv ⊢
  by_cases h : mask0 x <;> by_cases h' : mask1 x <;>
    simp [dir, rowPerm, rhoPerm, hv, h, h'] <;> first | rfl | decide

theorem uvec_e_c2p0 : uvec (1 : Fin 5) = uvec 2 + castV (m := m) e_c2p0 := by
  ext i
  fin_cases i <;> simp [uvec, castV, e_c2p0]

theorem layer_c2_t0 (hm : 6 ≤ m) (x : Root m) :
    (schedule m).layerMap (((0 : ℕ) : ℕ) : ZMod m) 2 x = preLayer 2 0 x := by
  rw [layerMap_eq_uvec, dir_c2_t0 hm, preLayer, show neut 2 0 = (2 : Fin 5) by rfl]
  simp only [rowOf, maskP]
  split_ifs with h
  · rw [uvec_e_c2p0]
    abel
  · abel

theorem dir_c3_t0 (hm : 6 ≤ m) (x : Root m) :
    dir (((0 : ℕ) : ℕ) : ZMod m) x 3 = if mask1 x then (4 : Fin 5) else 3 := by
  have hv : (((0 : ℕ) : ℕ) : ZMod m).val = 0 := val_natCast_of_lt (by omega)
  simp only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero] at hv ⊢
  by_cases h : mask1 x <;> by_cases h' : mask0 x <;>
    simp [dir, rowPerm, rhoPerm, hv, h, h'] <;> first | rfl | decide

theorem uvec_e_c3p1 : uvec (4 : Fin 5) = uvec 3 + castV (m := m) e_c3p1 := by
  ext i
  fin_cases i <;> simp [uvec, castV, e_c3p1]

theorem layer_c3_t0 (hm : 6 ≤ m) (x : Root m) :
    (schedule m).layerMap (((0 : ℕ) : ℕ) : ZMod m) 3 x = preLayer 3 0 x := by
  rw [layerMap_eq_uvec, dir_c3_t0 hm, preLayer, show neut 3 0 = (3 : Fin 5) by rfl]
  simp only [rowOf, maskP]
  split_ifs with h
  · rw [uvec_e_c3p1]
    abel
  · abel

theorem dir_c4_t0 (hm : 6 ≤ m) (x : Root m) :
    dir (((0 : ℕ) : ℕ) : ZMod m) x 4 = if mask1 x then (3 : Fin 5) else 4 := by
  have hv : (((0 : ℕ) : ℕ) : ZMod m).val = 0 := val_natCast_of_lt (by omega)
  simp only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero] at hv ⊢
  by_cases h : mask1 x <;> by_cases h' : mask0 x <;>
    simp [dir, rowPerm, rhoPerm, hv, h, h'] <;> first | rfl | decide

theorem uvec_e_c4p1 : uvec (3 : Fin 5) = uvec 4 + castV (m := m) e_c4p1 := by
  ext i
  fin_cases i <;> simp [uvec, castV, e_c4p1]

theorem layer_c4_t0 (hm : 6 ≤ m) (x : Root m) :
    (schedule m).layerMap (((0 : ℕ) : ℕ) : ZMod m) 4 x = preLayer 4 0 x := by
  rw [layerMap_eq_uvec, dir_c4_t0 hm, preLayer, show neut 4 0 = (4 : Fin 5) by rfl]
  simp only [rowOf, maskP]
  split_ifs with h
  · rw [uvec_e_c4p1]
    abel
  · abel

theorem dir_c0_t1 (hm : 6 ≤ m) (x : Root m) :
    dir (((1 : ℕ) : ℕ) : ZMod m) x 0 = if mask2 x then (0 : Fin 5) else 1 := by
  have hv : (((1 : ℕ) : ℕ) : ZMod m).val = 1 := val_natCast_of_lt (by omega)
  simp only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero] at hv ⊢
  by_cases h : mask2 x <;> by_cases h' : mask3 x <;>
    simp [dir, rowPerm, rhoPerm, hv, h, h'] <;> first | rfl | decide

theorem uvec_e_c0p2 : uvec (0 : Fin 5) = uvec 1 + castV (m := m) e_c0p2 := by
  ext i
  fin_cases i <;> simp [uvec, castV, e_c0p2]

theorem layer_c0_t1 (hm : 6 ≤ m) (x : Root m) :
    (schedule m).layerMap (((1 : ℕ) : ℕ) : ZMod m) 0 x = preLayer 0 1 x := by
  rw [layerMap_eq_uvec, dir_c0_t1 hm, preLayer, show neut 0 1 = (1 : Fin 5) by rfl]
  simp only [rowOf, maskP]
  split_ifs with h
  · rw [uvec_e_c0p2]
    abel
  · abel

theorem dir_c3_t1 (hm : 6 ≤ m) (x : Root m) :
    dir (((1 : ℕ) : ℕ) : ZMod m) x 3 = if mask2 x then (1 : Fin 5) else 4 := by
  have hv : (((1 : ℕ) : ℕ) : ZMod m).val = 1 := val_natCast_of_lt (by omega)
  simp only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero] at hv ⊢
  by_cases h : mask2 x <;> by_cases h' : mask3 x <;>
    simp [dir, rowPerm, rhoPerm, hv, h, h'] <;> first | rfl | decide

theorem uvec_e_c3p2 : uvec (1 : Fin 5) = uvec 4 + castV (m := m) e_c3p2 := by
  ext i
  fin_cases i <;> simp [uvec, castV, e_c3p2]

theorem layer_c3_t1 (hm : 6 ≤ m) (x : Root m) :
    (schedule m).layerMap (((1 : ℕ) : ℕ) : ZMod m) 3 x = preLayer 3 1 x := by
  rw [layerMap_eq_uvec, dir_c3_t1 hm, preLayer, show neut 3 1 = (4 : Fin 5) by rfl]
  simp only [rowOf, maskP]
  split_ifs with h
  · rw [uvec_e_c3p2]
    abel
  · abel

theorem dir_c4_t1 (hm : 6 ≤ m) (x : Root m) :
    dir (((1 : ℕ) : ℕ) : ZMod m) x 4 = if mask2 x then (4 : Fin 5) else 0 := by
  have hv : (((1 : ℕ) : ℕ) : ZMod m).val = 1 := val_natCast_of_lt (by omega)
  simp only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero] at hv ⊢
  by_cases h : mask2 x <;> by_cases h' : mask3 x <;>
    simp [dir, rowPerm, rhoPerm, hv, h, h'] <;> first | rfl | decide

theorem uvec_e_c4p2 : uvec (4 : Fin 5) = uvec 0 + castV (m := m) e_c4p2 := by
  ext i
  fin_cases i <;> simp [uvec, castV, e_c4p2]

theorem layer_c4_t1 (hm : 6 ≤ m) (x : Root m) :
    (schedule m).layerMap (((1 : ℕ) : ℕ) : ZMod m) 4 x = preLayer 4 1 x := by
  rw [layerMap_eq_uvec, dir_c4_t1 hm, preLayer, show neut 4 1 = (0 : Fin 5) by rfl]
  simp only [rowOf, maskP]
  split_ifs with h
  · rw [uvec_e_c4p2]
    abel
  · abel

theorem dir_c1_t1 (hm : 6 ≤ m) (x : Root m) :
    dir (((1 : ℕ) : ℕ) : ZMod m) x 1 = if mask3 x then (3 : Fin 5) else 2 := by
  have hv : (((1 : ℕ) : ℕ) : ZMod m).val = 1 := val_natCast_of_lt (by omega)
  simp only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero] at hv ⊢
  by_cases h : mask3 x <;> by_cases h' : mask2 x <;>
    simp [dir, rowPerm, rhoPerm, hv, h, h'] <;> first | rfl | decide

theorem uvec_e_c1p3 : uvec (3 : Fin 5) = uvec 2 + castV (m := m) e_c1p3 := by
  ext i
  fin_cases i <;> simp [uvec, castV, e_c1p3]

theorem layer_c1_t1 (hm : 6 ≤ m) (x : Root m) :
    (schedule m).layerMap (((1 : ℕ) : ℕ) : ZMod m) 1 x = preLayer 1 1 x := by
  rw [layerMap_eq_uvec, dir_c1_t1 hm, preLayer, show neut 1 1 = (2 : Fin 5) by rfl]
  simp only [rowOf, maskP]
  split_ifs with h
  · rw [uvec_e_c1p3]
    abel
  · abel

theorem dir_c2_t1 (hm : 6 ≤ m) (x : Root m) :
    dir (((1 : ℕ) : ℕ) : ZMod m) x 2 = if mask3 x then (2 : Fin 5) else 3 := by
  have hv : (((1 : ℕ) : ℕ) : ZMod m).val = 1 := val_natCast_of_lt (by omega)
  simp only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero] at hv ⊢
  by_cases h : mask3 x <;> by_cases h' : mask2 x <;>
    simp [dir, rowPerm, rhoPerm, hv, h, h'] <;> first | rfl | decide

theorem uvec_e_c2p3 : uvec (2 : Fin 5) = uvec 3 + castV (m := m) e_c2p3 := by
  ext i
  fin_cases i <;> simp [uvec, castV, e_c2p3]

theorem layer_c2_t1 (hm : 6 ≤ m) (x : Root m) :
    (schedule m).layerMap (((1 : ℕ) : ℕ) : ZMod m) 2 x = preLayer 2 1 x := by
  rw [layerMap_eq_uvec, dir_c2_t1 hm, preLayer, show neut 2 1 = (3 : Fin 5) by rfl]
  simp only [rowOf, maskP]
  split_ifs with h
  · rw [uvec_e_c2p3]
    abel
  · abel

theorem dir_c0_t2 (hm : 6 ≤ m) (x : Root m) :
    dir (((2 : ℕ) : ℕ) : ZMod m) x 0 = if mask4 x then (4 : Fin 5) else 2 := by
  have hv : (((2 : ℕ) : ℕ) : ZMod m).val = 2 := val_natCast_of_lt (by omega)
  simp only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero] at hv ⊢
  by_cases h : mask4 x <;> by_cases h' : plane x <;>
    simp [dir, rowPerm, rhoPerm, hv, h, h'] <;> first | rfl | decide

theorem uvec_e_c0p4 : uvec (4 : Fin 5) = uvec 2 + castV (m := m) e_c0p4 := by
  ext i
  fin_cases i <;> simp [uvec, castV, e_c0p4]

theorem layer_c0_t2 (hm : 6 ≤ m) (x : Root m) :
    (schedule m).layerMap (((2 : ℕ) : ℕ) : ZMod m) 0 x = preLayer 0 2 x := by
  rw [layerMap_eq_uvec, dir_c0_t2 hm, preLayer, show neut 0 2 = (2 : Fin 5) by rfl]
  simp only [rowOf, maskP]
  split_ifs with h
  · rw [uvec_e_c0p4]
    abel
  · abel

theorem dir_c2_t2 (hm : 6 ≤ m) (x : Root m) :
    dir (((2 : ℕ) : ℕ) : ZMod m) x 2 = if mask4 x then (2 : Fin 5) else 4 := by
  have hv : (((2 : ℕ) : ℕ) : ZMod m).val = 2 := val_natCast_of_lt (by omega)
  simp only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero] at hv ⊢
  by_cases h : mask4 x <;> by_cases h' : plane x <;>
    simp [dir, rowPerm, rhoPerm, hv, h, h'] <;> first | rfl | decide

theorem uvec_e_c2p4 : uvec (2 : Fin 5) = uvec 4 + castV (m := m) e_c2p4 := by
  ext i
  fin_cases i <;> simp [uvec, castV, e_c2p4]

theorem layer_c2_t2 (hm : 6 ≤ m) (x : Root m) :
    (schedule m).layerMap (((2 : ℕ) : ℕ) : ZMod m) 2 x = preLayer 2 2 x := by
  rw [layerMap_eq_uvec, dir_c2_t2 hm, preLayer, show neut 2 2 = (4 : Fin 5) by rfl]
  simp only [rowOf, maskP]
  split_ifs with h
  · rw [uvec_e_c2p4]
    abel
  · abel

/-! ### The terminal plane at height `2` for colours `1, 3, 4` -/

/-- The plane permutation for terminal direction `d`: on `Θ` replace the step `u_d` by
`u_{τ_ω(d)}`, i.e. `x ↦ x + u_{τ d} - u_d`; identity off `Θ`. -/
def Jplane (d : Fin 5) (x : Root m) : Root m :=
  if plane x then x + uvec (tau (omega (planePoint x)) d) - uvec d else x

theorem dir_terminal (hm : 6 ≤ m) (x : Root m) (c : Fin 5) (hc : c = 1 ∨ c = 3 ∨ c = 4) :
    dir (((2 : ℕ) : ℕ) : ZMod m) x c =
      if plane x then tau (omega (planePoint x)) (neut c 2) else neut c 2 := by
  have hv : (((2 : ℕ) : ℕ) : ZMod m).val = 2 := val_natCast_of_lt (by omega)
  simp only [Nat.cast_ofNat] at hv ⊢
  have hn1 : neut 1 2 = 3 := by decide
  have hn3 : neut 3 2 = 0 := by decide
  have hn4 : neut 4 2 = 1 := by decide
  have hs3 : swap24 3 = 3 := by decide
  have hs0 : swap24 0 = 0 := by decide
  have hs1 : swap24 1 = 1 := by decide
  have hr : ∀ c : Fin 5, rhoPerm (2 : ZMod m) c = neut c 2 := by
    intro c
    have := rhoPerm_natCast (m := m) (t := 2) (by omega) c
    simpa using this
  rcases hc with rfl | rfl | rfl <;> by_cases h : plane x <;> by_cases h4 : mask4 x <;>
    simp [dir, rowPerm, hv, h, h4, hr, hn1, hn3, hn4, Equiv.Perm.mul_apply, hs3, hs0, hs1]

theorem layer_terminal (hm : 6 ≤ m) (c : Fin 5) (hc : c = 1 ∨ c = 3 ∨ c = 4) (x : Root m) :
    (schedule m).layerMap (((2 : ℕ) : ℕ) : ZMod m) c x = preLayer c 2 (Jplane (neut c 2) x) := by
  rw [layerMap_eq_uvec, dir_terminal hm x c hc]
  have hrow : rowOf c 2 = none := by rcases hc with rfl | rfl | rfl <;> rfl
  simp only [preLayer, hrow, Jplane]
  split_ifs <;> abel

end D5
end TorusEven
