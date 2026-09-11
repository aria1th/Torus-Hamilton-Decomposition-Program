-- STATUS: main-path
import TorusEven.Entry.Rows

namespace TorusEven.Entry.Star

abbrev Plane (m : ℕ) := ZMod m × ZMod m

variable {m : ℕ}

def generator : Fin 3 → Plane m := ![(0, 0), (1, 0), (0, 1)]

def turn : Plane m ≃+ Plane m where
  toFun p := (-p.1 - p.2, p.1)
  invFun p := (p.2, -p.1 - p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp; ring
  map_add' p q := by ext <;> simp; ring

def ray (z : Fin 3) (t : ZMod m) : Plane m := ![(t, -t), (0, t), (-t, 0)] z

@[simp] theorem turn_three (p : Plane m) : turn (turn (turn p)) = p := by
  ext <;> simp [turn]; ring

theorem turn_ray (z : Fin 3) (t : ZMod m) : turn (ray z t) = ray (rotate z) t := by
  fin_cases z <;> simp [turn, ray, rotate]

theorem turn_generator (c : Fin 3) :
    turn (generator (m := m) c) = generator (rotate c) - generator 1 := by
  fin_cases c <;> simp [turn, generator, rotate]

theorem row_ray (z : Fin 3) {t : ZMod m} (ht : t ≠ 0) :
    starRow (ray z t).1 (ray z t).2 = starRayRow z t := by
  fin_cases z <;> simp [ray, starRow, ht]

theorem ray_row_rotate (z c : Fin 3) (t : ZMod m) :
    starRayRow (rotate z) t (rotate c) = rotate (starRayRow z t c) := by
  by_cases h1 : t = 1
  · fin_cases z <;> fin_cases c <;> simp [starRayRow, h1, rotate]
  · by_cases hn : t = -1
    · simp only [starRayRow, if_neg h1, if_pos hn]
    · fin_cases z <;> fin_cases c <;>
        simp [starRayRow, h1, hn, rotate, reflection, Equiv.swap_apply_def]

theorem plane_cases (p : Plane m) : p = 0 ∨
    (∃ z t, t ≠ 0 ∧ p = ray z t) ∨ (p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 + p.2 ≠ 0) := by
  rcases p with ⟨a, b⟩
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · exact Or.inl (Prod.ext rfl hb)
    · exact Or.inr (Or.inl ⟨1, b, hb, rfl⟩)
  · by_cases hb : b = 0
    · subst b
      exact Or.inr (Or.inl ⟨2, -a, neg_ne_zero.mpr ha, by simp [ray]⟩)
    · by_cases hab : a + b = 0
      · exact Or.inr (Or.inl ⟨0, a, ha, Prod.ext rfl (eq_neg_of_add_eq_zero_right hab)⟩)
      · exact Or.inr (Or.inr ⟨ha, hb, hab⟩)

theorem row_rotate (p : Plane m) (c : Fin 3) :
    starRow (turn p).1 (turn p).2 (rotate c) = rotate (starRow p.1 p.2 c) := by
  rcases plane_cases p with rfl | ⟨z, t, ht, rfl⟩ | ⟨ha, hb, hab⟩
  · simp [turn, starRow]
  · rw [turn_ray, row_ray _ ht, row_ray _ ht]
    exact ray_row_rotate z c t
  · have hsum : (turn p).1 + (turn p).2 = -p.2 := by simp [turn]; ring
    have hfirst : (turn p).1 ≠ 0 := by
      change -p.1 - p.2 ≠ 0
      intro h
      apply hab
      linear_combination -h
    simp [starRow, ha, hab, hb, hfirst, hsum, show (turn p).2 ≠ 0 from ha]

def surgeryMap (c : Fin 3) (p : Plane m) : Plane m :=
  p + generator (starRow p.1 p.2 c) - generator c

theorem surgeryMap_rotate (c : Fin 3) (p : Plane m) :
    surgeryMap (rotate c) (turn p) = turn (surgeryMap c p) := by
  simp only [surgeryMap, row_rotate, map_sub, map_add, turn_generator]
  abel

theorem one_ne_zero_of_four_le (hm : 4 ≤ m) : (1 : ZMod m) ≠ 0 := by
  simpa using cast_ne_zero (m := m) (n := 1) (by omega) (by omega)

theorem one_ne_neg_one (hm : 4 ≤ m) : (1 : ZMod m) ≠ -1 := by
  have h2 : (2 : ZMod m) ≠ 0 := by
    simpa using cast_ne_zero (m := m) (n := 2) (by omega) (by omega)
  intro h
  apply h2
  linear_combination h

end TorusEven.Entry.Star
