-- STATUS: main-path
import TorusEven.Entry.Star.Geometry

namespace TorusEven.Entry.Star

variable {m : ℕ} [NeZero m] (hm : 4 ≤ m)

def carry (c : Fin 3) (h : ZMod m) : Plane m :=
  if h = 1 then generator c else generator (constantRow h c)

def voltage (c : Fin 3) : Plane m :=
  if 3 ∣ m then ![(1, 3), (-4, 1), (3, -4)] c else ![(1, -2), (1, 1), (-2, 1)] c

theorem sum_constant_plane (v : Plane m) : (∑ _h : ZMod m, v) = 0 := by
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card]
  apply Prod.ext <;> simp [nsmul_eq_mul]

include hm

theorem carry_sum_nondiv (hd : ¬ 3 ∣ m) (c : Fin 3) : (∑ h, carry c h) = voltage (m := m) c := by
  classical
  have h1 := one_ne_zero_of_four_le hm
  have h12 : (1 : ZMod m) ≠ 2 := by intro h; apply h1; linear_combination -h
  have he (h : ZMod m) : carry c h = generator (rotate.symm c) +
      (if h = 1 then generator c - generator (rotate.symm c) else 0) +
      (if h = 2 then generator (rotate c) - generator (rotate.symm c) else 0) := by
    by_cases hh1 : h = 1
    · subst h
      simp [carry, h12]
    · by_cases hh2 : h = 2
      · simp [carry, constantRow, hh2, Ne.symm h12]
      · simp [carry, constantRow, hh1, hh2, hd]
  calc
    (∑ h, carry c h) = (generator c - generator (rotate.symm c)) +
        (generator (rotate c) - generator (rotate.symm c)) := by
      simp only [he, Finset.sum_add_distrib, sum_constant_plane, zero_add]
      simp
    _ = voltage c := by
      fin_cases c <;> apply Prod.ext <;> simp [voltage, hd, generator, rotate] <;> ring

theorem carry_sum_div (hd : 3 ∣ m) (c : Fin 3) : (∑ h, carry c h) = voltage (m := m) c := by
  classical
  have hm5 : 5 ≤ m := by obtain ⟨k, hk⟩ := hd; omega
  have h1 := one_ne_zero_of_four_le hm
  have h2 : (2 : ZMod m) ≠ 0 := by simpa using cast_ne_zero (m := m) (n := 2) (by omega) (by omega)
  have h3 : (3 : ZMod m) ≠ 0 := by simpa using cast_ne_zero (m := m) (n := 3) (by omega) (by omega)
  have h4 : (4 : ZMod m) ≠ 0 := by simpa using cast_ne_zero (m := m) (n := 4) (by omega) (by omega)
  have h21 : (2 : ZMod m) ≠ 1 := by intro h; apply h1; linear_combination h
  have h31 : (3 : ZMod m) ≠ 1 := by intro h; apply h2; linear_combination h
  have h41 : (4 : ZMod m) ≠ 1 := by intro h; apply h3; linear_combination h
  have h32 : (3 : ZMod m) ≠ 2 := by intro h; apply h1; linear_combination h
  have h42 : (4 : ZMod m) ≠ 2 := by intro h; apply h2; linear_combination h
  have h43 : (4 : ZMod m) ≠ 3 := by intro h; apply h1; linear_combination h
  let v := generator (m := m) c
  let d := generator (m := m) (rotate.symm c) - v
  let e := generator (m := m) (rotate c) - v
  have he (h : ZMod m) : carry c h = v + (if h = 2 then e else 0) +
      (if h = 0 then d else 0) + (if h = 3 then d else 0) + (if h = 4 then d else 0) := by
    by_cases hh2 : h = 2
    · subst h
      simp [carry, constantRow, v, e, h21, h2, Ne.symm h32, Ne.symm h42]
    · by_cases hh0 : h = 0
      · subst h
        simp [carry, constantRow, v, d, hd, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4]
      · by_cases hh3 : h = 3
        · subst h
          simp [carry, constantRow, v, d, hd, h31, h32, h3, Ne.symm h43]
        · by_cases hh4 : h = 4
          · subst h
            simp [carry, constantRow, v, d, hd, h41, h42, h4, h43]
          · simp [carry, constantRow, v, hd, hh2, hh0, hh3, hh4]
  calc
    (∑ h, carry c h) = e + d + d + d := by
      simp only [he, Finset.sum_add_distrib, sum_constant_plane, zero_add]
      simp
    _ = voltage c := by
      fin_cases c <;> apply Prod.ext <;> simp [voltage, hd, v, e, d, generator, rotate] <;> ring

theorem carry_sum (c : Fin 3) : (∑ h, carry c h) = voltage (m := m) c := by
  by_cases hd : 3 ∣ m
  · exact carry_sum_div hm hd c
  · exact carry_sum_nondiv hm hd c

omit hm [NeZero m] in
theorem voltage_rotate (c : Fin 3) : voltage (m := m) (rotate c) = turn (voltage c) := by
  by_cases hd : 3 ∣ m <;> fin_cases c <;> apply Prod.ext <;>
    simp [voltage, hd, turn, rotate] <;> ring

end TorusEven.Entry.Star
