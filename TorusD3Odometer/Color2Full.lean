import TorusD3Odometer.Color2
import Mathlib.Tactic

namespace TorusD3Odometer

open TorusD4
open TorusD3Even

def KMapXY : Color → FullCoord m → FullCoord m
  | 0, ((x, y), s) => ((x + 1, y + 1), s + 1)
  | 1, ((x, y), s) => ((x, y), s + 1)
  | 2, ((x, y), s) => ((x, y + 1), s + 1)

@[simp] theorem KMapXY_snd (c : Color) (z : FullCoord m) :
    (KMapXY (m := m) c z).2 = z.2 + 1 := by
  rcases z with ⟨u, s⟩
  rcases u with ⟨x, y⟩
  fin_cases c <;> rfl

instance factZeroOfFactFive [Fact (5 < m)] : Fact (0 < m) :=
  ⟨lt_trans (by decide : 0 < 5) Fact.out⟩

instance factOneOfFactFive [Fact (5 < m)] : Fact (1 < m) :=
  ⟨lt_trans (by decide : 1 < 5) Fact.out⟩

instance factTwoOfFactFive [Fact (5 < m)] : Fact (2 < m) :=
  ⟨lt_trans (by decide : 2 < 5) Fact.out⟩

@[simp] theorem one_add_one_zmod : ((1 : ZMod m) + 1) = (2 : ZMod m) := by ring

@[simp] theorem two_add_one_zmod : ((2 : ZMod m) + 1) = (3 : ZMod m) := by ring

@[simp] theorem neg_two_add_one_zmod : ((-2 : ZMod m) + 1) = (-1 : ZMod m) := by ring

@[simp] theorem add_one_add_one_zmod (z : ZMod m) : z + 1 + 1 = z + 2 := by ring

@[simp] theorem add_two_add_one_zmod (z : ZMod m) : z + 2 + 1 = z + 3 := by ring

theorem iterate_KMapXY_two (n : ℕ) (x y s : ZMod m) :
    ((KMapXY (m := m) 2)^[n]) ((x, y), s) = ((x, y + n), s + n) := by
  induction n generalizing x y s with
  | zero =>
      simp [KMapXY]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      ext <;> simp [KMapXY, Nat.cast_add]
      all_goals ring

def dir2LayerZeroXY (u : P0Coord m) : Color :=
  let (x, y) := u
  if x = 0 ∧ y = 0 then
    2
  else if y = (-1 : ZMod m) ∧ x ≠ 0 ∧ x ≠ (-1 : ZMod m) then
    2
  else if x = (-1 : ZMod m) ∧ y = (-2 : ZMod m) then
    2
  else if x = 0 ∧ y = (-1 : ZMod m) then
    1
  else if y = x ∧ x ≠ 0 ∧ x ≠ (-1 : ZMod m) then
    1
  else if x = (-1 : ZMod m) ∧ y = 0 then
    1
  else
    0

def dir2XY (z : FullCoord m) : Color :=
  let (u, s) := z
  let (x, y) := u
  if s = 0 then
    dir2LayerZeroXY (m := m) (x, y)
  else if s = 1 then
    if x = 0 then 2 else 1
  else if s = 2 then
    if y = 2 then 0 else 2
  else
    2

def fullMap2XY (z : FullCoord m) : FullCoord m :=
  KMapXY (m := m) (dir2XY (m := m) z) z

@[simp] theorem fullMap2XY_snd (z : FullCoord m) :
    (fullMap2XY (m := m) z).2 = z.2 + 1 := by
  simp [fullMap2XY, KMapXY_snd]

theorem iterate_fullMap2XY_from_three [Fact (5 < m)] (x y : ZMod m) :
    ∀ n, n ≤ m - 3 → ((fullMap2XY (m := m)^[n]) ((x, y), (3 : ZMod m))) =
      ((x, y + n), (3 : ZMod m) + n)
  | 0, _ => by simp
  | n + 1, hn => by
      have hm5 : 5 < m := Fact.out
      letI : Fact (0 < m) := inferInstance
      letI : Fact (1 < m) := inferInstance
      letI : Fact (2 < m) := inferInstance
      have hn' : n ≤ m - 3 := Nat.le_of_succ_le hn
      have hcur_lt : n + 3 < m := by omega
      have hs0 : (3 : ZMod m) + n ≠ 0 := by
        simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
          natCast_ne_zero_of_pos_lt (m := m) (n := n + 3) (by omega) hcur_lt
      have hs1 : (3 : ZMod m) + n ≠ 1 := by
        simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
          natCast_ne_one_of_two_le_lt (m := m) (n := n + 3) (by omega) hcur_lt
      have hs2 : (3 : ZMod m) + n ≠ 2 := by
        simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
          natCast_ne_two_of_three_le_lt (m := m) (n := n + 3) (by omega) hcur_lt
      have hstep :
          ((fullMap2XY (m := m)^[n + 1]) ((x, y), (3 : ZMod m))) =
            ((x, y + ((n : ZMod m) + 1)), (3 : ZMod m) + ((n : ZMod m) + 1)) := by
        calc
          ((fullMap2XY (m := m)^[n + 1]) ((x, y), (3 : ZMod m)))
              = fullMap2XY (m := m) (((fullMap2XY (m := m)^[n]) ((x, y), (3 : ZMod m)))) := by
                  rw [Function.iterate_succ_apply']
          _ = fullMap2XY (m := m) ((x, y + n), (3 : ZMod m) + n) := by
                exact congrArg (fullMap2XY (m := m))
                  (iterate_fullMap2XY_from_three (m := m) x y n hn')
          _ = KMapXY (m := m) 2 ((x, y + n), (3 : ZMod m) + n) := by
                simp [fullMap2XY, dir2XY, hs0, hs1, hs2]
          _ = ((x, y + ((n : ZMod m) + 1)), (3 : ZMod m) + ((n : ZMod m) + 1)) := by
                simp [KMapXY, add_assoc]
      simpa [Nat.cast_add, add_assoc] using hstep

theorem iterate_m_sub_three_fullMap2XY [Fact (5 < m)] (x y : ZMod m) :
    ((fullMap2XY (m := m)^[m - 3]) ((x, y), (3 : ZMod m))) = ((x, y - 3), (0 : ZMod m)) := by
  have hmain := iterate_fullMap2XY_from_three (m := m) x y (m - 3) le_rfl
  have hm3 : 3 ≤ m := by
    have hm5 : 5 < m := Fact.out
    omega
  calc
    ((fullMap2XY (m := m)^[m - 3]) ((x, y), (3 : ZMod m)))
        = ((x, y + ((m - 3 : ℕ) : ZMod m)), (3 : ZMod m) + ((m - 3 : ℕ) : ZMod m)) := hmain
    _ = ((x, y - 3), (0 : ZMod m)) := by
          ext <;> simp [Nat.cast_sub hm3]
          all_goals ring

theorem iterate_fullMap2XY_split_three [Fact (5 < m)] (z : FullCoord m) :
    ((fullMap2XY (m := m)^[m]) z) =
      ((fullMap2XY (m := m)^[m - 3]) (((fullMap2XY (m := m)^[3]) z))) := by
  have hm3 : 3 ≤ m := by
    have hm5 : 5 < m := Fact.out
    omega
  simpa [Nat.sub_add_cancel hm3] using
    (Function.iterate_add_apply (f := fullMap2XY (m := m)) (m := m - 3) (n := 3) z)

theorem add_one_ne_zero_of_ne_neg_one {x : ZMod m} (hxneg1 : x ≠ (-1 : ZMod m)) :
    x + 1 ≠ 0 := by
  intro h
  apply hxneg1
  calc
    x = (x + 1) - 1 := by ring
    _ = (-1 : ZMod m) := by rw [h]; ring

theorem add_one_ne_two_of_ne_one {y : ZMod m} (hy1 : y ≠ (1 : ZMod m)) :
    y + 1 ≠ (2 : ZMod m) := by
  intro h
  apply hy1
  calc
    y = (y + 1) - 1 := by ring
    _ = (1 : ZMod m) := by rw [h]; ring

theorem add_two_ne_two_of_ne_zero {y : ZMod m} (hy0 : y ≠ (0 : ZMod m)) :
    y + 2 ≠ (2 : ZMod m) := by
  intro h
  apply hy0
  calc
    y = (y + 2) - 2 := by ring
    _ = (0 : ZMod m) := by rw [h]; ring

theorem zero_ne_two [Fact (2 < m)] : (0 : ZMod m) ≠ (2 : ZMod m) := by
  intro h
  exact TorusD3Even.two_ne_zero (m := m) h.symm

theorem neg_one_ne_zero [Fact (1 < m)] : (-1 : ZMod m) ≠ (0 : ZMod m) := by
  exact neg_ne_zero.mpr (TorusD3Even.one_ne_zero (m := m))

theorem two_ne_neg_one [Fact (5 < m)] : (2 : ZMod m) ≠ (-1 : ZMod m) := by
  have hm5 : 5 < m := Fact.out
  letI : Fact (0 < m) := inferInstance
  exact natCast_ne_neg_one_of_lt (m := m) (n := 2) (by omega)

theorem neg_one_ne_two [Fact (5 < m)] : (-1 : ZMod m) ≠ (2 : ZMod m) := by
  intro h
  exact two_ne_neg_one (m := m) h.symm

theorem neg_one_ne_neg_two [Fact (1 < m)] : (-1 : ZMod m) ≠ (-2 : ZMod m) := by
  intro h
  have hzero : (1 : ZMod m) = 0 := by
    calc
      (1 : ZMod m) = (-1 : ZMod m) + 2 := by ring
      _ = (-2 : ZMod m) + 2 := by rw [h]
      _ = 0 := by ring
  exact one_ne_zero (m := m) hzero

theorem one_ne_neg_two [Fact (5 < m)] : (1 : ZMod m) ≠ (-2 : ZMod m) := by
  intro h
  have hzero : (3 : ZMod m) = 0 := by
    calc
      (3 : ZMod m) = (1 : ZMod m) + 2 := by norm_num
      _ = (-2 : ZMod m) + 2 := by rw [h]
      _ = 0 := by ring
  exact TorusD3Even.three_ne_zero (m := m) hzero

theorem fullMap2XY_layer1_of_x_zero [Fact (1 < m)] (y : ZMod m) :
    fullMap2XY (m := m) (((0 : ZMod m), y), (1 : ZMod m)) =
      (((0 : ZMod m), y + 1), (2 : ZMod m)) := by
  ext <;> simp [fullMap2XY, dir2XY, KMapXY, TorusD3Even.one_ne_zero (m := m)] <;> ring

theorem fullMap2XY_layer1_of_x_ne_zero [Fact (1 < m)] {x y : ZMod m} (hx0 : x ≠ 0) :
    fullMap2XY (m := m) ((x, y), (1 : ZMod m)) = ((x, y), (2 : ZMod m)) := by
  ext <;> simp [fullMap2XY, dir2XY, KMapXY, TorusD3Even.one_ne_zero (m := m), hx0] <;> ring

theorem fullMap2XY_layer2_of_y_two [Fact (2 < m)] (x : ZMod m) :
    fullMap2XY (m := m) ((x, (2 : ZMod m)), (2 : ZMod m)) =
      ((x + 1, (3 : ZMod m)), (3 : ZMod m)) := by
  ext <;> simp [fullMap2XY, dir2XY, KMapXY, TorusD3Even.two_ne_zero (m := m),
    TorusD3Even.two_ne_one (m := m)] <;> ring

theorem fullMap2XY_layer2_of_y_ne_two [Fact (2 < m)] {x y : ZMod m} (hy2 : y ≠ (2 : ZMod m)) :
    fullMap2XY (m := m) ((x, y), (2 : ZMod m)) = ((x, y + 1), (3 : ZMod m)) := by
  ext <;> simp [fullMap2XY, dir2XY, KMapXY, TorusD3Even.two_ne_zero (m := m),
    TorusD3Even.two_ne_one (m := m), hy2] <;> ring

theorem iterate_three_fullMap2XY_A [Fact (5 < m)] :
    ((fullMap2XY (m := m)^[3]) (slicePoint (0 : ZMod m) ((2 : ZMod m), (2 : ZMod m)))) =
      (((3 : ZMod m), (3 : ZMod m)), (3 : ZMod m)) := by
  letI : Fact (0 < m) := inferInstance
  calc
    ((fullMap2XY (m := m)^[3]) (slicePoint (0 : ZMod m) ((2 : ZMod m), (2 : ZMod m))))
        = ((fullMap2XY (m := m)^[2]) (((2 : ZMod m), (2 : ZMod m)), (1 : ZMod m))) := by
            simp [slicePoint, fullMap2XY, dir2XY, dir2LayerZeroXY, KMapXY,
              Function.iterate_succ_apply', TorusD3Even.two_ne_zero (m := m), two_ne_neg_one (m := m)]
    _ = fullMap2XY (m := m) (((2 : ZMod m), (2 : ZMod m)), (2 : ZMod m)) := by
          rw [Function.iterate_succ_apply']
          simpa using congrArg (fullMap2XY (m := m))
            (fullMap2XY_layer1_of_x_ne_zero (m := m) (x := (2 : ZMod m)) (y := (2 : ZMod m))
              (TorusD3Even.two_ne_zero (m := m)))
    _ = (((3 : ZMod m), (3 : ZMod m)), (3 : ZMod m)) := by
          simpa using fullMap2XY_layer2_of_y_two (m := m) (x := (2 : ZMod m))

theorem fullMap2XY_B_start [Fact (5 < m)] {x : ZMod m}
    (hx1 : x ≠ (1 : ZMod m)) (hxneg1 : x ≠ (-1 : ZMod m)) :
    fullMap2XY (m := m) (slicePoint (0 : ZMod m) (x, (1 : ZMod m))) =
      ((x + 1, (2 : ZMod m)), (1 : ZMod m)) := by
  letI : Fact (0 < m) := inferInstance
  have h1x : (1 : ZMod m) ≠ x := by
    intro h
    exact hx1 h.symm
  have hdir : dir2XY (m := m) ((x, (1 : ZMod m)), (0 : ZMod m)) = 0 := by
    simp [slicePoint, dir2XY, dir2LayerZeroXY, TorusD3Even.one_ne_zero (m := m),
      TorusD3Even.one_ne_neg_one (m := m), h1x, hx1, hxneg1]
  have hdir' : dir2XY (m := m) (slicePoint (0 : ZMod m) (x, (1 : ZMod m))) = 0 := by
    simpa [slicePoint] using hdir
  rw [fullMap2XY, hdir']
  simp [KMapXY, slicePoint]

theorem iterate_three_fullMap2XY_B_of [Fact (5 < m)] {x : ZMod m}
    (hx1 : x ≠ (1 : ZMod m)) (hxneg1 : x ≠ (-1 : ZMod m)) :
    ((fullMap2XY (m := m)^[3]) (slicePoint (0 : ZMod m) (x, (1 : ZMod m)))) =
      ((x + 2, (3 : ZMod m)), (3 : ZMod m)) := by
  letI : Fact (0 < m) := inferInstance
  letI : Fact (1 < m) := inferInstance
  letI : Fact (2 < m) := inferInstance
  have h1x : (1 : ZMod m) ≠ x := by
    intro h
    exact hx1 h.symm
  have hx10 : x + 1 ≠ 0 := add_one_ne_zero_of_ne_neg_one (m := m) hxneg1
  calc
    ((fullMap2XY (m := m)^[3]) (slicePoint (0 : ZMod m) (x, (1 : ZMod m))))
        = ((fullMap2XY (m := m)^[2]) ((x + 1, (2 : ZMod m)), (1 : ZMod m))) := by
            rw [Function.iterate_succ_apply']
            simpa [h1x] using congrArg (fun z => (fullMap2XY (m := m)^[2]) z)
              (fullMap2XY_B_start (m := m) hx1 hxneg1)
    _ = fullMap2XY (m := m) ((x + 1, (2 : ZMod m)), (2 : ZMod m)) := by
          rw [Function.iterate_succ_apply']
          simpa using congrArg (fullMap2XY (m := m))
            (fullMap2XY_layer1_of_x_ne_zero (m := m) (x := x + 1) (y := (2 : ZMod m)) hx10)
    _ = ((x + 2, (3 : ZMod m)), (3 : ZMod m)) := by
          simpa [add_assoc] using fullMap2XY_layer2_of_y_two (m := m) (x := x + 1)

theorem iterate_three_fullMap2XY_C_of [Fact (5 < m)] {x : ZMod m}
    (hxneg1 : x ≠ (-1 : ZMod m)) :
    ((fullMap2XY (m := m)^[3]) (slicePoint (0 : ZMod m) (x, (-1 : ZMod m)))) =
      ((x, (1 : ZMod m)), (3 : ZMod m)) := by
  letI : Fact (0 < m) := inferInstance
  letI : Fact (1 < m) := inferInstance
  letI : Fact (2 < m) := inferInstance
  by_cases hx0 : x = 0
  · subst hx0
    calc
      ((fullMap2XY (m := m)^[3]) (slicePoint (0 : ZMod m) ((0 : ZMod m), (-1 : ZMod m))))
          = ((fullMap2XY (m := m)^[2]) (((0 : ZMod m), (-1 : ZMod m)), (1 : ZMod m))) := by
              simp [slicePoint, fullMap2XY, dir2XY, dir2LayerZeroXY, KMapXY,
                Function.iterate_succ_apply', neg_one_ne_zero (m := m)]
      _ = fullMap2XY (m := m) (((0 : ZMod m), (0 : ZMod m)), (2 : ZMod m)) := by
            rw [Function.iterate_succ_apply']
            simpa using congrArg (fullMap2XY (m := m))
              (fullMap2XY_layer1_of_x_zero (m := m) (-1 : ZMod m))
      _ = (((0 : ZMod m), (1 : ZMod m)), (3 : ZMod m)) := by
            simpa using fullMap2XY_layer2_of_y_ne_two (m := m) (x := (0 : ZMod m))
              (y := (0 : ZMod m)) (zero_ne_two (m := m))
  · calc
      ((fullMap2XY (m := m)^[3]) (slicePoint (0 : ZMod m) (x, (-1 : ZMod m))))
          = ((fullMap2XY (m := m)^[2]) ((x, (0 : ZMod m)), (1 : ZMod m))) := by
              simp [slicePoint, fullMap2XY, dir2XY, dir2LayerZeroXY, KMapXY,
                Function.iterate_succ_apply', hx0, hxneg1, neg_one_ne_two (m := m)]
      _ = fullMap2XY (m := m) ((x, (0 : ZMod m)), (2 : ZMod m)) := by
            rw [Function.iterate_succ_apply']
            simpa using congrArg (fullMap2XY (m := m))
              (fullMap2XY_layer1_of_x_ne_zero (m := m) (x := x) (y := (0 : ZMod m)) hx0)
      _ = ((x, (1 : ZMod m)), (3 : ZMod m)) := by
            simpa using fullMap2XY_layer2_of_y_ne_two (m := m) (x := x) (y := (0 : ZMod m))
              (zero_ne_two (m := m))

theorem iterate_three_fullMap2XY_C_neg_one_neg_two [Fact (5 < m)] :
    ((fullMap2XY (m := m)^[3]) (slicePoint (0 : ZMod m) ((-1 : ZMod m), (-2 : ZMod m)))) =
      (((-1 : ZMod m), (0 : ZMod m)), (3 : ZMod m)) := by
  letI : Fact (1 < m) := inferInstance
  letI : Fact (2 < m) := inferInstance
  calc
    ((fullMap2XY (m := m)^[3]) (slicePoint (0 : ZMod m) ((-1 : ZMod m), (-2 : ZMod m))))
        = ((fullMap2XY (m := m)^[2]) (((-1 : ZMod m), (-1 : ZMod m)), (1 : ZMod m))) := by
            simp [slicePoint, fullMap2XY, dir2XY, dir2LayerZeroXY, KMapXY,
              Function.iterate_succ_apply', neg_one_ne_zero (m := m), neg_one_ne_two (m := m)]
    _ = fullMap2XY (m := m) (((-1 : ZMod m), (-1 : ZMod m)), (2 : ZMod m)) := by
          rw [Function.iterate_succ_apply']
          simpa using congrArg (fullMap2XY (m := m))
            (fullMap2XY_layer1_of_x_ne_zero (m := m) (x := (-1 : ZMod m)) (y := (-1 : ZMod m))
              (neg_one_ne_zero (m := m)))
    _ = (((-1 : ZMod m), (0 : ZMod m)), (3 : ZMod m)) := by
          simpa using fullMap2XY_layer2_of_y_ne_two (m := m) (x := (-1 : ZMod m))
            (y := (-1 : ZMod m)) (neg_one_ne_two (m := m))

theorem iterate_three_fullMap2XY_D_of [Fact (5 < m)] {x : ZMod m}
    (hx0 : x ≠ (0 : ZMod m)) (hx2 : x ≠ (2 : ZMod m)) (hxneg1 : x ≠ (-1 : ZMod m)) :
    ((fullMap2XY (m := m)^[3]) (slicePoint (0 : ZMod m) (x, x))) =
      ((x, x + 1), (3 : ZMod m)) := by
  calc
    ((fullMap2XY (m := m)^[3]) (slicePoint (0 : ZMod m) (x, x)))
        = ((fullMap2XY (m := m)^[2]) ((x, x), (1 : ZMod m))) := by
            simp [slicePoint, fullMap2XY, dir2XY, dir2LayerZeroXY, KMapXY,
              Function.iterate_succ_apply', hx0, hx2, hxneg1]
    _ = fullMap2XY (m := m) ((x, x), (2 : ZMod m)) := by
          rw [Function.iterate_succ_apply']
          simpa using congrArg (fullMap2XY (m := m))
            (fullMap2XY_layer1_of_x_ne_zero (m := m) (x := x) (y := x) hx0)
    _ = ((x, x + 1), (3 : ZMod m)) := by
          simpa using fullMap2XY_layer2_of_y_ne_two (m := m) (x := x) (y := x) hx2

theorem iterate_three_fullMap2XY_D_neg_one_zero [Fact (5 < m)] :
    ((fullMap2XY (m := m)^[3]) (slicePoint (0 : ZMod m) ((-1 : ZMod m), (0 : ZMod m)))) =
      (((-1 : ZMod m), (1 : ZMod m)), (3 : ZMod m)) := by
  letI : Fact (1 < m) := inferInstance
  letI : Fact (2 < m) := inferInstance
  calc
    ((fullMap2XY (m := m)^[3]) (slicePoint (0 : ZMod m) ((-1 : ZMod m), (0 : ZMod m))))
        = ((fullMap2XY (m := m)^[2]) (((-1 : ZMod m), (0 : ZMod m)), (1 : ZMod m))) := by
            rw [Function.iterate_succ_apply']
            have hstart :
                fullMap2XY (m := m) (slicePoint (0 : ZMod m) ((-1 : ZMod m), (0 : ZMod m))) =
                  (((-1 : ZMod m), (0 : ZMod m)), (1 : ZMod m)) := by
              have hdir :
                  dir2XY (m := m) (((-1 : ZMod m), (0 : ZMod m)), (0 : ZMod m)) = 1 := by
                simp [slicePoint, dir2XY, dir2LayerZeroXY, neg_one_ne_zero (m := m),
                  TorusD3Even.two_ne_zero (m := m)]
              have hdir' :
                  dir2XY (m := m)
                    (slicePoint (0 : ZMod m) ((-1 : ZMod m), (0 : ZMod m))) = 1 := by
                simpa [slicePoint] using hdir
              rw [fullMap2XY, hdir']
              simp [KMapXY, slicePoint]
            simpa using congrArg (fun z => (fullMap2XY (m := m)^[2]) z) hstart
    _ = fullMap2XY (m := m) (((-1 : ZMod m), (0 : ZMod m)), (2 : ZMod m)) := by
          rw [Function.iterate_succ_apply']
          simpa using congrArg (fullMap2XY (m := m))
            (fullMap2XY_layer1_of_x_ne_zero (m := m) (x := (-1 : ZMod m)) (y := (0 : ZMod m))
              (neg_one_ne_zero (m := m)))
    _ = (((-1 : ZMod m), (1 : ZMod m)), (3 : ZMod m)) := by
          simpa using fullMap2XY_layer2_of_y_ne_two (m := m) (x := (-1 : ZMod m))
            (y := (0 : ZMod m)) (zero_ne_two (m := m))

theorem iterate_three_fullMap2XY_E_of [Fact (5 < m)] {y : ZMod m}
    (hy0 : y ≠ (0 : ZMod m)) (hyneg2 : y ≠ (-2 : ZMod m)) :
    ((fullMap2XY (m := m)^[3]) (slicePoint (0 : ZMod m) ((-1 : ZMod m), y))) =
      (((0 : ZMod m), y + 3), (3 : ZMod m)) := by
  letI : Fact (1 < m) := inferInstance
  calc
    ((fullMap2XY (m := m)^[3]) (slicePoint (0 : ZMod m) ((-1 : ZMod m), y)))
        = ((fullMap2XY (m := m)^[2]) (((0 : ZMod m), y + 1), (1 : ZMod m))) := by
            simp [slicePoint, fullMap2XY, dir2XY, dir2LayerZeroXY, KMapXY,
              Function.iterate_succ_apply', hy0, hyneg2]
    _ = fullMap2XY (m := m) (((0 : ZMod m), y + 2), (2 : ZMod m)) := by
          rw [Function.iterate_succ_apply']
          simpa using congrArg (fullMap2XY (m := m))
            (fullMap2XY_layer1_of_x_zero (m := m) (y + 1))
    _ = (((0 : ZMod m), y + 3), (3 : ZMod m)) := by
          simpa [add_assoc] using fullMap2XY_layer2_of_y_ne_two (m := m) (x := (0 : ZMod m))
            (y := y + 2) (add_two_ne_two_of_ne_zero (m := m) hy0)

theorem iterate_three_fullMap2XY_origin [Fact (5 < m)] :
    ((fullMap2XY (m := m)^[3]) (slicePoint (0 : ZMod m) ((0 : ZMod m), (0 : ZMod m)))) =
      (((1 : ZMod m), (3 : ZMod m)), (3 : ZMod m)) := by
  calc
    ((fullMap2XY (m := m)^[3]) (slicePoint (0 : ZMod m) ((0 : ZMod m), (0 : ZMod m))))
        = ((fullMap2XY (m := m)^[2]) (((0 : ZMod m), (1 : ZMod m)), (1 : ZMod m))) := by
            simp [slicePoint, fullMap2XY, dir2XY, dir2LayerZeroXY, KMapXY,
              Function.iterate_succ_apply']
    _ = fullMap2XY (m := m) (((0 : ZMod m), (2 : ZMod m)), (2 : ZMod m)) := by
          rw [Function.iterate_succ_apply']
          simpa using congrArg (fullMap2XY (m := m))
            (fullMap2XY_layer1_of_x_zero (m := m) (1 : ZMod m))
    _ = (((1 : ZMod m), (3 : ZMod m)), (3 : ZMod m)) := by
          simpa using fullMap2XY_layer2_of_y_two (m := m) (x := (0 : ZMod m))

theorem iterate_three_fullMap2XY_G_of [Fact (5 < m)] {x y : ZMod m}
    (hy1 : y ≠ (1 : ZMod m))
    (hyneg1 : y ≠ (-1 : ZMod m))
    (hdiag : y ≠ x)
    (hxneg1 : x ≠ (-1 : ZMod m))
    (h00 : ¬ (x = 0 ∧ y = 0)) :
    ((fullMap2XY (m := m)^[3]) (slicePoint (0 : ZMod m) (x, y))) =
      ((x + 1, y + 2), (3 : ZMod m)) := by
  have hx10 : x + 1 ≠ 0 := add_one_ne_zero_of_ne_neg_one (m := m) hxneg1
  calc
    ((fullMap2XY (m := m)^[3]) (slicePoint (0 : ZMod m) (x, y)))
        = ((fullMap2XY (m := m)^[2]) ((x + 1, y + 1), (1 : ZMod m))) := by
            simp [slicePoint, fullMap2XY, dir2XY, dir2LayerZeroXY, KMapXY,
              Function.iterate_succ_apply', hyneg1, hdiag, hxneg1, h00]
    _ = fullMap2XY (m := m) ((x + 1, y + 1), (2 : ZMod m)) := by
          rw [Function.iterate_succ_apply']
          simpa using congrArg (fullMap2XY (m := m))
            (fullMap2XY_layer1_of_x_ne_zero (m := m) (x := x + 1) (y := y + 1) hx10)
    _ = ((x + 1, y + 2), (3 : ZMod m)) := by
          simpa [add_assoc] using fullMap2XY_layer2_of_y_ne_two (m := m) (x := x + 1)
            (y := y + 1) (add_one_ne_two_of_ne_one (m := m) hy1)

theorem iterate_m_fullMap2XY_A [Fact (5 < m)] :
    ((fullMap2XY (m := m)^[m]) (slicePoint (0 : ZMod m) ((2 : ZMod m), (2 : ZMod m)))) =
      slicePoint (0 : ZMod m) ((3 : ZMod m), (0 : ZMod m)) := by
  calc
    ((fullMap2XY (m := m)^[m]) (slicePoint (0 : ZMod m) ((2 : ZMod m), (2 : ZMod m))))
        = ((fullMap2XY (m := m)^[m - 3]) (((3 : ZMod m), (3 : ZMod m)), (3 : ZMod m))) := by
            rw [iterate_fullMap2XY_split_three (m := m),
              iterate_three_fullMap2XY_A (m := m)]
    _ = (((3 : ZMod m), (0 : ZMod m)), (0 : ZMod m)) := by
          simpa using iterate_m_sub_three_fullMap2XY (m := m) (3 : ZMod m) (3 : ZMod m)
    _ = slicePoint (0 : ZMod m) ((3 : ZMod m), (0 : ZMod m)) := rfl

theorem iterate_m_fullMap2XY_B_of [Fact (5 < m)] {x : ZMod m}
    (hx1 : x ≠ (1 : ZMod m)) (hxneg1 : x ≠ (-1 : ZMod m)) :
    ((fullMap2XY (m := m)^[m]) (slicePoint (0 : ZMod m) (x, (1 : ZMod m)))) =
      slicePoint (0 : ZMod m) (x + 2, (0 : ZMod m)) := by
  calc
    ((fullMap2XY (m := m)^[m]) (slicePoint (0 : ZMod m) (x, (1 : ZMod m))))
        = ((fullMap2XY (m := m)^[m - 3]) ((x + 2, (3 : ZMod m)), (3 : ZMod m))) := by
            rw [iterate_fullMap2XY_split_three (m := m),
              iterate_three_fullMap2XY_B_of (m := m) hx1 hxneg1]
    _ = ((x + 2, (0 : ZMod m)), (0 : ZMod m)) := by
          simpa using iterate_m_sub_three_fullMap2XY (m := m) (x + 2) (3 : ZMod m)
    _ = slicePoint (0 : ZMod m) (x + 2, (0 : ZMod m)) := rfl

theorem iterate_m_fullMap2XY_C_of [Fact (5 < m)] {x : ZMod m}
    (hxneg1 : x ≠ (-1 : ZMod m)) :
    ((fullMap2XY (m := m)^[m]) (slicePoint (0 : ZMod m) (x, (-1 : ZMod m)))) =
      slicePoint (0 : ZMod m) (x, (-2 : ZMod m)) := by
  calc
    ((fullMap2XY (m := m)^[m]) (slicePoint (0 : ZMod m) (x, (-1 : ZMod m))))
        = ((fullMap2XY (m := m)^[m - 3]) ((x, (1 : ZMod m)), (3 : ZMod m))) := by
            rw [iterate_fullMap2XY_split_three (m := m),
              iterate_three_fullMap2XY_C_of (m := m) hxneg1]
    _ = ((x, (-2 : ZMod m)), (0 : ZMod m)) := by
          calc
            ((fullMap2XY (m := m)^[m - 3]) ((x, (1 : ZMod m)), (3 : ZMod m)))
                = ((x, (1 : ZMod m) - 3), (0 : ZMod m)) := by
                    simpa using iterate_m_sub_three_fullMap2XY (m := m) x (1 : ZMod m)
            _ = ((x, (-2 : ZMod m)), (0 : ZMod m)) := by
                  ext <;> ring
    _ = slicePoint (0 : ZMod m) (x, (-2 : ZMod m)) := rfl

theorem iterate_m_fullMap2XY_C_neg_one_neg_two [Fact (5 < m)] :
    ((fullMap2XY (m := m)^[m]) (slicePoint (0 : ZMod m) ((-1 : ZMod m), (-2 : ZMod m)))) =
      slicePoint (0 : ZMod m) ((-1 : ZMod m), (-3 : ZMod m)) := by
  calc
    ((fullMap2XY (m := m)^[m]) (slicePoint (0 : ZMod m) ((-1 : ZMod m), (-2 : ZMod m))))
        = ((fullMap2XY (m := m)^[m - 3]) (((-1 : ZMod m), (0 : ZMod m)), (3 : ZMod m))) := by
            rw [iterate_fullMap2XY_split_three (m := m),
              iterate_three_fullMap2XY_C_neg_one_neg_two (m := m)]
    _ = (((-1 : ZMod m), (-3 : ZMod m)), (0 : ZMod m)) := by
          simpa using iterate_m_sub_three_fullMap2XY (m := m) (-1 : ZMod m) (0 : ZMod m)
    _ = slicePoint (0 : ZMod m) ((-1 : ZMod m), (-3 : ZMod m)) := rfl

theorem iterate_m_fullMap2XY_D_of [Fact (5 < m)] {x : ZMod m}
    (hx0 : x ≠ (0 : ZMod m)) (hx2 : x ≠ (2 : ZMod m)) (hxneg1 : x ≠ (-1 : ZMod m)) :
    ((fullMap2XY (m := m)^[m]) (slicePoint (0 : ZMod m) (x, x))) =
      slicePoint (0 : ZMod m) (x, x - 2) := by
  calc
    ((fullMap2XY (m := m)^[m]) (slicePoint (0 : ZMod m) (x, x)))
        = ((fullMap2XY (m := m)^[m - 3]) ((x, x + 1), (3 : ZMod m))) := by
            rw [iterate_fullMap2XY_split_three (m := m),
              iterate_three_fullMap2XY_D_of (m := m) hx0 hx2 hxneg1]
    _ = ((x, x - 2), (0 : ZMod m)) := by
          calc
            ((fullMap2XY (m := m)^[m - 3]) ((x, x + 1), (3 : ZMod m)))
                = ((x, (x + 1) - 3), (0 : ZMod m)) := by
                    simpa using iterate_m_sub_three_fullMap2XY (m := m) x (x + 1)
            _ = ((x, x - 2), (0 : ZMod m)) := by
                  ext <;> ring
    _ = slicePoint (0 : ZMod m) (x, x - 2) := rfl

theorem iterate_m_fullMap2XY_D_neg_one_zero [Fact (5 < m)] :
    ((fullMap2XY (m := m)^[m]) (slicePoint (0 : ZMod m) ((-1 : ZMod m), (0 : ZMod m)))) =
      slicePoint (0 : ZMod m) ((-1 : ZMod m), (-2 : ZMod m)) := by
  calc
    ((fullMap2XY (m := m)^[m]) (slicePoint (0 : ZMod m) ((-1 : ZMod m), (0 : ZMod m))))
        = ((fullMap2XY (m := m)^[m - 3]) (((-1 : ZMod m), (1 : ZMod m)), (3 : ZMod m))) := by
            rw [iterate_fullMap2XY_split_three (m := m),
              iterate_three_fullMap2XY_D_neg_one_zero (m := m)]
    _ = (((-1 : ZMod m), (-2 : ZMod m)), (0 : ZMod m)) := by
          calc
            ((fullMap2XY (m := m)^[m - 3]) (((-1 : ZMod m), (1 : ZMod m)), (3 : ZMod m)))
                = (((-1 : ZMod m), (1 : ZMod m) - 3), (0 : ZMod m)) := by
                    simpa using iterate_m_sub_three_fullMap2XY (m := m) (-1 : ZMod m) (1 : ZMod m)
            _ = (((-1 : ZMod m), (-2 : ZMod m)), (0 : ZMod m)) := by
                  ext <;> ring
    _ = slicePoint (0 : ZMod m) ((-1 : ZMod m), (-2 : ZMod m)) := rfl

theorem iterate_m_fullMap2XY_E_of [Fact (5 < m)] {y : ZMod m}
    (hy0 : y ≠ (0 : ZMod m)) (hyneg2 : y ≠ (-2 : ZMod m)) :
    ((fullMap2XY (m := m)^[m]) (slicePoint (0 : ZMod m) ((-1 : ZMod m), y))) =
      slicePoint (0 : ZMod m) ((0 : ZMod m), y) := by
  calc
    ((fullMap2XY (m := m)^[m]) (slicePoint (0 : ZMod m) ((-1 : ZMod m), y)))
        = ((fullMap2XY (m := m)^[m - 3]) (((0 : ZMod m), y + 3), (3 : ZMod m))) := by
            rw [iterate_fullMap2XY_split_three (m := m),
              iterate_three_fullMap2XY_E_of (m := m) hy0 hyneg2]
    _ = (((0 : ZMod m), y), (0 : ZMod m)) := by
          calc
            ((fullMap2XY (m := m)^[m - 3]) (((0 : ZMod m), y + 3), (3 : ZMod m)))
                = (((0 : ZMod m), (y + 3) - 3), (0 : ZMod m)) := by
                    simpa using iterate_m_sub_three_fullMap2XY (m := m) (0 : ZMod m) (y + 3)
            _ = (((0 : ZMod m), y), (0 : ZMod m)) := by
                  ext <;> ring
    _ = slicePoint (0 : ZMod m) ((0 : ZMod m), y) := rfl

theorem iterate_m_fullMap2XY_origin [Fact (5 < m)] :
    ((fullMap2XY (m := m)^[m]) (slicePoint (0 : ZMod m) ((0 : ZMod m), (0 : ZMod m)))) =
      slicePoint (0 : ZMod m) ((1 : ZMod m), (0 : ZMod m)) := by
  calc
    ((fullMap2XY (m := m)^[m]) (slicePoint (0 : ZMod m) ((0 : ZMod m), (0 : ZMod m))))
        = ((fullMap2XY (m := m)^[m - 3]) (((1 : ZMod m), (3 : ZMod m)), (3 : ZMod m))) := by
            rw [iterate_fullMap2XY_split_three (m := m),
              iterate_three_fullMap2XY_origin (m := m)]
    _ = (((1 : ZMod m), (0 : ZMod m)), (0 : ZMod m)) := by
          simpa using iterate_m_sub_three_fullMap2XY (m := m) (1 : ZMod m) (3 : ZMod m)
    _ = slicePoint (0 : ZMod m) ((1 : ZMod m), (0 : ZMod m)) := rfl

theorem iterate_m_fullMap2XY_G_of [Fact (5 < m)] {x y : ZMod m}
    (hy1 : y ≠ (1 : ZMod m))
    (hyneg1 : y ≠ (-1 : ZMod m))
    (hdiag : y ≠ x)
    (hxneg1 : x ≠ (-1 : ZMod m))
    (h00 : ¬ (x = 0 ∧ y = 0)) :
    ((fullMap2XY (m := m)^[m]) (slicePoint (0 : ZMod m) (x, y))) =
      slicePoint (0 : ZMod m) (x + 1, y - 1) := by
  calc
    ((fullMap2XY (m := m)^[m]) (slicePoint (0 : ZMod m) (x, y)))
        = ((fullMap2XY (m := m)^[m - 3]) ((x + 1, y + 2), (3 : ZMod m))) := by
            rw [iterate_fullMap2XY_split_three (m := m),
              iterate_three_fullMap2XY_G_of (m := m) hy1 hyneg1 hdiag hxneg1 h00]
    _ = ((x + 1, y - 1), (0 : ZMod m)) := by
          calc
            ((fullMap2XY (m := m)^[m - 3]) ((x + 1, y + 2), (3 : ZMod m)))
                = ((x + 1, (y + 2) - 3), (0 : ZMod m)) := by
                    simpa using iterate_m_sub_three_fullMap2XY (m := m) (x + 1) (y + 2)
            _ = ((x + 1, y - 1), (0 : ZMod m)) := by
                  ext <;> ring
    _ = slicePoint (0 : ZMod m) (x + 1, y - 1) := rfl

theorem returnMap2_origin [Fact (2 < m)] :
    returnMap2 (m := m) ((0 : ZMod m), (0 : ZMod m)) = ((1 : ZMod m), (0 : ZMod m)) := by
  letI : Fact (1 < m) := ⟨lt_trans (by decide : 1 < 2) Fact.out⟩
  have h01 : (0 : ZMod m) ≠ (1 : ZMod m) := by
    intro h
    exact TorusD3Even.one_ne_zero (m := m) h.symm
  have h02 : (0 : ZMod m) ≠ (2 : ZMod m) := by
    intro h
    exact TorusD3Even.two_ne_zero (m := m) h.symm
  ext <;> simp [returnMap2, TorusD3Even.R2xy, h01, h02, TorusD3Even.one_ne_zero (m := m)]

theorem returnMap2_neg_one_zero [Fact (5 < m)] :
    returnMap2 (m := m) ((-1 : ZMod m), (0 : ZMod m)) = ((-1 : ZMod m), (-2 : ZMod m)) := by
  letI : Fact (2 < m) := inferInstance
  ext <;> simp [returnMap2, TorusD3Even.R2xy, TorusD3Even.two_ne_zero (m := m),
    neg_one_ne_two (m := m)] <;> ring

theorem returnMap2_neg_one_neg_two [Fact (5 < m)] :
    returnMap2 (m := m) ((-1 : ZMod m), (-2 : ZMod m)) = ((-1 : ZMod m), (-3 : ZMod m)) := by
  letI : Fact (2 < m) := inferInstance
  ext <;> simp [returnMap2, TorusD3Even.R2xy, neg_one_ne_two (m := m)] <;> ring

theorem iterate_m_fullMap2XY_slice_zero [Fact (5 < m)] (u : P0Coord m) :
    ((fullMap2XY (m := m)^[m]) (slicePoint (0 : ZMod m) u)) =
      slicePoint (0 : ZMod m) (returnMap2 (m := m) u) := by
  letI : Fact (0 < m) := inferInstance
  letI : Fact (1 < m) := inferInstance
  letI : Fact (2 < m) := inferInstance
  rcases u with ⟨x, y⟩
  by_cases hA : x = (2 : ZMod m) ∧ y = (2 : ZMod m)
  · rcases hA with ⟨rfl, rfl⟩
    simpa [returnMap2, TorusD3Even.R2xy] using iterate_m_fullMap2XY_A (m := m)
  · by_cases hy1 : y = (1 : ZMod m)
    · by_cases hx1 : x = (1 : ZMod m)
      · subst hy1
        subst hx1
        simpa [returnMap2, R2xy_eq_D_of (m := m) (x := (1 : ZMod m))
          (by simpa using one_ne_zero (m := m))
          (by simpa using two_ne_one (m := m).symm)
          (by simpa using one_ne_neg_one (m := m))] using
          iterate_m_fullMap2XY_D_of (m := m) (x := (1 : ZMod m))
          (by simpa using one_ne_zero (m := m))
          (by simpa using two_ne_one (m := m).symm)
          (by simpa using one_ne_neg_one (m := m))
      · by_cases hxneg1 : x = (-1 : ZMod m)
        · subst hy1
          subst hxneg1
          simpa [returnMap2, R2xy_eq_E_of (m := m) (y := (1 : ZMod m))
            (one_ne_zero (m := m)) (one_ne_neg_two (m := m))] using
            iterate_m_fullMap2XY_E_of (m := m) (y := (1 : ZMod m))
            (one_ne_zero (m := m)) (one_ne_neg_two (m := m))
        · subst hy1
          simpa [returnMap2, R2xy_eq_B_of (m := m) (x := x) hx1 hxneg1] using
            iterate_m_fullMap2XY_B_of (m := m) hx1 hxneg1
    · by_cases hyneg1 : y = (-1 : ZMod m)
      · by_cases hxneg1 : x = (-1 : ZMod m)
        · subst hyneg1
          subst hxneg1
          simpa [returnMap2, R2xy_eq_E_of (m := m) (y := (-1 : ZMod m))
            (neg_one_ne_zero (m := m)) (neg_one_ne_neg_two (m := m))] using
            iterate_m_fullMap2XY_E_of (m := m) (y := (-1 : ZMod m))
            (neg_one_ne_zero (m := m)) (neg_one_ne_neg_two (m := m))
        · subst hyneg1
          simpa [returnMap2, R2xy_eq_C_of (m := m) (x := x) hxneg1] using
            iterate_m_fullMap2XY_C_of (m := m) hxneg1
      · by_cases hdiag : y = x
        · subst y
          by_cases hx0 : x = (0 : ZMod m)
          · subst x
            simpa [returnMap2_origin (m := m)] using iterate_m_fullMap2XY_origin (m := m)
          · by_cases hx2 : x = (2 : ZMod m)
            · exact False.elim (hA ⟨hx2, hx2⟩)
            ·
              have hxneg1 : x ≠ (-1 : ZMod m) := by
                intro hxneg1
                exact hyneg1 (by simpa [hxneg1])
              simpa [returnMap2, R2xy_eq_D_of (m := m) (x := x) hx0 hx2 hxneg1] using
                iterate_m_fullMap2XY_D_of (m := m) hx0 hx2 hxneg1
        · by_cases hxneg1 : x = (-1 : ZMod m)
          · by_cases hy0 : y = (0 : ZMod m)
            · subst hxneg1
              subst hy0
              simpa [returnMap2_neg_one_zero (m := m)] using iterate_m_fullMap2XY_D_neg_one_zero (m := m)
            · by_cases hyneg2 : y = (-2 : ZMod m)
              · subst hxneg1
                subst hyneg2
                simpa [returnMap2_neg_one_neg_two (m := m)] using
                  iterate_m_fullMap2XY_C_neg_one_neg_two (m := m)
              · subst hxneg1
                simpa [returnMap2, R2xy_eq_E_of (m := m) (y := y) hy0 hyneg2] using
                  iterate_m_fullMap2XY_E_of (m := m) hy0 hyneg2
          · have h00 : ¬ (x = (0 : ZMod m) ∧ y = (0 : ZMod m)) := by
              intro h
              exact hdiag (by simpa [h.1, h.2])
            have hA' : (x, y) ≠ ((2 : ZMod m), (2 : ZMod m)) := by
              simpa [Prod.mk.injEq] using hA
            have h00' : (x, y) ≠ ((0 : ZMod m), (0 : ZMod m)) := by
              simpa [Prod.mk.injEq] using h00
            simpa [returnMap2, R2xy_eq_G_of (m := m) hA' hy1 hyneg1 hdiag hxneg1 h00'] using
              iterate_m_fullMap2XY_G_of (m := m) hy1 hyneg1 hdiag hxneg1 h00

theorem cycleOn_fullMap2XY [Fact (Even m)] [Fact (5 < m)] :
    TorusD4.CycleOn (m ^ 3) (fullMap2XY (m := m))
      (slicePoint (0 : ZMod m) (linePoint2 (m := m) (0 : ZMod m))) := by
  have hm0 : 0 < m := by
    have hm5 : 5 < m := Fact.out
    omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : NeZero m := ⟨Nat.ne_of_gt hm0⟩
  exact cycleOn_full_of_color2_return (m := m)
    (hstep := fullMap2XY_snd (m := m))
    (hreturn := iterate_m_fullMap2XY_slice_zero (m := m))

end TorusD3Odometer
