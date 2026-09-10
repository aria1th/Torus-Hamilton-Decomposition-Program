import TorusD3Odometer.Color1FullCaseI
import TorusD3Odometer.Color0
import TorusD3Even.Counting
import Mathlib.Tactic

namespace TorusD3Odometer

open TorusD4
open TorusD3Even

instance factZeroOfFactFour [Fact (4 < m)] : Fact (0 < m) :=
  ⟨lt_trans (by decide : 0 < 4) Fact.out⟩

instance factOneOfFactFour [Fact (4 < m)] : Fact (1 < m) :=
  ⟨lt_trans (by decide : 1 < 4) Fact.out⟩

instance factTwoOfFactFour [Fact (4 < m)] : Fact (2 < m) :=
  ⟨lt_trans (by decide : 2 < 4) Fact.out⟩

instance factFourOfFactFive [Fact (5 < m)] : Fact (4 < m) :=
  ⟨lt_trans (by decide : 4 < 5) Fact.out⟩

theorem natCast_ne_two_of_three_le_lt [Fact (2 < m)] {n : ℕ} (hn2 : 3 ≤ n) (hnm : n < m) :
    ((n : ℕ) : ZMod m) ≠ 2 := by
  intro h
  have h' : n % m = 2 % m := (ZMod.natCast_eq_natCast_iff' n 2 m).1 (by simpa using h)
  rw [Nat.mod_eq_of_lt hnm, Nat.mod_eq_of_lt Fact.out] at h'
  omega

theorem natCast_eq_natCast_of_lt [Fact (0 < m)] {a b : ℕ}
    (ha : a < m) (hb : b < m)
    (h : (((a : ℕ) : ZMod m)) = ((b : ℕ) : ZMod m)) : a = b := by
  have hmod : a % m = b % m := (ZMod.natCast_eq_natCast_iff' a b m).1 h
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hmod

theorem one_ne_neg_two_case0 [Fact (4 < m)] : (1 : ZMod m) ≠ (-2 : ZMod m) := by
  have hm4 : 4 < m := Fact.out
  simpa using natCast_ne_neg_two_of_lt (m := m) (n := 1) (by omega)

def dir0CaseILayerZero (u : P0Coord m) : Color :=
  let i : ZMod m := u.1
  let k : ZMod m := u.2
  if (k = 0 ∧ i ≠ 0 ∧ i ≠ (-2 : ZMod m) ∧ i ≠ (-1 : ZMod m)) ∨
      (i = 0 ∧ k = (-1 : ZMod m)) ∨
      (i = (-1 : ZMod m) ∧ k = (1 : ZMod m)) ∨
      (i = (-2 : ZMod m) ∧ k = (1 : ZMod m)) then
    0
  else if (i = 0 ∧ k ≠ 0 ∧ k ≠ (-1 : ZMod m)) ∨
      (i = (1 : ZMod m) ∧ k = (-1 : ZMod m)) ∨
      (i = (-2 : ZMod m) ∧ k = 0) then
    2
  else
    1

def dir0CaseI (z : FullCoord m) : Color :=
  let (u, s) := z
  if s = 0 then
    dir0CaseILayerZero (m := m) u
  else if s = 1 then
    if u.1 = 0 then 1 else 2
  else if s = 2 then
    if u.1 + u.2 = (2 : ZMod m) then 2 else 0
  else
    0

def fullMap0CaseI (z : FullCoord m) : FullCoord m :=
  KMap (m := m) (dir0CaseI (m := m) z) z

def returnMap0CaseI (u : P0Coord m) : P0Coord m :=
  let i : ZMod m := u.1
  let k : ZMod m := u.2
  if i = 0 ∧ k = 0 then
    ((-2 : ZMod m), 0)
  else if i = (1 : ZMod m) ∧ k = (-1 : ZMod m) then
    ((-2 : ZMod m), 2)
  else if i = (-2 : ZMod m) ∧ k = 0 then
    ((-4 : ZMod m), 2)
  else if i = (-1 : ZMod m) ∧ k = (1 : ZMod m) then
    ((-2 : ZMod m), 1)
  else if i + k = (1 : ZMod m) ∧ ¬ (i = (1 : ZMod m) ∧ k = 0) then
    (i - 3, k + 2)
  else if (k = 0 ∧ i ≠ 0 ∧ i ≠ (-2 : ZMod m) ∧ i ≠ (-1 : ZMod m)) ∨
      (i = 0 ∧ k = (-1 : ZMod m)) ∨
      (i = (-2 : ZMod m) ∧ k = (1 : ZMod m)) then
    (i - 1, k + 1)
  else
    (i - 2, k + 1)

@[simp] theorem fullMap0CaseI_snd (z : FullCoord m) :
    (fullMap0CaseI (m := m) z).2 = z.2 + 1 := by
  simp [fullMap0CaseI, KMap_snd]

def toXY (u : P0Coord m) : P0Coord m :=
  (u.1 + 2 * u.2, u.2)

def fromXY (u : P0Coord m) : P0Coord m :=
  (u.1 - 2 * u.2, u.2)

theorem fromXY_toXY (u : P0Coord m) :
    fromXY (m := m) (toXY (m := m) u) = u := by
  rcases u with ⟨i, k⟩
  ext <;> simp [toXY, fromXY]

theorem toXY_fromXY (u : P0Coord m) :
    toXY (m := m) (fromXY (m := m) u) = u := by
  rcases u with ⟨x, y⟩
  ext <;> simp [toXY, fromXY]

def xyEquiv : P0Coord m ≃ P0Coord m where
  toFun := toXY (m := m)
  invFun := fromXY (m := m)
  left_inv := fromXY_toXY (m := m)
  right_inv := toXY_fromXY (m := m)

def linePoint0 (x : Fin m) : P0Coord m :=
  (((x : Fin m) : ZMod m), 0)

theorem linePoint0_injective : Function.Injective (linePoint0 (m := m)) := by
  intro x y h
  apply Fin.ext
  have hcast : (((x : Fin m) : ZMod m)) = ((y : ZMod m)) := by
    simpa [linePoint0] using congrArg Prod.fst h
  have hmod : x.1 % m = y.1 % m := (ZMod.natCast_eq_natCast_iff' x.1 y.1 m).1 hcast
  simpa [Nat.mod_eq_of_lt x.2, Nat.mod_eq_of_lt y.2] using hmod

theorem mem_range_linePoint0_iff [Fact (0 < m)] {u : P0Coord m} :
    u ∈ Set.range (linePoint0 (m := m)) ↔ u.2 = 0 := by
  letI : NeZero m := ⟨Nat.ne_of_gt Fact.out⟩
  rcases u with ⟨x, y⟩
  constructor
  · rintro ⟨z, hz⟩
    simpa [linePoint0] using (congrArg Prod.snd hz).symm
  · intro hy
    refine ⟨⟨x.val, x.val_lt⟩, ?_⟩
    ext
    · simpa [linePoint0] using (ZMod.natCast_zmod_val x).symm
    · simpa [linePoint0] using hy.symm

theorem not_mem_range_linePoint0_of_snd_ne_zero [Fact (0 < m)] {u : P0Coord m} (hy : u.2 ≠ 0) :
    u ∉ Set.range (linePoint0 (m := m)) := by
  intro hu
  exact hy ((mem_range_linePoint0_iff (m := m)).1 hu)

theorem not_mem_range_linePoint0_of_nat_snd_pos_lt [Fact (0 < m)] {a : ZMod m} {n : ℕ}
    (hn0 : 0 < n) (hnm : n < m) :
    (a, (((n : ℕ) : ZMod m))) ∉ Set.range (linePoint0 (m := m)) := by
  apply not_mem_range_linePoint0_of_snd_ne_zero
  exact natCast_ne_zero_of_pos_lt (m := m) (n := n) hn0 hnm

theorem dir0CaseILayerZero_origin [Fact (4 < m)] :
    dir0CaseILayerZero (m := m) ((0 : ZMod m), (0 : ZMod m)) = 1 := by
  have h10 : (1 : ZMod m) ≠ 0 := one_ne_zero (m := m)
  have h20 : (2 : ZMod m) ≠ 0 := two_ne_zero (m := m)
  simp [dir0CaseILayerZero, h10, h20]

theorem dir0CaseILayerZero_one_neg_one [Fact (4 < m)] :
    dir0CaseILayerZero (m := m) ((1 : ZMod m), (-1 : ZMod m)) = 2 := by
  have hm4 : 4 < m := Fact.out
  have h10 : (1 : ZMod m) ≠ 0 := one_ne_zero (m := m)
  have h1neg1 : (1 : ZMod m) ≠ (-1 : ZMod m) := one_ne_neg_one (m := m)
  have h1neg2 : (1 : ZMod m) ≠ (-2 : ZMod m) := by
    simpa using natCast_ne_neg_two_of_lt (m := m) (n := 1) (by omega)
  simp [dir0CaseILayerZero, h10, h1neg1, h1neg2]

theorem dir0CaseILayerZero_neg_two_zero [Fact (4 < m)] :
    dir0CaseILayerZero (m := m) ((-2 : ZMod m), (0 : ZMod m)) = 2 := by
  have hm4 : 4 < m := Fact.out
  have h20 : (2 : ZMod m) ≠ 0 := two_ne_zero (m := m)
  have hneg20 : (-2 : ZMod m) ≠ 0 := neg_ne_zero.mpr h20
  have h01 : (0 : ZMod m) ≠ (1 : ZMod m) := by
    intro h
    exact one_ne_zero (m := m) h.symm
  have h21 : (2 : ZMod m) ≠ (1 : ZMod m) := two_ne_one (m := m)
  have h1neg2 : (1 : ZMod m) ≠ (-2 : ZMod m) := by
    simpa using natCast_ne_neg_two_of_lt (m := m) (n := 1) (by omega)
  have hneg2ne1 : (-2 : ZMod m) ≠ (1 : ZMod m) := by
    intro h
    exact h1neg2 h.symm
  simp [dir0CaseILayerZero, hneg20, h01, h21, hneg2ne1]

theorem dir0CaseILayerZero_neg_one_one [Fact (4 < m)] :
    dir0CaseILayerZero (m := m) ((-1 : ZMod m), (1 : ZMod m)) = 0 := by
  simp [dir0CaseILayerZero, one_ne_zero (m := m), one_ne_neg_one (m := m),
    two_ne_zero (m := m)]

theorem dir0CaseILayerZero_eq_zero_of_k_zero [Fact (4 < m)] {i : ZMod m}
    (hi0 : i ≠ 0) (hineg2 : i ≠ (-2 : ZMod m)) (hineg1 : i ≠ (-1 : ZMod m)) :
    dir0CaseILayerZero (m := m) (i, (0 : ZMod m)) = 0 := by
  simp [dir0CaseILayerZero, hi0, hineg2, hineg1]

theorem dir0CaseILayerZero_eq_two_of_i_zero [Fact (4 < m)] {k : ZMod m}
    (hk0 : k ≠ 0) (hkneg1 : k ≠ (-1 : ZMod m)) :
    dir0CaseILayerZero (m := m) ((0 : ZMod m), k) = 2 := by
  have h10 : (1 : ZMod m) ≠ 0 := one_ne_zero (m := m)
  have h20 : (2 : ZMod m) ≠ 0 := two_ne_zero (m := m)
  simp [dir0CaseILayerZero, hk0, hkneg1, h10, h20]

theorem dir0CaseILayerZero_eq_zero_neg_two_one [Fact (4 < m)] :
    dir0CaseILayerZero (m := m) ((-2 : ZMod m), (1 : ZMod m)) = 0 := by
  simp [dir0CaseILayerZero, one_ne_zero (m := m), one_ne_neg_one (m := m),
    two_ne_zero (m := m)]

theorem dir0CaseILayerZero_eq_one_of_diag [Fact (4 < m)] {i k : ZMod m}
    (hdiag : i + k = (1 : ZMod m))
    (h10 : ¬ (i = (1 : ZMod m) ∧ k = 0))
    (hk0 : k ≠ 0)
    (hi0 : i ≠ 0)
    (hik_special : ¬ (i = (-1 : ZMod m) ∧ k = (1 : ZMod m)))
    (hkneg1 : k ≠ (-1 : ZMod m))
    (h10' : ¬ (i = (1 : ZMod m) ∧ k = (-1 : ZMod m)))
    (hineg2zero : ¬ (i = (-2 : ZMod m) ∧ k = 0))
    (hineg2one : ¬ (i = (-2 : ZMod m) ∧ k = (1 : ZMod m))) :
    dir0CaseILayerZero (m := m) (i, k) = 1 := by
  simp [dir0CaseILayerZero, h10, hk0, hi0, hik_special, hkneg1, h10', hineg2zero,
    hineg2one]

theorem iterate_KMap0 (n : ℕ) (u : P0Coord m) (s : ZMod m) :
    ((KMap (m := m) 0)^[n]) (u, s) = ((u.1 + n, u.2), s + n) := by
  induction n generalizing u s with
  | zero =>
      simp [KMap]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      ext <;> simp [KMap, Nat.cast_add]
      all_goals ring

theorem fullMap0CaseI_of_s_ne_zero_one_two {u : P0Coord m} {s : ZMod m}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hs2 : s ≠ 2) :
    fullMap0CaseI (m := m) (u, s) = KMap (m := m) 0 (u, s) := by
  simp [fullMap0CaseI, dir0CaseI, hs0, hs1, hs2]

theorem iterate_fullMap0CaseI_from_three [Fact (4 < m)] :
    ∀ n u, n ≤ m - 3 →
      ((fullMap0CaseI (m := m)^[n]) (u, (3 : ZMod m))) =
        ((KMap (m := m) 0)^[n]) (u, (3 : ZMod m))
  | 0, u, _ => by simp
  | n + 1, u, hn => by
      have hm4 : 4 < m := Fact.out
      have hcur_lt : n + 3 < m := by omega
      have hn' : n ≤ m - 3 := Nat.le_of_succ_le hn
      have hs0 : (3 : ZMod m) + n ≠ 0 := by
        simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
          natCast_ne_zero_of_pos_lt (m := m) (n := n + 3) (by omega) hcur_lt
      have hs1 : (3 : ZMod m) + n ≠ 1 := by
        simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
          natCast_ne_one_of_two_le_lt (m := m) (n := n + 3) (by omega) hcur_lt
      have hs2 : (3 : ZMod m) + n ≠ 2 := by
        simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
          natCast_ne_two_of_three_le_lt (m := m) (n := n + 3) (by omega) hcur_lt
      calc
        ((fullMap0CaseI (m := m)^[n + 1]) (u, (3 : ZMod m)))
            = fullMap0CaseI (m := m) (((fullMap0CaseI (m := m)^[n]) (u, (3 : ZMod m)))) := by
                rw [Function.iterate_succ_apply']
        _ = fullMap0CaseI (m := m) (((KMap (m := m) 0)^[n]) (u, (3 : ZMod m))) := by
              rw [iterate_fullMap0CaseI_from_three (m := m) n u hn']
        _ = fullMap0CaseI (m := m) ((u.1 + n, u.2), (3 : ZMod m) + n) := by
              rw [iterate_KMap0]
        _ = KMap (m := m) 0 ((u.1 + n, u.2), (3 : ZMod m) + n) := by
              simpa using fullMap0CaseI_of_s_ne_zero_one_two (m := m) (u := (u.1 + n, u.2))
                hs0 hs1 hs2
        _ = ((KMap (m := m) 0)^[n + 1]) (u, (3 : ZMod m)) := by
              symm
              rw [Function.iterate_succ_apply', iterate_KMap0]

theorem iterate_m_sub_three_fullMap0CaseI [Fact (4 < m)] (u : P0Coord m) :
    ((fullMap0CaseI (m := m)^[m - 3]) (u, (3 : ZMod m))) =
      slicePoint (0 : ZMod m) (u.1 - 3, u.2) := by
  have hm3 : 3 ≤ m := by
    have hm4 : 4 < m := Fact.out
    omega
  calc
    ((fullMap0CaseI (m := m)^[m - 3]) (u, (3 : ZMod m)))
        = ((KMap (m := m) 0)^[m - 3]) (u, (3 : ZMod m)) := by
            rw [iterate_fullMap0CaseI_from_three (m := m) (m - 3) u le_rfl]
    _ = ((u.1 + ((m - 3 : ℕ) : ZMod m), u.2), (3 : ZMod m) + ((m - 3 : ℕ) : ZMod m)) := by
          rw [iterate_KMap0]
    _ = slicePoint (0 : ZMod m) (u.1 - 3, u.2) := by
          ext <;> simp [slicePoint, Nat.cast_sub hm3]
          all_goals ring

theorem fullMap0CaseI_step_zero_of_dir0 {u : P0Coord m}
    (hdir : dir0CaseILayerZero (m := m) u = 0) :
    fullMap0CaseI (m := m) (slicePoint (0 : ZMod m) u) = ((u.1 + 1, u.2), (1 : ZMod m)) := by
  simp [fullMap0CaseI, dir0CaseI, hdir, KMap, slicePoint]

theorem fullMap0CaseI_step_zero_of_dir1 {u : P0Coord m}
    (hdir : dir0CaseILayerZero (m := m) u = 1) :
    fullMap0CaseI (m := m) (slicePoint (0 : ZMod m) u) = (u, (1 : ZMod m)) := by
  simp [fullMap0CaseI, dir0CaseI, hdir, KMap, slicePoint]

theorem fullMap0CaseI_step_zero_of_dir2 {u : P0Coord m}
    (hdir : dir0CaseILayerZero (m := m) u = 2) :
    fullMap0CaseI (m := m) (slicePoint (0 : ZMod m) u) = ((u.1, u.2 + 1), (1 : ZMod m)) := by
  simp [fullMap0CaseI, dir0CaseI, hdir, KMap, slicePoint]

theorem fullMap0CaseI_step_one_of_i_zero [Fact (4 < m)] {k : ZMod m} :
    fullMap0CaseI (m := m) (((0 : ZMod m), k), (1 : ZMod m)) =
      (((0 : ZMod m), k), (2 : ZMod m)) := by
  ext <;> simp [fullMap0CaseI, dir0CaseI, KMap, one_ne_zero (m := m)]
  ring

theorem fullMap0CaseI_step_one_of_i_ne_zero [Fact (4 < m)] {i k : ZMod m} (hi0 : i ≠ 0) :
    fullMap0CaseI (m := m) ((i, k), (1 : ZMod m)) =
      ((i, k + 1), (2 : ZMod m)) := by
  ext <;> simp [fullMap0CaseI, dir0CaseI, KMap, one_ne_zero (m := m), hi0]
  ring

theorem fullMap0CaseI_step_two_of_sum_two [Fact (4 < m)] {i k : ZMod m}
    (hsum : i + k = (2 : ZMod m)) :
    fullMap0CaseI (m := m) ((i, k), (2 : ZMod m)) =
      ((i, k + 1), (3 : ZMod m)) := by
  ext <;> simp [fullMap0CaseI, dir0CaseI, KMap, two_ne_zero (m := m), two_ne_one (m := m), hsum]
  ring

theorem fullMap0CaseI_step_two_of_sum_ne_two [Fact (4 < m)] {i k : ZMod m}
    (hsum : i + k ≠ (2 : ZMod m)) :
    fullMap0CaseI (m := m) ((i, k), (2 : ZMod m)) =
      ((i + 1, k), (3 : ZMod m)) := by
  ext <;> simp [fullMap0CaseI, dir0CaseI, KMap, two_ne_zero (m := m), two_ne_one (m := m), hsum]
  ring

theorem iterate_three_fullMap0CaseI_of_dir0_generic [Fact (4 < m)] {u : P0Coord m}
    (hdir : dir0CaseILayerZero (m := m) u = 0)
    (hi : u.1 ≠ (-1 : ZMod m)) :
    ((fullMap0CaseI (m := m)^[3]) (slicePoint (0 : ZMod m) u)) =
      ((u.1 + 2, u.2 + 1), (3 : ZMod m)) := by
  have hi1 : u.1 + 1 ≠ 0 := by
    intro h
    apply hi
    calc
      u.1 = (u.1 + 1) - 1 := by ring
      _ = (-1 : ZMod m) := by rw [h]; ring
  calc
    ((fullMap0CaseI (m := m)^[3]) (slicePoint (0 : ZMod m) u))
        = ((fullMap0CaseI (m := m)^[2]) ((u.1 + 1, u.2), (1 : ZMod m))) := by
            rw [Function.iterate_succ_apply']
            simpa using congrArg (fun z => (fullMap0CaseI (m := m)^[2]) z)
              (fullMap0CaseI_step_zero_of_dir0 (m := m) hdir)
    _ = fullMap0CaseI (m := m) ((u.1 + 1, u.2 + 1), (2 : ZMod m)) := by
          rw [Function.iterate_succ_apply']
          simpa using congrArg (fullMap0CaseI (m := m))
            (fullMap0CaseI_step_one_of_i_ne_zero (m := m) (i := u.1 + 1) (k := u.2) hi1)
    _ = ((u.1 + 2, u.2 + 1), (3 : ZMod m)) := by
          have hsum : u.1 + 1 + (u.2 + 1) ≠ (2 : ZMod m) := by
            intro h
            have hsum0 : u.1 + u.2 = 0 := by
              calc
                u.1 + u.2 = (u.1 + 1 + (u.2 + 1)) - 2 := by ring
                _ = 0 := by rw [h]; ring
            have hdir0 :
                (u.2 = 0 ∧ u.1 ≠ 0 ∧ u.1 ≠ (-2 : ZMod m) ∧ u.1 ≠ (-1 : ZMod m)) ∨
                  (u.1 = 0 ∧ u.2 = (-1 : ZMod m)) ∨
                  (u.1 = (-1 : ZMod m) ∧ u.2 = (1 : ZMod m)) ∨
                  (u.1 = (-2 : ZMod m) ∧ u.2 = (1 : ZMod m)) := by
              by_cases hA :
                  (u.2 = 0 ∧ u.1 ≠ 0 ∧ u.1 ≠ (-2 : ZMod m) ∧ u.1 ≠ (-1 : ZMod m)) ∨
                    (u.1 = 0 ∧ u.2 = (-1 : ZMod m)) ∨
                    (u.1 = (-1 : ZMod m) ∧ u.2 = (1 : ZMod m)) ∨
                    (u.1 = (-2 : ZMod m) ∧ u.2 = (1 : ZMod m))
              · exact hA
              · have hne : dir0CaseILayerZero (m := m) u ≠ 0 := by
                  by_cases hB :
                      (u.1 = 0 ∧ u.2 ≠ 0 ∧ u.2 ≠ (-1 : ZMod m)) ∨
                        (u.1 = (1 : ZMod m) ∧ u.2 = (-1 : ZMod m)) ∨
                        (u.1 = (-2 : ZMod m) ∧ u.2 = 0)
                  · simp [dir0CaseILayerZero, hA, hB, two_ne_zero (m := m)]
                  · simp [dir0CaseILayerZero, hA, hB, one_ne_zero (m := m)]
                exact False.elim (hne hdir)
            rcases hdir0 with hzero | hneg | hone | htwo
            · rcases hzero with ⟨hk0, hi0', -, -⟩
              have : u.1 = 0 := by simpa [hk0] using hsum0
              exact hi0' this
            · have : (-1 : ZMod m) = 0 := by
                calc
                  (-1 : ZMod m) = u.1 + u.2 := by rw [hneg.1, hneg.2]; ring
                  _ = 0 := hsum0
              exact neg_ne_zero.mpr (one_ne_zero (m := m)) this
            · exact hi hone.1
            · have : (-1 : ZMod m) = 0 := by
                calc
                  (-1 : ZMod m) = u.1 + u.2 := by rw [htwo.1, htwo.2]; ring
                  _ = 0 := hsum0
              exact neg_ne_zero.mpr (one_ne_zero (m := m)) this
          have hstep := fullMap0CaseI_step_two_of_sum_ne_two (m := m)
            (i := u.1 + 1) (k := u.2 + 1) hsum
          calc
            fullMap0CaseI (m := m) ((u.1 + 1, u.2 + 1), (2 : ZMod m))
                = ((u.1 + (1 + 1), u.2 + 1), (3 : ZMod m)) := by
                    simpa [add_assoc] using hstep
            _ = ((u.1 + 2, u.2 + 1), (3 : ZMod m)) := by
                  ext <;> ring

theorem iterate_three_fullMap0CaseI_origin [Fact (4 < m)] :
    ((fullMap0CaseI (m := m)^[3]) (slicePoint (0 : ZMod m) ((0 : ZMod m), (0 : ZMod m)))) =
      (((1 : ZMod m), (0 : ZMod m)), (3 : ZMod m)) := by
  calc
    ((fullMap0CaseI (m := m)^[3]) (slicePoint (0 : ZMod m) ((0 : ZMod m), (0 : ZMod m))))
        = ((fullMap0CaseI (m := m)^[2]) (((0 : ZMod m), (0 : ZMod m)), (1 : ZMod m))) := by
            rw [Function.iterate_succ_apply']
            simpa using congrArg (fun z => (fullMap0CaseI (m := m)^[2]) z)
              (fullMap0CaseI_step_zero_of_dir1 (m := m)
                (u := ((0 : ZMod m), (0 : ZMod m))) (dir0CaseILayerZero_origin (m := m)))
    _ = fullMap0CaseI (m := m) (((0 : ZMod m), (0 : ZMod m)), (2 : ZMod m)) := by
          rw [Function.iterate_succ_apply']
          simpa using congrArg (fullMap0CaseI (m := m))
            (fullMap0CaseI_step_one_of_i_zero (m := m) (k := (0 : ZMod m)))
    _ = (((1 : ZMod m), (0 : ZMod m)), (3 : ZMod m)) := by
          have hsum : ((0 : ZMod m) + (0 : ZMod m)) ≠ (2 : ZMod m) := by
            intro h
            exact two_ne_zero (m := m) (by simpa using h.symm)
          calc
            fullMap0CaseI (m := m) ((0, 0), (2 : ZMod m))
                = (((0 : ZMod m) + 1, (0 : ZMod m)), (3 : ZMod m)) := by
                    exact fullMap0CaseI_step_two_of_sum_ne_two (m := m)
                      (i := (0 : ZMod m)) (k := (0 : ZMod m)) hsum
            _ = (((1 : ZMod m), (0 : ZMod m)), (3 : ZMod m)) := by
                  ext <;> ring

theorem iterate_three_fullMap0CaseI_of_dir1_sum_eq_one [Fact (4 < m)] {u : P0Coord m}
    (hdir : dir0CaseILayerZero (m := m) u = 1)
    (hi0 : u.1 ≠ 0)
    (hsum : u.1 + u.2 = (1 : ZMod m)) :
    ((fullMap0CaseI (m := m)^[3]) (slicePoint (0 : ZMod m) u)) =
      ((u.1, u.2 + 2), (3 : ZMod m)) := by
  calc
    ((fullMap0CaseI (m := m)^[3]) (slicePoint (0 : ZMod m) u))
        = ((fullMap0CaseI (m := m)^[2]) (u, (1 : ZMod m))) := by
            rw [Function.iterate_succ_apply']
            simpa using congrArg (fun z => (fullMap0CaseI (m := m)^[2]) z)
              (fullMap0CaseI_step_zero_of_dir1 (m := m) hdir)
    _ = fullMap0CaseI (m := m) ((u.1, u.2 + 1), (2 : ZMod m)) := by
          rw [Function.iterate_succ_apply']
          simpa using congrArg (fullMap0CaseI (m := m))
            (fullMap0CaseI_step_one_of_i_ne_zero (m := m) (i := u.1) (k := u.2) hi0)
    _ = ((u.1, u.2 + 2), (3 : ZMod m)) := by
          have hsum' : u.1 + (u.2 + 1) = (2 : ZMod m) := by
            calc
              u.1 + (u.2 + 1) = (u.1 + u.2) + 1 := by ring
              _ = (2 : ZMod m) := by rw [hsum]; norm_num
          calc
            fullMap0CaseI (m := m) ((u.1, u.2 + 1), (2 : ZMod m))
                = ((u.1, (u.2 + 1) + 1), (3 : ZMod m)) := by
                    exact fullMap0CaseI_step_two_of_sum_two (m := m)
                      (i := u.1) (k := u.2 + 1) hsum'
            _ = ((u.1, u.2 + 2), (3 : ZMod m)) := by
                  ext <;> ring

theorem iterate_three_fullMap0CaseI_of_dir1_generic [Fact (4 < m)] {u : P0Coord m}
    (hdir : dir0CaseILayerZero (m := m) u = 1)
    (hi0 : u.1 ≠ 0)
    (hsum : u.1 + u.2 ≠ (1 : ZMod m)) :
    ((fullMap0CaseI (m := m)^[3]) (slicePoint (0 : ZMod m) u)) =
      ((u.1 + 1, u.2 + 1), (3 : ZMod m)) := by
  calc
    ((fullMap0CaseI (m := m)^[3]) (slicePoint (0 : ZMod m) u))
        = ((fullMap0CaseI (m := m)^[2]) (u, (1 : ZMod m))) := by
            rw [Function.iterate_succ_apply']
            simpa using congrArg (fun z => (fullMap0CaseI (m := m)^[2]) z)
              (fullMap0CaseI_step_zero_of_dir1 (m := m) hdir)
    _ = fullMap0CaseI (m := m) ((u.1, u.2 + 1), (2 : ZMod m)) := by
          rw [Function.iterate_succ_apply']
          simpa using congrArg (fullMap0CaseI (m := m))
            (fullMap0CaseI_step_one_of_i_ne_zero (m := m) (i := u.1) (k := u.2) hi0)
    _ = ((u.1 + 1, u.2 + 1), (3 : ZMod m)) := by
          have hsum' : u.1 + (u.2 + 1) ≠ (2 : ZMod m) := by
            intro h
            apply hsum
            calc
              u.1 + u.2 = (u.1 + (u.2 + 1)) - 1 := by ring
              _ = (1 : ZMod m) := by rw [h]; ring
          simpa [add_assoc] using fullMap0CaseI_step_two_of_sum_ne_two (m := m)
            (i := u.1) (k := u.2 + 1) hsum'

theorem iterate_three_fullMap0CaseI_neg_one_one [Fact (4 < m)] :
    ((fullMap0CaseI (m := m)^[3]) (slicePoint (0 : ZMod m) ((-1 : ZMod m), (1 : ZMod m)))) =
      (((1 : ZMod m), (1 : ZMod m)), (3 : ZMod m)) := by
  calc
    ((fullMap0CaseI (m := m)^[3]) (slicePoint (0 : ZMod m) ((-1 : ZMod m), (1 : ZMod m))))
        = ((fullMap0CaseI (m := m)^[2]) (((0 : ZMod m), (1 : ZMod m)), (1 : ZMod m))) := by
            rw [Function.iterate_succ_apply']
            simpa using congrArg (fun z => (fullMap0CaseI (m := m)^[2]) z)
              (fullMap0CaseI_step_zero_of_dir0 (m := m)
                (u := ((-1 : ZMod m), (1 : ZMod m))) (dir0CaseILayerZero_neg_one_one (m := m)))
    _ = fullMap0CaseI (m := m) (((0 : ZMod m), (1 : ZMod m)), (2 : ZMod m)) := by
          rw [Function.iterate_succ_apply']
          simpa using congrArg (fullMap0CaseI (m := m))
            (fullMap0CaseI_step_one_of_i_zero (m := m) (k := (1 : ZMod m)))
    _ = (((1 : ZMod m), (1 : ZMod m)), (3 : ZMod m)) := by
          have hsum : ((0 : ZMod m) + (1 : ZMod m)) ≠ (2 : ZMod m) := by
            intro h
            exact two_ne_one (m := m) (by simpa using h.symm)
          simpa using fullMap0CaseI_step_two_of_sum_ne_two (m := m)
            (i := (0 : ZMod m)) (k := (1 : ZMod m)) hsum

theorem iterate_three_fullMap0CaseI_of_dir2_i_zero_generic [Fact (4 < m)] {k : ZMod m}
    (hdir : dir0CaseILayerZero (m := m) ((0 : ZMod m), k) = 2)
    (hk1 : k ≠ (1 : ZMod m)) :
    ((fullMap0CaseI (m := m)^[3]) (slicePoint (0 : ZMod m) ((0 : ZMod m), k))) =
      (((1 : ZMod m), k + 1), (3 : ZMod m)) := by
  calc
    ((fullMap0CaseI (m := m)^[3]) (slicePoint (0 : ZMod m) ((0 : ZMod m), k)))
        = ((fullMap0CaseI (m := m)^[2]) (((0 : ZMod m), k + 1), (1 : ZMod m))) := by
            rw [Function.iterate_succ_apply']
            simpa using congrArg (fun z => (fullMap0CaseI (m := m)^[2]) z)
              (fullMap0CaseI_step_zero_of_dir2 (m := m) (u := ((0 : ZMod m), k)) hdir)
    _ = fullMap0CaseI (m := m) (((0 : ZMod m), k + 1), (2 : ZMod m)) := by
          rw [Function.iterate_succ_apply']
          simpa using congrArg (fullMap0CaseI (m := m))
            (fullMap0CaseI_step_one_of_i_zero (m := m) (k := k + 1))
    _ = (((1 : ZMod m), k + 1), (3 : ZMod m)) := by
          have hsum : ((0 : ZMod m) + (k + 1)) ≠ (2 : ZMod m) := by
            intro h
            apply hk1
            calc
              k = ((0 : ZMod m) + (k + 1)) - 1 := by ring
              _ = (1 : ZMod m) := by rw [h]; ring
          simpa using fullMap0CaseI_step_two_of_sum_ne_two (m := m)
            (i := (0 : ZMod m)) (k := k + 1) hsum

theorem iterate_three_fullMap0CaseI_zero_one [Fact (4 < m)] :
    ((fullMap0CaseI (m := m)^[3]) (slicePoint (0 : ZMod m) ((0 : ZMod m), (1 : ZMod m)))) =
      (((0 : ZMod m), (3 : ZMod m)), (3 : ZMod m)) := by
  calc
    ((fullMap0CaseI (m := m)^[3]) (slicePoint (0 : ZMod m) ((0 : ZMod m), (1 : ZMod m))))
        = ((fullMap0CaseI (m := m)^[2]) (((0 : ZMod m), (2 : ZMod m)), (1 : ZMod m))) := by
            rw [Function.iterate_succ_apply']
            have hdir : dir0CaseILayerZero (m := m) ((0 : ZMod m), (1 : ZMod m)) = 2 := by
              exact dir0CaseILayerZero_eq_two_of_i_zero (m := m) (k := (1 : ZMod m))
                (by exact one_ne_zero (m := m)) (by
                  intro h
                  exact one_ne_neg_one (m := m) h)
            calc
              ((fullMap0CaseI (m := m)^[2]) (fullMap0CaseI (m := m)
                  (slicePoint (0 : ZMod m) ((0 : ZMod m), (1 : ZMod m)))))
                  = ((fullMap0CaseI (m := m)^[2]) (((0 : ZMod m), (1 : ZMod m) + 1), (1 : ZMod m))) := by
                      simpa using congrArg (fun z => (fullMap0CaseI (m := m)^[2]) z)
                        (fullMap0CaseI_step_zero_of_dir2 (m := m)
                          (u := ((0 : ZMod m), (1 : ZMod m))) hdir)
              _ = ((fullMap0CaseI (m := m)^[2]) (((0 : ZMod m), (2 : ZMod m)), (1 : ZMod m))) := by
                    ext <;> ring
    _ = fullMap0CaseI (m := m) (((0 : ZMod m), (2 : ZMod m)), (2 : ZMod m)) := by
          rw [Function.iterate_succ_apply']
          simpa using congrArg (fullMap0CaseI (m := m))
            (fullMap0CaseI_step_one_of_i_zero (m := m) (k := (2 : ZMod m)))
    _ = (((0 : ZMod m), (3 : ZMod m)), (3 : ZMod m)) := by
          have hsum : ((0 : ZMod m) + (2 : ZMod m)) = (2 : ZMod m) := by ring
          calc
            fullMap0CaseI (m := m) ((0, (2 : ZMod m)), (2 : ZMod m))
                = (((0 : ZMod m), (2 : ZMod m) + 1), (3 : ZMod m)) := by
                    exact fullMap0CaseI_step_two_of_sum_two (m := m)
                      (i := (0 : ZMod m)) (k := (2 : ZMod m)) hsum
            _ = (((0 : ZMod m), (3 : ZMod m)), (3 : ZMod m)) := by
                  ext <;> ring

theorem iterate_three_fullMap0CaseI_of_dir2_i_ne_zero_sum_zero [Fact (4 < m)] {u : P0Coord m}
    (hdir : dir0CaseILayerZero (m := m) u = 2)
    (hi0 : u.1 ≠ 0)
    (hsum0 : u.1 + u.2 = 0) :
    ((fullMap0CaseI (m := m)^[3]) (slicePoint (0 : ZMod m) u)) =
      ((u.1, u.2 + 3), (3 : ZMod m)) := by
  calc
    ((fullMap0CaseI (m := m)^[3]) (slicePoint (0 : ZMod m) u))
        = ((fullMap0CaseI (m := m)^[2]) ((u.1, u.2 + 1), (1 : ZMod m))) := by
            rw [Function.iterate_succ_apply']
            simpa using congrArg (fun z => (fullMap0CaseI (m := m)^[2]) z)
              (fullMap0CaseI_step_zero_of_dir2 (m := m) hdir)
    _ = fullMap0CaseI (m := m) ((u.1, u.2 + 2), (2 : ZMod m)) := by
          rw [Function.iterate_succ_apply']
          calc
            fullMap0CaseI (m := m) (fullMap0CaseI (m := m) ((u.1, u.2 + 1), (1 : ZMod m)))
                = fullMap0CaseI (m := m) ((u.1, (u.2 + 1) + 1), (2 : ZMod m)) := by
                    simpa using congrArg (fullMap0CaseI (m := m))
                      (fullMap0CaseI_step_one_of_i_ne_zero (m := m)
                        (i := u.1) (k := u.2 + 1) hi0)
            _ = fullMap0CaseI (m := m) ((u.1, u.2 + 2), (2 : ZMod m)) := by
                  have hpair :
                      ((u.1, (u.2 + 1) + 1), (2 : ZMod m)) =
                        ((u.1, u.2 + 2), (2 : ZMod m)) := by
                    ext <;> ring
                  rw [hpair]
    _ = ((u.1, u.2 + 3), (3 : ZMod m)) := by
          have hsum' : u.1 + (u.2 + 2) = (2 : ZMod m) := by
            calc
              u.1 + (u.2 + 2) = (u.1 + u.2) + 2 := by ring
              _ = (2 : ZMod m) := by rw [hsum0]; ring
          calc
            fullMap0CaseI (m := m) ((u.1, u.2 + 2), (2 : ZMod m))
                = ((u.1, (u.2 + 2) + 1), (3 : ZMod m)) := by
                    exact fullMap0CaseI_step_two_of_sum_two (m := m)
                      (i := u.1) (k := u.2 + 2) hsum'
            _ = ((u.1, u.2 + 3), (3 : ZMod m)) := by
                  ext <;> ring

theorem iterate_three_fullMap0CaseI_of_dir2_i_ne_zero_generic [Fact (4 < m)] {u : P0Coord m}
    (hdir : dir0CaseILayerZero (m := m) u = 2)
    (hi0 : u.1 ≠ 0)
    (hsum0 : u.1 + u.2 ≠ 0) :
    ((fullMap0CaseI (m := m)^[3]) (slicePoint (0 : ZMod m) u)) =
      ((u.1 + 1, u.2 + 2), (3 : ZMod m)) := by
  calc
    ((fullMap0CaseI (m := m)^[3]) (slicePoint (0 : ZMod m) u))
        = ((fullMap0CaseI (m := m)^[2]) ((u.1, u.2 + 1), (1 : ZMod m))) := by
            rw [Function.iterate_succ_apply']
            simpa using congrArg (fun z => (fullMap0CaseI (m := m)^[2]) z)
              (fullMap0CaseI_step_zero_of_dir2 (m := m) hdir)
    _ = fullMap0CaseI (m := m) ((u.1, u.2 + 2), (2 : ZMod m)) := by
          rw [Function.iterate_succ_apply']
          calc
            fullMap0CaseI (m := m) (fullMap0CaseI (m := m) ((u.1, u.2 + 1), (1 : ZMod m)))
                = fullMap0CaseI (m := m) ((u.1, (u.2 + 1) + 1), (2 : ZMod m)) := by
                    simpa using congrArg (fullMap0CaseI (m := m))
                      (fullMap0CaseI_step_one_of_i_ne_zero (m := m)
                        (i := u.1) (k := u.2 + 1) hi0)
            _ = fullMap0CaseI (m := m) ((u.1, u.2 + 2), (2 : ZMod m)) := by
                  have hpair :
                      ((u.1, (u.2 + 1) + 1), (2 : ZMod m)) =
                        ((u.1, u.2 + 2), (2 : ZMod m)) := by
                    ext <;> ring
                  rw [hpair]
    _ = ((u.1 + 1, u.2 + 2), (3 : ZMod m)) := by
          have hsum' : u.1 + (u.2 + 2) ≠ (2 : ZMod m) := by
            intro h
            apply hsum0
            calc
              u.1 + u.2 = (u.1 + (u.2 + 2)) - 2 := by ring
              _ = 0 := by rw [h]; ring
          calc
            fullMap0CaseI (m := m) ((u.1, u.2 + 2), (2 : ZMod m))
                = (((u.1 + 1), u.2 + 2), (3 : ZMod m)) := by
                    exact fullMap0CaseI_step_two_of_sum_ne_two (m := m)
                      (i := u.1) (k := u.2 + 2) hsum'
            _ = ((u.1 + 1, u.2 + 2), (3 : ZMod m)) := by rfl

theorem iterate_m_fullMap0CaseI_of_three [Fact (4 < m)] {u v : P0Coord m}
    (h3 : ((fullMap0CaseI (m := m)^[3]) (slicePoint (0 : ZMod m) u)) = (v, (3 : ZMod m))) :
    ((fullMap0CaseI (m := m)^[m]) (slicePoint (0 : ZMod m) u)) =
      slicePoint (0 : ZMod m) (v.1 - 3, v.2) := by
  have hm3 : 3 ≤ m := by
    have hm4 : 4 < m := Fact.out
    omega
  calc
    ((fullMap0CaseI (m := m)^[m]) (slicePoint (0 : ZMod m) u))
        = ((fullMap0CaseI (m := m)^[m - 3])
            (((fullMap0CaseI (m := m)^[3]) (slicePoint (0 : ZMod m) u)))) := by
              simpa [Nat.sub_add_cancel hm3] using
                (Function.iterate_add_apply (f := fullMap0CaseI (m := m)) (m := m - 3) (n := 3)
                  (slicePoint (0 : ZMod m) u))
    _ = ((fullMap0CaseI (m := m)^[m - 3]) (v, (3 : ZMod m))) := by rw [h3]
    _ = slicePoint (0 : ZMod m) (v.1 - 3, v.2) := iterate_m_sub_three_fullMap0CaseI (m := m) v

theorem returnMap0CaseI_zero_neg_one [Fact (4 < m)] :
    returnMap0CaseI (m := m) ((0 : ZMod m), (-1 : ZMod m)) = ((-1 : ZMod m), (0 : ZMod m)) := by
  have h00' : ¬ ((0 : ZMod m) = 0 ∧ (-1 : ZMod m) = 0) := by
    intro h
    exact neg_ne_zero.mpr (one_ne_zero (m := m)) h.2
  have h1neg1' : ¬ ((0 : ZMod m) = (1 : ZMod m) ∧ (-1 : ZMod m) = (-1 : ZMod m)) := by
    intro h
    exact one_ne_zero (m := m) (by simpa using h.1.symm)
  have hneg20' : ¬ ((0 : ZMod m) = (-2 : ZMod m) ∧ (-1 : ZMod m) = 0) := by
    intro h
    exact neg_ne_zero.mpr (one_ne_zero (m := m)) h.2
  have hneg11' : ¬ ((0 : ZMod m) = (-1 : ZMod m) ∧ (-1 : ZMod m) = (1 : ZMod m)) := by
    intro h
    exact one_ne_neg_one (m := m) h.2.symm
  have hdiag : ¬ (((0 : ZMod m) + (-1 : ZMod m) = (1 : ZMod m)) ∧
      ¬ ((0 : ZMod m) = (1 : ZMod m) ∧ (-1 : ZMod m) = 0)) := by
    intro h
    exact one_ne_neg_one (m := m) (by simpa using h.1.symm)
  have hA :
      (((-1 : ZMod m) = 0 ∧ (0 : ZMod m) ≠ 0 ∧ (0 : ZMod m) ≠ (-2 : ZMod m) ∧
          (0 : ZMod m) ≠ (-1 : ZMod m))) ∨
        ((0 : ZMod m) = 0 ∧ (-1 : ZMod m) = (-1 : ZMod m)) ∨
        ((0 : ZMod m) = (-2 : ZMod m) ∧ (-1 : ZMod m) = (1 : ZMod m)) := by
    right
    left
    exact ⟨rfl, rfl⟩
  unfold returnMap0CaseI
  rw [if_neg h00', if_neg h1neg1', if_neg hneg20', if_neg hneg11', if_neg hdiag, if_pos hA]
  ext <;> ring

theorem returnMap0CaseI_zero_one [Fact (4 < m)] :
    returnMap0CaseI (m := m) ((0 : ZMod m), (1 : ZMod m)) = ((-3 : ZMod m), (3 : ZMod m)) := by
  have h00' : ¬ ((0 : ZMod m) = 0 ∧ (1 : ZMod m) = 0) := by
    intro h
    exact one_ne_zero (m := m) h.2
  have h1neg1' : ¬ ((0 : ZMod m) = (1 : ZMod m) ∧ (1 : ZMod m) = (-1 : ZMod m)) := by
    intro h
    exact one_ne_zero (m := m) (by simpa using h.1.symm)
  have hneg20' : ¬ ((0 : ZMod m) = (-2 : ZMod m) ∧ (1 : ZMod m) = 0) := by
    intro h
    exact one_ne_zero (m := m) h.2
  have hneg11' : ¬ ((0 : ZMod m) = (-1 : ZMod m) ∧ (1 : ZMod m) = (1 : ZMod m)) := by
    intro h
    exact neg_ne_zero.mpr (one_ne_zero (m := m)) (by simpa using h.1)
  have hdiag : ((0 : ZMod m) + (1 : ZMod m) = (1 : ZMod m)) ∧
      ¬ ((0 : ZMod m) = (1 : ZMod m) ∧ (1 : ZMod m) = 0) := by
    refine ⟨by ring, ?_⟩
    intro h
    exact one_ne_zero (m := m) h.2
  unfold returnMap0CaseI
  rw [if_neg h00', if_neg h1neg1', if_neg hneg20', if_neg hneg11', if_pos hdiag]
  ext <;> ring

theorem returnMap0CaseI_i_zero_generic [Fact (4 < m)] {k : ZMod m}
    (hk0 : k ≠ 0) (hkneg1 : k ≠ (-1 : ZMod m)) (hk1 : k ≠ (1 : ZMod m)) :
    returnMap0CaseI (m := m) ((0 : ZMod m), k) = ((-2 : ZMod m), k + 1) := by
  have h00' : ¬ ((0 : ZMod m) = 0 ∧ k = 0) := by
    intro h
    exact hk0 h.2
  have h1neg1' : ¬ ((0 : ZMod m) = (1 : ZMod m) ∧ k = (-1 : ZMod m)) := by
    intro h
    exact one_ne_zero (m := m) (by simpa using h.1.symm)
  have hneg20' : ¬ ((0 : ZMod m) = (-2 : ZMod m) ∧ k = 0) := by
    intro h
    exact hk0 h.2
  have hneg11' : ¬ ((0 : ZMod m) = (-1 : ZMod m) ∧ k = (1 : ZMod m)) := by
    intro h
    exact hk1 h.2
  have hdiag : ¬ (((0 : ZMod m) + k = (1 : ZMod m)) ∧
      ¬ ((0 : ZMod m) = (1 : ZMod m) ∧ k = 0)) := by
    intro h
    exact hk1 (by simpa using h.1)
  have hA :
      ¬ (((k = 0 ∧ (0 : ZMod m) ≠ 0 ∧ (0 : ZMod m) ≠ (-2 : ZMod m) ∧ (0 : ZMod m) ≠ (-1 : ZMod m))) ∨
          ((0 : ZMod m) = 0 ∧ k = (-1 : ZMod m)) ∨
          ((0 : ZMod m) = (-2 : ZMod m) ∧ k = (1 : ZMod m))) := by
    intro h
    rcases h with h0 | hneg1 | h1
    · exact hk0 h0.1
    · exact hkneg1 hneg1.2
    · exact hk1 h1.2
  unfold returnMap0CaseI
  rw [if_neg h00', if_neg h1neg1', if_neg hneg20', if_neg hneg11', if_neg hdiag, if_neg hA]
  ext <;> ring

theorem iterate_m_fullMap0CaseI_i_zero_of_ne_zero [Fact (4 < m)] {k : ZMod m} (hk0 : k ≠ 0) :
    ((fullMap0CaseI (m := m)^[m]) (slicePoint (0 : ZMod m) ((0 : ZMod m), k))) =
      slicePoint (0 : ZMod m) (returnMap0CaseI (m := m) ((0 : ZMod m), k)) := by
  by_cases hkneg1 : k = (-1 : ZMod m)
  · subst hkneg1
    have hdir : dir0CaseILayerZero (m := m) ((0 : ZMod m), (-1 : ZMod m)) = 0 := by
      simp [dir0CaseILayerZero, one_ne_zero (m := m), two_ne_zero (m := m)]
    have h3 := iterate_three_fullMap0CaseI_of_dir0_generic (m := m)
      (u := ((0 : ZMod m), (-1 : ZMod m))) hdir (by
        intro h
        exact neg_ne_zero.mpr (one_ne_zero (m := m)) h.symm)
    have hmain := iterate_m_fullMap0CaseI_of_three (m := m)
      (u := ((0 : ZMod m), (-1 : ZMod m)))
      (v := (((0 : ZMod m) + 2), ((-1 : ZMod m) + 1))) h3
    calc
      ((fullMap0CaseI (m := m)^[m]) (slicePoint (0 : ZMod m) ((0 : ZMod m), (-1 : ZMod m))))
          = slicePoint (0 : ZMod m)
              ((((0 : ZMod m) + 2, (-1 : ZMod m) + 1).1 - 3),
                (((0 : ZMod m) + 2, (-1 : ZMod m) + 1).2)) := hmain
      _ = slicePoint (0 : ZMod m) (((2 : ZMod m) - 3), (0 : ZMod m)) := by
            ext <;> ring
      _ = slicePoint (0 : ZMod m) ((-1 : ZMod m), (0 : ZMod m)) := by
            ext <;> ring
      _ = slicePoint (0 : ZMod m) (returnMap0CaseI (m := m) ((0 : ZMod m), (-1 : ZMod m))) := by
            rw [returnMap0CaseI_zero_neg_one (m := m)]
  · by_cases hk1 : k = (1 : ZMod m)
    · subst hk1
      have hmain := iterate_m_fullMap0CaseI_of_three (m := m)
        (u := ((0 : ZMod m), (1 : ZMod m))) (v := ((0 : ZMod m), (3 : ZMod m)))
        (iterate_three_fullMap0CaseI_zero_one (m := m))
      calc
        ((fullMap0CaseI (m := m)^[m]) (slicePoint (0 : ZMod m) ((0 : ZMod m), (1 : ZMod m))))
            = slicePoint (0 : ZMod m) (((0 : ZMod m) - 3), (3 : ZMod m)) := hmain
        _ = slicePoint (0 : ZMod m) ((-3 : ZMod m), (3 : ZMod m)) := by
              ext <;> ring
        _ = slicePoint (0 : ZMod m) (returnMap0CaseI (m := m) ((0 : ZMod m), (1 : ZMod m))) := by
              rw [returnMap0CaseI_zero_one (m := m)]
    · have hdir : dir0CaseILayerZero (m := m) ((0 : ZMod m), k) = 2 :=
        dir0CaseILayerZero_eq_two_of_i_zero (m := m) hk0 hkneg1
      have h3 := iterate_three_fullMap0CaseI_of_dir2_i_zero_generic (m := m)
        (k := k) hdir hk1
      have hmain := iterate_m_fullMap0CaseI_of_three (m := m)
        (u := ((0 : ZMod m), k)) (v := ((1 : ZMod m), k + 1)) h3
      calc
        ((fullMap0CaseI (m := m)^[m]) (slicePoint (0 : ZMod m) ((0 : ZMod m), k)))
            = slicePoint (0 : ZMod m) (((1 : ZMod m) - 3), k + 1) := hmain
        _ = slicePoint (0 : ZMod m) ((-2 : ZMod m), k + 1) := by
              ext <;> ring
        _ = slicePoint (0 : ZMod m) (returnMap0CaseI (m := m) ((0 : ZMod m), k)) := by
              rw [returnMap0CaseI_i_zero_generic (m := m) hk0 hkneg1 hk1]

theorem iterate_m_fullMap0CaseI_slicePoint_zero [Fact (4 < m)] (u : P0Coord m) :
    ((fullMap0CaseI (m := m)^[m]) (slicePoint (0 : ZMod m) u)) =
      slicePoint (0 : ZMod m) (returnMap0CaseI (m := m) u) := by
  rcases u with ⟨i, k⟩
  by_cases h00 : i = 0 ∧ k = 0
  · rcases h00 with ⟨hi0, hk0⟩
    subst hi0
    subst hk0
    have hmain := iterate_m_fullMap0CaseI_of_three (m := m)
      (u := ((0 : ZMod m), (0 : ZMod m))) (v := ((1 : ZMod m), (0 : ZMod m)))
      (iterate_three_fullMap0CaseI_origin (m := m))
    calc
      ((fullMap0CaseI (m := m)^[m]) (slicePoint (0 : ZMod m) ((0 : ZMod m), (0 : ZMod m))))
          = slicePoint (0 : ZMod m) (((1 : ZMod m) - 3), (0 : ZMod m)) := hmain
      _ = slicePoint (0 : ZMod m) ((-2 : ZMod m), (0 : ZMod m)) := by
            ext <;> ring
      _ = slicePoint (0 : ZMod m) (returnMap0CaseI (m := m) ((0 : ZMod m), (0 : ZMod m))) := by
            simp [returnMap0CaseI]
  by_cases h1neg1 : i = (1 : ZMod m) ∧ k = (-1 : ZMod m)
  · rcases h1neg1 with ⟨hi1, hkneg1⟩
    subst hi1
    subst hkneg1
    have hdir : dir0CaseILayerZero (m := m) ((1 : ZMod m), (-1 : ZMod m)) = 2 :=
      dir0CaseILayerZero_one_neg_one (m := m)
    have h3 := iterate_three_fullMap0CaseI_of_dir2_i_ne_zero_sum_zero (m := m)
      (u := ((1 : ZMod m), (-1 : ZMod m))) hdir (one_ne_zero (m := m)) (by ring)
    have hmain := iterate_m_fullMap0CaseI_of_three (m := m)
      (u := ((1 : ZMod m), (-1 : ZMod m))) (v := ((1 : ZMod m), (-1 : ZMod m) + 3)) h3
    calc
      ((fullMap0CaseI (m := m)^[m]) (slicePoint (0 : ZMod m) ((1 : ZMod m), (-1 : ZMod m))))
          = slicePoint (0 : ZMod m) (((1 : ZMod m) - 3), ((-1 : ZMod m) + 3)) := hmain
      _ = slicePoint (0 : ZMod m) ((-2 : ZMod m), (2 : ZMod m)) := by
            ext <;> ring
      _ = slicePoint (0 : ZMod m) (returnMap0CaseI (m := m) ((1 : ZMod m), (-1 : ZMod m))) := by
            simp [returnMap0CaseI]
  by_cases hneg20 : i = (-2 : ZMod m) ∧ k = 0
  · rcases hneg20 with ⟨hineg2, hk0⟩
    subst hineg2
    subst hk0
    have hdir : dir0CaseILayerZero (m := m) ((-2 : ZMod m), (0 : ZMod m)) = 2 :=
      dir0CaseILayerZero_neg_two_zero (m := m)
    have hi0' : (-2 : ZMod m) ≠ 0 := by
      intro h
      exact two_ne_zero (m := m) (by simpa using congrArg Neg.neg h)
    have hsum0' : (-2 : ZMod m) + (0 : ZMod m) ≠ 0 := by
      simpa using hi0'
    have h3 := iterate_three_fullMap0CaseI_of_dir2_i_ne_zero_generic (m := m)
      (u := ((-2 : ZMod m), (0 : ZMod m))) hdir
      hi0' hsum0'
    have hmain := iterate_m_fullMap0CaseI_of_three (m := m)
      (u := ((-2 : ZMod m), (0 : ZMod m))) (v := (((-2 : ZMod m) + 1), (0 : ZMod m) + 2)) h3
    have hne1 : (-2 : ZMod m) ≠ (1 : ZMod m) := by
      intro h
      exact one_ne_neg_two_case0 (m := m) h.symm
    have hret :
        returnMap0CaseI (m := m) ((-2 : ZMod m), (0 : ZMod m)) = ((-4 : ZMod m), (2 : ZMod m)) := by
      simp [returnMap0CaseI, hi0', hne1]
    calc
      ((fullMap0CaseI (m := m)^[m]) (slicePoint (0 : ZMod m) ((-2 : ZMod m), (0 : ZMod m))))
          = slicePoint (0 : ZMod m) ((((-2 : ZMod m) + 1) - 3), ((0 : ZMod m) + 2)) := hmain
      _ = slicePoint (0 : ZMod m) ((-4 : ZMod m), (2 : ZMod m)) := by
            ext <;> ring
      _ = slicePoint (0 : ZMod m) (returnMap0CaseI (m := m) ((-2 : ZMod m), (0 : ZMod m))) := by
            rw [hret]
  by_cases hneg11 : i = (-1 : ZMod m) ∧ k = (1 : ZMod m)
  · rcases hneg11 with ⟨hineg1, hk1⟩
    subst hineg1
    subst hk1
    have hmain := iterate_m_fullMap0CaseI_of_three (m := m)
      (u := ((-1 : ZMod m), (1 : ZMod m))) (v := ((1 : ZMod m), (1 : ZMod m)))
      (iterate_three_fullMap0CaseI_neg_one_one (m := m))
    have hneg10 : (-1 : ZMod m) ≠ 0 := by
      exact neg_ne_zero.mpr (one_ne_zero (m := m))
    have hneg11' : (-1 : ZMod m) ≠ (1 : ZMod m) := by
      intro h
      exact one_ne_neg_one (m := m) h.symm
    have hret :
        returnMap0CaseI (m := m) ((-1 : ZMod m), (1 : ZMod m)) = ((-2 : ZMod m), (1 : ZMod m)) := by
      simp [returnMap0CaseI, hneg10, hneg11']
    calc
      ((fullMap0CaseI (m := m)^[m]) (slicePoint (0 : ZMod m) ((-1 : ZMod m), (1 : ZMod m))))
          = slicePoint (0 : ZMod m) (((1 : ZMod m) - 3), (1 : ZMod m)) := hmain
      _ = slicePoint (0 : ZMod m) ((-2 : ZMod m), (1 : ZMod m)) := by
            ext <;> ring
      _ = slicePoint (0 : ZMod m) (returnMap0CaseI (m := m) ((-1 : ZMod m), (1 : ZMod m))) := by
            rw [hret]
  by_cases hi0 : i = 0
  · subst hi0
    have hk0 : k ≠ 0 := by
      intro hk0
      exact h00 ⟨rfl, hk0⟩
    exact iterate_m_fullMap0CaseI_i_zero_of_ne_zero (m := m) hk0
  · by_cases hA :
        (k = 0 ∧ i ≠ 0 ∧ i ≠ (-2 : ZMod m) ∧ i ≠ (-1 : ZMod m)) ∨
          (i = 0 ∧ k = (-1 : ZMod m)) ∨
          (i = (-1 : ZMod m) ∧ k = (1 : ZMod m)) ∨
          (i = (-2 : ZMod m) ∧ k = (1 : ZMod m))
    · have hdir : dir0CaseILayerZero (m := m) (i, k) = 0 := by
        simp [dir0CaseILayerZero, hA]
      have hineg1 : i ≠ (-1 : ZMod m) := by
        intro hi
        subst hi
        rcases hA with hzero | h0neg | hneg1 | hneg2
        · exact hzero.2.2.2 rfl
        · exact hi0 h0neg.1
        · exact hneg11 hneg1
        · have h21 : (1 : ZMod m) = (2 : ZMod m) := by
            simpa using congrArg Neg.neg hneg2.1
          exact two_ne_one (m := m) h21.symm
      have h3 := iterate_three_fullMap0CaseI_of_dir0_generic (m := m)
        (u := (i, k)) hdir hineg1
      have hmain := iterate_m_fullMap0CaseI_of_three (m := m)
        (u := (i, k)) (v := (i + 2, k + 1)) h3
      have hdiag' : ¬ (i + k = (1 : ZMod m) ∧ ¬ (i = (1 : ZMod m) ∧ k = 0)) := by
        intro hd
        rcases hA with hzero | h0neg | hneg1 | hneg2
        · rcases hzero with ⟨hk0, _, _, _⟩
          have hi1 : i = (1 : ZMod m) := by
            simpa [hk0] using hd.1
          exact hd.2 ⟨hi1, hk0⟩
        · exact hi0 h0neg.1
        · exact hneg11 hneg1
        · have hne : (-1 : ZMod m) = (1 : ZMod m) := by
            calc
              (-1 : ZMod m) = i + k := by rw [hneg2.1, hneg2.2]; ring
              _ = (1 : ZMod m) := hd.1
          exact one_ne_neg_one (m := m) hne.symm
      have hAret :
          (k = 0 ∧ i ≠ 0 ∧ i ≠ (-2 : ZMod m) ∧ i ≠ (-1 : ZMod m)) ∨
            (i = 0 ∧ k = (-1 : ZMod m)) ∨
            (i = (-2 : ZMod m) ∧ k = (1 : ZMod m)) := by
        rcases hA with hzero | h0neg | hneg1 | hneg2
        · exact Or.inl hzero
        · exact Or.inr (Or.inl h0neg)
        · exact False.elim (hneg11 hneg1)
        · exact Or.inr (Or.inr hneg2)
      have hret : returnMap0CaseI (m := m) (i, k) = (i - 1, k + 1) := by
        unfold returnMap0CaseI
        rw [if_neg h00, if_neg h1neg1, if_neg hneg20, if_neg hneg11, if_neg hdiag', if_pos hAret]
      calc
        ((fullMap0CaseI (m := m)^[m]) (slicePoint (0 : ZMod m) (i, k)))
            = slicePoint (0 : ZMod m) ((i + 2) - 3, k + 1) := hmain
        _ = slicePoint (0 : ZMod m) (i - 1, k + 1) := by
              have hpair : (((i + 2) - 3, k + 1) : P0Coord m) = (i - 1, k + 1) := by
                ext <;> ring
              rw [hpair]
        _ = slicePoint (0 : ZMod m) (returnMap0CaseI (m := m) (i, k)) := by
              rw [hret]

    · by_cases hdiag : i + k = (1 : ZMod m) ∧ ¬ (i = (1 : ZMod m) ∧ k = 0)
      · have hB : ¬ ((i = 0 ∧ k ≠ 0 ∧ k ≠ (-1 : ZMod m)) ∨
            (i = (1 : ZMod m) ∧ k = (-1 : ZMod m)) ∨
            (i = (-2 : ZMod m) ∧ k = 0)) := by
          intro hB
          rcases hB with hB0 | hB1 | hB2
          · exact hi0 hB0.1
          · exact h1neg1 hB1
          · exact hneg20 hB2
        have hdir : dir0CaseILayerZero (m := m) (i, k) = 1 := by
          simp [dir0CaseILayerZero, hA, hB]
        have h3 := iterate_three_fullMap0CaseI_of_dir1_sum_eq_one (m := m)
          (u := (i, k)) hdir hi0 hdiag.1
        have hmain := iterate_m_fullMap0CaseI_of_three (m := m)
          (u := (i, k)) (v := (i, k + 2)) h3
        simpa [slicePoint, returnMap0CaseI, h00, h1neg1, hneg20, hneg11, hdiag, hA] using hmain
      · have hB : ¬ ((i = 0 ∧ k ≠ 0 ∧ k ≠ (-1 : ZMod m)) ∨
            (i = (1 : ZMod m) ∧ k = (-1 : ZMod m)) ∨
            (i = (-2 : ZMod m) ∧ k = 0)) := by
          intro hB
          rcases hB with hB0 | hB1 | hB2
          · exact hi0 hB0.1
          · exact h1neg1 hB1
          · exact hneg20 hB2
        have hdir : dir0CaseILayerZero (m := m) (i, k) = 1 := by
          simp [dir0CaseILayerZero, hA, hB]
        have hsum : i + k ≠ (1 : ZMod m) := by
          intro hs
          apply hdiag
          refine ⟨hs, ?_⟩
          intro h10
          apply hA
          left
          refine ⟨h10.2, hi0, ?_, ?_⟩
          · rw [h10.1]
            exact one_ne_neg_two_case0 (m := m)
          · rw [h10.1]
            exact one_ne_neg_one (m := m)
        have h3 := iterate_three_fullMap0CaseI_of_dir1_generic (m := m)
          (u := (i, k)) hdir hi0 hsum
        have hmain := iterate_m_fullMap0CaseI_of_three (m := m)
          (u := (i, k)) (v := (i + 1, k + 1)) h3
        have hAret :
            ¬ ((k = 0 ∧ i ≠ 0 ∧ i ≠ (-2 : ZMod m) ∧ i ≠ (-1 : ZMod m)) ∨
                (i = 0 ∧ k = (-1 : ZMod m)) ∨
                (i = (-2 : ZMod m) ∧ k = (1 : ZMod m))) := by
          intro hAret
          rcases hAret with h0 | h1 | h2
          · exact hA (Or.inl h0)
          · exact hA (Or.inr (Or.inl h1))
          · exact hA (Or.inr (Or.inr (Or.inr h2)))
        have hret : returnMap0CaseI (m := m) (i, k) = (i - 2, k + 1) := by
          unfold returnMap0CaseI
          rw [if_neg h00, if_neg h1neg1, if_neg hneg20, if_neg hneg11, if_neg hdiag, if_neg hAret]
        calc
          ((fullMap0CaseI (m := m)^[m]) (slicePoint (0 : ZMod m) (i, k)))
              = slicePoint (0 : ZMod m) ((i + 1) - 3, k + 1) := hmain
          _ = slicePoint (0 : ZMod m) (i - 2, k + 1) := by
                have hpair : (((i + 1) - 3, k + 1) : P0Coord m) = (i - 2, k + 1) := by
                  ext <;> ring
                rw [hpair]
          _ = slicePoint (0 : ZMod m) (returnMap0CaseI (m := m) (i, k)) := by
                rw [hret]

def returnMap0CaseIXY (u : P0Coord m) : P0Coord m :=
  toXY (m := m) (returnMap0CaseI (m := m) (fromXY (m := m) u))

theorem toXY_linePoint0 (x : Fin m) :
    toXY (m := m) (linePoint0 (m := m) x) = linePoint0 (m := m) x := by
  ext <;> simp [toXY, linePoint0]

theorem fromXY_linePoint0 (x : Fin m) :
    fromXY (m := m) (linePoint0 (m := m) x) = linePoint0 (m := m) x := by
  ext <;> simp [fromXY, linePoint0]

theorem returnMap0CaseI_semiconj_xy :
    Function.Semiconj (xyEquiv (m := m)) (returnMap0CaseI (m := m)) (returnMap0CaseIXY (m := m)) := by
  intro u
  change toXY (m := m) (returnMap0CaseI (m := m) u) =
    toXY (m := m) (returnMap0CaseI (m := m) (fromXY (m := m) (toXY (m := m) u)))
  rw [fromXY_toXY]

theorem returnMap0CaseI_semiconj_xy_symm :
    Function.Semiconj (xyEquiv (m := m)).symm (returnMap0CaseIXY (m := m)) (returnMap0CaseI (m := m)) := by
  intro u
  change fromXY (m := m) (toXY (m := m) (returnMap0CaseI (m := m) (fromXY (m := m) u))) =
    returnMap0CaseI (m := m) (fromXY (m := m) u)
  simpa using fromXY_toXY (m := m) (returnMap0CaseI (m := m) (fromXY (m := m) u))

theorem returnMap0CaseIXY_zero_zero [Fact (4 < m)] :
    returnMap0CaseIXY (m := m) ((0 : ZMod m), (0 : ZMod m)) = ((-2 : ZMod m), (0 : ZMod m)) := by
  simp [returnMap0CaseIXY, toXY, fromXY, returnMap0CaseI]

theorem returnMap0CaseIXY_m_sub_two_zero [Fact (4 < m)] :
    returnMap0CaseIXY (m := m) ((-2 : ZMod m), (0 : ZMod m)) = ((0 : ZMod m), (2 : ZMod m)) := by
  have h20 : (2 : ZMod m) ≠ 0 := two_ne_zero (m := m)
  have hneg20 : (-2 : ZMod m) ≠ 0 := neg_ne_zero.mpr h20
  have hne1 : (-2 : ZMod m) ≠ (1 : ZMod m) := by
    intro h
    exact one_ne_neg_two_case0 (m := m) h.symm
  have hret : returnMap0CaseI (m := m) ((-2 : ZMod m), (0 : ZMod m)) = ((-4 : ZMod m), (2 : ZMod m)) := by
    simp [returnMap0CaseI, hneg20, hne1]
  calc
    returnMap0CaseIXY (m := m) ((-2 : ZMod m), (0 : ZMod m))
        = toXY (m := m) (returnMap0CaseI (m := m) ((-2 : ZMod m), (0 : ZMod m))) := by
            simp [returnMap0CaseIXY, fromXY]
    _ = toXY (m := m) ((-4 : ZMod m), (2 : ZMod m)) := by rw [hret]
    _ = ((0 : ZMod m), (2 : ZMod m)) := by
          ext <;> simp [toXY]
          ring_nf

theorem returnMap0CaseIXY_one_one [Fact (4 < m)] :
    returnMap0CaseIXY (m := m) ((1 : ZMod m), (1 : ZMod m)) = ((0 : ZMod m), (1 : ZMod m)) := by
  have h10 : (1 : ZMod m) ≠ 0 := one_ne_zero (m := m)
  have h1neg1 : (1 : ZMod m) ≠ (-1 : ZMod m) := one_ne_neg_one (m := m)
  have hfrom : fromXY (m := m) ((1 : ZMod m), (1 : ZMod m)) = ((-1 : ZMod m), (1 : ZMod m)) := by
    ext <;> simp [fromXY]
    ring
  have hret : returnMap0CaseI (m := m) ((-1 : ZMod m), (1 : ZMod m)) = ((-2 : ZMod m), (1 : ZMod m)) := by
    simp [returnMap0CaseI, h10, h1neg1]
  calc
    returnMap0CaseIXY (m := m) ((1 : ZMod m), (1 : ZMod m))
        = toXY (m := m) (returnMap0CaseI (m := m) ((-1 : ZMod m), (1 : ZMod m))) := by
            simp [returnMap0CaseIXY, hfrom]
    _ = toXY (m := m) ((-2 : ZMod m), (1 : ZMod m)) := by rw [hret]
    _ = ((0 : ZMod m), (1 : ZMod m)) := by
          ext <;> simp [toXY]

theorem returnMap0CaseIXY_m_sub_one_m_sub_one [Fact (4 < m)] :
    returnMap0CaseIXY (m := m) ((-1 : ZMod m), (-1 : ZMod m)) = ((2 : ZMod m), (2 : ZMod m)) := by
  have h10 : (1 : ZMod m) ≠ 0 := one_ne_zero (m := m)
  have hfrom : fromXY (m := m) ((-1 : ZMod m), (-1 : ZMod m)) = ((1 : ZMod m), (-1 : ZMod m)) := by
    ext <;> simp [fromXY]
    ring
  have hret : returnMap0CaseI (m := m) ((1 : ZMod m), (-1 : ZMod m)) = ((-2 : ZMod m), (2 : ZMod m)) := by
    simp [returnMap0CaseI, h10]
  calc
    returnMap0CaseIXY (m := m) ((-1 : ZMod m), (-1 : ZMod m))
        = toXY (m := m) (returnMap0CaseI (m := m) ((1 : ZMod m), (-1 : ZMod m))) := by
            simp [returnMap0CaseIXY, hfrom]
    _ = toXY (m := m) ((-2 : ZMod m), (2 : ZMod m)) := by rw [hret]
    _ = ((2 : ZMod m), (2 : ZMod m)) := by
          ext <;> simp [toXY]
          ring_nf

theorem returnMap0CaseIXY_zero_one [Fact (4 < m)] :
    returnMap0CaseIXY (m := m) ((0 : ZMod m), (1 : ZMod m)) = ((1 : ZMod m), (2 : ZMod m)) := by
  have h10 : (1 : ZMod m) ≠ 0 := one_ne_zero (m := m)
  have h20 : (2 : ZMod m) ≠ 0 := two_ne_zero (m := m)
  have h1neg2 : (1 : ZMod m) ≠ (-2 : ZMod m) := one_ne_neg_two_case0 (m := m)
  have hfrom : fromXY (m := m) ((0 : ZMod m), (1 : ZMod m)) = ((-2 : ZMod m), (1 : ZMod m)) := by
    ext <;> simp [fromXY]
  have h00 : ¬ (((-2 : ZMod m) = 0) ∧ ((1 : ZMod m) = 0)) := by
    intro h
    exact h20 (by simpa using congrArg Neg.neg h.1)
  have h1neg1' : ¬ (((-2 : ZMod m) = (1 : ZMod m)) ∧ ((1 : ZMod m) = (-1 : ZMod m))) := by
    intro h
    exact h1neg2 h.1.symm
  have hneg20' : ¬ (((-2 : ZMod m) = (-2 : ZMod m)) ∧ ((1 : ZMod m) = 0)) := by
    intro h
    exact one_ne_zero (m := m) h.2
  have hneg11' : ¬ (((-2 : ZMod m) = (-1 : ZMod m)) ∧ ((1 : ZMod m) = (1 : ZMod m))) := by
    intro h
    have : (2 : ZMod m) = (1 : ZMod m) := by
      simpa using congrArg Neg.neg h.1
    exact two_ne_one (m := m) this
  have hdiag : ¬ (((-2 : ZMod m) + (1 : ZMod m) = (1 : ZMod m)) ∧
      ¬ (((-2 : ZMod m) = (1 : ZMod m)) ∧ ((1 : ZMod m) = 0))) := by
    intro h
    have : (-1 : ZMod m) = (1 : ZMod m) := by
      calc
        (-1 : ZMod m) = (-2 : ZMod m) + (1 : ZMod m) := by ring
        _ = (1 : ZMod m) := h.1
    exact one_ne_neg_one (m := m) this.symm
  have hA :
      (((1 : ZMod m) = 0 ∧ (-2 : ZMod m) ≠ 0 ∧ (-2 : ZMod m) ≠ (-2 : ZMod m) ∧ (-2 : ZMod m) ≠ (-1 : ZMod m))) ∨
        (((-2 : ZMod m) = 0 ∧ (1 : ZMod m) = (-1 : ZMod m)) ∨
          (((-2 : ZMod m) = (-2 : ZMod m) ∧ (1 : ZMod m) = (1 : ZMod m)))) := by
    right
    right
    exact ⟨rfl, rfl⟩
  have hret : returnMap0CaseI (m := m) ((-2 : ZMod m), (1 : ZMod m)) = ((-3 : ZMod m), (2 : ZMod m)) := by
    unfold returnMap0CaseI
    rw [if_neg h00, if_neg h1neg1', if_neg hneg20', if_neg hneg11', if_neg hdiag, if_pos hA]
    ext <;> ring
  calc
    returnMap0CaseIXY (m := m) ((0 : ZMod m), (1 : ZMod m))
        = toXY (m := m) (returnMap0CaseI (m := m) ((-2 : ZMod m), (1 : ZMod m))) := by
            simp [returnMap0CaseIXY, hfrom]
    _ = toXY (m := m) ((-3 : ZMod m), (2 : ZMod m)) := by rw [hret]
    _ = ((1 : ZMod m), (2 : ZMod m)) := by
          ext <;> simp [toXY]
          ring_nf

theorem returnMap0CaseIXY_m_sub_two_m_sub_one [Fact (4 < m)] :
    returnMap0CaseIXY (m := m) ((-2 : ZMod m), (-1 : ZMod m)) = ((-1 : ZMod m), (0 : ZMod m)) := by
  have hfrom : fromXY (m := m) ((-2 : ZMod m), (-1 : ZMod m)) = ((0 : ZMod m), (-1 : ZMod m)) := by
    ext <;> simp [fromXY]
  calc
    returnMap0CaseIXY (m := m) ((-2 : ZMod m), (-1 : ZMod m))
        = toXY (m := m) (returnMap0CaseI (m := m) ((0 : ZMod m), (-1 : ZMod m))) := by
            simp [returnMap0CaseIXY, hfrom]
    _ = toXY (m := m) ((-1 : ZMod m), (0 : ZMod m)) := by
          rw [returnMap0CaseI_zero_neg_one (m := m)]
    _ = ((-1 : ZMod m), (0 : ZMod m)) := by
          ext <;> simp [toXY]

theorem returnMap0CaseIXY_line_generic [Fact (4 < m)] {x : ℕ}
    (hx1 : 1 ≤ x) (hxle : x ≤ m - 3) :
    returnMap0CaseIXY (m := m) ((((x : ℕ) : ZMod m)), (0 : ZMod m)) =
      ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m)) := by
  have hxm : x < m := by omega
  have hxm2 : x + 2 < m := by omega
  have hxm1 : x + 1 < m := by omega
  have hx0 : (((x : ℕ) : ZMod m)) ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := x) hx1 hxm
  have hxneg2 : (((x : ℕ) : ZMod m)) ≠ (-2 : ZMod m) := by
    exact natCast_ne_neg_two_of_lt (m := m) (n := x) hxm2
  have hxneg1 : (((x : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := x) hxm1
  have h00 : ¬ ((((x : ℕ) : ZMod m)) = 0 ∧ (0 : ZMod m) = 0) := by
    intro h
    exact hx0 h.1
  have h1neg1' : ¬ ((((x : ℕ) : ZMod m)) = (1 : ZMod m) ∧ (0 : ZMod m) = (-1 : ZMod m)) := by
    intro h
    exact neg_ne_zero.mpr (one_ne_zero (m := m)) h.2.symm
  have hneg20' : ¬ ((((x : ℕ) : ZMod m)) = (-2 : ZMod m) ∧ (0 : ZMod m) = 0) := by
    intro h
    exact hxneg2 h.1
  have hneg11' : ¬ ((((x : ℕ) : ZMod m)) = (-1 : ZMod m) ∧ (0 : ZMod m) = (1 : ZMod m)) := by
    intro h
    exact one_ne_zero (m := m) h.2.symm
  have hdiag : ¬ ((((x : ℕ) : ZMod m)) + (0 : ZMod m) = (1 : ZMod m) ∧
      ¬ ((((x : ℕ) : ZMod m)) = (1 : ZMod m) ∧ (0 : ZMod m) = 0)) := by
    intro h
    exact h.2 ⟨by simpa using h.1, rfl⟩
  have hA :
      (((0 : ZMod m) = 0 ∧ (((x : ℕ) : ZMod m)) ≠ 0 ∧ (((x : ℕ) : ZMod m)) ≠ (-2 : ZMod m) ∧
          (((x : ℕ) : ZMod m)) ≠ (-1 : ZMod m))) ∨
        ((((x : ℕ) : ZMod m)) = 0 ∧ (0 : ZMod m) = (-1 : ZMod m)) ∨
        ((((x : ℕ) : ZMod m)) = (-2 : ZMod m) ∧ (0 : ZMod m) = (1 : ZMod m)) := by
    left
    exact ⟨rfl, hx0, hxneg2, hxneg1⟩
  have hret :
      returnMap0CaseI (m := m) ((((x : ℕ) : ZMod m)), (0 : ZMod m)) =
        ((((x : ℕ) : ZMod m)) - 1, (1 : ZMod m)) := by
    unfold returnMap0CaseI
    rw [if_neg h00, if_neg h1neg1', if_neg hneg20', if_neg hneg11', if_neg hdiag, if_pos hA]
    ext <;> ring
  calc
    returnMap0CaseIXY (m := m) ((((x : ℕ) : ZMod m)), (0 : ZMod m))
        = toXY (m := m) (returnMap0CaseI (m := m) ((((x : ℕ) : ZMod m)), (0 : ZMod m))) := by
            simp [returnMap0CaseIXY, fromXY]
    _ = toXY (m := m) ((((x : ℕ) : ZMod m)) - 1, (1 : ZMod m)) := by rw [hret]
    _ = ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m)) := by
          ext <;> simp [toXY, Nat.cast_add]
          ring_nf

theorem returnMap0CaseIXY_m_sub_one_start [Fact (4 < m)] :
    returnMap0CaseIXY (m := m) ((-1 : ZMod m), (0 : ZMod m)) = ((-1 : ZMod m), (1 : ZMod m)) := by
  have h00 : ¬ (((-1 : ZMod m) = 0) ∧ ((0 : ZMod m) = 0)) := by
    intro h
    exact neg_ne_zero.mpr (one_ne_zero (m := m)) h.1
  have h1neg1' : ¬ (((-1 : ZMod m) = (1 : ZMod m)) ∧ ((0 : ZMod m) = (-1 : ZMod m))) := by
    intro h
    exact one_ne_neg_one (m := m) h.1.symm
  have hneg20' : ¬ (((-1 : ZMod m) = (-2 : ZMod m)) ∧ ((0 : ZMod m) = 0)) := by
    intro h
    have : (1 : ZMod m) = (2 : ZMod m) := by
      simpa using congrArg Neg.neg h.1
    exact two_ne_one (m := m) this.symm
  have hneg11' : ¬ (((-1 : ZMod m) = (-1 : ZMod m)) ∧ ((0 : ZMod m) = (1 : ZMod m))) := by
    intro h
    exact one_ne_zero (m := m) h.2.symm
  have hdiag : ¬ (((-1 : ZMod m) + (0 : ZMod m) = (1 : ZMod m)) ∧
      ¬ (((-1 : ZMod m) = (1 : ZMod m)) ∧ ((0 : ZMod m) = 0))) := by
    intro h
    exact one_ne_neg_one (m := m) (by simpa using h.1.symm)
  have hA :
      ¬ ((((0 : ZMod m) = 0 ∧ (-1 : ZMod m) ≠ 0 ∧ (-1 : ZMod m) ≠ (-2 : ZMod m) ∧
          (-1 : ZMod m) ≠ (-1 : ZMod m))) ∨
        (((-1 : ZMod m) = 0 ∧ (0 : ZMod m) = (-1 : ZMod m)) ∨
          (((-1 : ZMod m) = (-2 : ZMod m) ∧ (0 : ZMod m) = (1 : ZMod m))))) := by
    intro h
    rcases h with h0 | h1 | h2
    · exact h0.2.2.2 rfl
    · exact neg_ne_zero.mpr (one_ne_zero (m := m)) h1.1
    · exact one_ne_zero (m := m) h2.2.symm
  have hret :
      returnMap0CaseI (m := m) ((-1 : ZMod m), (0 : ZMod m)) = ((-3 : ZMod m), (1 : ZMod m)) := by
    unfold returnMap0CaseI
    rw [if_neg h00, if_neg h1neg1', if_neg hneg20', if_neg hneg11', if_neg hdiag, if_neg hA]
    ext <;> ring
  calc
    returnMap0CaseIXY (m := m) ((-1 : ZMod m), (0 : ZMod m))
        = toXY (m := m) (returnMap0CaseI (m := m) ((-1 : ZMod m), (0 : ZMod m))) := by
            simp [returnMap0CaseIXY, fromXY]
    _ = toXY (m := m) ((-3 : ZMod m), (1 : ZMod m)) := by rw [hret]
    _ = ((-1 : ZMod m), (1 : ZMod m)) := by
          ext <;> simp [toXY]
          ring_nf

def verticalMap0XY (u : P0Coord m) : P0Coord m :=
  (u.1, u.2 + 1)

theorem iterate_verticalMap0XY (n : ℕ) (u : P0Coord m) :
    ((verticalMap0XY (m := m)^[n]) u) = (u.1, u.2 + n) := by
  induction n generalizing u with
  | zero =>
      rcases u with ⟨a, b⟩
      simp [verticalMap0XY]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      rcases u with ⟨a, b⟩
      ext <;> simp [verticalMap0XY, Nat.cast_add]
      ring

theorem returnMap0CaseIXY_prefix_step [Fact (4 < m)] {x s : ℕ}
    (hx2 : 2 ≤ x) (hxle : x ≤ m - 2) (hs : s ≤ x - 2) :
    returnMap0CaseIXY (m := m) ((((x + 1 : ℕ) : ZMod m)), (((1 + s : ℕ) : ZMod m))) =
      ((((x + 1 : ℕ) : ZMod m)), (((2 + s : ℕ) : ZMod m))) := by
  have hm0 : 0 < m := Fact.out
  have hx1 : 1 ≤ x := le_trans (by decide : 1 ≤ 2) hx2
  have hxm : x < m := by omega
  have hxlt1 : x + 1 < m := by omega
  have hslt : s < m := by omega
  have hksucc_lt : 1 + s < m := by omega
  have hk2_lt : 2 + s < m := by omega
  have hk_ne_zero : (((1 + s : ℕ) : ZMod m)) ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := 1 + s) (by omega) hksucc_lt
  have hk_ne_neg_one : (((1 + s : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := 1 + s) (by omega)
  have hfrom :
      fromXY (m := m) ((((x + 1 : ℕ) : ZMod m)), (((1 + s : ℕ) : ZMod m))) =
        ((((x + 1 : ℕ) : ZMod m)) - 2 * (((1 + s : ℕ) : ZMod m)), (((1 + s : ℕ) : ZMod m))) := by
    ext <;> simp [fromXY]
  have h00 :
      ¬ ((((x + 1 : ℕ) : ZMod m)) - 2 * (((1 + s : ℕ) : ZMod m)) = 0 ∧
          (((1 + s : ℕ) : ZMod m)) = 0) := by
    intro h
    exact hk_ne_zero h.2
  have h1neg1 :
      ¬ ((((x + 1 : ℕ) : ZMod m)) - 2 * (((1 + s : ℕ) : ZMod m)) = (1 : ZMod m) ∧
          (((1 + s : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
    intro h
    exact hk_ne_neg_one h.2
  have hneg20 :
      ¬ ((((x + 1 : ℕ) : ZMod m)) - 2 * (((1 + s : ℕ) : ZMod m)) = (-2 : ZMod m) ∧
          (((1 + s : ℕ) : ZMod m)) = 0) := by
    intro h
    exact hk_ne_zero h.2
  have hneg11 :
      ¬ ((((x + 1 : ℕ) : ZMod m)) - 2 * (((1 + s : ℕ) : ZMod m)) = (-1 : ZMod m) ∧
          (((1 + s : ℕ) : ZMod m)) = (1 : ZMod m)) := by
    intro h
    have hs0 : s = 0 := by
      exact natCast_eq_natCast_of_lt (m := m) (by omega) Fact.out (by simpa using h.2)
    subst hs0
    have hcastx : (((x : ℕ) : ZMod m)) = 0 := by
      have h' := congrArg (fun z : ZMod m => z + 1) h.1
      ring_nf at h'
      simpa [Nat.cast_add] using h'
    have hx0 : x = 0 := by
      exact natCast_eq_natCast_of_lt (m := m) hxm hm0 (by simpa using hcastx)
    omega
  have hdiag :
      ¬ ((((x + 1 : ℕ) : ZMod m)) - 2 * (((1 + s : ℕ) : ZMod m)) + (((1 + s : ℕ) : ZMod m)) = (1 : ZMod m) ∧
          ¬ ((((x + 1 : ℕ) : ZMod m)) - 2 * (((1 + s : ℕ) : ZMod m)) = (1 : ZMod m) ∧
            (((1 + s : ℕ) : ZMod m)) = 0)) := by
    intro h
    have hcast : (((x - s : ℕ) : ZMod m)) = (1 : ZMod m) := by
      have hsx : s ≤ x := by omega
      calc
        (((x - s : ℕ) : ZMod m))
            = ((((x + 1 : ℕ) : ZMod m)) - 2 * (((1 + s : ℕ) : ZMod m)) + (((1 + s : ℕ) : ZMod m))) := by
              rw [Nat.cast_sub hsx, Nat.cast_add, Nat.cast_add]
              ring
        _ = (1 : ZMod m) := h.1
    have hneq : (((x - s : ℕ) : ZMod m)) ≠ (1 : ZMod m) := by
      have hx2 : 2 ≤ x := by omega
      have hsx2' : s + 2 ≤ (x - 2) + 2 := Nat.add_le_add_right hs 2
      have hsx2 : 2 + s ≤ x := by
        simpa [Nat.add_comm, Nat.sub_add_cancel hx2] using hsx2'
      have hxsub2 : 2 ≤ x - s := Nat.le_sub_of_add_le hsx2
      have hxsub_lt : x - s < m := lt_of_le_of_lt (Nat.sub_le _ _) hxm
      exact natCast_ne_one_of_two_le_lt (m := m) (n := x - s) hxsub2 hxsub_lt
    exact hneq hcast
  have hA :
      ¬ ((((1 + s : ℕ) : ZMod m) = 0 ∧
            ((((x + 1 : ℕ) : ZMod m)) - 2 * (((1 + s : ℕ) : ZMod m))) ≠ 0 ∧
            ((((x + 1 : ℕ) : ZMod m)) - 2 * (((1 + s : ℕ) : ZMod m))) ≠ (-2 : ZMod m) ∧
            ((((x + 1 : ℕ) : ZMod m)) - 2 * (((1 + s : ℕ) : ZMod m))) ≠ (-1 : ZMod m)) ∨
          ((((x + 1 : ℕ) : ZMod m)) - 2 * (((1 + s : ℕ) : ZMod m)) = 0 ∧
            (((1 + s : ℕ) : ZMod m)) = (-1 : ZMod m)) ∨
          ((((x + 1 : ℕ) : ZMod m)) - 2 * (((1 + s : ℕ) : ZMod m)) = (-2 : ZMod m) ∧
            (((1 + s : ℕ) : ZMod m)) = (1 : ZMod m))) := by
    intro h
    rcases h with h0 | hrest
    · exact hk_ne_zero h0.1
    · rcases hrest with h1 | h2
      · exact hk_ne_neg_one h1.2
      · have hs0 : s = 0 := by
          exact natCast_eq_natCast_of_lt (m := m) (by omega) Fact.out (by simpa using h2.2)
        subst hs0
        have hcastx : (((x : ℕ) : ZMod m)) = (-1 : ZMod m) := by
          have h' := congrArg (fun z : ZMod m => z + 1) h2.1
          ring_nf at h'
          simpa [Nat.cast_add] using h'
        exact (natCast_ne_neg_one_of_lt (m := m) (n := x) (by omega)) hcastx
  have hret :
      returnMap0CaseI (m := m)
        ((((x + 1 : ℕ) : ZMod m)) - 2 * (((1 + s : ℕ) : ZMod m)), (((1 + s : ℕ) : ZMod m))) =
          (((((x + 1 : ℕ) : ZMod m)) - 2 * (((1 + s : ℕ) : ZMod m)) - 2), (((2 + s : ℕ) : ZMod m))) := by
    unfold returnMap0CaseI
    rw [if_neg h00, if_neg h1neg1, if_neg hneg20, if_neg hneg11, if_neg hdiag, if_neg hA]
    ext <;> simp [Nat.cast_add] <;> ring
  calc
    returnMap0CaseIXY (m := m) ((((x + 1 : ℕ) : ZMod m)), (((1 + s : ℕ) : ZMod m)))
        = toXY (m := m)
            (returnMap0CaseI (m := m)
              (fromXY (m := m) ((((x + 1 : ℕ) : ZMod m)), (((1 + s : ℕ) : ZMod m))))) := by
                rfl
    _ = toXY (m := m)
          (returnMap0CaseI (m := m)
            ((((x + 1 : ℕ) : ZMod m)) - 2 * (((1 + s : ℕ) : ZMod m)), (((1 + s : ℕ) : ZMod m)))) := by
            rw [hfrom]
    _ = toXY (m := m)
          (((((x + 1 : ℕ) : ZMod m)) - 2 * (((1 + s : ℕ) : ZMod m)) - 2), (((2 + s : ℕ) : ZMod m))) := by
            rw [hret]
    _ = ((((x + 1 : ℕ) : ZMod m)), (((2 + s : ℕ) : ZMod m))) := by
          ext <;> simp [toXY, Nat.cast_add] <;> ring_nf

theorem returnMap0CaseIXY_diag_step [Fact (4 < m)] {x : ℕ}
    (hx1 : 1 ≤ x) (hxle : x ≤ m - 2) :
    returnMap0CaseIXY (m := m) ((((x + 1 : ℕ) : ZMod m)), (((x : ℕ) : ZMod m))) =
      ((((x + 2 : ℕ) : ZMod m)), (((x + 2 : ℕ) : ZMod m))) := by
  have hxm : x < m := by omega
  have hx1lt : x + 1 < m := by omega
  have hx_ne_zero : (((x : ℕ) : ZMod m)) ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := x) hx1 hxm
  have hx_ne_neg_one : (((x : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := x) (by omega)
  have hfrom :
      fromXY (m := m) ((((x + 1 : ℕ) : ZMod m)), (((x : ℕ) : ZMod m))) =
        ((((x + 1 : ℕ) : ZMod m)) - 2 * (((x : ℕ) : ZMod m)), (((x : ℕ) : ZMod m))) := by
    ext <;> simp [fromXY]
  have h00 :
      ¬ ((((x + 1 : ℕ) : ZMod m)) - 2 * (((x : ℕ) : ZMod m)) = 0 ∧ (((x : ℕ) : ZMod m)) = 0) := by
    intro h
    exact hx_ne_zero h.2
  have h1neg1 :
      ¬ ((((x + 1 : ℕ) : ZMod m)) - 2 * (((x : ℕ) : ZMod m)) = (1 : ZMod m) ∧ (((x : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
    intro h
    exact hx_ne_neg_one h.2
  have hneg20 :
      ¬ ((((x + 1 : ℕ) : ZMod m)) - 2 * (((x : ℕ) : ZMod m)) = (-2 : ZMod m) ∧ (((x : ℕ) : ZMod m)) = 0) := by
    intro h
    exact hx_ne_zero h.2
  have hneg11 :
      ¬ ((((x + 1 : ℕ) : ZMod m)) - 2 * (((x : ℕ) : ZMod m)) = (-1 : ZMod m) ∧ (((x : ℕ) : ZMod m)) = (1 : ZMod m)) := by
    intro h
    have hxeq1 : x = 1 := by
      exact natCast_eq_natCast_of_lt (m := m) hxm Fact.out (by simpa using h.2)
    subst hxeq1
    have : (((0 : ℕ) : ZMod m)) = (-1 : ZMod m) := by
      simpa using h.1
    have hneg1_ne_zero : (-1 : ZMod m) ≠ 0 := neg_ne_zero.mpr (one_ne_zero (m := m))
    exact hneg1_ne_zero (by simpa using this.symm)
  have hdiag :
      ((((x + 1 : ℕ) : ZMod m)) - 2 * (((x : ℕ) : ZMod m)) + (((x : ℕ) : ZMod m)) = (1 : ZMod m) ∧
        ¬ ((((x + 1 : ℕ) : ZMod m)) - 2 * (((x : ℕ) : ZMod m)) = (1 : ZMod m) ∧ (((x : ℕ) : ZMod m)) = 0)) := by
    refine ⟨?_, ?_⟩
    · rw [Nat.cast_add]
      ring
    · intro h
      exact hx_ne_zero h.2
  have hret :
      returnMap0CaseI (m := m)
        ((((x + 1 : ℕ) : ZMod m)) - 2 * (((x : ℕ) : ZMod m)), (((x : ℕ) : ZMod m))) =
          (((((x + 1 : ℕ) : ZMod m)) - 2 * (((x : ℕ) : ZMod m)) - 3), (((x + 2 : ℕ) : ZMod m))) := by
    unfold returnMap0CaseI
    rw [if_neg h00, if_neg h1neg1, if_neg hneg20, if_neg hneg11, if_pos hdiag]
    ext <;> simp [Nat.cast_add] <;> ring
  calc
    returnMap0CaseIXY (m := m) ((((x + 1 : ℕ) : ZMod m)), (((x : ℕ) : ZMod m)))
        = toXY (m := m)
            (returnMap0CaseI (m := m)
              (fromXY (m := m) ((((x + 1 : ℕ) : ZMod m)), (((x : ℕ) : ZMod m))))) := by
                rfl
    _ = toXY (m := m)
          (returnMap0CaseI (m := m)
            ((((x + 1 : ℕ) : ZMod m)) - 2 * (((x : ℕ) : ZMod m)), (((x : ℕ) : ZMod m)))) := by
            rw [hfrom]
    _ = toXY (m := m)
          (((((x + 1 : ℕ) : ZMod m)) - 2 * (((x : ℕ) : ZMod m)) - 3), (((x + 2 : ℕ) : ZMod m))) := by
            rw [hret]
    _ = ((((x + 2 : ℕ) : ZMod m)), (((x + 2 : ℕ) : ZMod m))) := by
          ext <;> simp [toXY, Nat.cast_add] <;> ring_nf

theorem returnMap0CaseIXY_suffix_step [Fact (4 < m)] {x s : ℕ}
    (hxle : x ≤ m - 5) (hs : s ≤ m - x - 3) :
    returnMap0CaseIXY (m := m) ((((x + 2 : ℕ) : ZMod m)), (((x + 2 + s : ℕ) : ZMod m))) =
      ((((x + 2 : ℕ) : ZMod m)), (((x + 3 + s : ℕ) : ZMod m))) := by
  have hm4 : 4 < m := Fact.out
  have hxm : x < m := by omega
  have hylt : x + 2 + s < m := by omega
  have hy_ne_zero : (((x + 2 + s : ℕ) : ZMod m)) ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := x + 2 + s) (by omega) hylt
  have hfrom :
      fromXY (m := m) ((((x + 2 : ℕ) : ZMod m)), (((x + 2 + s : ℕ) : ZMod m))) =
        ((((x + 2 : ℕ) : ZMod m)) - 2 * (((x + 2 + s : ℕ) : ZMod m)), (((x + 2 + s : ℕ) : ZMod m))) := by
    ext <;> simp [fromXY]
  have h00 :
      ¬ ((((x + 2 : ℕ) : ZMod m)) - 2 * (((x + 2 + s : ℕ) : ZMod m)) = 0 ∧
          (((x + 2 + s : ℕ) : ZMod m)) = 0) := by
    intro h
    exact hy_ne_zero h.2
  have h1neg1 :
      ¬ ((((x + 2 : ℕ) : ZMod m)) - 2 * (((x + 2 + s : ℕ) : ZMod m)) = (1 : ZMod m) ∧
          (((x + 2 + s : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
    intro h
    have hm1lt : m - 1 < m := by omega
    have hm1cast : (((m - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) := by
      rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one, ZMod.natCast_self]
      ring
    have hy_last : x + 2 + s = m - 1 := by
      exact natCast_eq_natCast_of_lt (m := m) hylt hm1lt (by rw [hm1cast]; simpa using h.2)
    have hx4eq : (((x + 4 : ℕ) : ZMod m)) = (1 : ZMod m) := by
      calc
        (((x + 4 : ℕ) : ZMod m))
            = ((((x + 2 : ℕ) : ZMod m)) - 2 * (((m - 1 : ℕ) : ZMod m))) := by
                simp [Nat.cast_add]
                rw [hm1cast]
                ring
        _ = (1 : ZMod m) := by simpa [hy_last] using h.1
    have hx4lt : x + 4 < m := by omega
    exact natCast_ne_one_of_two_le_lt (m := m) (n := x + 4) (by omega) hx4lt hx4eq
  have hneg20 :
      ¬ ((((x + 2 : ℕ) : ZMod m)) - 2 * (((x + 2 + s : ℕ) : ZMod m)) = (-2 : ZMod m) ∧
          (((x + 2 + s : ℕ) : ZMod m)) = 0) := by
    intro h
    exact hy_ne_zero h.2
  have hneg11 :
      ¬ ((((x + 2 : ℕ) : ZMod m)) - 2 * (((x + 2 + s : ℕ) : ZMod m)) = (-1 : ZMod m) ∧
          (((x + 2 + s : ℕ) : ZMod m)) = (1 : ZMod m)) := by
    intro h
    have hy_eq : x + 2 + s = 1 := by
      exact natCast_eq_natCast_of_lt (m := m) hylt Fact.out (by simpa using h.2)
    omega
  have hdiag :
      ¬ ((((x + 2 : ℕ) : ZMod m)) - 2 * (((x + 2 + s : ℕ) : ZMod m)) + (((x + 2 + s : ℕ) : ZMod m)) = (1 : ZMod m) ∧
          ¬ ((((x + 2 : ℕ) : ZMod m)) - 2 * (((x + 2 + s : ℕ) : ZMod m)) = (1 : ZMod m) ∧
            (((x + 2 + s : ℕ) : ZMod m)) = 0)) := by
    intro h
    have hexpr :
        ((((x + 2 : ℕ) : ZMod m)) - 2 * (((x + 2 + s : ℕ) : ZMod m)) + (((x + 2 + s : ℕ) : ZMod m))) =
          - (((s : ℕ) : ZMod m)) := by
      simp [Nat.cast_add]
      ring_nf
    have hs_cast : (((s : ℕ) : ZMod m)) = (-1 : ZMod m) := by
      calc
        (((s : ℕ) : ZMod m))
            = - ((((x + 2 : ℕ) : ZMod m)) - 2 * (((x + 2 + s : ℕ) : ZMod m)) + (((x + 2 + s : ℕ) : ZMod m))) := by
              rw [hexpr]
              ring
        _ = (-1 : ZMod m) := by
              simpa using congrArg Neg.neg h.1
    exact (natCast_ne_neg_one_of_lt (m := m) (n := s) (by omega)) hs_cast
  have hA :
      ¬ ((((x + 2 + s : ℕ) : ZMod m) = 0 ∧
            ((((x + 2 : ℕ) : ZMod m)) - 2 * (((x + 2 + s : ℕ) : ZMod m))) ≠ 0 ∧
            ((((x + 2 : ℕ) : ZMod m)) - 2 * (((x + 2 + s : ℕ) : ZMod m))) ≠ (-2 : ZMod m) ∧
            ((((x + 2 : ℕ) : ZMod m)) - 2 * (((x + 2 + s : ℕ) : ZMod m))) ≠ (-1 : ZMod m)) ∨
          ((((x + 2 : ℕ) : ZMod m)) - 2 * (((x + 2 + s : ℕ) : ZMod m)) = 0 ∧
            (((x + 2 + s : ℕ) : ZMod m)) = (-1 : ZMod m)) ∨
          ((((x + 2 : ℕ) : ZMod m)) - 2 * (((x + 2 + s : ℕ) : ZMod m)) = (-2 : ZMod m) ∧
            (((x + 2 + s : ℕ) : ZMod m)) = (1 : ZMod m))) := by
    intro h
    rcases h with h0 | hrest
    · exact hy_ne_zero h0.1
    · rcases hrest with h1 | h2
      · have hm1lt : m - 1 < m := by omega
        have hm1cast : (((m - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) := by
          rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one, ZMod.natCast_self]
          ring
        have hy_last : x + 2 + s = m - 1 := by
          exact natCast_eq_natCast_of_lt (m := m) hylt hm1lt (by rw [hm1cast]; simpa using h1.2)
        have hx4eq0 : (((x + 4 : ℕ) : ZMod m)) = 0 := by
          calc
            (((x + 4 : ℕ) : ZMod m))
                = ((((x + 2 : ℕ) : ZMod m)) - 2 * (((m - 1 : ℕ) : ZMod m))) := by
                    simp [Nat.cast_add]
                    rw [hm1cast]
                    ring
            _ = 0 := by simpa [hy_last] using h1.1
        have hx4lt : x + 4 < m := by omega
        exact natCast_ne_zero_of_pos_lt (m := m) (n := x + 4) (by omega) hx4lt hx4eq0
      · have hy_eq : x + 2 + s = 1 := by
          exact natCast_eq_natCast_of_lt (m := m) hylt Fact.out (by simpa using h2.2)
        omega
  have hret :
      returnMap0CaseI (m := m)
        ((((x + 2 : ℕ) : ZMod m)) - 2 * (((x + 2 + s : ℕ) : ZMod m)), (((x + 2 + s : ℕ) : ZMod m))) =
          (((((x + 2 : ℕ) : ZMod m)) - 2 * (((x + 2 + s : ℕ) : ZMod m)) - 2), (((x + 3 + s : ℕ) : ZMod m))) := by
    unfold returnMap0CaseI
    rw [if_neg h00, if_neg h1neg1, if_neg hneg20, if_neg hneg11, if_neg hdiag]
    rw [if_neg hA]
    ext <;> simp [Nat.cast_add] <;> ring
  calc
    returnMap0CaseIXY (m := m) ((((x + 2 : ℕ) : ZMod m)), (((x + 2 + s : ℕ) : ZMod m)))
        = toXY (m := m)
            (returnMap0CaseI (m := m)
              (fromXY (m := m) ((((x + 2 : ℕ) : ZMod m)), (((x + 2 + s : ℕ) : ZMod m))))) := by
                rfl
    _ = toXY (m := m)
          (returnMap0CaseI (m := m)
            ((((x + 2 : ℕ) : ZMod m)) - 2 * (((x + 2 + s : ℕ) : ZMod m)), (((x + 2 + s : ℕ) : ZMod m)))) := by
            rw [hfrom]
    _ = toXY (m := m)
          (((((x + 2 : ℕ) : ZMod m)) - 2 * (((x + 2 + s : ℕ) : ZMod m)) - 2), (((x + 3 + s : ℕ) : ZMod m))) := by
            rw [hret]
    _ = ((((x + 2 : ℕ) : ZMod m)), (((x + 3 + s : ℕ) : ZMod m))) := by
          ext <;> simp [toXY, Nat.cast_add] <;> ring_nf

theorem iterate_returnMap0CaseIXY_prefix_partial [Fact (4 < m)] {x t : ℕ}
    (hx2 : 2 ≤ x) (hxle : x ≤ m - 2) (ht : t ≤ x - 1) :
    ((returnMap0CaseIXY (m := m)^[t]) ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m))) =
      ((((x + 1 : ℕ) : ZMod m)), (((1 + t : ℕ) : ZMod m))) := by
  induction t with
  | zero =>
      simp
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      have ht' : t ≤ x - 1 := Nat.le_trans (Nat.le_succ t) ht
      rw [ih ht']
      have hs : t ≤ x - 2 := by omega
      simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
        returnMap0CaseIXY_prefix_step (m := m) hx2 hxle hs

theorem iterate_returnMap0CaseIXY_suffix_partial [Fact (4 < m)] {x t : ℕ}
    (hxle : x ≤ m - 5) (ht : t ≤ m - x - 2) :
    ((returnMap0CaseIXY (m := m)^[t]) ((((x + 2 : ℕ) : ZMod m)), (((x + 2 : ℕ) : ZMod m)))) =
      ((((x + 2 : ℕ) : ZMod m)), (((x + 2 + t : ℕ) : ZMod m))) := by
  induction t with
  | zero =>
      simp
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      have ht' : t ≤ m - x - 2 := Nat.le_trans (Nat.le_succ t) ht
      rw [ih ht']
      have hs : t ≤ m - x - 3 := by omega
      simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
        returnMap0CaseIXY_suffix_step (m := m) hxle hs

theorem returnMap0CaseIXY_zero_column_step [Fact (4 < m)] {s : ℕ}
    (hs : s ≤ m - 4) :
    returnMap0CaseIXY (m := m) ((0 : ZMod m), (((2 + s : ℕ) : ZMod m))) =
      ((0 : ZMod m), (((3 + s : ℕ) : ZMod m))) := by
  have hm4 : 4 < m := Fact.out
  have hylt : 2 + s < m := by omega
  have hy1lt : 3 + s < m := by omega
  have hy_ne_zero : (((2 + s : ℕ) : ZMod m)) ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := 2 + s) (by omega) hylt
  have hy_ne_neg_one : (((2 + s : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := 2 + s) (by omega)
  have hfrom :
      fromXY (m := m) ((0 : ZMod m), (((2 + s : ℕ) : ZMod m))) =
        (-2 * (((2 + s : ℕ) : ZMod m)), (((2 + s : ℕ) : ZMod m))) := by
    ext <;> simp [fromXY]
  have h00 :
      ¬ (-2 * (((2 + s : ℕ) : ZMod m)) = 0 ∧ (((2 + s : ℕ) : ZMod m)) = 0) := by
    intro h
    exact hy_ne_zero h.2
  have h1neg1 :
      ¬ (-2 * (((2 + s : ℕ) : ZMod m)) = (1 : ZMod m) ∧ (((2 + s : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
    intro h
    exact hy_ne_neg_one h.2
  have hneg20 :
      ¬ (-2 * (((2 + s : ℕ) : ZMod m)) = (-2 : ZMod m) ∧ (((2 + s : ℕ) : ZMod m)) = 0) := by
    intro h
    exact hy_ne_zero h.2
  have hneg11 :
      ¬ (-2 * (((2 + s : ℕ) : ZMod m)) = (-1 : ZMod m) ∧ (((2 + s : ℕ) : ZMod m)) = (1 : ZMod m)) := by
    intro h
    have hy_eq : 2 + s = 1 := by
      exact natCast_eq_natCast_of_lt (m := m) hylt Fact.out (by simpa using h.2)
    omega
  have hdiag :
      ¬ (-2 * (((2 + s : ℕ) : ZMod m)) + (((2 + s : ℕ) : ZMod m)) = (1 : ZMod m) ∧
          ¬ (-2 * (((2 + s : ℕ) : ZMod m)) = (1 : ZMod m) ∧ (((2 + s : ℕ) : ZMod m)) = 0)) := by
    intro h
    have hs_cast : (((2 + s : ℕ) : ZMod m)) = (-1 : ZMod m) := by
      calc
        (((2 + s : ℕ) : ZMod m))
            = - (-2 * (((2 + s : ℕ) : ZMod m)) + (((2 + s : ℕ) : ZMod m))) := by ring
        _ = (-1 : ZMod m) := by simpa using congrArg Neg.neg h.1
    exact hy_ne_neg_one hs_cast
  have hA :
      ¬ ((((2 + s : ℕ) : ZMod m) = 0 ∧
            (-2 * (((2 + s : ℕ) : ZMod m))) ≠ 0 ∧
            (-2 * (((2 + s : ℕ) : ZMod m))) ≠ (-2 : ZMod m) ∧
            (-2 * (((2 + s : ℕ) : ZMod m))) ≠ (-1 : ZMod m)) ∨
          ((-2 * (((2 + s : ℕ) : ZMod m)) = 0 ∧ (((2 + s : ℕ) : ZMod m)) = (-1 : ZMod m)) ∨
            ((-2 * (((2 + s : ℕ) : ZMod m)) = (-2 : ZMod m) ∧ (((2 + s : ℕ) : ZMod m)) = (1 : ZMod m))))) := by
    intro h
    rcases h with h0 | h1 | h2
    · exact hy_ne_zero h0.1
    · exact hy_ne_neg_one h1.2
    · have hy_eq : 2 + s = 1 := by
        exact natCast_eq_natCast_of_lt (m := m) hylt Fact.out (by simpa using h2.2)
      omega
  have hret :
      returnMap0CaseI (m := m) (-2 * (((2 + s : ℕ) : ZMod m)), (((2 + s : ℕ) : ZMod m))) =
        (-2 * (((2 + s : ℕ) : ZMod m)) - 2, (((3 + s : ℕ) : ZMod m))) := by
    unfold returnMap0CaseI
    rw [if_neg h00, if_neg h1neg1, if_neg hneg20, if_neg hneg11, if_neg hdiag, if_neg hA]
    ext <;> simp [Nat.cast_add] <;> ring
  calc
    returnMap0CaseIXY (m := m) ((0 : ZMod m), (((2 + s : ℕ) : ZMod m)))
        = toXY (m := m)
            (returnMap0CaseI (m := m) (fromXY (m := m) ((0 : ZMod m), (((2 + s : ℕ) : ZMod m))))) := by
              rfl
    _ = toXY (m := m)
          (returnMap0CaseI (m := m) (-2 * (((2 + s : ℕ) : ZMod m)), (((2 + s : ℕ) : ZMod m)))) := by
            rw [hfrom]
    _ = toXY (m := m) (-2 * (((2 + s : ℕ) : ZMod m)) - 2, (((3 + s : ℕ) : ZMod m))) := by
          rw [hret]
    _ = ((0 : ZMod m), (((3 + s : ℕ) : ZMod m))) := by
          ext <;> simp [toXY, Nat.cast_add]
          ring_nf

theorem iterate_returnMap0CaseIXY_zero_column_partial [Fact (4 < m)] {t : ℕ}
    (ht : t ≤ m - 3) :
    ((returnMap0CaseIXY (m := m)^[t]) ((0 : ZMod m), (2 : ZMod m))) =
      ((0 : ZMod m), (((2 + t : ℕ) : ZMod m))) := by
  induction t with
  | zero =>
      simp
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      have ht' : t ≤ m - 3 := Nat.le_trans (Nat.le_succ t) ht
      rw [ih ht']
      have hs : t ≤ m - 4 := by omega
      simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
        returnMap0CaseIXY_zero_column_step (m := m) hs

theorem returnMap0CaseIXY_zero_m_sub_one [Fact (4 < m)] :
    returnMap0CaseIXY (m := m) ((0 : ZMod m), (-1 : ZMod m)) = ((1 : ZMod m), (1 : ZMod m)) := by
  have hm4 : 4 < m := Fact.out
  have h20 : (2 : ZMod m) ≠ 0 := two_ne_zero (m := m)
  have h21 : (2 : ZMod m) ≠ (1 : ZMod m) := two_ne_one (m := m)
  have h2neg2 : (2 : ZMod m) ≠ (-2 : ZMod m) := by
    exact natCast_ne_neg_two_of_lt (m := m) (n := 2) hm4
  have hfrom : fromXY (m := m) ((0 : ZMod m), (-1 : ZMod m)) = ((2 : ZMod m), (-1 : ZMod m)) := by
    ext <;> simp [fromXY]
  have h00 : ¬ ((2 : ZMod m) = 0 ∧ (-1 : ZMod m) = 0) := by
    intro h
    exact h20 h.1
  have h1neg1 : ¬ ((2 : ZMod m) = (1 : ZMod m) ∧ (-1 : ZMod m) = (-1 : ZMod m)) := by
    intro h
    exact h21 h.1
  have hneg20 : ¬ ((2 : ZMod m) = (-2 : ZMod m) ∧ (-1 : ZMod m) = 0) := by
    intro h
    exact h2neg2 h.1
  have hneg11 : ¬ ((2 : ZMod m) = (-1 : ZMod m) ∧ (-1 : ZMod m) = (1 : ZMod m)) := by
    intro h
    exact one_ne_neg_one (m := m) h.2.symm
  have hdiag : ((2 : ZMod m) + (-1 : ZMod m) = (1 : ZMod m) ∧
      ¬ ((2 : ZMod m) = (1 : ZMod m) ∧ (-1 : ZMod m) = 0)) := by
    refine ⟨by ring, ?_⟩
    intro h
    exact h21 h.1
  have hret : returnMap0CaseI (m := m) ((2 : ZMod m), (-1 : ZMod m)) = ((-1 : ZMod m), (1 : ZMod m)) := by
    unfold returnMap0CaseI
    rw [if_neg h00, if_neg h1neg1, if_neg hneg20, if_neg hneg11, if_pos hdiag]
    ext <;> ring
  calc
    returnMap0CaseIXY (m := m) ((0 : ZMod m), (-1 : ZMod m))
        = toXY (m := m) (returnMap0CaseI (m := m) (fromXY (m := m) ((0 : ZMod m), (-1 : ZMod m)))) := by
            rfl
    _ = toXY (m := m) (returnMap0CaseI (m := m) ((2 : ZMod m), (-1 : ZMod m))) := by
          rw [hfrom]
    _ = toXY (m := m) ((-1 : ZMod m), (1 : ZMod m)) := by
          rw [hret]
    _ = ((1 : ZMod m), (1 : ZMod m)) := by
          ext <;> simp [toXY]
          ring_nf

theorem returnMap0CaseIXY_one_column_step [Fact (4 < m)] {s : ℕ}
    (hs : s ≤ m - 4) :
    returnMap0CaseIXY (m := m) ((1 : ZMod m), (((2 + s : ℕ) : ZMod m))) =
      ((1 : ZMod m), (((3 + s : ℕ) : ZMod m))) := by
  have hm4 : 4 < m := Fact.out
  have hylt : 2 + s < m := by omega
  have hy1lt : 3 + s < m := by omega
  have hy_ne_zero : (((2 + s : ℕ) : ZMod m)) ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := 2 + s) (by omega) hylt
  have hy_ne_neg_one : (((2 + s : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := 2 + s) (by omega)
  have hfrom :
      fromXY (m := m) ((1 : ZMod m), (((2 + s : ℕ) : ZMod m))) =
        ((1 : ZMod m) - 2 * (((2 + s : ℕ) : ZMod m)), (((2 + s : ℕ) : ZMod m))) := by
    ext <;> simp [fromXY]
  have h00 :
      ¬ (((1 : ZMod m) - 2 * (((2 + s : ℕ) : ZMod m)) = 0) ∧ (((2 + s : ℕ) : ZMod m)) = 0) := by
    intro h
    exact hy_ne_zero h.2
  have h1neg1 :
      ¬ (((1 : ZMod m) - 2 * (((2 + s : ℕ) : ZMod m)) = (1 : ZMod m)) ∧ (((2 + s : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
    intro h
    exact hy_ne_neg_one h.2
  have hneg20 :
      ¬ (((1 : ZMod m) - 2 * (((2 + s : ℕ) : ZMod m)) = (-2 : ZMod m)) ∧ (((2 + s : ℕ) : ZMod m)) = 0) := by
    intro h
    exact hy_ne_zero h.2
  have hneg11 :
      ¬ (((1 : ZMod m) - 2 * (((2 + s : ℕ) : ZMod m)) = (-1 : ZMod m)) ∧ (((2 + s : ℕ) : ZMod m)) = (1 : ZMod m)) := by
    intro h
    have hy_eq : 2 + s = 1 := by
      exact natCast_eq_natCast_of_lt (m := m) hylt Fact.out (by simpa using h.2)
    omega
  have hdiag :
      ¬ (((1 : ZMod m) - 2 * (((2 + s : ℕ) : ZMod m)) + (((2 + s : ℕ) : ZMod m)) = (1 : ZMod m)) ∧
          ¬ (((1 : ZMod m) - 2 * (((2 + s : ℕ) : ZMod m)) = (1 : ZMod m)) ∧ (((2 + s : ℕ) : ZMod m)) = 0)) := by
    intro h
    have hs_cast : (((2 + s : ℕ) : ZMod m)) = 0 := by
      calc
        (((2 + s : ℕ) : ZMod m))
            = (1 : ZMod m) - ((1 : ZMod m) - 2 * (((2 + s : ℕ) : ZMod m)) + (((2 + s : ℕ) : ZMod m))) := by ring
        _ = 0 := by simpa using congrArg (fun z : ZMod m => (1 : ZMod m) - z) h.1
    exact hy_ne_zero hs_cast
  calc
    returnMap0CaseIXY (m := m) ((1 : ZMod m), (((2 + s : ℕ) : ZMod m)))
        = toXY (m := m)
            (returnMap0CaseI (m := m) (fromXY (m := m) ((1 : ZMod m), (((2 + s : ℕ) : ZMod m))))) := by
              rfl
    _ = toXY (m := m)
          (returnMap0CaseI (m := m) ((1 : ZMod m) - 2 * (((2 + s : ℕ) : ZMod m)), (((2 + s : ℕ) : ZMod m)))) := by
            rw [hfrom]
    _ = toXY (m := m)
          (((1 : ZMod m) - 2 * (((2 + s : ℕ) : ZMod m)) - 2), (((3 + s : ℕ) : ZMod m))) := by
            unfold returnMap0CaseI
            rw [if_neg h00, if_neg h1neg1, if_neg hneg20, if_neg hneg11, if_neg hdiag]
            rw [if_neg (by
              intro h
              rcases h with h0 | hrest
              · exact hy_ne_zero h0.1
              · rcases hrest with h1 | h2
                · exact hy_ne_neg_one h1.2
                · have hy_eq : 2 + s = 1 := by
                    exact natCast_eq_natCast_of_lt (m := m) hylt Fact.out (by simpa using h2.2)
                  omega)]
            ext <;> simp [Nat.cast_add] <;> ring
    _ = ((1 : ZMod m), (((3 + s : ℕ) : ZMod m))) := by
          ext <;> simp [toXY, Nat.cast_add]
          ring_nf

theorem iterate_returnMap0CaseIXY_one_column_partial [Fact (4 < m)] {t : ℕ}
    (ht : t ≤ m - 3) :
    ((returnMap0CaseIXY (m := m)^[t]) ((1 : ZMod m), (2 : ZMod m))) =
      ((1 : ZMod m), (((2 + t : ℕ) : ZMod m))) := by
  induction t with
  | zero =>
      simp
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      have ht' : t ≤ m - 3 := Nat.le_trans (Nat.le_succ t) ht
      rw [ih ht']
      have hs : t ≤ m - 4 := by omega
      simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
        returnMap0CaseIXY_one_column_step (m := m) hs

theorem returnMap0CaseIXY_one_m_sub_one [Fact (4 < m)] :
    returnMap0CaseIXY (m := m) ((1 : ZMod m), (-1 : ZMod m)) = ((1 : ZMod m), (0 : ZMod m)) := by
  have hm4 : 4 < m := Fact.out
  have h30 : ((3 : ZMod m)) ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := 3) (by omega) (by omega)
  have h31 : ((3 : ZMod m)) ≠ (1 : ZMod m) := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := 3) (by omega) (by omega)
  have hfrom : fromXY (m := m) ((1 : ZMod m), (-1 : ZMod m)) = ((3 : ZMod m), (-1 : ZMod m)) := by
    ext <;> simp [fromXY]
    norm_num
  have h00 : ¬ ((3 : ZMod m) = 0 ∧ (-1 : ZMod m) = 0) := by
    intro h
    exact h30 h.1
  have h1neg1 : ¬ ((3 : ZMod m) = (1 : ZMod m) ∧ (-1 : ZMod m) = (-1 : ZMod m)) := by
    intro h
    exact h31 h.1
  have hneg20 : ¬ ((3 : ZMod m) = (-2 : ZMod m) ∧ (-1 : ZMod m) = 0) := by
    intro h
    exact neg_ne_zero.mpr (one_ne_zero (m := m)) h.2
  have hneg11 : ¬ ((3 : ZMod m) = (-1 : ZMod m) ∧ (-1 : ZMod m) = (1 : ZMod m)) := by
    intro h
    exact one_ne_neg_one (m := m) h.2.symm
  have hdiag : ¬ ((3 : ZMod m) + (-1 : ZMod m) = (1 : ZMod m) ∧ ¬ ((3 : ZMod m) = (1 : ZMod m) ∧ (-1 : ZMod m) = 0)) := by
    intro h
    have h21' : (2 : ZMod m) = (1 : ZMod m) := by
      calc
        (2 : ZMod m) = (3 : ZMod m) + (-1 : ZMod m) := by norm_num
        _ = (1 : ZMod m) := h.1
    exact two_ne_one (m := m) h21'
  have hA :
      ¬ ((((-1 : ZMod m) = 0 ∧ (3 : ZMod m) ≠ 0 ∧ (3 : ZMod m) ≠ (-2 : ZMod m) ∧ (3 : ZMod m) ≠ (-1 : ZMod m))) ∨
          (((3 : ZMod m) = 0 ∧ (-1 : ZMod m) = (-1 : ZMod m)) ∨
            (((3 : ZMod m) = (-2 : ZMod m) ∧ (-1 : ZMod m) = (1 : ZMod m))))) := by
    intro h
    rcases h with h0 | h1 | h2
    · exact neg_ne_zero.mpr (one_ne_zero (m := m)) h0.1
    · exact h30 h1.1
    · exact one_ne_neg_one (m := m) h2.2.symm
  have hret : returnMap0CaseI (m := m) ((3 : ZMod m), (-1 : ZMod m)) = ((1 : ZMod m), (0 : ZMod m)) := by
    unfold returnMap0CaseI
    rw [if_neg h00, if_neg h1neg1, if_neg hneg20, if_neg hneg11, if_neg hdiag, if_neg hA]
    ext <;> ring
  calc
    returnMap0CaseIXY (m := m) ((1 : ZMod m), (-1 : ZMod m))
        = toXY (m := m) (returnMap0CaseI (m := m) (fromXY (m := m) ((1 : ZMod m), (-1 : ZMod m)))) := by
            rfl
    _ = toXY (m := m) (returnMap0CaseI (m := m) ((3 : ZMod m), (-1 : ZMod m))) := by
          rw [hfrom]
    _ = toXY (m := m) ((1 : ZMod m), (0 : ZMod m)) := by
          rw [hret]
    _ = ((1 : ZMod m), (0 : ZMod m)) := by
          ext <;> simp [toXY]

theorem firstReturn_line_m_sub_two_case0 [Fact (4 < m)] :
    ((returnMap0CaseIXY (m := m)^[2 * m - 1])
        (linePoint0 (m := m) (⟨m - 2, by
          have hm4 : 4 < m := Fact.out
          omega⟩ : Fin m))) =
      linePoint0 (m := m) (⟨1, by
        have hm4 : 4 < m := Fact.out
        omega⟩ : Fin m) := by
  let F := returnMap0CaseIXY (m := m)
  let xFin : Fin m := ⟨m - 2, by
    have hm4 : 4 < m := Fact.out
    omega⟩
  have hm4 : 4 < m := Fact.out
  have hm2le : 2 ≤ m := by omega
  have hm1le : 1 ≤ m := by omega
  have hneg2cast : (((m - 2 : ℕ) : ZMod m)) = (-2 : ZMod m) :=
    cast_sub_two_eq_neg_two (m := m) hm2le
  have hneg1cast : (((m - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) :=
    cast_sub_one_eq_neg_one (m := m) hm1le
  have h1 :
      ((F^[1]) (linePoint0 (m := m) xFin)) =
        ((0 : ZMod m), (2 : ZMod m)) := by
    simpa [Function.iterate_one, linePoint0, xFin, hneg2cast] using
      returnMap0CaseIXY_m_sub_two_zero (m := m)
  have hzero :
      ((F^[m - 3]) ((0 : ZMod m), (2 : ZMod m))) =
        ((0 : ZMod m), (((m - 1 : ℕ) : ZMod m))) := by
    have h := iterate_returnMap0CaseIXY_zero_column_partial (m := m) (t := m - 3) le_rfl
    simpa [show 2 + (m - 3) = m - 1 by omega] using h
  have h2 :
      ((F^[m - 2]) (linePoint0 (m := m) xFin)) =
        ((0 : ZMod m), (((m - 1 : ℕ) : ZMod m))) := by
    rw [show m - 2 = (m - 3) + 1 by omega, Function.iterate_add_apply, h1, hzero]
  have h3 :
      ((F^[m - 1]) (linePoint0 (m := m) xFin)) =
        ((1 : ZMod m), (1 : ZMod m)) := by
    calc
      ((F^[m - 1]) (linePoint0 (m := m) xFin))
          = ((F^[1]) (((F^[m - 2]) (linePoint0 (m := m) xFin)))) := by
              rw [show m - 1 = 1 + (m - 2) by omega, Function.iterate_add_apply]
      _ = ((F^[1]) ((0 : ZMod m), (((m - 1 : ℕ) : ZMod m)))) := by
            rw [h2]
      _ = ((1 : ZMod m), (1 : ZMod m)) := by
            simpa [Function.iterate_one, hneg1cast] using
              returnMap0CaseIXY_zero_m_sub_one (m := m)
  have h4 :
      ((F^[m]) (linePoint0 (m := m) xFin)) =
        ((0 : ZMod m), (1 : ZMod m)) := by
    have h4' :
        F (((F^[m - 1]) (linePoint0 (m := m) xFin))) =
          ((0 : ZMod m), (1 : ZMod m)) := by
      rw [h3]
      simpa using returnMap0CaseIXY_one_one (m := m)
    have h4'' :
        ((F^[Nat.succ (m - 1)]) (linePoint0 (m := m) xFin)) =
          ((0 : ZMod m), (1 : ZMod m)) := by
      rw [Function.iterate_succ_apply']
      exact h4'
    simpa [Nat.succ_eq_add_one, Nat.sub_add_cancel hm1le] using h4''
  have h5 :
      ((F^[m + 1]) (linePoint0 (m := m) xFin)) =
        ((1 : ZMod m), (2 : ZMod m)) := by
    have h5' :
        F (((F^[m]) (linePoint0 (m := m) xFin))) =
          ((1 : ZMod m), (2 : ZMod m)) := by
      rw [h4]
      simpa using returnMap0CaseIXY_zero_one (m := m)
    have h5'' :
        ((F^[Nat.succ m]) (linePoint0 (m := m) xFin)) =
          ((1 : ZMod m), (2 : ZMod m)) := by
      rw [Function.iterate_succ_apply']
      exact h5'
    simpa [Nat.succ_eq_add_one] using h5''
  have hone :
      ((F^[m - 3]) ((1 : ZMod m), (2 : ZMod m))) =
        ((1 : ZMod m), (((m - 1 : ℕ) : ZMod m))) := by
    have h := iterate_returnMap0CaseIXY_one_column_partial (m := m) (t := m - 3) le_rfl
    simpa [show 2 + (m - 3) = m - 1 by omega] using h
  have h6 :
      ((F^[2 * m - 2]) (linePoint0 (m := m) xFin)) =
        ((1 : ZMod m), (((m - 1 : ℕ) : ZMod m))) := by
    rw [show 2 * m - 2 = (m - 3) + (m + 1) by omega, Function.iterate_add_apply, h5, hone]
  calc
    ((F^[2 * m - 1]) (linePoint0 (m := m) xFin))
        = ((F^[1]) (((F^[2 * m - 2]) (linePoint0 (m := m) xFin)))) := by
            rw [show 2 * m - 1 = 1 + (2 * m - 2) by omega, Function.iterate_add_apply]
    _ = ((F^[1]) ((1 : ZMod m), (((m - 1 : ℕ) : ZMod m)))) := by
          rw [h6]
    _ = ((1 : ZMod m), (0 : ZMod m)) := by
          simpa [Function.iterate_one, cast_sub_one_eq_neg_one (m := m) (by omega)] using
            returnMap0CaseIXY_one_m_sub_one (m := m)
    _ = linePoint0 (m := m) (⟨1, by
          have hm4 : 4 < m := Fact.out
          omega⟩ : Fin m) := by
          simp [linePoint0]

theorem firstReturn_line_generic [Fact (4 < m)] {x : ℕ}
    (hx2 : 2 ≤ x) (hxle : x ≤ m - 5) :
    ((returnMap0CaseIXY (m := m)^[m - 1]) (linePoint0 (m := m) (⟨x, by omega⟩ : Fin m))) =
      linePoint0 (m := m) (⟨x + 2, by omega⟩ : Fin m) := by
  let F := returnMap0CaseIXY (m := m)
  have hx1 : 1 ≤ x := le_trans (by decide : 1 ≤ 2) hx2
  have hxle' : x ≤ m - 2 := by omega
  let xFin : Fin m := ⟨x, by omega⟩
  have hstart :
      F (linePoint0 (m := m) xFin) =
        ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m)) := by
    simpa [linePoint0, xFin] using returnMap0CaseIXY_line_generic (m := m) hx1 (by omega)
  have h1 :
      ((F^[1]) (linePoint0 (m := m) xFin)) =
        ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m)) := by
    simpa [Function.iterate_one] using hstart
  have hprefix :
      ((F^[x - 1]) ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m))) =
        ((((x + 1 : ℕ) : ZMod m)), (((x : ℕ) : ZMod m))) := by
    have h := iterate_returnMap0CaseIXY_prefix_partial (m := m) hx2 hxle' (t := x - 1) le_rfl
    simpa [Nat.add_sub_of_le hx1] using h
  have h2 :
      ((F^[x]) (linePoint0 (m := m) xFin)) =
        ((((x + 1 : ℕ) : ZMod m)), (((x : ℕ) : ZMod m))) := by
    rw [show x = (x - 1) + 1 by omega, Function.iterate_add_apply, h1, hprefix]
    have hxsub : x - 1 + 1 = x := Nat.sub_add_cancel hx1
    simp [hxsub, Nat.add_assoc]
  have hdiag :
      F ((((x + 1 : ℕ) : ZMod m)), (((x : ℕ) : ZMod m))) =
        ((((x + 2 : ℕ) : ZMod m)), (((x + 2 : ℕ) : ZMod m))) :=
    returnMap0CaseIXY_diag_step (m := m) hx1 hxle'
  have h3 :
      ((F^[x + 1]) (linePoint0 (m := m) xFin)) =
        ((((x + 2 : ℕ) : ZMod m)), (((x + 2 : ℕ) : ZMod m))) := by
    rw [show x + 1 = 1 + x by omega, Function.iterate_add_apply, h2]
    simpa [Function.iterate_one] using hdiag
  have hsuffix :
      ((F^[m - x - 2]) ((((x + 2 : ℕ) : ZMod m)), (((x + 2 : ℕ) : ZMod m)))) =
        ((((x + 2 : ℕ) : ZMod m)), (0 : ZMod m)) := by
    have h := iterate_returnMap0CaseIXY_suffix_partial (m := m) hxle (t := m - x - 2) le_rfl
    have hsum : x + 2 + (m - x - 2) = m := by omega
    simpa [hsum, ZMod.natCast_self] using h
  have hsplit : m - 1 = (m - x - 2) + (x + 1) := by
    omega
  calc
    ((F^[m - 1]) (linePoint0 (m := m) xFin))
        = ((F^[m - x - 2]) ((F^[x + 1]) (linePoint0 (m := m) xFin))) := by
            rw [hsplit, Function.iterate_add_apply]
    _ = ((F^[m - x - 2]) ((((x + 2 : ℕ) : ZMod m)), (((x + 2 : ℕ) : ZMod m)))) := by
          rw [h3]
    _ = ((((x + 2 : ℕ) : ZMod m)), (0 : ZMod m)) := hsuffix
    _ = linePoint0 (m := m) (⟨x + 2, by omega⟩ : Fin m) := by
          simp [linePoint0]

theorem firstReturn_line_zero_case0 [Fact (4 < m)] :
    ((returnMap0CaseIXY (m := m)^[1])
        (linePoint0 (m := m) (0 : Fin m))) =
      linePoint0 (m := m) (⟨m - 2, by
        have hm4 : 4 < m := Fact.out
        omega⟩ : Fin m) := by
  have hm2le : 2 ≤ m := by
    have hm4 : 4 < m := Fact.out
    omega
  calc
    ((returnMap0CaseIXY (m := m)^[1]) (linePoint0 (m := m) (0 : Fin m)))
        = ((-2 : ZMod m), (0 : ZMod m)) := by
            simpa [Function.iterate_one, linePoint0] using returnMap0CaseIXY_zero_zero (m := m)
    _ = linePoint0 (m := m) (⟨m - 2, by
          have hm4 : 4 < m := Fact.out
          omega⟩ : Fin m) := by
          simp [linePoint0, cast_sub_two_eq_neg_two (m := m) hm2le]

theorem firstReturn_line_one [Fact (5 < m)] :
    ((returnMap0CaseIXY (m := m)^[m - 1])
        (linePoint0 (m := m) (⟨1, by
          have hm5 : 5 < m := Fact.out
          omega⟩ : Fin m))) =
      linePoint0 (m := m) (⟨3, by
        have hm5 : 5 < m := Fact.out
        omega⟩ : Fin m) := by
  let F := returnMap0CaseIXY (m := m)
  let xFin : Fin m := ⟨1, by
    have hm5 : 5 < m := Fact.out
    omega⟩
  have hm5 : 5 < m := Fact.out
  have h1 :
      ((F^[1]) (linePoint0 (m := m) xFin)) =
        ((2 : ZMod m), (1 : ZMod m)) := by
    simpa [Function.iterate_one, linePoint0, xFin] using
      returnMap0CaseIXY_line_generic (m := m) (x := 1) (by decide) (by omega)
  have hdiag :
      F ((2 : ZMod m), (1 : ZMod m)) = ((3 : ZMod m), (3 : ZMod m)) := by
    simpa using
      returnMap0CaseIXY_diag_step (m := m) (x := 1) (by decide) (by omega)
  have h2 :
      ((F^[2]) (linePoint0 (m := m) xFin)) =
        ((3 : ZMod m), (3 : ZMod m)) := by
    calc
      ((F^[2]) (linePoint0 (m := m) xFin))
          = F (((F^[1]) (linePoint0 (m := m) xFin))) := by
              simp [Function.iterate_succ_apply']
      _ = F ((2 : ZMod m), (1 : ZMod m)) := by rw [h1]
      _ = ((3 : ZMod m), (3 : ZMod m)) := hdiag
  have hsuffix :
      ((F^[m - 3]) ((3 : ZMod m), (3 : ZMod m))) =
        ((3 : ZMod m), (0 : ZMod m)) := by
    have h :=
      iterate_returnMap0CaseIXY_suffix_partial (m := m) (x := 1) (by omega)
        (t := m - 3) le_rfl
    have hsum : 3 + (m - 3) = m := by omega
    simpa [hsum, ZMod.natCast_self] using h
  calc
    ((F^[m - 1]) (linePoint0 (m := m) xFin))
        = ((F^[m - 3]) ((F^[2]) (linePoint0 (m := m) xFin))) := by
            rw [show m - 1 = (m - 3) + 2 by omega, Function.iterate_add_apply]
    _ = ((F^[m - 3]) ((3 : ZMod m), (3 : ZMod m))) := by
          rw [h2]
    _ = ((3 : ZMod m), (0 : ZMod m)) := hsuffix
    _ = linePoint0 (m := m) (⟨3, by
          have hm5 : 5 < m := Fact.out
          omega⟩ : Fin m) := by
          simp [linePoint0]

theorem returnMap0CaseIXY_m_sub_two_m_sub_two [Fact (4 < m)] :
    returnMap0CaseIXY (m := m) ((-2 : ZMod m), (-2 : ZMod m)) = ((-2 : ZMod m), (-1 : ZMod m)) := by
  have hm4 : 4 < m := Fact.out
  have h20 : (2 : ZMod m) ≠ 0 := two_ne_zero (m := m)
  have h21 : (2 : ZMod m) ≠ (1 : ZMod m) := two_ne_one (m := m)
  have h2neg2 : (2 : ZMod m) ≠ (-2 : ZMod m) := by
    exact natCast_ne_neg_two_of_lt (m := m) (n := 2) hm4
  have h2neg1 : (2 : ZMod m) ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := 2) (by omega)
  have hfrom : fromXY (m := m) ((-2 : ZMod m), (-2 : ZMod m)) = ((2 : ZMod m), (-2 : ZMod m)) := by
    ext <;> simp [fromXY]
    ring
  have h00 : ¬ (((2 : ZMod m) = 0) ∧ ((-2 : ZMod m) = 0)) := by
    intro h
    exact h20 h.1
  have h1neg1 : ¬ (((2 : ZMod m) = (1 : ZMod m)) ∧ ((-2 : ZMod m) = (-1 : ZMod m))) := by
    intro h
    exact h21 h.1
  have hneg20 : ¬ (((2 : ZMod m) = (-2 : ZMod m)) ∧ ((-2 : ZMod m) = 0)) := by
    intro h
    exact h2neg2 h.1
  have hneg11 : ¬ (((2 : ZMod m) = (-1 : ZMod m)) ∧ ((-2 : ZMod m) = (1 : ZMod m))) := by
    intro h
    exact h2neg1 h.1
  have hdiag : ¬ (((2 : ZMod m) + (-2 : ZMod m) = (1 : ZMod m)) ∧
      ¬ (((2 : ZMod m) = (1 : ZMod m)) ∧ ((-2 : ZMod m) = 0))) := by
    intro h
    exact one_ne_zero (m := m) (by simpa using h.1.symm)
  have hA :
      ¬ ((((-2 : ZMod m) = 0 ∧ (2 : ZMod m) ≠ 0 ∧ (2 : ZMod m) ≠ (-2 : ZMod m) ∧
            (2 : ZMod m) ≠ (-1 : ZMod m))) ∨
          (((2 : ZMod m) = 0 ∧ (-2 : ZMod m) = (-1 : ZMod m)) ∨
            (((2 : ZMod m) = (-2 : ZMod m) ∧ (-2 : ZMod m) = (1 : ZMod m))))) := by
    intro h
    rcases h with h0 | h1 | h2
    · exact neg_ne_zero.mpr h20 h0.1
    · exact h20 h1.1
    · exact h2neg2 h2.1
  have hret : returnMap0CaseI (m := m) ((2 : ZMod m), (-2 : ZMod m)) = ((0 : ZMod m), (-1 : ZMod m)) := by
    unfold returnMap0CaseI
    rw [if_neg h00, if_neg h1neg1, if_neg hneg20, if_neg hneg11, if_neg hdiag, if_neg hA]
    ext <;> ring
  calc
    returnMap0CaseIXY (m := m) ((-2 : ZMod m), (-2 : ZMod m))
        = toXY (m := m) (returnMap0CaseI (m := m) (fromXY (m := m) ((-2 : ZMod m), (-2 : ZMod m)))) := by
            rfl
    _ = toXY (m := m) (returnMap0CaseI (m := m) ((2 : ZMod m), (-2 : ZMod m))) := by
          rw [hfrom]
    _ = toXY (m := m) ((0 : ZMod m), (-1 : ZMod m)) := by
          rw [hret]
    _ = ((-2 : ZMod m), (-1 : ZMod m)) := by
          ext <;> simp [toXY]

theorem firstReturn_line_m_sub_four [Fact (5 < m)] :
    ((returnMap0CaseIXY (m := m)^[m - 1])
        (linePoint0 (m := m) (⟨m - 4, by
          have hm5 : 5 < m := Fact.out
          omega⟩ : Fin m))) =
      linePoint0 (m := m) (⟨m - 1, by
        have hm5 : 5 < m := Fact.out
        omega⟩ : Fin m) := by
  let F := returnMap0CaseIXY (m := m)
  let xFin : Fin m := ⟨m - 4, by
    have hm5 : 5 < m := Fact.out
    omega⟩
  have hm5 : 5 < m := Fact.out
  have hm2le : 2 ≤ m := by omega
  have hm1le : 1 ≤ m := by omega
  have hneg2cast : (((m - 2 : ℕ) : ZMod m)) = (-2 : ZMod m) :=
    cast_sub_two_eq_neg_two (m := m) hm2le
  have hneg1cast : (((m - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) :=
    cast_sub_one_eq_neg_one (m := m) hm1le
  have h1 :
      ((F^[1]) (linePoint0 (m := m) xFin)) =
        ((((m - 3 : ℕ) : ZMod m)), (1 : ZMod m)) := by
    simpa [Function.iterate_one, linePoint0, xFin, show m - 4 + 1 = m - 3 by omega] using
      returnMap0CaseIXY_line_generic (m := m) (x := m - 4) (by omega) (by omega)
  have hprefix :
      ((F^[m - 5]) ((((m - 3 : ℕ) : ZMod m)), (1 : ZMod m))) =
        ((((m - 3 : ℕ) : ZMod m)), (((m - 4 : ℕ) : ZMod m))) := by
    have h :=
      iterate_returnMap0CaseIXY_prefix_partial (m := m) (x := m - 4) (by omega) (by omega)
        (t := m - 5) le_rfl
    simpa [show m - 4 + 1 = m - 3 by omega, show 1 + (m - 5) = m - 4 by omega] using h
  have h2 :
      ((F^[m - 4]) (linePoint0 (m := m) xFin)) =
        ((((m - 3 : ℕ) : ZMod m)), (((m - 4 : ℕ) : ZMod m))) := by
    rw [show m - 4 = (m - 5) + 1 by omega, Function.iterate_add_apply, h1, hprefix]
    simpa [show m - 5 + 1 = m - 4 by omega]
  have hdiag :
      F ((((m - 3 : ℕ) : ZMod m)), (((m - 4 : ℕ) : ZMod m))) =
        ((((m - 2 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) := by
    simpa [show m - 4 + 1 = m - 3 by omega, show m - 4 + 2 = m - 2 by omega] using
      returnMap0CaseIXY_diag_step (m := m) (x := m - 4) (by omega) (by omega)
  have h3 :
      ((F^[m - 3]) (linePoint0 (m := m) xFin)) =
        ((((m - 2 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) := by
    rw [show m - 3 = 1 + (m - 4) by omega, Function.iterate_add_apply, h2]
    simpa [Function.iterate_one] using hdiag
  have htop :
      F ((((m - 2 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) =
        ((-2 : ZMod m), (-1 : ZMod m)) := by
    simpa [hneg2cast] using returnMap0CaseIXY_m_sub_two_m_sub_two (m := m)
  have h4 :
      ((F^[m - 2]) (linePoint0 (m := m) xFin)) =
        ((-2 : ZMod m), (-1 : ZMod m)) := by
    rw [show m - 2 = 1 + (m - 3) by omega, Function.iterate_add_apply, h3]
    simpa [Function.iterate_one] using htop
  calc
    ((F^[m - 1]) (linePoint0 (m := m) xFin))
        = ((F^[1]) (((F^[m - 2]) (linePoint0 (m := m) xFin)))) := by
            rw [show m - 1 = 1 + (m - 2) by omega, Function.iterate_add_apply]
    _ = ((F^[1]) ((-2 : ZMod m), (-1 : ZMod m))) := by rw [h4]
    _ = ((-1 : ZMod m), (0 : ZMod m)) := by
          simpa [Function.iterate_one] using returnMap0CaseIXY_m_sub_two_m_sub_one (m := m)
    _ = linePoint0 (m := m) (⟨m - 1, by
          have hm5 : 5 < m := Fact.out
          omega⟩ : Fin m) := by
          simpa [linePoint0] using (congrArg (fun z : ZMod m => (z, (0 : ZMod m))) hneg1cast).symm

theorem firstReturn_line_m_sub_one_case0 [Fact (4 < m)] :
    ((returnMap0CaseIXY (m := m)^[m - 1])
        (linePoint0 (m := m) (⟨m - 1, by
          have hm4 : 4 < m := Fact.out
          omega⟩ : Fin m))) =
      linePoint0 (m := m) (0 : Fin m) := by
  let F := returnMap0CaseIXY (m := m)
  let xFin : Fin m := ⟨m - 1, by
    have hm4 : 4 < m := Fact.out
    omega⟩
  have hm4 : 4 < m := Fact.out
  have hm1le : 1 ≤ m := by omega
  have hneg1cast : (((m - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) :=
    cast_sub_one_eq_neg_one (m := m) hm1le
  have h1 :
      ((F^[1]) (linePoint0 (m := m) xFin)) =
        ((-1 : ZMod m), (1 : ZMod m)) := by
    simpa [Function.iterate_one, linePoint0, xFin, hneg1cast] using
      returnMap0CaseIXY_m_sub_one_start (m := m)
  have hprefix :
      ((F^[m - 3]) ((-1 : ZMod m), (1 : ZMod m))) =
        ((-1 : ZMod m), (((m - 2 : ℕ) : ZMod m))) := by
    have h :=
      iterate_returnMap0CaseIXY_prefix_partial (m := m) (x := m - 2) (by omega) (by omega)
        (t := m - 3) le_rfl
    simpa [hneg1cast, show m - 2 + 1 = m - 1 by omega, show 1 + (m - 3) = m - 2 by omega] using h
  have h2 :
      ((F^[m - 2]) (linePoint0 (m := m) xFin)) =
        ((-1 : ZMod m), (((m - 2 : ℕ) : ZMod m))) := by
    rw [show m - 2 = (m - 3) + 1 by omega, Function.iterate_add_apply, h1, hprefix]
    simpa [show m - 3 + 1 = m - 2 by omega]
  have hdiag :
      F ((-1 : ZMod m), (((m - 2 : ℕ) : ZMod m))) =
        ((0 : ZMod m), (0 : ZMod m)) := by
    simpa [hneg1cast, show m - 2 + 1 = m - 1 by omega, show m - 2 + 2 = m by omega, ZMod.natCast_self] using
      returnMap0CaseIXY_diag_step (m := m) (x := m - 2) (by omega) (by omega)
  calc
    ((F^[m - 1]) (linePoint0 (m := m) xFin))
        = ((F^[1]) (((F^[m - 2]) (linePoint0 (m := m) xFin)))) := by
            rw [show m - 1 = 1 + (m - 2) by omega, Function.iterate_add_apply]
    _ = ((F^[1]) ((-1 : ZMod m), (((m - 2 : ℕ) : ZMod m)))) := by
          rw [h2]
    _ = ((0 : ZMod m), (0 : ZMod m)) := by
          simpa [Function.iterate_one] using hdiag
    _ = linePoint0 (m := m) (0 : Fin m) := by
          simp [linePoint0]

theorem firstReturn_line_m_sub_three_case0 [Fact (4 < m)] :
    ((returnMap0CaseIXY (m := m)^[2 * m - 3])
        (linePoint0 (m := m) (⟨m - 3, by
          have hm4 : 4 < m := Fact.out
          omega⟩ : Fin m))) =
      linePoint0 (m := m) (⟨2, by
        have hm4 : 4 < m := Fact.out
        omega⟩ : Fin m) := by
  let F := returnMap0CaseIXY (m := m)
  let xFin : Fin m := ⟨m - 3, by
    have hm4 : 4 < m := Fact.out
    omega⟩
  have hm4 : 4 < m := Fact.out
  have hm2le : 2 ≤ m := by omega
  have hm1le : 1 ≤ m := by omega
  have hneg2cast : (((m - 2 : ℕ) : ZMod m)) = (-2 : ZMod m) :=
    cast_sub_two_eq_neg_two (m := m) hm2le
  have hneg1cast : (((m - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) :=
    cast_sub_one_eq_neg_one (m := m) hm1le
  have h1 :
      ((F^[1]) (linePoint0 (m := m) xFin)) =
        (((((m - 2 : ℕ) : ZMod m))), (1 : ZMod m)) := by
    simpa [Function.iterate_one, linePoint0, xFin, show m - 3 + 1 = m - 2 by omega] using
      returnMap0CaseIXY_line_generic (m := m) (x := m - 3) (by omega) (by omega)
  have hprefix :
      ((F^[m - 4]) ((((m - 2 : ℕ) : ZMod m)), (1 : ZMod m))) =
        ((((m - 2 : ℕ) : ZMod m)), (((m - 3 : ℕ) : ZMod m))) := by
    have h :=
      iterate_returnMap0CaseIXY_prefix_partial (m := m) (x := m - 3) (by omega) (by omega)
        (t := m - 4) le_rfl
    simpa [show m - 3 + 1 = m - 2 by omega, hneg2cast,
      show 1 + (m - 4) = m - 3 by omega] using h
  have h2 :
      ((F^[m - 3]) (linePoint0 (m := m) xFin)) =
        ((((m - 2 : ℕ) : ZMod m)), (((m - 3 : ℕ) : ZMod m))) := by
    rw [show m - 3 = (m - 4) + 1 by omega, Function.iterate_add_apply, h1, hprefix]
    simpa [show m - 4 + 1 = m - 3 by omega]
  have hdiag :
      F ((((m - 2 : ℕ) : ZMod m)), (((m - 3 : ℕ) : ZMod m))) =
        ((-1 : ZMod m), (-1 : ZMod m)) := by
    have hx1' : 1 ≤ m - 3 := by
      have hm4' : 4 < m := Fact.out
      omega
    have hxle' : m - 3 ≤ m - 2 := by
      have hm4' : 4 < m := Fact.out
      omega
    simpa [show m - 3 + 1 = m - 2 by omega, show m - 3 + 2 = m - 1 by omega, hneg1cast] using
      returnMap0CaseIXY_diag_step (m := m) (x := m - 3) hx1' hxle'
  have h3 :
      ((F^[m - 2]) (linePoint0 (m := m) xFin)) =
        ((-1 : ZMod m), (-1 : ZMod m)) := by
    rw [show m - 2 = 1 + (m - 3) by omega, Function.iterate_add_apply, h2]
    simpa [Function.iterate_one] using hdiag
  have h4 :
      ((F^[m - 1]) (linePoint0 (m := m) xFin)) =
        ((2 : ZMod m), (2 : ZMod m)) := by
    rw [show m - 1 = 1 + (m - 2) by omega, Function.iterate_add_apply, h3]
    simpa [Function.iterate_one] using returnMap0CaseIXY_m_sub_one_m_sub_one (m := m)
  have hsuffix :
      ((F^[m - 2]) ((2 : ZMod m), (2 : ZMod m))) =
        ((2 : ZMod m), (0 : ZMod m)) := by
    have h :=
      iterate_returnMap0CaseIXY_suffix_partial (m := m) (x := 0) (by omega)
        (t := m - 2) le_rfl
    have hsum : 2 + (m - 2) = m := by omega
    simpa [hsum, ZMod.natCast_self] using h
  calc
    ((F^[2 * m - 3]) (linePoint0 (m := m) xFin))
        = ((F^[m - 2]) (((F^[m - 1]) (linePoint0 (m := m) xFin)))) := by
            rw [show 2 * m - 3 = (m - 2) + (m - 1) by omega, Function.iterate_add_apply]
    _ = ((F^[m - 2]) ((2 : ZMod m), (2 : ZMod m))) := by
          rw [h4]
    _ = ((2 : ZMod m), (0 : ZMod m)) := hsuffix
    _ = linePoint0 (m := m) (⟨2, by
          have hm4 : 4 < m := Fact.out
          omega⟩ : Fin m) := by
          simp [linePoint0]


def rho0CaseI [Fact (4 < m)] (x : Fin m) : ℕ :=
  if hx0 : x.1 = 0 then
    1
  else if hxm3 : x.1 = m - 3 then
    2 * m - 3
  else if hxm2 : x.1 = m - 2 then
    2 * m - 1
  else
    m - 1

theorem rho0CaseI_zero [Fact (4 < m)] :
    rho0CaseI (m := m) (0 : Fin m) = 1 := by
  simp [rho0CaseI]

theorem rho0CaseI_m_sub_three [Fact (4 < m)] :
    rho0CaseI (m := m) (⟨m - 3, by
      have hm4 : 4 < m := Fact.out
      omega⟩ : Fin m) = 2 * m - 3 := by
  have hm4 : 4 < m := Fact.out
  have hm30 : m - 3 ≠ 0 := by omega
  simp [rho0CaseI, hm30]

theorem rho0CaseI_m_sub_two [Fact (4 < m)] :
    rho0CaseI (m := m) (⟨m - 2, by
      have hm4 : 4 < m := Fact.out
      omega⟩ : Fin m) = 2 * m - 1 := by
  have hm4 : 4 < m := Fact.out
  have hm20 : m - 2 ≠ 0 := by omega
  have hm23 : m - 2 ≠ m - 3 := by omega
  simp [rho0CaseI, hm20, hm23]

theorem rho0CaseI_other [Fact (4 < m)] {x : ℕ}
    (hxlt : x < m)
    (hx0 : x ≠ 0)
    (hxm3 : x ≠ m - 3)
    (hxm2 : x ≠ m - 2) :
    rho0CaseI (m := m) (⟨x, hxlt⟩ : Fin m) = m - 1 := by
  simp [rho0CaseI, hx0, hxm3, hxm2]

theorem sum_rho0CaseI [Fact (4 < m)] :
    (∑ x : Fin m, rho0CaseI (m := m) x) = m ^ 2 := by
  have hm0 : 0 < m := by
    have hm4 : 4 < m := Fact.out
    omega
  have hm1 : 1 ≤ m - 3 := by
    have hm4 : 4 < m := Fact.out
    omega
  let g : ℕ → ℕ := fun k =>
    if hk : k < m then rho0CaseI (m := m) (⟨k, hk⟩ : Fin m) else 0
  have hsumRange :
      (∑ x : Fin m, rho0CaseI (m := m) x) = Finset.sum (Finset.range m) g := by
    simpa [g] using (Fin.sum_univ_eq_sum_range g m)
  have hm4 : 4 < m := Fact.out
  have hm3lt : m - 3 < m := by omega
  have hm2lt : m - 2 < m := by omega
  have hhead : Finset.sum (Finset.range 1) g = 1 := by
    have hg0 : g 0 = 1 := by
      simpa [g, hm0] using rho0CaseI_zero (m := m)
    simpa [hg0]
  have hmid :
      Finset.sum (Finset.Ico 1 (m - 3)) g = (m - 4) * (m - 1) := by
    calc
      Finset.sum (Finset.Ico 1 (m - 3)) g
          = Finset.sum (Finset.Ico 1 (m - 3)) (fun _ => m - 1) := by
              apply Finset.sum_congr rfl
              intro k hk
              have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
              have hklt : k < m - 3 := (Finset.mem_Ico.mp hk).2
              have hkm : k < m := by omega
              have hk0 : k ≠ 0 := by omega
              have hkm3 : k ≠ m - 3 := by omega
              have hkm2 : k ≠ m - 2 := by omega
              simpa [g, hkm] using rho0CaseI_other (m := m) hkm hk0 hkm3 hkm2
      _ = (Finset.Ico 1 (m - 3)).card * (m - 1) := by
            simp
      _ = (m - 4) * (m - 1) := by
            simp [Nat.card_Ico]
            omega
  have hsuffix :
      Finset.sum (Finset.Ico (m - 3) m) g = 5 * m - 5 := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hlen : m - (m - 3) = 3 := by omega
    rw [hlen, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    rw [Finset.sum_range_zero]
    have hm1lt : m - 1 < m := by omega
    have hm30 : m - 3 ≠ 0 := by omega
    have hm20 : m - 2 ≠ 0 := by omega
    have hm23 : m - 2 ≠ m - 3 := by omega
    have hm10 : m - 1 ≠ 0 := by omega
    have hm13 : m - 1 ≠ m - 3 := by omega
    have hm12 : m - 1 ≠ m - 2 := by omega
    rw [show m - 3 + 0 = m - 3 by omega,
      show m - 3 + 1 = m - 2 by omega,
      show m - 3 + 2 = m - 1 by omega]
    simp [g, hm3lt, hm2lt, hm1lt, rho0CaseI, hm30, hm20, hm23, hm10, hm13, hm12]
    omega
  have hm3le : m - 3 ≤ m := by omega
  calc
    (∑ x : Fin m, rho0CaseI (m := m) x) = Finset.sum (Finset.range m) g := hsumRange
    _ = Finset.sum (Finset.range (m - 3)) g + Finset.sum (Finset.Ico (m - 3) m) g := by
          symm
          exact Finset.sum_range_add_sum_Ico g hm3le
    _ = (Finset.sum (Finset.range 1) g + Finset.sum (Finset.Ico 1 (m - 3)) g)
          + Finset.sum (Finset.Ico (m - 3) m) g := by
            rw [show Finset.sum (Finset.range (m - 3)) g =
              Finset.sum (Finset.range 1) g + Finset.sum (Finset.Ico 1 (m - 3)) g by
                symm
                exact Finset.sum_range_add_sum_Ico g hm1]
    _ = (1 + (m - 4) * (m - 1)) + (5 * m - 5) := by
          rw [hhead, hmid, hsuffix]
    _ = m ^ 2 := by
          let k : ℕ := m - 4
          have hmEq : m = k + 4 := by
            dsimp [k]
            omega
          rw [hmEq, pow_two]
          have hk1 : k + 4 - 4 = k := by omega
          have hk2 : k + 4 - 1 = k + 3 := by omega
          have hk3 : 5 * (k + 4) - 5 = 5 * k + 15 := by omega
          rw [hk1, hk2, hk3]
          ring_nf

theorem hreturn_line_case0_caseI [Fact (5 < m)] (x : Fin m) :
    ((returnMap0CaseIXY (m := m)^[rho0CaseI (m := m) x]) (linePoint0 (m := m) x)) =
      linePoint0 (m := m) (TorusD3Even.T0CaseI (m := m) x) := by
  have hm5 : 5 < m := Fact.out
  rcases x with ⟨x, hxlt⟩
  by_cases hx0 : x = 0
  · subst hx0
    simpa [rho0CaseI, TorusD3Even.T0CaseI] using
      firstReturn_line_zero_case0 (m := m)
  · by_cases hx1 : x = 1
    · subst hx1
      have hxm4 : 1 ≠ m - 4 := by omega
      have hxm3 : 1 ≠ m - 3 := by omega
      have hxm2 : 1 ≠ m - 2 := by omega
      have hxm1 : 1 ≠ m - 1 := by omega
      simpa [rho0CaseI, TorusD3Even.T0CaseI, hx0, hxm4, hxm3, hxm2, hxm1] using
        firstReturn_line_one (m := m)
    · by_cases hxm4 : x = m - 4
      · subst hxm4
        have hx0' : m - 4 ≠ 0 := by omega
        have hxm3 : m - 4 ≠ m - 3 := by omega
        have hxm2 : m - 4 ≠ m - 2 := by omega
        simpa [rho0CaseI, TorusD3Even.T0CaseI, hx0', hxm3, hxm2] using
          firstReturn_line_m_sub_four (m := m)
      · by_cases hxm3 : x = m - 3
        · subst hxm3
          have hx0' : m - 3 ≠ 0 := by omega
          have hxm2 : m - 3 ≠ m - 2 := by omega
          simpa [rho0CaseI, TorusD3Even.T0CaseI, hx0', hxm4, hxm2] using
            firstReturn_line_m_sub_three_case0 (m := m)
        · by_cases hxm2 : x = m - 2
          · subst hxm2
            have hx0' : m - 2 ≠ 0 := by omega
            have hxm3' : m - 2 ≠ m - 3 := by omega
            simpa [rho0CaseI, TorusD3Even.T0CaseI, hx0', hxm4, hxm3'] using
              firstReturn_line_m_sub_two_case0 (m := m)
          · by_cases hxm1 : x = m - 1
            · subst hxm1
              have hx0' : m - 1 ≠ 0 := by omega
              have hxm3' : m - 1 ≠ m - 3 := by omega
              have hxm2' : m - 1 ≠ m - 2 := by omega
              simpa [rho0CaseI, TorusD3Even.T0CaseI, hx0', hxm4, hxm3', hxm2'] using
                firstReturn_line_m_sub_one_case0 (m := m)
            · have hx2 : 2 ≤ x := by omega
              have hxle : x ≤ m - 5 := by omega
              simpa [rho0CaseI, TorusD3Even.T0CaseI, hx0, hx1, hxm4, hxm3, hxm2, hxm1] using
                firstReturn_line_generic (m := m) (x := x) hx2 hxle

theorem hsum_case0_caseI [Fact (5 < m)] (hmCaseI : m % 6 = 0 ∨ m % 6 = 2) :
    TorusD3Even.blockTime
        (TorusD3Even.T0CaseI (m := m))
        (rho0CaseI (m := m))
        ⟨0, by
          have hm0 : 0 < m := by
            have hm5 : 5 < m := Fact.out
            omega
          exact hm0⟩
        m = m ^ 2 := by
  have hm0 : 0 < m := by
    have hm5 : 5 < m := Fact.out
    omega
  let x0 : Fin m := ⟨0, hm0⟩
  let e : Fin m ≃ Fin m :=
    Equiv.ofBijective
      (fun i : Fin m => ((TorusD3Even.T0CaseI (m := m)^[i.1]) x0))
      (by
        simpa [laneMap0CaseI] using
          (cycleOn_laneMap0_caseI_mod_zeroTwo (m := m) hmCaseI).1)
  calc
    TorusD3Even.blockTime
        (TorusD3Even.T0CaseI (m := m))
        (rho0CaseI (m := m))
        x0
        m
        = Finset.sum (Finset.range m) (fun i =>
            rho0CaseI (m := m) (((TorusD3Even.T0CaseI (m := m)^[i]) x0))) := by
            simpa using
              blockTime_eq_sum_range
                (TorusD3Even.T0CaseI (m := m))
                (rho0CaseI (m := m))
                x0
                m
    _ = ∑ i : Fin m, rho0CaseI (m := m) (e i) := by
          rw [← Fin.sum_univ_eq_sum_range]
          rfl
    _ = ∑ x : Fin m, rho0CaseI (m := m) x := by
          exact Equiv.sum_comp e (fun x : Fin m => rho0CaseI (m := m) x)
    _ = m ^ 2 := by
          simpa using sum_rho0CaseI (m := m)

theorem hfirst_line_zero_case0 [Fact (5 < m)] :
    ∀ n, 0 < n →
      n < rho0CaseI (m := m) (0 : Fin m) →
        (returnMap0CaseIXY (m := m)^[n]) (linePoint0 (m := m) (0 : Fin m)) ∉
          Set.range (linePoint0 (m := m)) := by
  intro n hn0 hnlt
  have hrho : rho0CaseI (m := m) (0 : Fin m) = 1 := rho0CaseI_zero (m := m)
  omega

theorem hfirst_line_generic_case0 [Fact (5 < m)] {x : ℕ}
    (hx2 : 2 ≤ x) (hxle : x ≤ m - 5) :
    ∀ n, 0 < n →
      n < rho0CaseI (m := m) (⟨x, by omega⟩ : Fin m) →
        (returnMap0CaseIXY (m := m)^[n]) (linePoint0 (m := m) (⟨x, by omega⟩ : Fin m)) ∉
          Set.range (linePoint0 (m := m)) := by
  let F := returnMap0CaseIXY (m := m)
  let xFin : Fin m := ⟨x, by omega⟩
  intro n hn0 hnlt
  have hm0 : 0 < m := by
    have hm5 : 5 < m := Fact.out
    omega
  letI : Fact (0 < m) := ⟨hm0⟩
  have hx1 : 1 ≤ x := by omega
  have hx0 : x ≠ 0 := by omega
  have hxm3 : x ≠ m - 3 := by omega
  have hxm2 : x ≠ m - 2 := by omega
  have hrho : rho0CaseI (m := m) xFin = m - 1 := by
    simpa [xFin] using rho0CaseI_other (m := m) (x := x) (by omega) hx0 hxm3 hxm2
  have hnm : n < m - 1 := by
    simpa [xFin, hrho] using hnlt
  have hstart :
      F (linePoint0 (m := m) xFin) =
        ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m)) := by
    simpa [linePoint0, xFin] using returnMap0CaseIXY_line_generic (m := m) hx1 (by omega)
  have h1 :
      ((F^[1]) (linePoint0 (m := m) xFin)) =
        ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m)) := by
    simpa [Function.iterate_one] using hstart
  by_cases hprefix : n ≤ x
  · let t : ℕ := n - 1
    have ht : t ≤ x - 1 := by
      dsimp [t]
      omega
    have hnEq : n = t + 1 := by
      dsimp [t]
      omega
    have hprefixIter :
        ((F^[t]) ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m))) =
          ((((x + 1 : ℕ) : ZMod m)), (((1 + t : ℕ) : ZMod m))) := by
      simpa using iterate_returnMap0CaseIXY_prefix_partial (m := m) hx2 (by omega) ht
    have hiter :
        ((F^[n]) (linePoint0 (m := m) xFin)) =
          ((((x + 1 : ℕ) : ZMod m)), (((n : ℕ) : ZMod m))) := by
      rw [hnEq, Function.iterate_add_apply, h1, hprefixIter]
      dsimp [t]
      have hsub : n - 1 + 1 = n := Nat.sub_add_cancel hn0
      have hsub' : 1 + (n - 1) = n := by omega
      simpa [Nat.cast_add, hsub, hsub', add_comm, add_left_comm, add_assoc]
    rw [hiter]
    exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (((x + 1 : ℕ) : ZMod m)))
      hn0 (by omega)
  · have hx1le : x + 1 ≤ n := by omega
    let t : ℕ := n - (x + 1)
    have ht : t ≤ m - x - 3 := by
      dsimp [t]
      omega
    have hnEq : n = x + 1 + t := by
      dsimp [t]
      omega
    have hprefixEnd :
        ((F^[x]) (linePoint0 (m := m) xFin)) =
          ((((x + 1 : ℕ) : ZMod m)), (((x : ℕ) : ZMod m))) := by
      have hprefixIter :
          ((F^[x - 1]) ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m))) =
            ((((x + 1 : ℕ) : ZMod m)), (((x : ℕ) : ZMod m))) := by
        have h := iterate_returnMap0CaseIXY_prefix_partial (m := m) hx2 (by omega) (t := x - 1) le_rfl
        simpa [Nat.add_sub_of_le hx1] using h
      rw [show x = (x - 1) + 1 by omega, Function.iterate_add_apply, h1, hprefixIter]
      have hxsub : x - 1 + 1 = x := Nat.sub_add_cancel hx1
      simp [hxsub]
    have hdiag :
        F ((((x + 1 : ℕ) : ZMod m)), (((x : ℕ) : ZMod m))) =
          ((((x + 2 : ℕ) : ZMod m)), (((x + 2 : ℕ) : ZMod m))) :=
      returnMap0CaseIXY_diag_step (m := m) hx1 (by omega)
    have hdiagIter :
        ((F^[x + 1]) (linePoint0 (m := m) xFin)) =
          ((((x + 2 : ℕ) : ZMod m)), (((x + 2 : ℕ) : ZMod m))) := by
      rw [show x + 1 = 1 + x by omega, Function.iterate_add_apply, hprefixEnd]
      simpa [Function.iterate_one] using hdiag
    have hsuffix :
        ((F^[t]) ((((x + 2 : ℕ) : ZMod m)), (((x + 2 : ℕ) : ZMod m)))) =
          ((((x + 2 : ℕ) : ZMod m)), (((x + 2 + t : ℕ) : ZMod m))) := by
      have ht' : t ≤ m - x - 2 := by omega
      simpa using iterate_returnMap0CaseIXY_suffix_partial (m := m) hxle ht'
    have hiter :
        ((F^[n]) (linePoint0 (m := m) xFin)) =
          ((((x + 2 : ℕ) : ZMod m)), (((x + 2 + t : ℕ) : ZMod m))) := by
      rw [hnEq]
      rw [show x + 1 + t = t + (x + 1) by omega, Function.iterate_add_apply, hdiagIter, hsuffix]
    rw [hiter]
    exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (((x + 2 : ℕ) : ZMod m)))
      (by omega) (by omega)

theorem hfirst_line_one_case0 [Fact (5 < m)] :
    ∀ n, 0 < n →
      n < rho0CaseI (m := m) (⟨1, by
        have hm5 : 5 < m := Fact.out
        omega⟩ : Fin m) →
        (returnMap0CaseIXY (m := m)^[n])
            (linePoint0 (m := m)
              (⟨1, by
                have hm5 : 5 < m := Fact.out
                omega⟩ : Fin m)) ∉
          Set.range (linePoint0 (m := m)) := by
  let F := returnMap0CaseIXY (m := m)
  let xFin : Fin m := ⟨1, by
    have hm5 : 5 < m := Fact.out
    omega⟩
  intro n hn0 hnlt
  have hm0 : 0 < m := by
    have hm5 : 5 < m := Fact.out
    omega
  letI : Fact (0 < m) := ⟨hm0⟩
  have h10 : (1 : ℕ) ≠ 0 := by decide
  have h1m3 : (1 : ℕ) ≠ m - 3 := by
    have hm5 : 5 < m := Fact.out
    omega
  have h1m2 : (1 : ℕ) ≠ m - 2 := by
    have hm5 : 5 < m := Fact.out
    omega
  have hrho : rho0CaseI (m := m) xFin = m - 1 := by
    simpa [xFin] using rho0CaseI_other (m := m) (x := 1) (by
      have hm5 : 5 < m := Fact.out
      omega) h10 h1m3 h1m2
  have hnm : n < m - 1 := by
    simpa [xFin, hrho] using hnlt
  have h1 :
      ((F^[1]) (linePoint0 (m := m) xFin)) =
        ((2 : ZMod m), (1 : ZMod m)) := by
    simpa [Function.iterate_one, linePoint0, xFin] using
      returnMap0CaseIXY_line_generic (m := m) (x := 1) (by decide) (by omega)
  have hdiag :
      F ((2 : ZMod m), (1 : ZMod m)) = ((3 : ZMod m), (3 : ZMod m)) := by
    simpa using
      returnMap0CaseIXY_diag_step (m := m) (x := 1) (by decide) (by omega)
  have h2 :
      ((F^[2]) (linePoint0 (m := m) xFin)) =
        ((3 : ZMod m), (3 : ZMod m)) := by
    calc
      ((F^[2]) (linePoint0 (m := m) xFin))
          = F (((F^[1]) (linePoint0 (m := m) xFin))) := by
              simp [Function.iterate_succ_apply']
      _ = F ((2 : ZMod m), (1 : ZMod m)) := by rw [h1]
      _ = ((3 : ZMod m), (3 : ZMod m)) := hdiag
  by_cases hn1 : n = 1
  · rw [hn1, h1]
    simpa using
      (not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (2 : ZMod m)) (n := 1)
        (by decide) (by
          have hm5 : 5 < m := Fact.out
          omega))
  · let t : ℕ := n - 2
    have hn2 : 2 ≤ n := by omega
    have ht : t ≤ m - 4 := by
      dsimp [t]
      omega
    have ht' : t ≤ m - 3 := by omega
    have hnEq : n = t + 2 := by
      dsimp [t]
      omega
    have hsuffix :
        ((F^[t]) ((3 : ZMod m), (3 : ZMod m))) =
          ((3 : ZMod m), (((3 + t : ℕ) : ZMod m))) := by
      have hxle1 : 1 ≤ m - 5 := by
        have hm5 : 5 < m := Fact.out
        omega
      simpa using iterate_returnMap0CaseIXY_suffix_partial (m := m) (x := 1) hxle1 ht'
    have hiter :
        ((F^[n]) (linePoint0 (m := m) xFin)) =
          ((3 : ZMod m), (((3 + t : ℕ) : ZMod m))) := by
      rw [hnEq, show t + 2 = t + (1 + 1) by omega, Function.iterate_add_apply, h2, hsuffix]
    rw [hiter]
    exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (3 : ZMod m)) (by omega) (by omega)

theorem hfirst_line_m_sub_one_case0 [Fact (5 < m)] :
    ∀ n, 0 < n →
      n < rho0CaseI (m := m) (⟨m - 1, by
        have hm5 : 5 < m := Fact.out
        omega⟩ : Fin m) →
        (returnMap0CaseIXY (m := m)^[n])
            (linePoint0 (m := m)
              (⟨m - 1, by
                have hm5 : 5 < m := Fact.out
                omega⟩ : Fin m)) ∉
          Set.range (linePoint0 (m := m)) := by
  let F := returnMap0CaseIXY (m := m)
  let xFin : Fin m := ⟨m - 1, by
    have hm5 : 5 < m := Fact.out
    omega⟩
  intro n hn0 hnlt
  have hm0 : 0 < m := by
    have hm5 : 5 < m := Fact.out
    omega
  letI : Fact (0 < m) := ⟨hm0⟩
  have hm1le : 1 ≤ m := by
    have hm5 : 5 < m := Fact.out
    omega
  have hneg1cast : (((m - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) :=
    cast_sub_one_eq_neg_one (m := m) hm1le
  have hm10 : m - 1 ≠ 0 := by
    have hm5 : 5 < m := Fact.out
    omega
  have hm1m3 : m - 1 ≠ m - 3 := by
    have hm5 : 5 < m := Fact.out
    omega
  have hm1m2 : m - 1 ≠ m - 2 := by
    have hm5 : 5 < m := Fact.out
    omega
  have hrho : rho0CaseI (m := m) xFin = m - 1 := by
    simpa [xFin] using rho0CaseI_other (m := m) (x := m - 1) (by
      have hm5 : 5 < m := Fact.out
      omega) hm10 hm1m3 hm1m2
  have hnm : n < m - 1 := by
    simpa [xFin, hrho] using hnlt
  have h1 :
      ((F^[1]) (linePoint0 (m := m) xFin)) =
        ((-1 : ZMod m), (1 : ZMod m)) := by
    simpa [Function.iterate_one, linePoint0, xFin, hneg1cast] using
      returnMap0CaseIXY_m_sub_one_start (m := m)
  let t : ℕ := n - 1
  have ht : t ≤ m - 3 := by
    dsimp [t]
    omega
  have hnEq : n = t + 1 := by
    dsimp [t]
    omega
  have hprefix :
      ((F^[t]) ((-1 : ZMod m), (1 : ZMod m))) =
        ((-1 : ZMod m), (((1 + t : ℕ) : ZMod m))) := by
    have hx2' : 2 ≤ m - 2 := by
      have hm5 : 5 < m := Fact.out
      omega
    have hxle' : m - 2 ≤ m - 2 := le_rfl
    simpa [hneg1cast, show m - 2 + 1 = m - 1 by omega] using
      iterate_returnMap0CaseIXY_prefix_partial (m := m) (x := m - 2) hx2' hxle' ht
  have hiter :
      ((F^[n]) (linePoint0 (m := m) xFin)) =
        ((-1 : ZMod m), (((n : ℕ) : ZMod m))) := by
    rw [hnEq, Function.iterate_add_apply, h1, hprefix]
    dsimp [t]
    have hsub : n - 1 + 1 = n := Nat.sub_add_cancel hn0
    have hsub' : 1 + (n - 1) = n := by omega
    simpa [Nat.cast_add, hsub, hsub', add_comm, add_left_comm, add_assoc]
  rw [hiter]
  exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (-1 : ZMod m)) hn0 (by omega)

theorem hfirst_line_m_sub_four_case0 [Fact (5 < m)] :
    ∀ n, 0 < n →
      n < rho0CaseI (m := m) (⟨m - 4, by
        have hm5 : 5 < m := Fact.out
        omega⟩ : Fin m) →
        (returnMap0CaseIXY (m := m)^[n])
            (linePoint0 (m := m)
              (⟨m - 4, by
                have hm5 : 5 < m := Fact.out
                omega⟩ : Fin m)) ∉
          Set.range (linePoint0 (m := m)) := by
  let F := returnMap0CaseIXY (m := m)
  let xFin : Fin m := ⟨m - 4, by
    have hm5 : 5 < m := Fact.out
    omega⟩
  intro n hn0 hnlt
  have hm0 : 0 < m := by
    have hm5 : 5 < m := Fact.out
    omega
  letI : Fact (0 < m) := ⟨hm0⟩
  have hm2le : 2 ≤ m := by
    have hm5 : 5 < m := Fact.out
    omega
  have hxm40 : m - 4 ≠ 0 := by
    have hm5 : 5 < m := Fact.out
    omega
  have hxm4m3 : m - 4 ≠ m - 3 := by
    have hm5 : 5 < m := Fact.out
    omega
  have hxm4m2 : m - 4 ≠ m - 2 := by
    have hm5 : 5 < m := Fact.out
    omega
  have hrho : rho0CaseI (m := m) xFin = m - 1 := by
    simpa [xFin] using rho0CaseI_other (m := m) (x := m - 4) (by
      have hm5 : 5 < m := Fact.out
      omega) hxm40 hxm4m3 hxm4m2
  have hnm : n < m - 1 := by
    simpa [xFin, hrho] using hnlt
  have hneg2cast : (((m - 2 : ℕ) : ZMod m)) = (-2 : ZMod m) :=
    cast_sub_two_eq_neg_two (m := m) hm2le
  have h1 :
      ((F^[1]) (linePoint0 (m := m) xFin)) =
        ((((m - 3 : ℕ) : ZMod m)), (1 : ZMod m)) := by
    simpa [Function.iterate_one, linePoint0, xFin, show m - 4 + 1 = m - 3 by omega] using
      returnMap0CaseIXY_line_generic (m := m) (x := m - 4) (by omega) (by omega)
  have hprefixEnd :
      ((F^[m - 4]) (linePoint0 (m := m) xFin)) =
        ((((m - 3 : ℕ) : ZMod m)), (((m - 4 : ℕ) : ZMod m))) := by
    have hprefix :
        ((F^[m - 5]) ((((m - 3 : ℕ) : ZMod m)), (1 : ZMod m))) =
          ((((m - 3 : ℕ) : ZMod m)), (((m - 4 : ℕ) : ZMod m))) := by
      have hx2' : 2 ≤ m - 4 := by
        have hm5 : 5 < m := Fact.out
        omega
      have hxle' : m - 4 ≤ m - 2 := by
        have hm5 : 5 < m := Fact.out
        omega
      have h :=
        iterate_returnMap0CaseIXY_prefix_partial (m := m) (x := m - 4) hx2' hxle'
          (t := m - 5) le_rfl
      simpa [show m - 4 + 1 = m - 3 by omega, show 1 + (m - 5) = m - 4 by omega] using h
    rw [show m - 4 = (m - 5) + 1 by omega, Function.iterate_add_apply, h1, hprefix]
    simpa [show m - 5 + 1 = m - 4 by omega]
  have hdiag :
      F ((((m - 3 : ℕ) : ZMod m)), (((m - 4 : ℕ) : ZMod m))) =
        ((((m - 2 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) := by
    simpa [show m - 4 + 1 = m - 3 by omega, show m - 4 + 2 = m - 2 by omega] using
      returnMap0CaseIXY_diag_step (m := m) (x := m - 4) (by omega) (by omega)
  have hmid :
      ((F^[m - 3]) (linePoint0 (m := m) xFin)) =
        ((((m - 2 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) := by
    rw [show m - 3 = 1 + (m - 4) by omega, Function.iterate_add_apply, hprefixEnd]
    simpa [Function.iterate_one] using hdiag
  have htop :
      F ((((m - 2 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) =
        ((-2 : ZMod m), (-1 : ZMod m)) := by
    simpa [hneg2cast] using returnMap0CaseIXY_m_sub_two_m_sub_two (m := m)
  have hlast :
      ((F^[m - 2]) (linePoint0 (m := m) xFin)) =
        ((-2 : ZMod m), (-1 : ZMod m)) := by
    rw [show m - 2 = 1 + (m - 3) by omega, Function.iterate_add_apply, hmid]
    simpa [Function.iterate_one] using htop
  by_cases hprefix : n ≤ m - 4
  · let t : ℕ := n - 1
    have ht : t ≤ m - 5 := by
      dsimp [t]
      omega
    have hnEq : n = t + 1 := by
      dsimp [t]
      omega
    have hprefixIter :
        ((F^[t]) ((((m - 3 : ℕ) : ZMod m)), (1 : ZMod m))) =
          ((((m - 3 : ℕ) : ZMod m)), (((1 + t : ℕ) : ZMod m))) := by
      have hx2' : 2 ≤ m - 4 := by
        have hm5 : 5 < m := Fact.out
        omega
      have hxle' : m - 4 ≤ m - 2 := by
        have hm5 : 5 < m := Fact.out
        omega
      simpa [show m - 4 + 1 = m - 3 by omega] using
        iterate_returnMap0CaseIXY_prefix_partial (m := m) (x := m - 4) hx2' hxle' ht
    have hiter :
        ((F^[n]) (linePoint0 (m := m) xFin)) =
          ((((m - 3 : ℕ) : ZMod m)), (((n : ℕ) : ZMod m))) := by
      rw [hnEq, Function.iterate_add_apply, h1, hprefixIter]
      dsimp [t]
      have hsub : n - 1 + 1 = n := Nat.sub_add_cancel hn0
      have hsub' : 1 + (n - 1) = n := by omega
      simpa [Nat.cast_add, hsub, hsub', add_comm, add_left_comm, add_assoc]
    rw [hiter]
    exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (((m - 3 : ℕ) : ZMod m)))
      hn0 (by omega)
  · by_cases hmidEq : n = m - 3
    · rw [hmidEq, hmid]
      exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (((m - 2 : ℕ) : ZMod m)))
        (by omega) (by omega)
    · have hlastEq : n = m - 2 := by omega
      rw [hlastEq, hlast]
      exact not_mem_range_linePoint0_of_snd_ne_zero (m := m) (u := ((-2 : ZMod m), (-1 : ZMod m)))
        (by exact neg_ne_zero.mpr (one_ne_zero (m := m)))

theorem hfirst_line_m_sub_three_case0 [Fact (5 < m)] :
    ∀ n, 0 < n →
      n < rho0CaseI (m := m) (⟨m - 3, by
        have hm5 : 5 < m := Fact.out
        omega⟩ : Fin m) →
        (returnMap0CaseIXY (m := m)^[n])
            (linePoint0 (m := m)
              (⟨m - 3, by
                have hm5 : 5 < m := Fact.out
                omega⟩ : Fin m)) ∉
          Set.range (linePoint0 (m := m)) := by
  let F := returnMap0CaseIXY (m := m)
  let xFin : Fin m := ⟨m - 3, by
    have hm5 : 5 < m := Fact.out
    omega⟩
  intro n hn0 hnlt
  have hm0 : 0 < m := by
    have hm5 : 5 < m := Fact.out
    omega
  letI : Fact (0 < m) := ⟨hm0⟩
  have hrho : rho0CaseI (m := m) xFin = 2 * m - 3 := by
    simpa [xFin] using rho0CaseI_m_sub_three (m := m)
  have hnm : n < 2 * m - 3 := by
    simpa [xFin, hrho] using hnlt
  have hm2le : 2 ≤ m := by
    have hm5 : 5 < m := Fact.out
    omega
  have hm1le : 1 ≤ m := by
    have hm5 : 5 < m := Fact.out
    omega
  have hneg2cast : (((m - 2 : ℕ) : ZMod m)) = (-2 : ZMod m) :=
    cast_sub_two_eq_neg_two (m := m) hm2le
  have hneg1cast : (((m - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) :=
    cast_sub_one_eq_neg_one (m := m) hm1le
  have h1 :
      ((F^[1]) (linePoint0 (m := m) xFin)) =
        ((((m - 2 : ℕ) : ZMod m)), (1 : ZMod m)) := by
    have hx1' : 1 ≤ m - 3 := by
      have hm5 : 5 < m := Fact.out
      omega
    have hxle' : m - 3 ≤ m - 3 := le_rfl
    simpa [Function.iterate_one, linePoint0, xFin, show m - 3 + 1 = m - 2 by omega] using
      returnMap0CaseIXY_line_generic (m := m) (x := m - 3) hx1' hxle'
  have hprefixEnd :
      ((F^[m - 3]) (linePoint0 (m := m) xFin)) =
        ((((m - 2 : ℕ) : ZMod m)), (((m - 3 : ℕ) : ZMod m))) := by
    have hprefix :
        ((F^[m - 4]) ((((m - 2 : ℕ) : ZMod m)), (1 : ZMod m))) =
          ((((m - 2 : ℕ) : ZMod m)), (((m - 3 : ℕ) : ZMod m))) := by
      have hx2' : 2 ≤ m - 3 := by
        have hm5 : 5 < m := Fact.out
        omega
      have hxle' : m - 3 ≤ m - 2 := by
        have hm5 : 5 < m := Fact.out
        omega
      have h :=
        iterate_returnMap0CaseIXY_prefix_partial (m := m) (x := m - 3) hx2' hxle'
          (t := m - 4) le_rfl
      have hsum : (((1 + (m - 4) : ℕ) : ZMod m)) = (((m - 3 : ℕ) : ZMod m)) := by
        congr
        omega
      simpa [show m - 3 + 1 = m - 2 by omega, hneg2cast, hsum] using h
    have hsplit : m - 3 = (m - 4) + 1 := by
      have hm5 : 5 < m := Fact.out
      omega
    have hsucc : m - 4 + 1 = m - 3 := by
      have hm5 : 5 < m := Fact.out
      omega
    rw [hsplit, Function.iterate_add_apply, h1, hprefix]
    simpa [hsucc]
  have hdiag :
      F ((((m - 2 : ℕ) : ZMod m)), (((m - 3 : ℕ) : ZMod m))) =
        ((-1 : ZMod m), (-1 : ZMod m)) := by
    have hx1' : 1 ≤ m - 3 := by
      have hm5 : 5 < m := Fact.out
      omega
    have hxle' : m - 3 ≤ m - 2 := by
      have hm5 : 5 < m := Fact.out
      omega
    simpa [show m - 3 + 1 = m - 2 by omega, show m - 3 + 2 = m - 1 by omega, hneg1cast] using
      returnMap0CaseIXY_diag_step (m := m) (x := m - 3) hx1' hxle'
  have hdiagEnd :
      ((F^[m - 2]) (linePoint0 (m := m) xFin)) =
        ((-1 : ZMod m), (-1 : ZMod m)) := by
    rw [show m - 2 = 1 + (m - 3) by omega, Function.iterate_add_apply, hprefixEnd]
    simpa [Function.iterate_one] using hdiag
  have hturn :
      ((F^[m - 1]) (linePoint0 (m := m) xFin)) =
        ((2 : ZMod m), (2 : ZMod m)) := by
    rw [show m - 1 = 1 + (m - 2) by omega, Function.iterate_add_apply, hdiagEnd]
    simpa [Function.iterate_one] using returnMap0CaseIXY_m_sub_one_m_sub_one (m := m)
  by_cases hprefix : n ≤ m - 3
  · let t : ℕ := n - 1
    have ht : t ≤ m - 4 := by
      dsimp [t]
      omega
    have hnEq : n = t + 1 := by
      dsimp [t]
      omega
    have hprefixIter :
        ((F^[t]) ((((m - 2 : ℕ) : ZMod m)), (1 : ZMod m))) =
          ((((m - 2 : ℕ) : ZMod m)), (((1 + t : ℕ) : ZMod m))) := by
      have hx2' : 2 ≤ m - 3 := by
        have hm5 : 5 < m := Fact.out
        omega
      have hxle' : m - 3 ≤ m - 2 := by
        have hm5 : 5 < m := Fact.out
        omega
      simpa [show m - 3 + 1 = m - 2 by omega, hneg2cast] using
        iterate_returnMap0CaseIXY_prefix_partial (m := m) (x := m - 3) hx2' hxle' ht
    have hiter :
        ((F^[n]) (linePoint0 (m := m) xFin)) =
          ((((m - 2 : ℕ) : ZMod m)), (((n : ℕ) : ZMod m))) := by
      rw [hnEq, Function.iterate_add_apply, h1, hprefixIter]
      dsimp [t]
      have hsub : n - 1 + 1 = n := Nat.sub_add_cancel hn0
      have hsub' : 1 + (n - 1) = n := by omega
      simpa [Nat.cast_add, hsub, hsub', add_comm, add_left_comm, add_assoc]
    rw [hiter]
    exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (((m - 2 : ℕ) : ZMod m)))
      hn0 (by omega)
  · by_cases hdiagEq : n = m - 2
    · rw [hdiagEq, hdiagEnd]
      exact not_mem_range_linePoint0_of_snd_ne_zero (m := m) (u := ((-1 : ZMod m), (-1 : ZMod m)))
        (by exact neg_ne_zero.mpr (one_ne_zero (m := m)))
    · by_cases hturnEq : n = m - 1
      · rw [hturnEq, hturn]
        simpa using
          (not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (2 : ZMod m)) (n := 2)
            (by omega) (by omega))
      · have hm1 : m ≤ n := by omega
        let t : ℕ := n - (m - 1)
        have ht : t ≤ m - 3 := by
          dsimp [t]
          omega
        have hnEq : n = t + (m - 1) := by
          dsimp [t]
          omega
        have htpos : 0 < t := by
          dsimp [t]
          omega
        have hsuffix :
            ((F^[t]) ((2 : ZMod m), (2 : ZMod m))) =
              ((2 : ZMod m), (((2 + t : ℕ) : ZMod m))) := by
          have hxle0 : 0 ≤ m - 5 := by
            have hm5 : 5 < m := Fact.out
            omega
          have ht' : t ≤ m - 2 := by omega
          simpa using iterate_returnMap0CaseIXY_suffix_partial (m := m) (x := 0) hxle0 ht'
        have hiter :
            ((F^[n]) (linePoint0 (m := m) xFin)) =
              ((2 : ZMod m), (((2 + t : ℕ) : ZMod m))) := by
          rw [hnEq, Function.iterate_add_apply, hturn, hsuffix]
        rw [hiter]
        exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (2 : ZMod m))
          (by omega) (by omega)

theorem hfirst_line_m_sub_two_case0 [Fact (5 < m)] :
    ∀ n, 0 < n →
      n < rho0CaseI (m := m) (⟨m - 2, by
        have hm5 : 5 < m := Fact.out
        omega⟩ : Fin m) →
        (returnMap0CaseIXY (m := m)^[n])
            (linePoint0 (m := m)
              (⟨m - 2, by
                have hm5 : 5 < m := Fact.out
                omega⟩ : Fin m)) ∉
          Set.range (linePoint0 (m := m)) := by
  let F := returnMap0CaseIXY (m := m)
  let xFin : Fin m := ⟨m - 2, by
    have hm5 : 5 < m := Fact.out
    omega⟩
  intro n hn0 hnlt
  have hm0 : 0 < m := by
    have hm5 : 5 < m := Fact.out
    omega
  letI : Fact (0 < m) := ⟨hm0⟩
  have hrho : rho0CaseI (m := m) xFin = 2 * m - 1 := by
    simpa [xFin] using rho0CaseI_m_sub_two (m := m)
  have hnm : n < 2 * m - 1 := by
    simpa [xFin, hrho] using hnlt
  have hm2le : 2 ≤ m := by
    have hm5 : 5 < m := Fact.out
    omega
  have hm1le : 1 ≤ m := by
    have hm5 : 5 < m := Fact.out
    omega
  have hneg2cast : (((m - 2 : ℕ) : ZMod m)) = (-2 : ZMod m) :=
    cast_sub_two_eq_neg_two (m := m) hm2le
  have hneg1cast : (((m - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) :=
    cast_sub_one_eq_neg_one (m := m) hm1le
  have h1 :
      ((F^[1]) (linePoint0 (m := m) xFin)) =
        ((0 : ZMod m), (2 : ZMod m)) := by
    simpa [Function.iterate_one, linePoint0, xFin, hneg2cast] using
      returnMap0CaseIXY_m_sub_two_zero (m := m)
  have hzeroEnd :
      ((F^[m - 2]) (linePoint0 (m := m) xFin)) =
        ((0 : ZMod m), (((m - 1 : ℕ) : ZMod m))) := by
    have hzero :
        ((F^[m - 3]) ((0 : ZMod m), (2 : ZMod m))) =
          ((0 : ZMod m), (((m - 1 : ℕ) : ZMod m))) := by
      have h := iterate_returnMap0CaseIXY_zero_column_partial (m := m) (t := m - 3) le_rfl
      have hsumNat : 2 + (m - 3) = m - 1 := by
        have hm5 : 5 < m := Fact.out
        omega
      have hsum : (((2 + (m - 3) : ℕ) : ZMod m)) = (((m - 1 : ℕ) : ZMod m)) := by
        simpa [hsumNat]
      simpa [hsum] using h
    have hsplit : m - 2 = (m - 3) + 1 := by
      have hm5 : 5 < m := Fact.out
      omega
    rw [hsplit, Function.iterate_add_apply, h1, hzero]
  have hone :
      ((F^[m - 1]) (linePoint0 (m := m) xFin)) =
        ((1 : ZMod m), (1 : ZMod m)) := by
    calc
      ((F^[m - 1]) (linePoint0 (m := m) xFin))
          = ((F^[1]) (((F^[m - 2]) (linePoint0 (m := m) xFin)))) := by
              rw [show m - 1 = 1 + (m - 2) by omega, Function.iterate_add_apply]
      _ = ((F^[1]) ((0 : ZMod m), (((m - 1 : ℕ) : ZMod m)))) := by
            rw [hzeroEnd]
      _ = ((1 : ZMod m), (1 : ZMod m)) := by
            simpa [Function.iterate_one, hneg1cast] using
              returnMap0CaseIXY_zero_m_sub_one (m := m)
  have hzeroOne :
      ((F^[m]) (linePoint0 (m := m) xFin)) =
        ((0 : ZMod m), (1 : ZMod m)) := by
    have h' :
        F (((F^[m - 1]) (linePoint0 (m := m) xFin))) =
          ((0 : ZMod m), (1 : ZMod m)) := by
      rw [hone]
      simpa using returnMap0CaseIXY_one_one (m := m)
    have h'' :
        ((F^[Nat.succ (m - 1)]) (linePoint0 (m := m) xFin)) =
          ((0 : ZMod m), (1 : ZMod m)) := by
      rw [Function.iterate_succ_apply']
      exact h'
    simpa [Nat.succ_eq_add_one, Nat.sub_add_cancel hm1le] using h''
  have honeTwo :
      ((F^[m + 1]) (linePoint0 (m := m) xFin)) =
        ((1 : ZMod m), (2 : ZMod m)) := by
    have h' :
        F (((F^[m]) (linePoint0 (m := m) xFin))) =
          ((1 : ZMod m), (2 : ZMod m)) := by
      rw [hzeroOne]
      simpa using returnMap0CaseIXY_zero_one (m := m)
    have h'' :
        ((F^[Nat.succ m]) (linePoint0 (m := m) xFin)) =
          ((1 : ZMod m), (2 : ZMod m)) := by
      rw [Function.iterate_succ_apply']
      exact h'
    simpa [Nat.succ_eq_add_one] using h''
  by_cases hzero : n ≤ m - 2
  · let t : ℕ := n - 1
    have ht : t ≤ m - 3 := by
      dsimp [t]
      omega
    have hnEq : n = t + 1 := by
      dsimp [t]
      omega
    have hzeroIter :
        ((F^[t]) ((0 : ZMod m), (2 : ZMod m))) =
          ((0 : ZMod m), (((2 + t : ℕ) : ZMod m))) := by
      simpa using iterate_returnMap0CaseIXY_zero_column_partial (m := m) ht
    have hiter :
        ((F^[n]) (linePoint0 (m := m) xFin)) =
          ((0 : ZMod m), (((n + 1 : ℕ) : ZMod m))) := by
      rw [hnEq, Function.iterate_add_apply, h1, hzeroIter]
      dsimp [t]
      have hsub : n - 1 + 1 = n := Nat.sub_add_cancel hn0
      have hsub' : 2 + (n - 1) = n + 1 := by omega
      simpa [Nat.cast_add, hsub, hsub', add_comm, add_left_comm, add_assoc]
    rw [hiter]
    have hpos : 0 < n + 1 := by omega
    have hlt : n + 1 < m := by omega
    exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (0 : ZMod m)) hpos hlt
  · by_cases honeEq : n = m - 1
    · rw [honeEq, hone]
      simpa using
        (not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (1 : ZMod m)) (n := 1)
          (by omega) (by omega))
    · by_cases hzeroOneEq : n = m
      · rw [hzeroOneEq, hzeroOne]
        simpa using
          (not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (0 : ZMod m)) (n := 1)
            (by omega) (by omega))
      · have hm1 : m + 1 ≤ n := by omega
        let t : ℕ := n - (m + 1)
        have ht : t ≤ m - 3 := by
          dsimp [t]
          omega
        have hnEq : n = t + (m + 1) := by
          dsimp [t]
          omega
        have honeIter :
            ((F^[t]) ((1 : ZMod m), (2 : ZMod m))) =
              ((1 : ZMod m), (((2 + t : ℕ) : ZMod m))) := by
          simpa using iterate_returnMap0CaseIXY_one_column_partial (m := m) ht
        have hiter :
            ((F^[n]) (linePoint0 (m := m) xFin)) =
              ((1 : ZMod m), (((2 + t : ℕ) : ZMod m))) := by
          rw [hnEq, Function.iterate_add_apply, honeTwo, honeIter]
        rw [hiter]
        have hpos : 0 < 2 + t := by omega
        have hlt : 2 + t < m := by omega
        exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (1 : ZMod m)) hpos hlt

theorem hfirst_line_case0_caseI [Fact (5 < m)] (x : Fin m) :
    ∀ n, 0 < n →
      n < rho0CaseI (m := m) x →
        (returnMap0CaseIXY (m := m)^[n]) (linePoint0 (m := m) x) ∉ Set.range (linePoint0 (m := m)) := by
  by_cases hx0 : x.1 = 0
  · have hx' : x = 0 := Fin.ext hx0
    simpa [hx'] using hfirst_line_zero_case0 (m := m)
  by_cases hx1 : x.1 = 1
  · have hx' : x = ⟨1, by
        have hm5 : 5 < m := Fact.out
        omega⟩ := Fin.ext hx1
    simpa [hx'] using hfirst_line_one_case0 (m := m)
  by_cases hxm4 : x.1 = m - 4
  · have hx' : x = ⟨m - 4, by
        have hm5 : 5 < m := Fact.out
        omega⟩ := Fin.ext hxm4
    simpa [hx'] using hfirst_line_m_sub_four_case0 (m := m)
  by_cases hxm3 : x.1 = m - 3
  · have hx' : x = ⟨m - 3, by
        have hm5 : 5 < m := Fact.out
        omega⟩ := Fin.ext hxm3
    simpa [hx'] using hfirst_line_m_sub_three_case0 (m := m)
  by_cases hxm2 : x.1 = m - 2
  · have hx' : x = ⟨m - 2, by
        have hm5 : 5 < m := Fact.out
        omega⟩ := Fin.ext hxm2
    simpa [hx'] using hfirst_line_m_sub_two_case0 (m := m)
  by_cases hxm1 : x.1 = m - 1
  · have hx' : x = ⟨m - 1, by
        have hm5 : 5 < m := Fact.out
        omega⟩ := Fin.ext hxm1
    simpa [hx'] using hfirst_line_m_sub_one_case0 (m := m)
  have hx2 : 2 ≤ x.1 := by omega
  have hxle : x.1 ≤ m - 5 := by omega
  simpa using hfirst_line_generic_case0 (m := m) (x := x.1) hx2 hxle

theorem cycleOn_returnMap0CaseI_caseI [Fact (5 < m)] (hmCaseI : m % 6 = 0 ∨ m % 6 = 2) :
    TorusD4.CycleOn (m ^ 2) (returnMap0CaseIXY (m := m))
      (linePoint0 (m := m) (0 : Fin m)) := by
  have hm0 : 0 < m := by
    have hm5 : 5 < m := Fact.out
    omega
  letI : NeZero m := ⟨Nat.ne_of_gt hm0⟩
  letI : Fact (0 < m) := ⟨hm0⟩
  have hsumCard :
      TorusD3Even.blockTime
          (TorusD3Even.T0CaseI (m := m))
          (rho0CaseI (m := m))
          ⟨0, hm0⟩
          m = Fintype.card (P0Coord m) := by
    simpa [P0Coord, ZMod.card, pow_two] using hsum_case0_caseI (m := m) hmCaseI
  simpa [P0Coord, ZMod.card, pow_two] using
    (TorusD3Even.firstReturn_counting
      (α := P0Coord m) (β := Fin m)
      (F := returnMap0CaseIXY (m := m)) (embed := linePoint0 (m := m))
      (T := TorusD3Even.T0CaseI (m := m)) (rho := rho0CaseI (m := m))
      (M := m) (x0 := (0 : Fin m))
      linePoint0_injective
      (cycleOn_laneMap0_caseI_mod_zeroTwo (m := m) hmCaseI)
      (hreturn_line_case0_caseI (m := m))
      (hfirst_line_case0_caseI (m := m))
      hsumCard)

theorem cycleOn_fullMap0CaseI_caseI [Fact (5 < m)] (hmCaseI : m % 6 = 0 ∨ m % 6 = 2) :
    TorusD4.CycleOn (m ^ 3) (fullMap0CaseI (m := m))
      (slicePoint (0 : ZMod m) (linePoint0 (m := m) (0 : Fin m))) := by
  have hm0 : 0 < m := by
    have hm5 : 5 < m := Fact.out
    omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : NeZero m := ⟨Nat.ne_of_gt hm0⟩
  have hretOrig :
      TorusD4.CycleOn (m ^ 2) (returnMap0CaseI (m := m))
        ((xyEquiv (m := m)).symm (linePoint0 (m := m) (0 : Fin m))) := by
    exact TorusD4.cycleOn_conj (xyEquiv (m := m)).symm
      (f := returnMap0CaseIXY (m := m)) (g := returnMap0CaseI (m := m))
      (returnMap0CaseI_semiconj_xy_symm (m := m))
      (cycleOn_returnMap0CaseI_caseI (m := m) hmCaseI)
  simpa [xyEquiv, linePoint0, fromXY] using
    (cycleOn_full_of_cycleOn_p0 (m := m)
    (F := fullMap0CaseI (m := m)) (T := returnMap0CaseI (m := m))
    (hstep := fullMap0CaseI_snd (m := m))
    (hreturn := iterate_m_fullMap0CaseI_slicePoint_zero (m := m))
    (u := (xyEquiv (m := m)).symm (linePoint0 (m := m) (0 : Fin m)))
    hretOrig)

end TorusD3Odometer
