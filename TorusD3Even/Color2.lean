import TorusD3Even.Counting
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace TorusD3Even

abbrev P0Coord (m : ℕ) := ZMod m × ZMod m

def linePoint (x : ZMod m) : P0Coord m := (x, 0)

theorem linePoint_injective : Function.Injective (linePoint (m := m)) := by
  intro x y h
  simpa [linePoint] using congrArg Prod.fst h

theorem mem_range_linePoint_iff {u : P0Coord m} :
    u ∈ Set.range (linePoint (m := m)) ↔ u.2 = 0 := by
  rcases u with ⟨x, y⟩
  constructor
  · rintro ⟨z, hz⟩
    simpa [linePoint] using (congrArg Prod.snd hz).symm
  · intro hy
    refine ⟨x, ?_⟩
    cases hy
    rfl

theorem natCast_ne_zero_of_pos_lt [Fact (0 < m)] {n : ℕ} (hn0 : 0 < n) (hnm : n < m) :
    ((n : ℕ) : ZMod m) ≠ 0 := by
  intro h
  exact Nat.not_dvd_of_pos_of_lt hn0 hnm ((ZMod.natCast_eq_zero_iff n m).1 h)

theorem natCast_ne_one_of_two_le_lt [Fact (1 < m)] {n : ℕ} (hn1 : 2 ≤ n) (hnm : n < m) :
    ((n : ℕ) : ZMod m) ≠ 1 := by
  intro h
  have h' : n % m = 1 % m := (ZMod.natCast_eq_natCast_iff' n 1 m).1 (by simpa using h)
  rw [Nat.mod_eq_of_lt hnm, Nat.mod_eq_of_lt Fact.out] at h'
  omega

theorem natCast_ne_two_of_three_le_lt [Fact (2 < m)] {n : ℕ} (hn2 : 3 ≤ n) (hnm : n < m) :
    ((n : ℕ) : ZMod m) ≠ 2 := by
  intro h
  have h' : n % m = 2 % m := (ZMod.natCast_eq_natCast_iff' n 2 m).1 (by simpa using h)
  rw [Nat.mod_eq_of_lt hnm, Nat.mod_eq_of_lt Fact.out] at h'
  omega

theorem natCast_eq_natCast_iff_of_lt [Fact (0 < m)] {a b : ℕ} (ha : a < m) (hb : b < m) :
    (((a : ℕ) : ZMod m) = ((b : ℕ) : ZMod m)) ↔ a = b := by
  constructor
  · intro h
    have h' : a % m = b % m := (ZMod.natCast_eq_natCast_iff' a b m).1 h
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h'
    exact h'
  · intro h
    simpa [h]

theorem one_ne_zero [Fact (1 < m)] : (1 : ZMod m) ≠ 0 := by
  letI : Fact (0 < m) := ⟨lt_trans (by decide : 0 < 1) Fact.out⟩
  simpa using natCast_ne_zero_of_pos_lt (m := m) (n := 1) (by decide) Fact.out

theorem two_ne_zero [Fact (2 < m)] : (2 : ZMod m) ≠ 0 := by
  letI : Fact (0 < m) := ⟨lt_trans (by decide : 0 < 2) Fact.out⟩
  simpa using natCast_ne_zero_of_pos_lt (m := m) (n := 2) (by decide) Fact.out

theorem two_ne_one [Fact (2 < m)] : (2 : ZMod m) ≠ 1 := by
  letI : Fact (1 < m) := ⟨lt_trans (by decide : 1 < 2) Fact.out⟩
  simpa using natCast_ne_one_of_two_le_lt (m := m) (n := 2) (by decide) Fact.out

theorem three_ne_zero [Fact (5 < m)] : (3 : ZMod m) ≠ 0 := by
  have hm5 : 5 < m := Fact.out
  letI : Fact (0 < m) := ⟨lt_trans (by decide : 0 < 5) hm5⟩
  have h3m : 3 < m := lt_trans (by decide : 3 < 5) hm5
  simpa using natCast_ne_zero_of_pos_lt (m := m) (n := 3) (by decide) h3m

theorem four_ne_zero [Fact (5 < m)] : (4 : ZMod m) ≠ 0 := by
  have hm5 : 5 < m := Fact.out
  letI : Fact (0 < m) := ⟨lt_trans (by decide : 0 < 5) hm5⟩
  have h4m : 4 < m := lt_trans (by decide : 4 < 5) hm5
  simpa using natCast_ne_zero_of_pos_lt (m := m) (n := 4) (by decide) h4m

theorem five_ne_zero [Fact (7 < m)] : (5 : ZMod m) ≠ 0 := by
  have hm7 : 7 < m := Fact.out
  letI : Fact (0 < m) := ⟨lt_trans (by decide : 0 < 7) hm7⟩
  have h5m : 5 < m := lt_trans (by decide : 5 < 7) hm7
  simpa using natCast_ne_zero_of_pos_lt (m := m) (n := 5) (by decide) h5m

theorem six_ne_zero [Fact (7 < m)] : (6 : ZMod m) ≠ 0 := by
  have hm7 : 7 < m := Fact.out
  letI : Fact (0 < m) := ⟨lt_trans (by decide : 0 < 7) hm7⟩
  have h6m : 6 < m := lt_trans (by decide : 6 < 7) hm7
  simpa using natCast_ne_zero_of_pos_lt (m := m) (n := 6) (by decide) h6m

theorem one_ne_neg_one [Fact (2 < m)] : (1 : ZMod m) ≠ (-1 : ZMod m) := by
  intro h
  have htwo := congrArg (fun z : ZMod m => z + 1) h
  norm_num at htwo
  exact two_ne_zero (m := m) htwo

theorem neg_three_ne_zero [Fact (5 < m)] : (-3 : ZMod m) ≠ 0 := by
  exact neg_ne_zero.mpr (three_ne_zero (m := m))

theorem neg_three_ne_neg_two [Fact (2 < m)] : (-3 : ZMod m) ≠ (-2 : ZMod m) := by
  have hm2 : 2 < m := Fact.out
  have hm1 : 1 < m := lt_trans (by decide : 1 < 2) hm2
  letI : Fact (1 < m) := ⟨hm1⟩
  intro h
  have hneg1 : (-1 : ZMod m) = 0 := by
    calc
      (-1 : ZMod m) = (-3 : ZMod m) + 2 := by ring
      _ = (-2 : ZMod m) + 2 := by rw [h]
      _ = 0 := by ring
  exact neg_ne_zero.mpr (one_ne_zero (m := m)) hneg1

theorem four_ne_neg_two [Fact (7 < m)] : (4 : ZMod m) ≠ (-2 : ZMod m) := by
  have hm7 : 7 < m := Fact.out
  letI : Fact (0 < m) := ⟨lt_trans (by decide : 0 < 7) hm7⟩
  intro h
  have hzero : (((6 : ℕ) : ZMod m)) = 0 := by
    calc
      (((6 : ℕ) : ZMod m)) = (4 : ZMod m) + 2 := by norm_num
      _ = (-2 : ZMod m) + 2 := by rw [h]
      _ = 0 := by ring
  exact natCast_ne_zero_of_pos_lt (m := m) (n := 6) (by omega) (by omega) hzero

theorem five_ne_neg_one [Fact (7 < m)] : (5 : ZMod m) ≠ (-1 : ZMod m) := by
  have hm7 : 7 < m := Fact.out
  letI : Fact (0 < m) := ⟨lt_trans (by decide : 0 < 7) hm7⟩
  intro h
  have hzero : (((6 : ℕ) : ZMod m)) = 0 := by
    calc
      (((6 : ℕ) : ZMod m)) = (5 : ZMod m) + 1 := by norm_num
      _ = (-1 : ZMod m) + 1 := by rw [h]
      _ = 0 := by ring
  exact natCast_ne_zero_of_pos_lt (m := m) (n := 6) (by omega) (by omega) hzero

theorem six_ne_neg_two [Fact (9 < m)] : (6 : ZMod m) ≠ (-2 : ZMod m) := by
  have hm9 : 9 < m := Fact.out
  letI : Fact (0 < m) := ⟨lt_trans (by decide : 0 < 9) hm9⟩
  intro h
  have hzero : (((8 : ℕ) : ZMod m)) = 0 := by
    calc
      (((8 : ℕ) : ZMod m)) = (6 : ZMod m) + 2 := by norm_num
      _ = (-2 : ZMod m) + 2 := by rw [h]
      _ = 0 := by ring
  exact natCast_ne_zero_of_pos_lt (m := m) (n := 8) (by omega) (by omega) hzero

theorem seven_ne_neg_one [Fact (9 < m)] : (7 : ZMod m) ≠ (-1 : ZMod m) := by
  have hm9 : 9 < m := Fact.out
  letI : Fact (0 < m) := ⟨lt_trans (by decide : 0 < 9) hm9⟩
  intro h
  have hzero : (((8 : ℕ) : ZMod m)) = 0 := by
    calc
      (((8 : ℕ) : ZMod m)) = (7 : ZMod m) + 1 := by norm_num
      _ = (-1 : ZMod m) + 1 := by rw [h]
      _ = 0 := by ring
  exact natCast_ne_zero_of_pos_lt (m := m) (n := 8) (by omega) (by omega) hzero

theorem cast_sub_one_eq_neg_one (hm : 1 ≤ m) : (((m - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) := by
  rw [Nat.cast_sub hm]
  simp

theorem cast_sub_two_eq_neg_two (hm : 2 ≤ m) : (((m - 2 : ℕ) : ZMod m)) = (-2 : ZMod m) := by
  rw [Nat.cast_sub hm]
  simp

theorem cast_sub_three_eq_neg_three (hm : 3 ≤ m) : (((m - 3 : ℕ) : ZMod m)) = (-3 : ZMod m) := by
  rw [Nat.cast_sub hm]
  norm_num

theorem natCast_ne_neg_one_of_lt [Fact (0 < m)] {n : ℕ} (hnm : n + 1 < m) :
    ((n : ℕ) : ZMod m) ≠ (-1 : ZMod m) := by
  intro h
  have hzero : (((n + 1 : ℕ) : ZMod m)) = 0 := by
    have hstep := congrArg (fun z : ZMod m => z + 1) h
    simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using hstep
  exact natCast_ne_zero_of_pos_lt (m := m) (n := n + 1) (by omega) (by omega) hzero

theorem natCast_ne_neg_two_of_lt [Fact (0 < m)] {n : ℕ} (hnm : n + 2 < m) :
    ((n : ℕ) : ZMod m) ≠ (-2 : ZMod m) := by
  intro h
  have hstep := congrArg (fun z : ZMod m => z + 2) h
  have hzero : (((n + 2 : ℕ) : ZMod m)) = 0 := by
    simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using hstep
  exact natCast_ne_zero_of_pos_lt (m := m) (n := n + 2) (by omega) (by omega) hzero

theorem neg_two_sub_nat_ne_zero [Fact (0 < m)] {n : ℕ} (hn : n < m - 2) :
    (-2 : ZMod m) - n ≠ 0 := by
  intro h
  have hzero : (((n + 2 : ℕ) : ZMod m)) = 0 := by
    apply neg_eq_zero.mp
    simpa [Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
  exact natCast_ne_zero_of_pos_lt (m := m) (n := n + 2) (by omega) (by omega) hzero

theorem neg_two_sub_nat_ne_one [Fact (0 < m)] {n : ℕ} (hn : n + 3 < m) :
    (-2 : ZMod m) - n ≠ 1 := by
  intro h
  have hzero : (((n + 3 : ℕ) : ZMod m)) = 0 := by
    have hstep : (0 : ZMod m) = ((-2 : ZMod m) - n) + (((n + 2 : ℕ) : ZMod m)) := by
      calc
        (0 : ZMod m) = (-2 : ZMod m) + 2 := by norm_num
        _ = ((-2 : ZMod m) - n) + (((n + 2 : ℕ) : ZMod m)) := by
              simp [Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [h] at hstep
    calc
      (((n + 3 : ℕ) : ZMod m)) = (((n : ℕ) : ZMod m) + 3) := by
        simp [Nat.cast_add, add_assoc]
      _ = (1 : ZMod m) + ((((n : ℕ) : ZMod m) + 2)) := by
        ring
      _ = (1 : ZMod m) + (((n + 2 : ℕ) : ZMod m)) := by
        simp [Nat.cast_add, add_assoc]
      _ = 0 := hstep.symm
  exact natCast_ne_zero_of_pos_lt (m := m) (n := n + 3) (by omega) (by omega) hzero

theorem neg_two_sub_nat_ne_two [Fact (0 < m)] {n : ℕ} (hn : n + 4 < m) :
    (-2 : ZMod m) - n ≠ 2 := by
  intro h
  have hzero : (((n + 4 : ℕ) : ZMod m)) = 0 := by
    have hstep : (0 : ZMod m) = ((-2 : ZMod m) - n) + (((n + 2 : ℕ) : ZMod m)) := by
      calc
        (0 : ZMod m) = (-2 : ZMod m) + 2 := by norm_num
        _ = ((-2 : ZMod m) - n) + (((n + 2 : ℕ) : ZMod m)) := by
              simp [Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [h] at hstep
    calc
      (((n + 4 : ℕ) : ZMod m)) = (((n : ℕ) : ZMod m) + 4) := by
        simp [Nat.cast_add, add_assoc]
      _ = (2 : ZMod m) + ((((n : ℕ) : ZMod m) + 2)) := by
        ring
      _ = (2 : ZMod m) + (((n + 2 : ℕ) : ZMod m)) := by
        simp [Nat.cast_add, add_assoc]
      _ = 0 := hstep.symm
  exact natCast_ne_zero_of_pos_lt (m := m) (n := n + 4) (by omega) (by omega) hzero

theorem neg_two_sub_nat_ne_neg_one [Fact (0 < m)] {n : ℕ} (hn : n < m - 2) :
    (-2 : ZMod m) - n ≠ (-1 : ZMod m) := by
  intro h
  have hstep : (-1 : ZMod m) - n = 0 := by
    have this := congrArg (fun z : ZMod m => z + 1) h
    ring_nf at this ⊢
    exact this
  have hzero : (((n + 1 : ℕ) : ZMod m)) = 0 := by
    have hneg : (-(((n + 1 : ℕ) : ZMod m))) = 0 := by
      simpa [Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hstep
    exact neg_eq_zero.mp hneg
  exact natCast_ne_zero_of_pos_lt (m := m) (n := n + 1) (by omega) (by omega) hzero

theorem two_add_nat_ne_zero [Fact (0 < m)] {n : ℕ} (hn : n + 2 < m) :
    (2 : ZMod m) + n ≠ 0 := by
  simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
    natCast_ne_zero_of_pos_lt (m := m) (n := n + 2) (by omega) (by omega)

theorem two_add_nat_ne_neg_one [Fact (0 < m)] {n : ℕ} (hn : n + 3 < m) :
    (2 : ZMod m) + n ≠ (-1 : ZMod m) := by
  simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
    natCast_ne_neg_one_of_lt (m := m) (n := n + 2) hn

theorem two_add_nat_ne_neg_two_sub_nat [Fact (0 < m)] {n : ℕ} (hn : 2 * (n + 2) < m) :
    (2 : ZMod m) + n ≠ (-2 : ZMod m) - n := by
  intro h
  have hzero : (((2 * (n + 2) : ℕ) : ZMod m)) = 0 := by
    have hstep : (0 : ZMod m) = ((-2 : ZMod m) - n) + (((n + 2 : ℕ) : ZMod m)) := by
      calc
        (0 : ZMod m) = (-2 : ZMod m) + 2 := by norm_num
        _ = ((-2 : ZMod m) - n) + (((n + 2 : ℕ) : ZMod m)) := by
              simp [Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [← h] at hstep
    calc
      (((2 * (n + 2) : ℕ) : ZMod m))
          = (((n + 2 : ℕ) : ZMod m)) + (((n + 2 : ℕ) : ZMod m)) := by
              simp [two_mul, Nat.cast_add, Nat.cast_mul]
      _ = ((((n : ℕ) : ZMod m) + 2) + (((n + 2 : ℕ) : ZMod m))) := by
            simp [Nat.cast_add, add_assoc, add_left_comm, add_comm]
      _ = ((2 : ZMod m) + n) + (((n + 2 : ℕ) : ZMod m)) := by
            ring
      _ = 0 := hstep.symm
  exact natCast_ne_zero_of_pos_lt (m := m) (n := 2 * (n + 2)) (by omega) hn hzero

def succMap (x : ZMod m) : ZMod m := x + 1

theorem iterate_succMap (n : ℕ) (x : ZMod m) :
    (succMap (m := m)^[n]) x = x + n := by
  induction n generalizing x with
  | zero =>
      simp [succMap]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [succMap, Nat.cast_add, add_assoc, add_left_comm, add_comm]

theorem cycleOn_succMap [Fact (0 < m)] :
    TorusD4.CycleOn m (succMap (m := m)) (0 : ZMod m) := by
  letI : NeZero m := ⟨Nat.ne_of_gt Fact.out⟩
  simpa [ZMod.card m] using
    (cycleOn_of_period_card (α := ZMod m)
      (by simpa using iterate_succMap (m := m) m (0 : ZMod m))
      (by
        intro n hn0 hnm
        intro h
        have hnm' : n < m := by simpa [ZMod.card m] using hnm
        have hcast : ((n : ℕ) : ZMod m) = 0 := by
          calc
            ((n : ℕ) : ZMod m) = (succMap (m := m)^[n]) (0 : ZMod m) := by
              symm
              simpa using iterate_succMap (m := m) n (0 : ZMod m)
            _ = 0 := h
        exact natCast_ne_zero_of_pos_lt (m := m) hn0 hnm' hcast))

def T2 (x : ZMod m) : ZMod m :=
  if x = 0 then
    1
  else if x = 1 then
    (-1 : ZMod m)
  else if x = 2 then
    0
  else
    x - 1

def psiT2 (x : ZMod m) : ZMod m :=
  if x = 0 then
    0
  else if x = 1 then
    1
  else
    1 - x

def psiT2Equiv [Fact (2 < m)] : ZMod m ≃ ZMod m where
  toFun := psiT2 (m := m)
  invFun := psiT2 (m := m)
  left_inv x := by
    letI : Fact (1 < m) := ⟨lt_trans (by decide : 1 < 2) Fact.out⟩
    by_cases hx0 : x = 0
    · simp [psiT2, hx0]
    · by_cases hx1 : x = 1
      · have h10 : (1 : ZMod m) ≠ 0 := one_ne_zero (m := m)
        simp [psiT2, hx1, h10]
      · have hpsi0 : (1 - x : ZMod m) ≠ 0 := by
          intro h
          apply hx1
          calc
            x = 1 - (1 - x) := by ring
            _ = 1 := by rw [h]; ring
        have hpsi1 : (1 - x : ZMod m) ≠ 1 := by
          intro h
          apply hx0
          calc
            x = 1 - (1 - x) := by ring
            _ = 0 := by rw [h]; ring
        simp [psiT2, hx0, hx1, hpsi0, hpsi1]
  right_inv x := by
    letI : Fact (1 < m) := ⟨lt_trans (by decide : 1 < 2) Fact.out⟩
    by_cases hx0 : x = 0
    · simp [psiT2, hx0]
    · by_cases hx1 : x = 1
      · have h10 : (1 : ZMod m) ≠ 0 := one_ne_zero (m := m)
        simp [psiT2, hx1, h10]
      · have hpsi0 : (1 - x : ZMod m) ≠ 0 := by
          intro h
          apply hx1
          calc
            x = 1 - (1 - x) := by ring
            _ = 1 := by rw [h]; ring
        have hpsi1 : (1 - x : ZMod m) ≠ 1 := by
          intro h
          apply hx0
          calc
            x = 1 - (1 - x) := by ring
            _ = 0 := by rw [h]; ring
        simp [psiT2, hx0, hx1, hpsi0, hpsi1]

theorem psiT2_conj [Fact (2 < m)] (x : ZMod m) :
    psiT2 (m := m) (T2 (m := m) x) = succMap (m := m) (psiT2 (m := m) x) := by
  letI : Fact (1 < m) := ⟨lt_trans (by decide : 1 < 2) Fact.out⟩
  by_cases hx0 : x = 0
  · have h10 : (1 : ZMod m) ≠ 0 := one_ne_zero (m := m)
    simp [T2, psiT2, succMap, hx0, h10]
  · by_cases hx1 : x = 1
    · have hneg10 : (-1 : ZMod m) ≠ 0 := neg_ne_zero.mpr (one_ne_zero (m := m))
      have hneg11 : (-1 : ZMod m) ≠ 1 := by
        intro h
        have : (2 : ZMod m) = 0 := by
          calc
            (2 : ZMod m) = 1 - (-1 : ZMod m) := by ring
            _ = 1 - 1 := by rw [h]
            _ = 0 := by ring
        exact two_ne_zero (m := m) this
      have h10 : (1 : ZMod m) ≠ 0 := one_ne_zero (m := m)
      simp [T2, psiT2, succMap, hx1, h10, hneg10, hneg11]
    · by_cases hx2 : x = 2
      · simp [T2, psiT2, succMap, hx2, two_ne_zero (m := m), two_ne_one (m := m)]
        ring
      · have hxsub0 : x - 1 ≠ 0 := by
          intro h
          apply hx1
          calc
            x = (x - 1) + 1 := by ring
            _ = 1 := by rw [h]; ring
        have hxsub1 : x - 1 ≠ 1 := by
          intro h
          apply hx2
          calc
            x = (x - 1) + 1 := by ring
            _ = 2 := by rw [h]; ring
        simp [T2, psiT2, succMap, hx0, hx1, hx2, hxsub0, hxsub1]
        ring

theorem cycleOn_T2 [Fact (2 < m)] :
    TorusD4.CycleOn m (T2 (m := m)) (0 : ZMod m) := by
  letI : Fact (0 < m) := ⟨lt_trans (by decide : 0 < 2) Fact.out⟩
  have hsemi :
      Function.Semiconj (psiT2Equiv (m := m)) (T2 (m := m)) (succMap (m := m)) := psiT2_conj
  have hsymm :
      Function.Semiconj (psiT2Equiv (m := m)).symm (succMap (m := m)) (T2 (m := m)) :=
    hsemi.inverse_left (psiT2Equiv (m := m)).left_inv (psiT2Equiv (m := m)).right_inv
  simpa [psiT2Equiv, psiT2] using
    (TorusD4.cycleOn_conj (psiT2Equiv (m := m)).symm
      (f := succMap (m := m)) (g := T2 (m := m)) hsymm (cycleOn_succMap (m := m)))

theorem half_add_half_eq_zero [Fact (Even m)] :
    (((m / 2 : ℕ) : ZMod m) + ((m / 2 : ℕ) : ZMod m)) = 0 := by
  have hmEven : Even m := Fact.out
  have hsum : (m / 2 : ℕ) + (m / 2 : ℕ) = m := by
    simpa [two_mul] using (Nat.two_mul_div_two_of_even hmEven)
  calc
    (((m / 2 : ℕ) : ZMod m) + ((m / 2 : ℕ) : ZMod m))
        = (((m / 2 : ℕ) + (m / 2 : ℕ) : ℕ) : ZMod m) := by
            rw [Nat.cast_add]
    _ = ((m : ℕ) : ZMod m) := by rw [hsum]
    _ = 0 := by simp

theorem neg_half_eq_half [Fact (Even m)] :
    (-(((m / 2 : ℕ) : ZMod m))) = (((m / 2 : ℕ) : ZMod m)) := by
  have hhalf : (((m / 2 : ℕ) : ZMod m) + ((m / 2 : ℕ) : ZMod m)) = 0 := half_add_half_eq_zero (m := m)
  exact (eq_neg_iff_add_eq_zero.mpr hhalf).symm

theorem half_ne_zero [Fact (Even m)] [Fact (5 < m)] :
    (((m / 2 : ℕ) : ZMod m)) ≠ 0 := by
  have hm5 : 5 < m := Fact.out
  letI : Fact (0 < m) := ⟨lt_trans (by decide : 0 < 5) hm5⟩
  exact natCast_ne_zero_of_pos_lt (m := m) (n := m / 2) (by omega) (by omega)

theorem half_ne_two [Fact (Even m)] [Fact (5 < m)] :
    (((m / 2 : ℕ) : ZMod m)) ≠ 2 := by
  have hm5 : 5 < m := Fact.out
  letI : Fact (2 < m) := ⟨by omega⟩
  exact natCast_ne_two_of_three_le_lt (m := m) (n := m / 2) (by omega) (by omega)

theorem half_ne_neg_one [Fact (Even m)] [Fact (5 < m)] :
    (((m / 2 : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
  have hm5 : 5 < m := Fact.out
  letI : Fact (0 < m) := ⟨lt_trans (by decide : 0 < 5) hm5⟩
  exact natCast_ne_neg_one_of_lt (m := m) (n := m / 2) (by omega)

theorem half_sub_two_ne_zero [Fact (Even m)] [Fact (5 < m)] :
    (((m / 2 : ℕ) : ZMod m) - 2) ≠ 0 := by
  intro h
  have hstep := congrArg (fun z : ZMod m => z + 2) h
  have hhalf : (((m / 2 : ℕ) : ZMod m)) = (2 : ZMod m) := by
    simpa [sub_eq_add_neg, Nat.cast_add, add_assoc, add_left_comm, add_comm] using hstep
  exact half_ne_two (m := m) hhalf

theorem not_mem_range_linePoint_of_snd_ne_zero {u : P0Coord m} (hy : u.2 ≠ 0) :
    u ∉ Set.range (linePoint (m := m)) := by
  intro hu
  exact hy ((mem_range_linePoint_iff (m := m) (u := u)).1 hu)

def G (u : P0Coord m) : P0Coord m :=
  (u.1 + 1, u.2 - 1)

theorem iterate_G (n : ℕ) (x y : ZMod m) :
    (G (m := m)^[n]) (x, y) = (x + n, y - n) := by
  induction n generalizing x y with
  | zero =>
      simp [G]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      ext <;> simp [G, Nat.cast_add]
      all_goals ring

theorem iterate_eq_iterate_of_step_eq {α : Type*} {f g : α → α} :
    ∀ n z, (∀ t, t < n → f ((g^[t]) z) = g ((g^[t]) z)) → (f^[n]) z = (g^[n]) z
  | 0, z, _ => by simp
  | n + 1, z, h => by
      have h0 : f ((g^[n]) z) = g ((g^[n]) z) := h n (Nat.lt_succ_self n)
      have hind : (f^[n]) z = (g^[n]) z := iterate_eq_iterate_of_step_eq n z (by
        intro t ht
        exact h t (Nat.lt_trans ht (Nat.lt_succ_self n)))
      calc
        (f^[n + 1]) z = f ((f^[n]) z) := by rw [Function.iterate_succ_apply']
        _ = f ((g^[n]) z) := by rw [hind]
        _ = g ((g^[n]) z) := h0
        _ = (g^[n + 1]) z := by rw [Function.iterate_succ_apply']

def R2xy (u : P0Coord m) : P0Coord m :=
  let (x, y) := u
  if x = 2 ∧ y = 2 then
    (x + 1, y - 2)
  else if y = 1 ∧ x ≠ 1 ∧ x ≠ (-1 : ZMod m) then
    (x + 2, y - 1)
  else if (y = (-1 : ZMod m) ∧ x ≠ (-1 : ZMod m)) ∨ (x = (-1 : ZMod m) ∧ y = (-2 : ZMod m)) then
    (x, y - 1)
  else if
      (y = x ∧ x ≠ 0 ∧ x ≠ 2 ∧ x ≠ (-1 : ZMod m)) ∨
        (x = (-1 : ZMod m) ∧ y = 0) then
    (x, y - 2)
  else if (x = (-1 : ZMod m) ∧ y ≠ 0 ∧ y ≠ (-2 : ZMod m)) ∨ (x = 0 ∧ y = 0) then
    (x + 1, y)
  else
    (x + 1, y - 1)

theorem R2xy_eq_A :
    R2xy (m := m) ((2 : ZMod m), (2 : ZMod m)) = ((3 : ZMod m), (0 : ZMod m)) := by
  ext <;> simp [R2xy] <;> ring

theorem R2xy_eq_B_of [Fact (2 < m)] {x : ZMod m}
    (hx1 : x ≠ (1 : ZMod m)) (hxneg1 : x ≠ (-1 : ZMod m)) :
    R2xy (m := m) (x, (1 : ZMod m)) = (x + 2, (0 : ZMod m)) := by
  have h12 : (1 : ZMod m) ≠ (2 : ZMod m) := by
    intro h
    exact two_ne_one (m := m) h.symm
  simp [R2xy, h12, hx1, hxneg1]

theorem R2xy_eq_C_of [Fact (2 < m)] {x : ZMod m} (hxneg1 : x ≠ (-1 : ZMod m)) :
    R2xy (m := m) (x, (-1 : ZMod m)) = (x, (-2 : ZMod m)) := by
  have hA : ¬ (x = (2 : ZMod m) ∧ (-1 : ZMod m) = (2 : ZMod m)) := by
    intro h
    exact hxneg1 (by rw [h.1]; exact h.2.symm)
  have hneg11 : (-1 : ZMod m) ≠ (1 : ZMod m) := by
    intro h
    have : (2 : ZMod m) = 0 := by
      calc
        (2 : ZMod m) = (1 : ZMod m) - (-1 : ZMod m) := by ring
        _ = 0 := by rw [h]; ring
    exact two_ne_zero (m := m) this
  have hcore : R2xy (m := m) (x, (-1 : ZMod m)) = (x, (-1 : ZMod m) - 1) := by
    simp [R2xy, hA, hneg11, hxneg1]
  calc
    R2xy (m := m) (x, (-1 : ZMod m)) = (x, (-1 : ZMod m) - 1) := hcore
    _ = (x, (-2 : ZMod m)) := by
          ext <;> ring

theorem R2xy_eq_D_of {x : ZMod m}
    (hx0 : x ≠ (0 : ZMod m)) (hx2 : x ≠ (2 : ZMod m)) (hxneg1 : x ≠ (-1 : ZMod m)) :
    R2xy (m := m) (x, x) = (x, x - 2) := by
  have hA : ¬ (x = (2 : ZMod m) ∧ x = (2 : ZMod m)) := by
    intro h
    exact hx2 h.1
  have hB : ¬ (x = (1 : ZMod m) ∧ x ≠ (1 : ZMod m) ∧ x ≠ (-1 : ZMod m)) := by
    intro h
    exact h.2.1 h.1
  have hC :
      ¬ ((x = (-1 : ZMod m) ∧ x ≠ (-1 : ZMod m)) ∨
          (x = (-1 : ZMod m) ∧ x = (-2 : ZMod m))) := by
    intro h
    rcases h with h | h
    · exact h.2 h.1
    · exact hxneg1 h.1
  simp [R2xy, hA, hB, hC, hx0, hx2, hxneg1]

theorem R2xy_eq_E_of [Fact (5 < m)] {y : ZMod m}
    (hy0 : y ≠ (0 : ZMod m)) (hyneg2 : y ≠ (-2 : ZMod m)) :
    R2xy (m := m) ((-1 : ZMod m), y) = ((0 : ZMod m), y) := by
  have hm5 : 5 < m := Fact.out
  letI : Fact (0 < m) := ⟨lt_trans (by decide : 0 < 5) Fact.out⟩
  have hneg12 : (-1 : ZMod m) ≠ (2 : ZMod m) := by
    exact (natCast_ne_neg_one_of_lt (m := m) (n := 2) (by omega)).symm
  have hA : ¬ (((-1 : ZMod m) = (2 : ZMod m)) ∧ y = (2 : ZMod m)) := by
    intro h
    exact hneg12 h.1
  have hB : ¬ (y = (1 : ZMod m) ∧ (-1 : ZMod m) ≠ (1 : ZMod m) ∧ (-1 : ZMod m) ≠ (-1 : ZMod m)) := by
    intro h
    exact h.2.2 rfl
  have hC :
      ¬ ((y = (-1 : ZMod m) ∧ (-1 : ZMod m) ≠ (-1 : ZMod m)) ∨
          ((-1 : ZMod m) = (-1 : ZMod m) ∧ y = (-2 : ZMod m))) := by
    intro h
    rcases h with h | h
    · exact h.2 rfl
    · exact hyneg2 h.2
  have hD :
      ¬ (((y = (-1 : ZMod m) ∧ (-1 : ZMod m) ≠ (0 : ZMod m) ∧ (-1 : ZMod m) ≠ (2 : ZMod m) ∧
              (-1 : ZMod m) ≠ (-1 : ZMod m))) ∨
          ((-1 : ZMod m) = (-1 : ZMod m) ∧ y = (0 : ZMod m))) := by
    intro h
    rcases h with h | h
    · exact h.2.2.2 rfl
    · exact hy0 h.2
  simp [R2xy, hA, hB, hC, hD, hy0, hyneg2]

theorem R2xy_eq_G_of {x y : ZMod m}
    (hA : (x, y) ≠ ((2 : ZMod m), (2 : ZMod m)))
    (hy1 : y ≠ (1 : ZMod m))
    (hyneg1 : y ≠ (-1 : ZMod m))
    (hdiag : y ≠ x)
    (hxneg1 : x ≠ (-1 : ZMod m))
    (h00 : (x, y) ≠ ((0 : ZMod m), (0 : ZMod m))) :
    R2xy (m := m) (x, y) = G (m := m) (x, y) := by
  have hA' : ¬ (x = (2 : ZMod m) ∧ y = (2 : ZMod m)) := by
    intro h
    apply hA
    rcases h with ⟨hx, hy⟩
    simp [hx, hy]
  have hB' : ¬ (y = (1 : ZMod m) ∧ x ≠ (1 : ZMod m) ∧ x ≠ (-1 : ZMod m)) := by
    intro h
    exact hy1 h.1
  have hC' :
      ¬ ((y = (-1 : ZMod m) ∧ x ≠ (-1 : ZMod m)) ∨
          (x = (-1 : ZMod m) ∧ y = (-2 : ZMod m))) := by
    intro h
    rcases h with h | h
    · exact hyneg1 h.1
    · exact hxneg1 h.1
  have hD' :
      ¬ (((y = x ∧ x ≠ (0 : ZMod m) ∧ x ≠ (2 : ZMod m) ∧ x ≠ (-1 : ZMod m)) ∨
          (x = (-1 : ZMod m) ∧ y = (0 : ZMod m)))) := by
    intro h
    rcases h with h | h
    · exact hdiag h.1
    · exact hxneg1 h.1
  have hE' :
      ¬ (((x = (-1 : ZMod m) ∧ y ≠ (0 : ZMod m) ∧ y ≠ (-2 : ZMod m)) ∨
          (x = (0 : ZMod m) ∧ y = (0 : ZMod m)))) := by
    intro h
    rcases h with h | h
    · exact hxneg1 h.1
    · apply h00
      simp [h.1, h.2]
  simp [R2xy, G, hA', hB', hC', hD', hE']

theorem iterate_R2xy_from_two_neg_two [Fact (Even m)] [Fact (5 < m)] :
    ∀ n, n ≤ m / 2 - 2 →
      (R2xy (m := m)^[n]) ((2 : ZMod m), (-2 : ZMod m)) =
        ((2 : ZMod m) + n, (-2 : ZMod m) - n)
  | 0, _ => by simp
  | n + 1, hn => by
      have hm5 : 5 < m := Fact.out
      letI : Fact (0 < m) := ⟨lt_trans (by decide : 0 < 5) hm5⟩
      have hn' : n < m / 2 - 2 := Nat.lt_of_succ_le hn
      rw [Function.iterate_succ_apply', iterate_R2xy_from_two_neg_two n (Nat.le_of_succ_le hn)]
      have hA : ((2 : ZMod m) + n, (-2 : ZMod m) - n) ≠ ((2 : ZMod m), (2 : ZMod m)) := by
        intro h
        exact neg_two_sub_nat_ne_two (m := m) (n := n) (by omega) (congrArg Prod.snd h)
      have hy1 : (-2 : ZMod m) - n ≠ (1 : ZMod m) :=
        neg_two_sub_nat_ne_one (m := m) (n := n) (by omega)
      have hyneg1 : (-2 : ZMod m) - n ≠ (-1 : ZMod m) :=
        neg_two_sub_nat_ne_neg_one (m := m) (n := n) (by omega)
      have hdiag : (-2 : ZMod m) - n ≠ (2 : ZMod m) + n := by
        intro h
        exact two_add_nat_ne_neg_two_sub_nat (m := m) (n := n) (by omega) h.symm
      have hxneg1 : (2 : ZMod m) + n ≠ (-1 : ZMod m) :=
        two_add_nat_ne_neg_one (m := m) (n := n) (by omega)
      have h00 : ((2 : ZMod m) + n, (-2 : ZMod m) - n) ≠ ((0 : ZMod m), (0 : ZMod m)) := by
        intro h
        exact two_add_nat_ne_zero (m := m) (n := n) (by omega) (congrArg Prod.fst h)
      rw [R2xy_eq_G_of (m := m) hA hy1 hyneg1 hdiag hxneg1 h00]
      ext <;> simp [G, Nat.cast_add, sub_eq_add_neg] <;> ring

def rho2 (x : ZMod m) : ℕ :=
  if x = 0 then
    1
  else if x = 1 then
    m - 1
  else if x = 2 then
    2 * m
  else
    m

theorem rho2_pos [Fact (1 < m)] (x : ZMod m) : 0 < rho2 (m := m) x := by
  have hm0 : 0 < m := lt_trans (by decide : 0 < 1) Fact.out
  by_cases hx0 : x = 0
  · simp [rho2, hx0]
  · by_cases hx1 : x = 1
    · have h10 : (1 : ZMod m) ≠ 0 := by
        intro h
        apply hx0
        simpa [hx1] using h
      simp [rho2, hx1, h10]
      exact Fact.out
    · by_cases hx2 : x = 2
      · have h20 : (2 : ZMod m) ≠ 0 := by
          intro h
          apply hx0
          simpa [hx2] using h
        have h21 : (2 : ZMod m) ≠ 1 := by
          intro h
          apply hx1
          simpa [hx2] using h
        simp [rho2, hx2, h20, h21]
        exact hm0
      · simp [rho2, hx0, hx1, hx2]
        exact hm0

theorem R2xy_linePoint_zero [Fact (2 < m)] :
    R2xy (m := m) (linePoint (m := m) (0 : ZMod m)) = linePoint (m := m) (1 : ZMod m) := by
  letI : Fact (1 < m) := ⟨lt_trans (by decide : 1 < 2) Fact.out⟩
  have h20 : (2 : ZMod m) ≠ 0 := two_ne_zero (m := m)
  have h02 : (0 : ZMod m) ≠ 2 := by
    intro h
    exact h20 h.symm
  have h10 : (1 : ZMod m) ≠ 0 := one_ne_zero (m := m)
  have hneg10 : (-1 : ZMod m) ≠ 0 := neg_ne_zero.mpr (one_ne_zero (m := m))
  have hneg20 : (-2 : ZMod m) ≠ 0 := by
    intro h
    exact two_ne_zero (m := m) (by simpa using neg_eq_iff_add_eq_zero.mp h)
  simp [R2xy, linePoint, h20, h02, h10, hneg10, hneg20]

theorem firstReturn_zero [Fact (2 < m)] :
    (R2xy (m := m)^[rho2 (m := m) (0 : ZMod m)]) (linePoint (m := m) (0 : ZMod m)) =
      linePoint (m := m) (T2 (m := m) (0 : ZMod m)) := by
  simpa [rho2, T2] using R2xy_linePoint_zero (m := m)

theorem R2xy_linePoint_one [Fact (2 < m)] :
    R2xy (m := m) (linePoint (m := m) (1 : ZMod m)) = ((2 : ZMod m), (-1 : ZMod m)) := by
  letI : Fact (1 < m) := ⟨lt_trans (by decide : 1 < 2) Fact.out⟩
  have hA : linePoint (m := m) (1 : ZMod m) ≠ ((2 : ZMod m), (2 : ZMod m)) := by
    intro h
    exact two_ne_zero (m := m) (by simpa [linePoint] using (congrArg Prod.snd h).symm)
  have hy1 : (0 : ZMod m) ≠ (1 : ZMod m) := (one_ne_zero (m := m)).symm
  have hyneg1 : (0 : ZMod m) ≠ (-1 : ZMod m) := by
    intro h
    exact neg_ne_zero.mpr (one_ne_zero (m := m)) h.symm
  have hdiag : (0 : ZMod m) ≠ (1 : ZMod m) := (one_ne_zero (m := m)).symm
  have hxneg1 : (1 : ZMod m) ≠ (-1 : ZMod m) := one_ne_neg_one (m := m)
  have h00 : linePoint (m := m) (1 : ZMod m) ≠ ((0 : ZMod m), (0 : ZMod m)) := by
    intro h
    exact one_ne_zero (m := m) (by simpa [linePoint] using congrArg Prod.fst h)
  calc
    R2xy (m := m) (linePoint (m := m) (1 : ZMod m))
        = G (m := m) (linePoint (m := m) (1 : ZMod m)) := by
            simpa [linePoint] using R2xy_eq_G_of (m := m) hA hy1 hyneg1 hdiag hxneg1 h00
    _ = ((2 : ZMod m), (-1 : ZMod m)) := by
          ext <;> simp [linePoint, G] <;> ring

theorem R2xy_two_neg_one [Fact (5 < m)] :
    R2xy (m := m) ((2 : ZMod m), (-1 : ZMod m)) = ((2 : ZMod m), (-2 : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  letI : Fact (0 < m) := ⟨lt_trans (by decide : 0 < 5) hm5⟩
  letI : Fact (2 < m) := ⟨by omega⟩
  have h2neg1 : (2 : ZMod m) ≠ (-1 : ZMod m) :=
    natCast_ne_neg_one_of_lt (m := m) (n := 2) (by omega)
  simpa using R2xy_eq_C_of (m := m) h2neg1

theorem iterate_to_half_half_from_two_neg_two [Fact (Even m)] [Fact (5 < m)] :
    (R2xy (m := m)^[m / 2 - 2]) ((2 : ZMod m), (-2 : ZMod m)) =
      ((((m / 2 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m))) := by
  have hmEven : Even m := Fact.out
  have hm5 : 5 < m := Fact.out
  have hmhalf : 2 ≤ m / 2 := by
    have hm6 : 6 ≤ m := by omega
    omega
  rw [iterate_R2xy_from_two_neg_two (m := m) (m / 2 - 2) le_rfl]
  ext
  · simp [Nat.cast_sub hmhalf]
  · have hsub : (((m / 2 - 2 : ℕ) : ZMod m)) = (((m / 2 : ℕ) : ZMod m)) - 2 := by
      rw [Nat.cast_sub hmhalf]
      ring
    calc
      (-2 : ZMod m) - (((m / 2 - 2 : ℕ) : ZMod m))
          = (-2 : ZMod m) - ((((m / 2 : ℕ) : ZMod m)) - 2) := by rw [hsub]
      _ = -(((m / 2 : ℕ) : ZMod m)) := by ring
      _ = (((m / 2 : ℕ) : ZMod m)) := neg_half_eq_half (m := m)

theorem R2xy_half_half [Fact (Even m)] [Fact (5 < m)] :
    R2xy (m := m) ((((m / 2 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m))) =
      ((((m / 2 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m)) - 2) := by
  exact R2xy_eq_D_of (m := m)
    (half_ne_zero (m := m)) (half_ne_two (m := m)) (half_ne_neg_one (m := m))

theorem iterate_R2xy_from_half_half_sub_two [Fact (Even m)] [Fact (5 < m)] :
    ∀ n, n ≤ m / 2 - 3 →
      (R2xy (m := m)^[n])
          ((((m / 2 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m)) - 2) =
        ((((m / 2 : ℕ) : ZMod m)) + n, (((m / 2 : ℕ) : ZMod m)) - 2 - n)
  | 0, _ => by simp
  | n + 1, hn => by
      have hm5 : 5 < m := Fact.out
      have hm0 : 0 < m := by omega
      have hm1 : 1 < m := by omega
      have hm2 : 2 < m := by omega
      letI : Fact (0 < m) := ⟨hm0⟩
      letI : Fact (1 < m) := ⟨hm1⟩
      letI : Fact (2 < m) := ⟨hm2⟩
      let h : ℕ := m / 2
      have hn' : n < h - 3 := by
        dsimp [h] at hn ⊢
        exact Nat.lt_of_succ_le hn
      have hx_lt : h + n < m := by
        dsimp [h]
        omega
      have hy_lt : h - 2 - n < m := by
        dsimp [h]
        omega
      have hxcast :
          (((h : ℕ) : ZMod m) + n) = (((h + n : ℕ) : ZMod m)) := by
        rw [Nat.cast_add]
      have hycast :
          (((h : ℕ) : ZMod m) - 2 - n) = (((h - 2 - n : ℕ) : ZMod m)) := by
        have h2n : 2 + n ≤ h := by omega
        have hsub : h - n - 2 = h - 2 - n := by omega
        calc
          (((h : ℕ) : ZMod m) - 2 - n)
              = (((h : ℕ) : ZMod m) - (((2 + n : ℕ) : ZMod m))) := by
                  simp [Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          _ = (((h - (2 + n) : ℕ) : ZMod m)) := by rw [Nat.cast_sub h2n]
          _ = (((h - n - 2 : ℕ) : ZMod m)) := by rw [Nat.add_comm 2 n, ← Nat.sub_sub]
          _ = (((h - 2 - n : ℕ) : ZMod m)) := by
                simpa using congrArg (fun t : ℕ => ((t : ℕ) : ZMod m)) hsub
      have hA : ((((h : ℕ) : ZMod m)) + n, (((h : ℕ) : ZMod m)) - 2 - n) ≠
          ((2 : ZMod m), (2 : ZMod m)) := by
        intro hEq
        have hfst : (((h : ℕ) : ZMod m) + n) = (2 : ZMod m) := congrArg Prod.fst hEq
        have hxeq : (((h + n : ℕ) : ZMod m)) = ((2 : ℕ) : ZMod m) := by
          calc
            (((h + n : ℕ) : ZMod m)) = (((h : ℕ) : ZMod m) + n) := by
              rw [hxcast]
            _ = (2 : ZMod m) := hfst
            _ = ((2 : ℕ) : ZMod m) := by norm_num
        exact natCast_ne_two_of_three_le_lt (m := m) (n := h + n) (by omega) hx_lt hxeq
      have hy1 : (((h : ℕ) : ZMod m) - 2 - n) ≠ (1 : ZMod m) := by
        rw [hycast]
        exact natCast_ne_one_of_two_le_lt (m := m) (n := h - 2 - n) (by omega) hy_lt
      have hyneg1 : (((h : ℕ) : ZMod m) - 2 - n) ≠ (-1 : ZMod m) := by
        rw [hycast]
        exact natCast_ne_neg_one_of_lt (m := m) (n := h - 2 - n) (by omega)
      have hdiag : (((h : ℕ) : ZMod m) - 2 - n) ≠ (((h : ℕ) : ZMod m) + n) := by
        intro hEq
        have hxeq :
            (((h - 2 - n : ℕ) : ZMod m)) = (((h + n : ℕ) : ZMod m)) := by
          rw [hycast, hxcast] at hEq
          exact hEq
        have hnat := (natCast_eq_natCast_iff_of_lt (m := m) (a := h - 2 - n) (b := h + n)
          hy_lt hx_lt).1 hxeq
        omega
      have hxneg1 : (((h : ℕ) : ZMod m) + n) ≠ (-1 : ZMod m) := by
        rw [hxcast]
        exact natCast_ne_neg_one_of_lt (m := m) (n := h + n) (by omega)
      have h00 : ((((h : ℕ) : ZMod m)) + n, (((h : ℕ) : ZMod m)) - 2 - n) ≠
          ((0 : ZMod m), (0 : ZMod m)) := by
        intro hEq
        have hfst : (((h : ℕ) : ZMod m) + n) = 0 := congrArg Prod.fst hEq
        have hxeq : (((h + n : ℕ) : ZMod m)) = 0 := by
          calc
            (((h + n : ℕ) : ZMod m)) = (((h : ℕ) : ZMod m) + n) := by
              rw [hxcast]
            _ = 0 := hfst
        exact natCast_ne_zero_of_pos_lt (m := m) (n := h + n) (by omega) hx_lt hxeq
      rw [Function.iterate_succ_apply',
        iterate_R2xy_from_half_half_sub_two n (Nat.le_of_succ_le hn)]
      rw [R2xy_eq_G_of (m := m) hA hy1 hyneg1 hdiag hxneg1 h00]
      ext <;> simp [G, Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] <;> ring

theorem iterate_to_m_sub_three_one_from_half_half_sub_two [Fact (Even m)] [Fact (5 < m)] :
    (R2xy (m := m)^[m / 2 - 3])
        ((((m / 2 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m)) - 2) =
      (((((m - 3 : ℕ) : ZMod m))), (1 : ZMod m)) := by
  have hmEven : Even m := Fact.out
  have hm5 : 5 < m := Fact.out
  let h : ℕ := m / 2
  have hsum : h + h = m := by
    dsimp [h]
    simpa [two_mul] using (Nat.two_mul_div_two_of_even hmEven)
  have hh3 : 3 ≤ h := by
    have hm6 : 6 ≤ m := Nat.succ_le_of_lt hm5
    have h6 : 6 ≤ h + h := by simpa [hsum] using hm6
    omega
  have hfst : h + (h - 3) = m - 3 := by
    rw [← hsum]
    omega
  have hsnd : h - 2 - (h - 3) = 1 := by
    omega
  rw [iterate_R2xy_from_half_half_sub_two (m := m) (m / 2 - 3) le_rfl]
  ext
  · change (((h : ℕ) : ZMod m) + (((h - 3 : ℕ) : ZMod m))) = (((m - 3 : ℕ) : ZMod m))
    calc
      (((h : ℕ) : ZMod m) + (((h - 3 : ℕ) : ZMod m)))
          = (((h + (h - 3) : ℕ) : ZMod m)) := by rw [Nat.cast_add]
      _ = (((m - 3 : ℕ) : ZMod m)) := by rw [hfst]
  · change (((h : ℕ) : ZMod m) - 2 - (((h - 3 : ℕ) : ZMod m))) = (1 : ZMod m)
    have h2n : 2 + (h - 3) ≤ h := by omega
    have hsub : h - (h - 3) - 2 = h - 2 - (h - 3) := by omega
    calc
      (((h : ℕ) : ZMod m) - 2 - (((h - 3 : ℕ) : ZMod m)))
          = (((h : ℕ) : ZMod m) - (((2 + (h - 3) : ℕ) : ZMod m))) := by
              simp [Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = (((h - (2 + (h - 3)) : ℕ) : ZMod m)) := by rw [Nat.cast_sub h2n]
      _ = (((h - (h - 3) - 2 : ℕ) : ZMod m)) := by
            rw [Nat.add_comm 2 (h - 3), ← Nat.sub_sub]
      _ = (((h - 2 - (h - 3) : ℕ) : ZMod m)) := by
            simpa using congrArg (fun t : ℕ => ((t : ℕ) : ZMod m)) hsub
      _ = (((1 : ℕ) : ZMod m)) := by rw [hsnd]
      _ = (1 : ZMod m) := by norm_num

theorem R2xy_m_sub_three_one [Fact (5 < m)] :
    R2xy (m := m) ((((m - 3 : ℕ) : ZMod m)), (1 : ZMod m)) =
      linePoint (m := m) (((m - 1 : ℕ) : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm1 : 1 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (1 < m) := ⟨hm1⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  have hx1 : (((m - 3 : ℕ) : ZMod m)) ≠ (1 : ZMod m) := by
    apply natCast_ne_one_of_two_le_lt (m := m) (n := m - 3)
    · omega
    · omega
  have hxneg1 : (((m - 3 : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
    apply natCast_ne_neg_one_of_lt (m := m) (n := m - 3)
    omega
  have hcoord : (((m - 3 : ℕ) : ZMod m) + 2) = (((m - 1 : ℕ) : ZMod m)) := by
    change (((m - 3 : ℕ) : ZMod m) + (((2 : ℕ) : ZMod m))) = (((m - 1 : ℕ) : ZMod m))
    rw [← Nat.cast_add]
    congr
    omega
  calc
    R2xy (m := m) ((((m - 3 : ℕ) : ZMod m)), (1 : ZMod m))
        = ((((m - 3 : ℕ) : ZMod m)) + 2, (0 : ZMod m)) := by
            simpa using R2xy_eq_B_of (m := m) hx1 hxneg1
    _ = linePoint (m := m) (((m - 1 : ℕ) : ZMod m)) := by
          simp [linePoint, hcoord]

theorem iterate_two_from_linePoint_one [Fact (Even m)] [Fact (5 < m)] :
    (R2xy (m := m)^[2]) (linePoint (m := m) (1 : ZMod m)) =
      ((2 : ZMod m), (-2 : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  have hm2 : 2 < m := by omega
  letI : Fact (2 < m) := ⟨hm2⟩
  calc
    (R2xy (m := m)^[2]) (linePoint (m := m) (1 : ZMod m))
        = R2xy (m := m) (R2xy (m := m) (linePoint (m := m) (1 : ZMod m))) := by simp
    _ = R2xy (m := m) ((2 : ZMod m), (-1 : ZMod m)) := by rw [R2xy_linePoint_one (m := m)]
    _ = ((2 : ZMod m), (-2 : ZMod m)) := R2xy_two_neg_one (m := m)

theorem iterate_R2xy_from_linePoint_one_after_two [Fact (Even m)] [Fact (5 < m)] :
    ∀ n, n ≤ m / 2 - 2 →
      (R2xy (m := m)^[n + 2]) (linePoint (m := m) (1 : ZMod m)) =
        ((2 : ZMod m) + n, (-2 : ZMod m) - n)
  | n, hn => by
      rw [Function.iterate_add_apply]
      simpa [iterate_two_from_linePoint_one (m := m)] using
        iterate_R2xy_from_two_neg_two (m := m) n hn

theorem iterate_to_half_half_sub_two_from_linePoint_one [Fact (Even m)] [Fact (5 < m)] :
    (R2xy (m := m)^[m / 2 + 1]) (linePoint (m := m) (1 : ZMod m)) =
      ((((m / 2 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m)) - 2) := by
  have hhalf :
      (R2xy (m := m)^[m / 2]) (linePoint (m := m) (1 : ZMod m)) =
        ((((m / 2 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m))) := by
    have hm5 : 5 < m := Fact.out
    have hmhalf : 2 ≤ m / 2 := by
      have hm6 : 6 ≤ m := Nat.succ_le_of_lt hm5
      omega
    rw [show m / 2 = (m / 2 - 2) + 2 by omega, Function.iterate_add_apply]
    rw [iterate_two_from_linePoint_one (m := m)]
    convert iterate_to_half_half_from_two_neg_two (m := m) using 1 <;> congr <;> omega
  rw [show m / 2 + 1 = 1 + m / 2 by omega, Function.iterate_add_apply]
  simpa [hhalf] using R2xy_half_half (m := m)

theorem iterate_R2xy_from_linePoint_one_after_half_half_sub_two [Fact (Even m)] [Fact (5 < m)] :
    ∀ n, n ≤ m / 2 - 3 →
      (R2xy (m := m)^[m / 2 + 1 + n]) (linePoint (m := m) (1 : ZMod m)) =
        ((((m / 2 : ℕ) : ZMod m)) + n, (((m / 2 : ℕ) : ZMod m)) - 2 - n)
  | n, hn => by
      rw [show m / 2 + 1 + n = n + (m / 2 + 1) by omega, Function.iterate_add_apply]
      simpa [iterate_to_half_half_sub_two_from_linePoint_one (m := m)] using
        iterate_R2xy_from_half_half_sub_two (m := m) n hn

theorem firstReturn_one [Fact (Even m)] [Fact (5 < m)] :
    (R2xy (m := m)^[rho2 (m := m) (1 : ZMod m)]) (linePoint (m := m) (1 : ZMod m)) =
      linePoint (m := m) (T2 (m := m) (1 : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  have hm1 : 1 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (1 < m) := ⟨hm1⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  have hrho : rho2 (m := m) (1 : ZMod m) = m - 1 := by
    have h10 : (1 : ZMod m) ≠ 0 := one_ne_zero (m := m)
    simp [rho2, h10]
  have hT : T2 (m := m) (1 : ZMod m) = (-1 : ZMod m) := by
    have h10 : (1 : ZMod m) ≠ 0 := one_ne_zero (m := m)
    simp [T2, h10]
  have hmEven : Even m := Fact.out
  have hsum : m / 2 + m / 2 = m := by
    simpa [two_mul] using (Nat.two_mul_div_two_of_even hmEven)
  have hmSplit : m - 1 = 2 + (m / 2 - 2) + 1 + (m / 2 - 3) + 1 := by
    rw [← hsum]
    omega
  have hm1le : 1 ≤ m := by omega
  have hneg1 : (((m - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) := cast_sub_one_eq_neg_one (m := m) hm1le
  have hstep2 :
      (R2xy (m := m)^[2]) (linePoint (m := m) (1 : ZMod m)) =
        ((2 : ZMod m), (-2 : ZMod m)) := by
    calc
      (R2xy (m := m)^[2]) (linePoint (m := m) (1 : ZMod m))
          = R2xy (m := m) (R2xy (m := m) (linePoint (m := m) (1 : ZMod m))) := by simp
      _ = R2xy (m := m) ((2 : ZMod m), (-1 : ZMod m)) := by rw [R2xy_linePoint_one (m := m)]
      _ = ((2 : ZMod m), (-2 : ZMod m)) := R2xy_two_neg_one (m := m)
  have hstepHalf :
      (R2xy (m := m)^[2 + (m / 2 - 2)]) (linePoint (m := m) (1 : ZMod m)) =
        ((((m / 2 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m))) := by
    rw [Nat.add_comm, Function.iterate_add_apply]
    simpa [hstep2] using iterate_to_half_half_from_two_neg_two (m := m)
  have hstepHalfSubTwo :
      (R2xy (m := m)^[2 + (m / 2 - 2) + 1]) (linePoint (m := m) (1 : ZMod m)) =
        ((((m / 2 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m)) - 2) := by
    rw [show 2 + (m / 2 - 2) + 1 = 1 + (2 + (m / 2 - 2)) by omega, Function.iterate_add_apply]
    simpa [hstepHalf] using R2xy_half_half (m := m)
  have hstepMSubThree :
      (R2xy (m := m)^[2 + (m / 2 - 2) + 1 + (m / 2 - 3)]) (linePoint (m := m) (1 : ZMod m)) =
        ((((m - 3 : ℕ) : ZMod m)), (1 : ZMod m)) := by
    rw [show 2 + (m / 2 - 2) + 1 + (m / 2 - 3) =
      (m / 2 - 3) + (2 + (m / 2 - 2) + 1) by omega, Function.iterate_add_apply]
    simpa [hstepHalfSubTwo] using
      iterate_to_m_sub_three_one_from_half_half_sub_two (m := m)
  have hstepFinal :
      (R2xy (m := m)^[2 + (m / 2 - 2) + 1 + (m / 2 - 3) + 1])
          (linePoint (m := m) (1 : ZMod m)) =
        linePoint (m := m) (((m - 1 : ℕ) : ZMod m)) := by
    rw [show 2 + (m / 2 - 2) + 1 + (m / 2 - 3) + 1 =
      1 + (2 + (m / 2 - 2) + 1 + (m / 2 - 3)) by omega, Function.iterate_add_apply]
    simpa [hstepMSubThree] using R2xy_m_sub_three_one (m := m)
  calc
    (R2xy (m := m)^[rho2 (m := m) (1 : ZMod m)]) (linePoint (m := m) (1 : ZMod m))
        = (R2xy (m := m)^[m - 1]) (linePoint (m := m) (1 : ZMod m)) := by rw [hrho]
    _ = (R2xy (m := m)^[2 + (m / 2 - 2) + 1 + (m / 2 - 3) + 1])
          (linePoint (m := m) (1 : ZMod m)) := by
          rw [hmSplit]
    _ = linePoint (m := m) (((m - 1 : ℕ) : ZMod m)) := by
          exact hstepFinal
    _ = linePoint (m := m) (-1 : ZMod m) := by rw [hneg1]
    _ = linePoint (m := m) (T2 (m := m) (1 : ZMod m)) := by rw [hT]

theorem hfirst_one [Fact (Even m)] [Fact (5 < m)] :
    ∀ n, 0 < n → n < rho2 (m := m) (1 : ZMod m) →
      (R2xy (m := m)^[n]) (linePoint (m := m) (1 : ZMod m)) ∉ Set.range (linePoint (m := m))
  | n, hn0, hnlt => by
      have hm5 : 5 < m := Fact.out
      have hm0 : 0 < m := by omega
      have hm1 : 1 < m := by omega
      have hm2 : 2 < m := by omega
      letI : Fact (0 < m) := ⟨hm0⟩
      letI : Fact (1 < m) := ⟨hm1⟩
      letI : Fact (2 < m) := ⟨hm2⟩
      have hmEven : Even m := Fact.out
      have hsum : m / 2 + m / 2 = m := by
        simpa [two_mul] using (Nat.two_mul_div_two_of_even hmEven)
      have hrho : rho2 (m := m) (1 : ZMod m) = m - 1 := by
        have h10 : (1 : ZMod m) ≠ 0 := one_ne_zero (m := m)
        simp [rho2, h10]
      have hnm1 : n < m - 1 := by rwa [hrho] at hnlt
      by_cases h1 : n = 1
      · apply not_mem_range_linePoint_of_snd_ne_zero
        rw [h1]
        simpa [Function.iterate_one, R2xy_linePoint_one (m := m)] using
          (neg_ne_zero.mpr (one_ne_zero (m := m)))
      · by_cases hhalf : n ≤ m / 2
        · let t : ℕ := n - 2
          have ht : t ≤ m / 2 - 2 := by
            dsimp [t]
            omega
          have hnEq : n = t + 2 := by
            dsimp [t]
            omega
          have hiter :
              (R2xy (m := m)^[n]) (linePoint (m := m) (1 : ZMod m)) =
                ((2 : ZMod m) + t, (-2 : ZMod m) - t) := by
            rw [hnEq]
            simpa using iterate_R2xy_from_linePoint_one_after_two (m := m) t ht
          apply not_mem_range_linePoint_of_snd_ne_zero
          rw [hiter]
          exact neg_two_sub_nat_ne_zero (m := m) (n := t) (by omega)
        · let t : ℕ := n - (m / 2 + 1)
          have ht : t ≤ m / 2 - 3 := by
            dsimp [t]
            rw [← hsum] at hnm1
            omega
          have hnEq : n = m / 2 + 1 + t := by
            dsimp [t]
            omega
          have hiter :
              (R2xy (m := m)^[n]) (linePoint (m := m) (1 : ZMod m)) =
                ((((m / 2 : ℕ) : ZMod m)) + t, (((m / 2 : ℕ) : ZMod m)) - 2 - t) := by
            rw [hnEq]
            simpa using iterate_R2xy_from_linePoint_one_after_half_half_sub_two (m := m) t ht
          have hycast :
              (((m / 2 : ℕ) : ZMod m) - 2 - t) = (((m / 2 - 2 - t : ℕ) : ZMod m)) := by
            have h2t : 2 + t ≤ m / 2 := by omega
            have hsub : m / 2 - t - 2 = m / 2 - 2 - t := by omega
            calc
              (((m / 2 : ℕ) : ZMod m) - 2 - t)
                  = (((m / 2 : ℕ) : ZMod m) - (((2 + t : ℕ) : ZMod m))) := by
                      simp [Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
              _ = (((m / 2 - (2 + t) : ℕ) : ZMod m)) := by rw [Nat.cast_sub h2t]
              _ = (((m / 2 - t - 2 : ℕ) : ZMod m)) := by rw [Nat.add_comm 2 t, ← Nat.sub_sub]
              _ = (((m / 2 - 2 - t : ℕ) : ZMod m)) := by
                    simpa using congrArg (fun s : ℕ => ((s : ℕ) : ZMod m)) hsub
          have hy : (((m / 2 : ℕ) : ZMod m) - 2 - t) ≠ 0 := by
            rw [hycast]
            exact natCast_ne_zero_of_pos_lt (m := m) (n := m / 2 - 2 - t) (by omega) (by omega)
          apply not_mem_range_linePoint_of_snd_ne_zero
          rw [hiter]
          exact hy

theorem R2xy_linePoint_two [Fact (Even m)] [Fact (5 < m)] :
    R2xy (m := m) (linePoint (m := m) (2 : ZMod m)) = ((3 : ZMod m), (-1 : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm1 : 1 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (1 < m) := ⟨hm1⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  have hA : linePoint (m := m) (2 : ZMod m) ≠ ((2 : ZMod m), (2 : ZMod m)) := by
    intro h
    exact two_ne_zero (m := m) (by simpa [linePoint] using (congrArg Prod.snd h).symm)
  have hy1 : (0 : ZMod m) ≠ (1 : ZMod m) := (one_ne_zero (m := m)).symm
  have hyneg1 : (0 : ZMod m) ≠ (-1 : ZMod m) := by
    intro h
    exact neg_ne_zero.mpr (one_ne_zero (m := m)) h.symm
  have hdiag : (0 : ZMod m) ≠ (2 : ZMod m) := by
    intro h
    exact two_ne_zero (m := m) h.symm
  have hxneg1 : (2 : ZMod m) ≠ (-1 : ZMod m) :=
    natCast_ne_neg_one_of_lt (m := m) (n := 2) (by omega)
  have h00 : linePoint (m := m) (2 : ZMod m) ≠ ((0 : ZMod m), (0 : ZMod m)) := by
    intro h
    exact two_ne_zero (m := m) (by simpa [linePoint] using congrArg Prod.fst h)
  calc
    R2xy (m := m) (linePoint (m := m) (2 : ZMod m))
        = G (m := m) (linePoint (m := m) (2 : ZMod m)) := by
            simpa [linePoint] using R2xy_eq_G_of (m := m) hA hy1 hyneg1 hdiag hxneg1 h00
    _ = ((3 : ZMod m), (-1 : ZMod m)) := by
          ext <;> simp [linePoint, G] <;> ring

theorem R2xy_three_neg_one [Fact (5 < m)] :
    R2xy (m := m) ((3 : ZMod m), (-1 : ZMod m)) = ((3 : ZMod m), (-2 : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  have h3neg1 : (3 : ZMod m) ≠ (-1 : ZMod m) :=
    natCast_ne_neg_one_of_lt (m := m) (n := 3) (by omega)
  simpa using R2xy_eq_C_of (m := m) h3neg1

theorem iterate_R2xy_from_three_neg_two [Fact (Even m)] [Fact (5 < m)] :
    ∀ n, n ≤ m - 4 →
      (R2xy (m := m)^[n]) ((3 : ZMod m), (-2 : ZMod m)) =
        ((3 : ZMod m) + n, (-2 : ZMod m) - n)
  | 0, _ => by simp
  | n + 1, hn => by
      have hmEven : Even m := Fact.out
      have hm5 : 5 < m := Fact.out
      have hm0 : 0 < m := by omega
      have hm1 : 1 < m := by omega
      have hm2 : 2 < m := by omega
      letI : Fact (0 < m) := ⟨hm0⟩
      letI : Fact (1 < m) := ⟨hm1⟩
      letI : Fact (2 < m) := ⟨hm2⟩
      have hn' : n < m - 4 := Nat.lt_of_succ_le hn
      have hx_lt : 3 + n < m := by omega
      have hy_lt : m - 2 - n < m := by omega
      have xcast : ((3 : ZMod m) + n) = (((3 + n : ℕ) : ZMod m)) := by
        simpa using (Nat.cast_add 3 n).symm
      have ycast : ((-2 : ZMod m) - n) = (((m - 2 - n : ℕ) : ZMod m)) := by
        have hm2le : 2 ≤ m := by omega
        have hnle : n ≤ m - 2 := by omega
        calc
          (-2 : ZMod m) - n = (((m - 2 : ℕ) : ZMod m)) - n := by
            rw [cast_sub_two_eq_neg_two (m := m) hm2le]
          _ = (((m - 2 - n : ℕ) : ZMod m)) := by rw [Nat.cast_sub hnle]
      have hA : ((3 : ZMod m) + n, (-2 : ZMod m) - n) ≠ ((2 : ZMod m), (2 : ZMod m)) := by
        intro hEq
        have hfst : (((3 + n : ℕ) : ZMod m)) = ((2 : ℕ) : ZMod m) := by
          calc
            (((3 + n : ℕ) : ZMod m)) = ((3 : ZMod m) + n) := by rw [xcast]
            _ = (2 : ZMod m) := congrArg Prod.fst hEq
            _ = ((2 : ℕ) : ZMod m) := by norm_num
        exact natCast_ne_two_of_three_le_lt (m := m) (n := 3 + n) (by omega) hx_lt hfst
      have hy1 : (-2 : ZMod m) - n ≠ (1 : ZMod m) := by
        rw [ycast]
        exact natCast_ne_one_of_two_le_lt (m := m) (n := m - 2 - n) (by omega) hy_lt
      have hyneg1 : (-2 : ZMod m) - n ≠ (-1 : ZMod m) := by
        rw [ycast]
        exact natCast_ne_neg_one_of_lt (m := m) (n := m - 2 - n) (by omega)
      have hdiag : (-2 : ZMod m) - n ≠ (3 : ZMod m) + n := by
        intro hEq
        have hnatEq :
            m - 2 - n = 3 + n := by
          have hcast : (((m - 2 - n : ℕ) : ZMod m)) = (((3 + n : ℕ) : ZMod m)) := by
            rw [ycast, xcast] at hEq
            exact hEq
          exact (natCast_eq_natCast_iff_of_lt (m := m) (a := m - 2 - n) (b := 3 + n)
            hy_lt hx_lt).1 hcast
        rcases hmEven with ⟨k, hk⟩
        omega
      have hxneg1 : (3 : ZMod m) + n ≠ (-1 : ZMod m) := by
        rw [xcast]
        exact natCast_ne_neg_one_of_lt (m := m) (n := 3 + n) (by omega)
      have h00 : ((3 : ZMod m) + n, (-2 : ZMod m) - n) ≠ ((0 : ZMod m), (0 : ZMod m)) := by
        intro hEq
        have hfst : (((3 + n : ℕ) : ZMod m)) = 0 := by
          calc
            (((3 + n : ℕ) : ZMod m)) = ((3 : ZMod m) + n) := by rw [xcast]
            _ = 0 := congrArg Prod.fst hEq
        exact natCast_ne_zero_of_pos_lt (m := m) (n := 3 + n) (by omega) hx_lt hfst
      rw [Function.iterate_succ_apply',
        iterate_R2xy_from_three_neg_two n (Nat.le_of_succ_le hn)]
      rw [R2xy_eq_G_of (m := m) hA hy1 hyneg1 hdiag hxneg1 h00]
      ext <;> simp [G, Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] <;> ring

theorem iterate_to_m_sub_one_two_from_three_neg_two [Fact (Even m)] [Fact (5 < m)] :
    (R2xy (m := m)^[m - 4]) ((3 : ZMod m), (-2 : ZMod m)) =
      ((((m - 1 : ℕ) : ZMod m)), (2 : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  rw [iterate_R2xy_from_three_neg_two (m := m) (m - 4) le_rfl]
  ext
  · change ((((3 : ℕ) : ZMod m)) + (((m - 4 : ℕ) : ZMod m))) = (((m - 1 : ℕ) : ZMod m))
    calc
      ((((3 : ℕ) : ZMod m)) + (((m - 4 : ℕ) : ZMod m))) = (((3 + (m - 4) : ℕ) : ZMod m)) := by
        rw [Nat.cast_add]
      _ = (((m - 1 : ℕ) : ZMod m)) := by congr; omega
  · have hm2le : 2 ≤ m := Nat.le_of_lt (lt_trans (by decide : 2 < 5) hm5)
    have hnle : m - 4 ≤ m - 2 := by
      have hm4le : 4 ≤ m := Nat.succ_le_of_lt (lt_trans (by decide : 3 < 5) hm5)
      omega
    have hnat : m - 2 - (m - 4) = 2 := by omega
    change (-2 : ZMod m) - (((m - 4 : ℕ) : ZMod m)) = (2 : ZMod m)
    calc
      (-2 : ZMod m) - (((m - 4 : ℕ) : ZMod m))
          = (((m - 2 : ℕ) : ZMod m)) - (((m - 4 : ℕ) : ZMod m)) := by
              rw [cast_sub_two_eq_neg_two (m := m) hm2le]
      _ = (((m - 2 - (m - 4) : ℕ) : ZMod m)) := by rw [Nat.cast_sub hnle]
      _ = (((2 : ℕ) : ZMod m)) := by rw [hnat]
      _ = (2 : ZMod m) := by norm_num

theorem R2xy_m_sub_one_two [Fact (Even m)] [Fact (5 < m)] :
    R2xy (m := m) ((((m - 1 : ℕ) : ZMod m)), (2 : ZMod m)) = ((0 : ZMod m), (2 : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  have h2neg2 : (2 : ZMod m) ≠ (-2 : ZMod m) := by
    intro h
    have hzero : (((4 : ℕ) : ZMod m)) = 0 := by
      have hstep := congrArg (fun z : ZMod m => z + 2) h
      norm_num [Nat.cast_add, add_assoc, add_left_comm, add_comm] at hstep ⊢
      exact hstep
    exact natCast_ne_zero_of_pos_lt (m := m) (n := 4) (by omega) (by omega) hzero
  simpa [cast_sub_one_eq_neg_one (m := m) (by omega)] using
    R2xy_eq_E_of (m := m) (hy0 := two_ne_zero (m := m)) (hyneg2 := h2neg2)

theorem R2xy_zero_two [Fact (Even m)] [Fact (5 < m)] :
    R2xy (m := m) ((0 : ZMod m), (2 : ZMod m)) = ((1 : ZMod m), (1 : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm1 : 1 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (1 < m) := ⟨hm1⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  have hA : ((0 : ZMod m), (2 : ZMod m)) ≠ ((2 : ZMod m), (2 : ZMod m)) := by
    intro h
    exact two_ne_zero (m := m) (congrArg Prod.fst h).symm
  have hy1 : (2 : ZMod m) ≠ (1 : ZMod m) := two_ne_one (m := m)
  have hyneg1 : (2 : ZMod m) ≠ (-1 : ZMod m) :=
    natCast_ne_neg_one_of_lt (m := m) (n := 2) (by omega)
  have hdiag : (2 : ZMod m) ≠ (0 : ZMod m) := by
    intro h
    exact two_ne_zero (m := m) h
  have hxneg1 : (0 : ZMod m) ≠ (-1 : ZMod m) := by
    intro h
    exact neg_ne_zero.mpr (one_ne_zero (m := m)) h.symm
  have h00 : ((0 : ZMod m), (2 : ZMod m)) ≠ ((0 : ZMod m), (0 : ZMod m)) := by
    intro h
    exact two_ne_zero (m := m) (congrArg Prod.snd h)
  calc
    R2xy (m := m) ((0 : ZMod m), (2 : ZMod m))
        = G (m := m) ((0 : ZMod m), (2 : ZMod m)) := by
            exact R2xy_eq_G_of (m := m) hA hy1 hyneg1 hdiag hxneg1 h00
    _ = ((1 : ZMod m), (1 : ZMod m)) := by
          ext <;> simp [G] <;> ring

theorem R2xy_one_one [Fact (Even m)] [Fact (5 < m)] :
    R2xy (m := m) ((1 : ZMod m), (1 : ZMod m)) = ((1 : ZMod m), (-1 : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  have hm1 : 1 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (1 < m) := ⟨hm1⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  calc
    R2xy (m := m) ((1 : ZMod m), (1 : ZMod m)) = ((1 : ZMod m), (1 : ZMod m) - 2) := by
      exact R2xy_eq_D_of (m := m)
        (one_ne_zero (m := m)) (two_ne_one (m := m)).symm (one_ne_neg_one (m := m))
    _ = ((1 : ZMod m), (-1 : ZMod m)) := by
      ext <;> ring

theorem R2xy_one_neg_one [Fact (Even m)] [Fact (5 < m)] :
    R2xy (m := m) ((1 : ZMod m), (-1 : ZMod m)) = ((1 : ZMod m), (-2 : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  simpa using R2xy_eq_C_of (m := m) (one_ne_neg_one (m := m))

theorem iterate_R2xy_from_one_neg_two [Fact (Even m)] [Fact (5 < m)] :
    ∀ n, n ≤ m - 3 →
      (R2xy (m := m)^[n]) ((1 : ZMod m), (-2 : ZMod m)) =
        ((1 : ZMod m) + n, (-2 : ZMod m) - n)
  | 0, _ => by simp
  | n + 1, hn => by
      have hmEven : Even m := Fact.out
      have hm5 : 5 < m := Fact.out
      have hm0 : 0 < m := by omega
      have hm1 : 1 < m := by omega
      have hm2 : 2 < m := by omega
      letI : Fact (0 < m) := ⟨hm0⟩
      letI : Fact (1 < m) := ⟨hm1⟩
      letI : Fact (2 < m) := ⟨hm2⟩
      have hn' : n < m - 3 := Nat.lt_of_succ_le hn
      have hx_lt : 1 + n < m := by omega
      have hy_lt : m - 2 - n < m := by omega
      have xcast : ((1 : ZMod m) + n) = (((1 + n : ℕ) : ZMod m)) := by
        simpa using (Nat.cast_add 1 n).symm
      have ycast : ((-2 : ZMod m) - n) = (((m - 2 - n : ℕ) : ZMod m)) := by
        have hm2le : 2 ≤ m := by omega
        have hnle : n ≤ m - 2 := by omega
        calc
          (-2 : ZMod m) - n = (((m - 2 : ℕ) : ZMod m)) - n := by
            rw [cast_sub_two_eq_neg_two (m := m) hm2le]
          _ = (((m - 2 - n : ℕ) : ZMod m)) := by rw [Nat.cast_sub hnle]
      have hdiag : (-2 : ZMod m) - n ≠ (1 : ZMod m) + n := by
        intro hEq
        have hnatEq : m - 2 - n = 1 + n := by
          have hcast : (((m - 2 - n : ℕ) : ZMod m)) = (((1 + n : ℕ) : ZMod m)) := by
            rw [ycast, xcast] at hEq
            exact hEq
          exact (natCast_eq_natCast_iff_of_lt (m := m) (a := m - 2 - n) (b := 1 + n)
            hy_lt hx_lt).1 hcast
        rcases hmEven with ⟨k, hk⟩
        omega
      have hA : ((1 : ZMod m) + n, (-2 : ZMod m) - n) ≠ ((2 : ZMod m), (2 : ZMod m)) := by
        intro hEq
        have hfst : (1 : ZMod m) + n = (2 : ZMod m) := congrArg Prod.fst hEq
        have hsnd : (-2 : ZMod m) - n = (2 : ZMod m) := congrArg Prod.snd hEq
        exact hdiag (by rw [hsnd, hfst])
      have hy1 : (-2 : ZMod m) - n ≠ (1 : ZMod m) := by
        rw [ycast]
        exact natCast_ne_one_of_two_le_lt (m := m) (n := m - 2 - n) (by omega) hy_lt
      have hyneg1 : (-2 : ZMod m) - n ≠ (-1 : ZMod m) := by
        rw [ycast]
        exact natCast_ne_neg_one_of_lt (m := m) (n := m - 2 - n) (by omega)
      have hxneg1 : (1 : ZMod m) + n ≠ (-1 : ZMod m) := by
        rw [xcast]
        exact natCast_ne_neg_one_of_lt (m := m) (n := 1 + n) (by omega)
      have h00 : ((1 : ZMod m) + n, (-2 : ZMod m) - n) ≠ ((0 : ZMod m), (0 : ZMod m)) := by
        intro hEq
        have hfst : (((1 + n : ℕ) : ZMod m)) = 0 := by
          calc
            (((1 + n : ℕ) : ZMod m)) = ((1 : ZMod m) + n) := by rw [xcast]
            _ = 0 := congrArg Prod.fst hEq
        exact natCast_ne_zero_of_pos_lt (m := m) (n := 1 + n) (by omega) hx_lt hfst
      rw [Function.iterate_succ_apply',
        iterate_R2xy_from_one_neg_two n (Nat.le_of_succ_le hn)]
      rw [R2xy_eq_G_of (m := m) hA hy1 hyneg1 hdiag hxneg1 h00]
      ext <;> simp [G, Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] <;> ring

theorem iterate_to_m_sub_two_one_from_one_neg_two [Fact (Even m)] [Fact (5 < m)] :
    (R2xy (m := m)^[m - 3]) ((1 : ZMod m), (-2 : ZMod m)) =
      ((((m - 2 : ℕ) : ZMod m)), (1 : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  rw [iterate_R2xy_from_one_neg_two (m := m) (m - 3) le_rfl]
  ext
  · have hfst : ((((1 : ℕ) : ZMod m)) + (((m - 3 : ℕ) : ZMod m))) = (((m - 2 : ℕ) : ZMod m)) := by
      calc
        ((((1 : ℕ) : ZMod m)) + (((m - 3 : ℕ) : ZMod m))) = (((1 + (m - 3) : ℕ) : ZMod m)) := by
          rw [Nat.cast_add]
        _ = (((m - 2 : ℕ) : ZMod m)) := by congr; omega
    simpa using hfst
  · have hm2le : 2 ≤ m := Nat.le_of_lt (lt_trans (by decide : 2 < 5) hm5)
    have hnle : m - 3 ≤ m - 2 := by
      have hm3le : 3 ≤ m := Nat.le_of_lt (lt_trans (by decide : 3 < 5) hm5)
      omega
    have hnat : m - 2 - (m - 3) = 1 := by omega
    change (-2 : ZMod m) - (((m - 3 : ℕ) : ZMod m)) = (1 : ZMod m)
    calc
      (-2 : ZMod m) - (((m - 3 : ℕ) : ZMod m))
          = (((m - 2 : ℕ) : ZMod m)) - (((m - 3 : ℕ) : ZMod m)) := by
              rw [cast_sub_two_eq_neg_two (m := m) hm2le]
      _ = (((m - 2 - (m - 3) : ℕ) : ZMod m)) := by rw [Nat.cast_sub hnle]
      _ = (((1 : ℕ) : ZMod m)) := by rw [hnat]
      _ = (1 : ZMod m) := by norm_num

theorem R2xy_m_sub_two_one [Fact (Even m)] [Fact (5 < m)] :
    R2xy (m := m) ((((m - 2 : ℕ) : ZMod m)), (1 : ZMod m)) = ((0 : ZMod m), (0 : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm1 : 1 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (1 < m) := ⟨hm1⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  have hm2le : 2 ≤ m := by omega
  have hx1 : (((m - 2 : ℕ) : ZMod m)) ≠ (1 : ZMod m) := by
    apply natCast_ne_one_of_two_le_lt (m := m) (n := m - 2)
    · omega
    · omega
  have hxneg1 : (((m - 2 : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
    intro h
    have hneg2 : (((m - 2 : ℕ) : ZMod m)) = (-2 : ZMod m) := cast_sub_two_eq_neg_two (m := m) hm2le
    rw [hneg2] at h
    have hstep := congrArg (fun z : ZMod m => z + 2) h
    norm_num at hstep
  calc
    R2xy (m := m) ((((m - 2 : ℕ) : ZMod m)), (1 : ZMod m))
        = ((((m - 2 : ℕ) : ZMod m)) + 2, (0 : ZMod m)) := by
            simpa using R2xy_eq_B_of (m := m) hx1 hxneg1
    _ = ((0 : ZMod m), (0 : ZMod m)) := by
          ext
          ·
            calc
              (((m - 2 : ℕ) : ZMod m) + 2)
                  = (((m - 2 : ℕ) : ZMod m) + (((2 : ℕ) : ZMod m))) := by norm_num
              _ = (((m : ℕ) : ZMod m)) := by rw [← Nat.cast_add]; congr; omega
              _ = 0 := by simp
          · rfl

theorem iterate_two_from_linePoint_two [Fact (Even m)] [Fact (5 < m)] :
    (R2xy (m := m)^[2]) (linePoint (m := m) (2 : ZMod m)) =
      ((3 : ZMod m), (-2 : ZMod m)) := by
  calc
    (R2xy (m := m)^[2]) (linePoint (m := m) (2 : ZMod m))
        = R2xy (m := m) (R2xy (m := m) (linePoint (m := m) (2 : ZMod m))) := by simp
    _ = R2xy (m := m) ((3 : ZMod m), (-1 : ZMod m)) := by rw [R2xy_linePoint_two (m := m)]
    _ = ((3 : ZMod m), (-2 : ZMod m)) := R2xy_three_neg_one (m := m)

theorem iterate_R2xy_from_linePoint_two_after_two [Fact (Even m)] [Fact (5 < m)] :
    ∀ n, n ≤ m - 4 →
      (R2xy (m := m)^[n + 2]) (linePoint (m := m) (2 : ZMod m)) =
        ((3 : ZMod m) + n, (-2 : ZMod m) - n)
  | n, hn => by
      rw [Function.iterate_add_apply]
      simpa [iterate_two_from_linePoint_two (m := m)] using
        iterate_R2xy_from_three_neg_two (m := m) n hn

theorem iterate_to_m_sub_one_two_from_linePoint_two [Fact (Even m)] [Fact (5 < m)] :
    (R2xy (m := m)^[m - 2]) (linePoint (m := m) (2 : ZMod m)) =
      ((((m - 1 : ℕ) : ZMod m)), (2 : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  rw [show m - 2 = (m - 4) + 2 by omega, Function.iterate_add_apply]
  rw [iterate_two_from_linePoint_two (m := m)]
  exact iterate_to_m_sub_one_two_from_three_neg_two (m := m)

theorem iterate_to_zero_two_from_linePoint_two [Fact (Even m)] [Fact (5 < m)] :
    (R2xy (m := m)^[m - 1]) (linePoint (m := m) (2 : ZMod m)) =
      ((0 : ZMod m), (2 : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  rw [show m - 1 = 1 + (m - 2) by omega, Function.iterate_add_apply]
  simp [Function.iterate_one]
  rw [iterate_to_m_sub_one_two_from_linePoint_two (m := m)]
  exact R2xy_m_sub_one_two (m := m)

theorem iterate_to_one_one_from_linePoint_two [Fact (Even m)] [Fact (5 < m)] :
    (R2xy (m := m)^[m]) (linePoint (m := m) (2 : ZMod m)) =
      ((1 : ZMod m), (1 : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  calc
    (R2xy (m := m)^[m]) (linePoint (m := m) (2 : ZMod m))
        = R2xy (m := m) ((R2xy (m := m)^[m - 1]) (linePoint (m := m) (2 : ZMod m))) := by
            rw [show m = 1 + (m - 1) by omega, Function.iterate_add_apply]
            simp
    _ = R2xy (m := m) ((0 : ZMod m), (2 : ZMod m)) := by
          rw [iterate_to_zero_two_from_linePoint_two (m := m)]
    _ = ((1 : ZMod m), (1 : ZMod m)) := R2xy_zero_two (m := m)

theorem iterate_to_one_neg_one_from_linePoint_two [Fact (Even m)] [Fact (5 < m)] :
    (R2xy (m := m)^[m + 1]) (linePoint (m := m) (2 : ZMod m)) =
      ((1 : ZMod m), (-1 : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  calc
    (R2xy (m := m)^[m + 1]) (linePoint (m := m) (2 : ZMod m))
        = R2xy (m := m) ((R2xy (m := m)^[m]) (linePoint (m := m) (2 : ZMod m))) := by
            rw [show m + 1 = 1 + m by omega, Function.iterate_add_apply]
            simp
    _ = R2xy (m := m) ((1 : ZMod m), (1 : ZMod m)) := by
          rw [iterate_to_one_one_from_linePoint_two (m := m)]
    _ = ((1 : ZMod m), (-1 : ZMod m)) := R2xy_one_one (m := m)

theorem iterate_to_one_neg_two_from_linePoint_two [Fact (Even m)] [Fact (5 < m)] :
    (R2xy (m := m)^[m + 2]) (linePoint (m := m) (2 : ZMod m)) =
      ((1 : ZMod m), (-2 : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  calc
    (R2xy (m := m)^[m + 2]) (linePoint (m := m) (2 : ZMod m))
        = R2xy (m := m) ((R2xy (m := m)^[m + 1]) (linePoint (m := m) (2 : ZMod m))) := by
            rw [show m + 2 = 1 + (m + 1) by omega, Function.iterate_add_apply]
            simp
    _ = R2xy (m := m) ((1 : ZMod m), (-1 : ZMod m)) := by
          rw [iterate_to_one_neg_one_from_linePoint_two (m := m)]
    _ = ((1 : ZMod m), (-2 : ZMod m)) := R2xy_one_neg_one (m := m)

theorem iterate_R2xy_from_linePoint_two_after_one_neg_two [Fact (Even m)] [Fact (5 < m)] :
    ∀ n, n ≤ m - 3 →
      (R2xy (m := m)^[m + 2 + n]) (linePoint (m := m) (2 : ZMod m)) =
        ((1 : ZMod m) + n, (-2 : ZMod m) - n)
  | n, hn => by
      rw [show m + 2 + n = n + (m + 2) by omega, Function.iterate_add_apply]
      simpa [iterate_to_one_neg_two_from_linePoint_two (m := m)] using
        iterate_R2xy_from_one_neg_two (m := m) n hn

theorem firstReturn_two [Fact (Even m)] [Fact (5 < m)] :
    (R2xy (m := m)^[rho2 (m := m) (2 : ZMod m)]) (linePoint (m := m) (2 : ZMod m)) =
      linePoint (m := m) (T2 (m := m) (2 : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm1 : 1 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (1 < m) := ⟨hm1⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  have hrho : rho2 (m := m) (2 : ZMod m) = 2 * m := by
    have h20 : (2 : ZMod m) ≠ 0 := two_ne_zero (m := m)
    have h21 : (2 : ZMod m) ≠ 1 := two_ne_one (m := m)
    simp [rho2, h20, h21]
  have hT : T2 (m := m) (2 : ZMod m) = 0 := by
    have h20 : (2 : ZMod m) ≠ 0 := two_ne_zero (m := m)
    have h21 : (2 : ZMod m) ≠ 1 := two_ne_one (m := m)
    simp [T2, h20, h21]
  have hstepMSubTwoOne :
      (R2xy (m := m)^[m + 2 + (m - 3)]) (linePoint (m := m) (2 : ZMod m)) =
        ((((m - 2 : ℕ) : ZMod m)), (1 : ZMod m)) := by
    rw [show m + 2 + (m - 3) = (m - 3) + (m + 2) by omega, Function.iterate_add_apply]
    simpa [iterate_to_one_neg_two_from_linePoint_two (m := m)] using
      iterate_to_m_sub_two_one_from_one_neg_two (m := m)
  have hstepFinal :
      (R2xy (m := m)^[2 * m]) (linePoint (m := m) (2 : ZMod m)) =
        linePoint (m := m) (0 : ZMod m) := by
    calc
      (R2xy (m := m)^[2 * m]) (linePoint (m := m) (2 : ZMod m))
          = R2xy (m := m) ((R2xy (m := m)^[m + 2 + (m - 3)]) (linePoint (m := m) (2 : ZMod m))) := by
              rw [show 2 * m = 1 + (m + 2 + (m - 3)) by omega, Function.iterate_add_apply]
              simp
      _ = R2xy (m := m) ((((m - 2 : ℕ) : ZMod m)), (1 : ZMod m)) := by rw [hstepMSubTwoOne]
      _ = linePoint (m := m) (0 : ZMod m) := by
            simpa [linePoint] using R2xy_m_sub_two_one (m := m)
  calc
    (R2xy (m := m)^[rho2 (m := m) (2 : ZMod m)]) (linePoint (m := m) (2 : ZMod m))
        = (R2xy (m := m)^[2 * m]) (linePoint (m := m) (2 : ZMod m)) := by rw [hrho]
    _ = linePoint (m := m) (0 : ZMod m) := hstepFinal
    _ = linePoint (m := m) (T2 (m := m) (2 : ZMod m)) := by rw [hT]

theorem hfirst_two [Fact (Even m)] [Fact (5 < m)] :
    ∀ n, 0 < n → n < rho2 (m := m) (2 : ZMod m) →
      (R2xy (m := m)^[n]) (linePoint (m := m) (2 : ZMod m)) ∉ Set.range (linePoint (m := m))
  | n, hn0, hnlt => by
      have hm5 : 5 < m := Fact.out
      have hm0 : 0 < m := by omega
      have hm1 : 1 < m := by omega
      have hm2 : 2 < m := by omega
      letI : Fact (0 < m) := ⟨hm0⟩
      letI : Fact (1 < m) := ⟨hm1⟩
      letI : Fact (2 < m) := ⟨hm2⟩
      have hrho : rho2 (m := m) (2 : ZMod m) = 2 * m := by
        have h20 : (2 : ZMod m) ≠ 0 := two_ne_zero (m := m)
        have h21 : (2 : ZMod m) ≠ 1 := two_ne_one (m := m)
        simp [rho2, h20, h21]
      have hn2m : n < 2 * m := by rwa [hrho] at hnlt
      by_cases h1 : n = 1
      · apply not_mem_range_linePoint_of_snd_ne_zero
        rw [h1]
        simpa [Function.iterate_one, R2xy_linePoint_two (m := m)] using
          (neg_ne_zero.mpr (one_ne_zero (m := m)))
      · by_cases hfront : n ≤ m - 2
        · let t : ℕ := n - 2
          have ht : t ≤ m - 4 := by
            dsimp [t]
            omega
          have hnEq : n = t + 2 := by
            dsimp [t]
            omega
          have hiter :
              (R2xy (m := m)^[n]) (linePoint (m := m) (2 : ZMod m)) =
                ((3 : ZMod m) + t, (-2 : ZMod m) - t) := by
            rw [hnEq]
            simpa using iterate_R2xy_from_linePoint_two_after_two (m := m) t ht
          apply not_mem_range_linePoint_of_snd_ne_zero
          rw [hiter]
          exact neg_two_sub_nat_ne_zero (m := m) (n := t) (by omega)
        · by_cases hm1case : n = m - 1
          · apply not_mem_range_linePoint_of_snd_ne_zero
            rw [hm1case, iterate_to_zero_two_from_linePoint_two (m := m)]
            exact two_ne_zero (m := m)
          · by_cases hmcase : n = m
            · apply not_mem_range_linePoint_of_snd_ne_zero
              rw [hmcase, iterate_to_one_one_from_linePoint_two (m := m)]
              exact one_ne_zero (m := m)
            · by_cases hmplus : n = m + 1
              · apply not_mem_range_linePoint_of_snd_ne_zero
                rw [hmplus, iterate_to_one_neg_one_from_linePoint_two (m := m)]
                exact neg_ne_zero.mpr (one_ne_zero (m := m))
              · let t : ℕ := n - (m + 2)
                have ht : t ≤ m - 3 := by
                  dsimp [t]
                  omega
                have hnEq : n = m + 2 + t := by
                  dsimp [t]
                  omega
                have hiter :
                    (R2xy (m := m)^[n]) (linePoint (m := m) (2 : ZMod m)) =
                      ((1 : ZMod m) + t, (-2 : ZMod m) - t) := by
                  rw [hnEq]
                  simpa using iterate_R2xy_from_linePoint_two_after_one_neg_two (m := m) t ht
                apply not_mem_range_linePoint_of_snd_ne_zero
                rw [hiter]
                exact neg_two_sub_nat_ne_zero (m := m) (n := t) (by omega)

theorem R2xy_linePoint_m_sub_one [Fact (5 < m)] :
    R2xy (m := m) (linePoint (m := m) ((((m - 1 : ℕ) : ZMod m)))) =
      ((((m - 1 : ℕ) : ZMod m)), (-2 : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm1 : 1 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (1 < m) := ⟨hm1⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  have hm1le : 1 ≤ m := by omega
  have hneg1 : (((m - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) := cast_sub_one_eq_neg_one (m := m) hm1le
  have hneg12 : (-1 : ZMod m) ≠ (2 : ZMod m) :=
    (natCast_ne_neg_one_of_lt (m := m) (n := 2) (by omega)).symm
  calc
    R2xy (m := m) (linePoint (m := m) ((((m - 1 : ℕ) : ZMod m))))
        = R2xy (m := m) ((-1 : ZMod m), (0 : ZMod m)) := by simp [linePoint, hneg1]
    _ = ((-1 : ZMod m), (-2 : ZMod m)) := by
          simp [R2xy, hneg12, one_ne_zero (m := m), two_ne_zero (m := m)]
    _ = ((((m - 1 : ℕ) : ZMod m)), (-2 : ZMod m)) := by rw [hneg1]

theorem R2xy_m_sub_one_neg_two [Fact (5 < m)] :
    R2xy (m := m) ((((m - 1 : ℕ) : ZMod m)), (-2 : ZMod m)) =
      ((((m - 1 : ℕ) : ZMod m)), (-3 : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  have hm0 : 0 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  have hm1le : 1 ≤ m := by omega
  have hneg1 : (((m - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) := cast_sub_one_eq_neg_one (m := m) hm1le
  have hneg12 : (-1 : ZMod m) ≠ (2 : ZMod m) :=
    (natCast_ne_neg_one_of_lt (m := m) (n := 2) (by omega)).symm
  calc
    R2xy (m := m) ((((m - 1 : ℕ) : ZMod m)), (-2 : ZMod m))
        = R2xy (m := m) ((-1 : ZMod m), (-2 : ZMod m)) := by rw [hneg1]
    _ = ((-1 : ZMod m), (-2 : ZMod m) - 1) := by simp [R2xy, hneg12]
    _ = ((-1 : ZMod m), (-3 : ZMod m)) := by
          ext <;> ring
    _ = ((((m - 1 : ℕ) : ZMod m)), (-3 : ZMod m)) := by rw [hneg1]

theorem R2xy_m_sub_one_neg_three [Fact (5 < m)] :
    R2xy (m := m) ((((m - 1 : ℕ) : ZMod m)), (-3 : ZMod m)) =
      ((0 : ZMod m), (-3 : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm1 : 1 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (1 < m) := ⟨hm1⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  have hm1le : 1 ≤ m := by omega
  have hneg1 : (((m - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) := cast_sub_one_eq_neg_one (m := m) hm1le
  calc
    R2xy (m := m) ((((m - 1 : ℕ) : ZMod m)), (-3 : ZMod m))
        = R2xy (m := m) ((-1 : ZMod m), (-3 : ZMod m)) := by rw [hneg1]
    _ = ((0 : ZMod m), (-3 : ZMod m)) := by
          simpa using R2xy_eq_E_of (m := m) (y := (-3 : ZMod m))
            (neg_three_ne_zero (m := m)) (neg_three_ne_neg_two (m := m))

theorem iterate_three_from_linePoint_m_sub_one [Fact (5 < m)] :
    (R2xy (m := m)^[3]) (linePoint (m := m) ((((m - 1 : ℕ) : ZMod m)))) =
      ((0 : ZMod m), (-3 : ZMod m)) := by
  calc
    (R2xy (m := m)^[3]) (linePoint (m := m) ((((m - 1 : ℕ) : ZMod m))))
        = R2xy (m := m) (R2xy (m := m) (R2xy (m := m) (linePoint (m := m) ((((m - 1 : ℕ) : ZMod m)))))) := by
            simp
    _ = R2xy (m := m) (R2xy (m := m) ((((m - 1 : ℕ) : ZMod m)), (-2 : ZMod m))) := by
          rw [R2xy_linePoint_m_sub_one (m := m)]
    _ = R2xy (m := m) ((((m - 1 : ℕ) : ZMod m)), (-3 : ZMod m)) := by
          rw [R2xy_m_sub_one_neg_two (m := m)]
    _ = ((0 : ZMod m), (-3 : ZMod m)) := R2xy_m_sub_one_neg_three (m := m)

theorem iterate_R2xy_from_zero_neg_three [Fact (Even m)] [Fact (5 < m)] :
    ∀ n, n ≤ m - 4 →
      (R2xy (m := m)^[n]) ((0 : ZMod m), (-3 : ZMod m)) =
        ((n : ZMod m), (-3 : ZMod m) - n)
  | 0, _ => by simp
  | n + 1, hn => by
      have hmEven : Even m := Fact.out
      have hm5 : 5 < m := Fact.out
      have hm0 : 0 < m := by omega
      have hm1 : 1 < m := by omega
      letI : Fact (0 < m) := ⟨hm0⟩
      letI : Fact (1 < m) := ⟨hm1⟩
      have hn' : n < m - 4 := Nat.lt_of_succ_le hn
      have hx_lt : n < m := by omega
      have hy_lt : m - 3 - n < m := by omega
      have hm3le : 3 ≤ m := by omega
      have ycast : ((-3 : ZMod m) - n) = (((m - 3 - n : ℕ) : ZMod m)) := by
        have hnle : n ≤ m - 3 := by omega
        calc
          (-3 : ZMod m) - n = (((m - 3 : ℕ) : ZMod m)) - n := by
            rw [cast_sub_three_eq_neg_three (m := m) hm3le]
          _ = (((m - 3 - n : ℕ) : ZMod m)) := by rw [Nat.cast_sub hnle]
      have hy0 : (-3 : ZMod m) - n ≠ 0 := by
        rw [ycast]
        exact natCast_ne_zero_of_pos_lt (m := m) (n := m - 3 - n) (by omega) hy_lt
      have hy1 : (-3 : ZMod m) - n ≠ (1 : ZMod m) := by
        rw [ycast]
        exact natCast_ne_one_of_two_le_lt (m := m) (n := m - 3 - n) (by omega) hy_lt
      have hyneg1 : (-3 : ZMod m) - n ≠ (-1 : ZMod m) := by
        rw [ycast]
        exact natCast_ne_neg_one_of_lt (m := m) (n := m - 3 - n) (by omega)
      have hdiag : (-3 : ZMod m) - n ≠ (n : ZMod m) := by
        intro hEq
        have hcast : (((m - 3 - n : ℕ) : ZMod m)) = (((n : ℕ) : ZMod m)) := by
          rw [ycast] at hEq
          simpa using hEq
        have hnat := (natCast_eq_natCast_iff_of_lt (m := m) (a := m - 3 - n) (b := n)
          hy_lt hx_lt).1 hcast
        rcases hmEven with ⟨k, hk⟩
        omega
      have hxneg1 : (n : ZMod m) ≠ (-1 : ZMod m) := by
        exact natCast_ne_neg_one_of_lt (m := m) (n := n) (by omega)
      have hA : ((n : ZMod m), (-3 : ZMod m) - n) ≠ ((2 : ZMod m), (2 : ZMod m)) := by
        intro hEq
        have hfst : (n : ZMod m) = (2 : ZMod m) := congrArg Prod.fst hEq
        have hsnd : (-3 : ZMod m) - n = (2 : ZMod m) := congrArg Prod.snd hEq
        exact hdiag (by rw [hsnd, hfst])
      have h00 : ((n : ZMod m), (-3 : ZMod m) - n) ≠ ((0 : ZMod m), (0 : ZMod m)) := by
        intro hEq
        exact hy0 (congrArg Prod.snd hEq)
      rw [Function.iterate_succ_apply',
        iterate_R2xy_from_zero_neg_three (m := m) n (Nat.le_of_succ_le hn)]
      rw [R2xy_eq_G_of (m := m) hA hy1 hyneg1 hdiag hxneg1 h00]
      ext <;> simp [G, Nat.cast_add, sub_eq_add_neg] <;> ring

theorem iterate_to_m_sub_four_one_from_zero_neg_three [Fact (Even m)] [Fact (5 < m)] :
    (R2xy (m := m)^[m - 4]) ((0 : ZMod m), (-3 : ZMod m)) =
      ((((m - 4 : ℕ) : ZMod m)), (1 : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  have hm3le : 3 ≤ m := by omega
  rw [iterate_R2xy_from_zero_neg_three (m := m) (m - 4) le_rfl]
  ext
  · simp
  · have hnle : m - 4 ≤ m - 3 := by omega
    have hnat : m - 3 - (m - 4) = 1 := by omega
    change (-3 : ZMod m) - (((m - 4 : ℕ) : ZMod m)) = (1 : ZMod m)
    calc
      (-3 : ZMod m) - (((m - 4 : ℕ) : ZMod m))
          = (((m - 3 : ℕ) : ZMod m)) - (((m - 4 : ℕ) : ZMod m)) := by
              rw [cast_sub_three_eq_neg_three (m := m) hm3le]
      _ = (((m - 3 - (m - 4) : ℕ) : ZMod m)) := by rw [Nat.cast_sub hnle]
      _ = (((1 : ℕ) : ZMod m)) := by rw [hnat]
      _ = (1 : ZMod m) := by norm_num

theorem iterate_R2xy_from_linePoint_m_sub_one_after_three [Fact (Even m)] [Fact (5 < m)] :
    ∀ n, n ≤ m - 4 →
      (R2xy (m := m)^[n + 3]) (linePoint (m := m) ((((m - 1 : ℕ) : ZMod m)))) =
        ((n : ZMod m), (-3 : ZMod m) - n)
  | n, hn => by
      rw [Function.iterate_add_apply]
      simpa [iterate_three_from_linePoint_m_sub_one (m := m)] using
        iterate_R2xy_from_zero_neg_three (m := m) n hn

theorem R2xy_m_sub_four_one [Fact (5 < m)] :
    R2xy (m := m) ((((m - 4 : ℕ) : ZMod m)), (1 : ZMod m)) =
      linePoint (m := m) (((m - 2 : ℕ) : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm1 : 1 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (1 < m) := ⟨hm1⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  have hx1 : (((m - 4 : ℕ) : ZMod m)) ≠ (1 : ZMod m) := by
    apply natCast_ne_one_of_two_le_lt (m := m) (n := m - 4)
    · omega
    · omega
  have hxneg1 : (((m - 4 : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := m - 4) (by omega)
  have hcoord : (((m - 4 : ℕ) : ZMod m) + 2) = (((m - 2 : ℕ) : ZMod m)) := by
    change (((m - 4 : ℕ) : ZMod m) + (((2 : ℕ) : ZMod m))) = (((m - 2 : ℕ) : ZMod m))
    rw [← Nat.cast_add]
    congr
    omega
  calc
    R2xy (m := m) ((((m - 4 : ℕ) : ZMod m)), (1 : ZMod m))
        = ((((m - 4 : ℕ) : ZMod m)) + 2, (0 : ZMod m)) := by
            simpa using R2xy_eq_B_of (m := m) hx1 hxneg1
    _ = linePoint (m := m) (((m - 2 : ℕ) : ZMod m)) := by
          simp [linePoint, hcoord]

theorem firstReturn_m_sub_one [Fact (Even m)] [Fact (5 < m)] :
    (R2xy (m := m)^[rho2 (m := m) ((((m - 1 : ℕ) : ZMod m)))])
        (linePoint (m := m) ((((m - 1 : ℕ) : ZMod m)))) =
      linePoint (m := m) (T2 (m := m) ((((m - 1 : ℕ) : ZMod m)))) := by
  have hm5 : 5 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm1 : 1 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (1 < m) := ⟨hm1⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  have hx0 : (((m - 1 : ℕ) : ZMod m)) ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := m - 1) (by omega) (by omega)
  have hx1 : (((m - 1 : ℕ) : ZMod m)) ≠ (1 : ZMod m) := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := m - 1) (by omega) (by omega)
  have hx2 : (((m - 1 : ℕ) : ZMod m)) ≠ (2 : ZMod m) := by
    exact natCast_ne_two_of_three_le_lt (m := m) (n := m - 1) (by omega) (by omega)
  have hrho : rho2 (m := m) ((((m - 1 : ℕ) : ZMod m))) = m := by
    simp [rho2, hx0, hx1, hx2]
  have hT : T2 (m := m) ((((m - 1 : ℕ) : ZMod m))) = (((m - 2 : ℕ) : ZMod m)) := by
    have hm1le : 1 ≤ m := by omega
    have hm2le : 2 ≤ m := by omega
    have hneg1 : (((m - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) := cast_sub_one_eq_neg_one (m := m) hm1le
    have hneg2 : (((m - 2 : ℕ) : ZMod m)) = (-2 : ZMod m) := cast_sub_two_eq_neg_two (m := m) hm2le
    simp [T2, hx0, hx1, hx2]
    rw [hneg1, hneg2]
    ring
  have hstepMSubFourOne :
      (R2xy (m := m)^[3 + (m - 4)]) (linePoint (m := m) ((((m - 1 : ℕ) : ZMod m)))) =
        ((((m - 4 : ℕ) : ZMod m)), (1 : ZMod m)) := by
    rw [show 3 + (m - 4) = (m - 4) + 3 by omega, Function.iterate_add_apply]
    simpa [iterate_three_from_linePoint_m_sub_one (m := m)] using
      iterate_to_m_sub_four_one_from_zero_neg_three (m := m)
  have hstepFinal :
      (R2xy (m := m)^[m]) (linePoint (m := m) ((((m - 1 : ℕ) : ZMod m)))) =
        linePoint (m := m) (((m - 2 : ℕ) : ZMod m)) := by
    have hstepFinal1 :
        (R2xy (m := m)^[1]) ((R2xy (m := m)^[3 + (m - 4)])
            (linePoint (m := m) ((((m - 1 : ℕ) : ZMod m))))) =
          linePoint (m := m) (((m - 2 : ℕ) : ZMod m)) := by
      simp [Function.iterate_one, hstepMSubFourOne, R2xy_m_sub_four_one (m := m)]
    calc
      (R2xy (m := m)^[m]) (linePoint (m := m) ((((m - 1 : ℕ) : ZMod m))))
          = (R2xy (m := m)^[1 + (3 + (m - 4))])
              (linePoint (m := m) ((((m - 1 : ℕ) : ZMod m)))) := by
                congr 1
                omega
      _ = (R2xy (m := m)^[1]) ((R2xy (m := m)^[3 + (m - 4)])
            (linePoint (m := m) ((((m - 1 : ℕ) : ZMod m))))) := by
              rw [Function.iterate_add_apply]
      _ = linePoint (m := m) (((m - 2 : ℕ) : ZMod m)) := hstepFinal1
  calc
    (R2xy (m := m)^[rho2 (m := m) ((((m - 1 : ℕ) : ZMod m)))])
        (linePoint (m := m) ((((m - 1 : ℕ) : ZMod m))))
        = (R2xy (m := m)^[m]) (linePoint (m := m) ((((m - 1 : ℕ) : ZMod m)))) := by
            rw [hrho]
    _ = linePoint (m := m) (((m - 2 : ℕ) : ZMod m)) := hstepFinal
    _ = linePoint (m := m) (T2 (m := m) ((((m - 1 : ℕ) : ZMod m)))) := by rw [hT]

theorem hfirst_m_sub_one [Fact (Even m)] [Fact (5 < m)] :
    ∀ n, 0 < n → n < rho2 (m := m) ((((m - 1 : ℕ) : ZMod m))) →
      (R2xy (m := m)^[n]) (linePoint (m := m) ((((m - 1 : ℕ) : ZMod m)))) ∉
        Set.range (linePoint (m := m))
  | n, hn0, hnlt => by
      have hm5 : 5 < m := Fact.out
      have hm0 : 0 < m := by omega
      have hm1 : 1 < m := by omega
      have hm2 : 2 < m := by omega
      letI : Fact (0 < m) := ⟨hm0⟩
      letI : Fact (1 < m) := ⟨hm1⟩
      letI : Fact (2 < m) := ⟨hm2⟩
      have hx0 : (((m - 1 : ℕ) : ZMod m)) ≠ 0 := by
        exact natCast_ne_zero_of_pos_lt (m := m) (n := m - 1) (by omega) (by omega)
      have hx1 : (((m - 1 : ℕ) : ZMod m)) ≠ (1 : ZMod m) := by
        exact natCast_ne_one_of_two_le_lt (m := m) (n := m - 1) (by omega) (by omega)
      have hx2 : (((m - 1 : ℕ) : ZMod m)) ≠ (2 : ZMod m) := by
        exact natCast_ne_two_of_three_le_lt (m := m) (n := m - 1) (by omega) (by omega)
      have hrho : rho2 (m := m) ((((m - 1 : ℕ) : ZMod m))) = m := by
        simp [rho2, hx0, hx1, hx2]
      have hnm : n < m := by rwa [hrho] at hnlt
      by_cases h1 : n = 1
      · apply not_mem_range_linePoint_of_snd_ne_zero
        rw [h1, Function.iterate_one, R2xy_linePoint_m_sub_one (m := m)]
        exact neg_ne_zero.mpr (two_ne_zero (m := m))
      · by_cases h2 : n = 2
        · apply not_mem_range_linePoint_of_snd_ne_zero
          rw [h2]
          have hiter2 :
              (R2xy (m := m)^[2]) (linePoint (m := m) ((((m - 1 : ℕ) : ZMod m)))) =
                ((((m - 1 : ℕ) : ZMod m)), (-3 : ZMod m)) := by
            calc
              (R2xy (m := m)^[2]) (linePoint (m := m) ((((m - 1 : ℕ) : ZMod m))))
                  = R2xy (m := m) (R2xy (m := m) (linePoint (m := m) ((((m - 1 : ℕ) : ZMod m))))) := by
                      simp
              _ = R2xy (m := m) ((((m - 1 : ℕ) : ZMod m)), (-2 : ZMod m)) := by
                    rw [R2xy_linePoint_m_sub_one (m := m)]
              _ = ((((m - 1 : ℕ) : ZMod m)), (-3 : ZMod m)) := by
                    rw [R2xy_m_sub_one_neg_two (m := m)]
          rw [hiter2]
          exact neg_three_ne_zero (m := m)
        · let t : ℕ := n - 3
          have ht : t ≤ m - 4 := by
            dsimp [t]
            omega
          have hnEq : n = t + 3 := by
            dsimp [t]
            omega
          have hiter :
              (R2xy (m := m)^[n]) (linePoint (m := m) ((((m - 1 : ℕ) : ZMod m)))) =
                ((t : ZMod m), (-3 : ZMod m) - t) := by
            rw [hnEq]
            simpa using iterate_R2xy_from_linePoint_m_sub_one_after_three (m := m) t ht
          have hm3le : 3 ≤ m := by omega
          have hycast : ((-3 : ZMod m) - t) = (((m - 3 - t : ℕ) : ZMod m)) := by
            have htle : t ≤ m - 3 := by omega
            calc
              (-3 : ZMod m) - t = (((m - 3 : ℕ) : ZMod m)) - t := by
                rw [cast_sub_three_eq_neg_three (m := m) hm3le]
              _ = (((m - 3 - t : ℕ) : ZMod m)) := by rw [Nat.cast_sub htle]
          have hy : (-3 : ZMod m) - t ≠ 0 := by
            rw [hycast]
            exact natCast_ne_zero_of_pos_lt (m := m) (n := m - 3 - t) (by omega) (by omega)
          apply not_mem_range_linePoint_of_snd_ne_zero
          rw [hiter]
          exact hy

theorem firstReturn_four_m6 :
    (R2xy (m := 6)^[rho2 (m := 6) (4 : ZMod 6)]) (linePoint (m := 6) (4 : ZMod 6)) =
      linePoint (m := 6) (T2 (m := 6) (4 : ZMod 6)) := by
  native_decide

theorem hfirst_four_m6 :
    ∀ n, 0 < n → n < rho2 (m := 6) (4 : ZMod 6) →
      (R2xy (m := 6)^[n]) (linePoint (m := 6) (4 : ZMod 6)) ∉ Set.range (linePoint (m := 6))
  | n, hn0, hnlt => by
      have hn : n < 6 := by simpa [rho2] using hnlt
      interval_cases n <;> native_decide

theorem R2xy_linePoint_four [Fact (5 < m)] :
    R2xy (m := m) (linePoint (m := m) (4 : ZMod m)) = ((5 : ZMod m), (-1 : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm1 : 1 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (1 < m) := ⟨hm1⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  have hA : linePoint (m := m) (4 : ZMod m) ≠ ((2 : ZMod m), (2 : ZMod m)) := by
    intro h
    exact two_ne_zero (m := m) (by simpa [linePoint] using (congrArg Prod.snd h).symm)
  have hy1 : (0 : ZMod m) ≠ (1 : ZMod m) := (one_ne_zero (m := m)).symm
  have hyneg1 : (0 : ZMod m) ≠ (-1 : ZMod m) := by
    intro h
    exact neg_ne_zero.mpr (one_ne_zero (m := m)) h.symm
  have hdiag : (0 : ZMod m) ≠ (4 : ZMod m) := by
    intro h
    exact four_ne_zero (m := m) h.symm
  have hxneg1 : (4 : ZMod m) ≠ (-1 : ZMod m) :=
    natCast_ne_neg_one_of_lt (m := m) (n := 4) (by omega)
  have h00 : linePoint (m := m) (4 : ZMod m) ≠ ((0 : ZMod m), (0 : ZMod m)) := by
    intro h
    exact four_ne_zero (m := m) (by simpa [linePoint] using congrArg Prod.fst h)
  calc
    R2xy (m := m) (linePoint (m := m) (4 : ZMod m))
        = G (m := m) (linePoint (m := m) (4 : ZMod m)) := by
            simpa [linePoint] using R2xy_eq_G_of (m := m) hA hy1 hyneg1 hdiag hxneg1 h00
    _ = ((5 : ZMod m), (-1 : ZMod m)) := by
          ext <;> simp [linePoint, G] <;> ring

theorem R2xy_five_neg_one [Fact (7 < m)] :
    R2xy (m := m) ((5 : ZMod m), (-1 : ZMod m)) = ((5 : ZMod m), (-2 : ZMod m)) := by
  have hm7 : 7 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  simpa using R2xy_eq_C_of (m := m) (x := 5) (five_ne_neg_one (m := m))

theorem iterate_two_from_linePoint_four [Fact (Even m)] [Fact (7 < m)] :
    (R2xy (m := m)^[2]) (linePoint (m := m) (4 : ZMod m)) =
      ((5 : ZMod m), (-2 : ZMod m)) := by
  have hm7 : 7 < m := Fact.out
  have hm5 : 5 < m := by omega
  letI : Fact (5 < m) := ⟨hm5⟩
  calc
    (R2xy (m := m)^[2]) (linePoint (m := m) (4 : ZMod m))
        = R2xy (m := m) (R2xy (m := m) (linePoint (m := m) (4 : ZMod m))) := by simp
    _ = R2xy (m := m) ((5 : ZMod m), (-1 : ZMod m)) := by rw [R2xy_linePoint_four (m := m)]
    _ = ((5 : ZMod m), (-2 : ZMod m)) := R2xy_five_neg_one (m := m)

theorem iterate_R2xy_from_five_neg_two [Fact (Even m)] [Fact (7 < m)] :
    ∀ n, n ≤ m - 6 →
      (R2xy (m := m)^[n]) ((5 : ZMod m), (-2 : ZMod m)) =
        ((5 : ZMod m) + n, (-2 : ZMod m) - n)
  | 0, _ => by simp
  | n + 1, hn => by
      have hmEven : Even m := Fact.out
      have hm7 : 7 < m := Fact.out
      have hm0 : 0 < m := by omega
      have hm1 : 1 < m := by omega
      have hm2 : 2 < m := by omega
      letI : Fact (0 < m) := ⟨hm0⟩
      letI : Fact (1 < m) := ⟨hm1⟩
      letI : Fact (2 < m) := ⟨hm2⟩
      have hn' : n < m - 6 := Nat.lt_of_succ_le hn
      have hx_lt : 5 + n < m := by omega
      have hy_lt : m - 2 - n < m := by omega
      have xcast : ((5 : ZMod m) + n) = (((5 + n : ℕ) : ZMod m)) := by
        simpa using (Nat.cast_add 5 n).symm
      have ycast : ((-2 : ZMod m) - n) = (((m - 2 - n : ℕ) : ZMod m)) := by
        have hm2le : 2 ≤ m := by omega
        have hnle : n ≤ m - 2 := by omega
        calc
          (-2 : ZMod m) - n = (((m - 2 : ℕ) : ZMod m)) - n := by
            rw [cast_sub_two_eq_neg_two (m := m) hm2le]
          _ = (((m - 2 - n : ℕ) : ZMod m)) := by rw [Nat.cast_sub hnle]
      have hA : ((5 : ZMod m) + n, (-2 : ZMod m) - n) ≠ ((2 : ZMod m), (2 : ZMod m)) := by
        intro hEq
        have hfst : (((5 + n : ℕ) : ZMod m)) = ((2 : ℕ) : ZMod m) := by
          calc
            (((5 + n : ℕ) : ZMod m)) = ((5 : ZMod m) + n) := by rw [xcast]
            _ = (2 : ZMod m) := congrArg Prod.fst hEq
            _ = ((2 : ℕ) : ZMod m) := by norm_num
        exact natCast_ne_two_of_three_le_lt (m := m) (n := 5 + n) (by omega) hx_lt hfst
      have hy1 : (-2 : ZMod m) - n ≠ (1 : ZMod m) := by
        rw [ycast]
        exact natCast_ne_one_of_two_le_lt (m := m) (n := m - 2 - n) (by omega) hy_lt
      have hyneg1 : (-2 : ZMod m) - n ≠ (-1 : ZMod m) := by
        rw [ycast]
        exact natCast_ne_neg_one_of_lt (m := m) (n := m - 2 - n) (by omega)
      have hdiag : (-2 : ZMod m) - n ≠ (5 : ZMod m) + n := by
        intro hEq
        have hnatEq : m - 2 - n = 5 + n := by
          have hcast : (((m - 2 - n : ℕ) : ZMod m)) = (((5 + n : ℕ) : ZMod m)) := by
            rw [ycast, xcast] at hEq
            exact hEq
          exact (natCast_eq_natCast_iff_of_lt (m := m) (a := m - 2 - n) (b := 5 + n)
            hy_lt hx_lt).1 hcast
        rcases hmEven with ⟨k, hk⟩
        omega
      have hxneg1 : (5 : ZMod m) + n ≠ (-1 : ZMod m) := by
        rw [xcast]
        exact natCast_ne_neg_one_of_lt (m := m) (n := 5 + n) (by omega)
      have h00 : ((5 : ZMod m) + n, (-2 : ZMod m) - n) ≠ ((0 : ZMod m), (0 : ZMod m)) := by
        intro hEq
        have hfst : (((5 + n : ℕ) : ZMod m)) = 0 := by
          calc
            (((5 + n : ℕ) : ZMod m)) = ((5 : ZMod m) + n) := by rw [xcast]
            _ = 0 := congrArg Prod.fst hEq
        exact natCast_ne_zero_of_pos_lt (m := m) (n := 5 + n) (by omega) hx_lt hfst
      rw [Function.iterate_succ_apply',
        iterate_R2xy_from_five_neg_two (m := m) n (Nat.le_of_succ_le hn)]
      rw [R2xy_eq_G_of (m := m) hA hy1 hyneg1 hdiag hxneg1 h00]
      ext <;> simp [G, Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] <;> ring

theorem iterate_R2xy_from_linePoint_four_after_two [Fact (Even m)] [Fact (7 < m)] :
    ∀ n, n ≤ m - 6 →
      (R2xy (m := m)^[n + 2]) (linePoint (m := m) (4 : ZMod m)) =
        ((5 : ZMod m) + n, (-2 : ZMod m) - n)
  | n, hn => by
      rw [Function.iterate_add_apply]
      simpa [iterate_two_from_linePoint_four (m := m)] using
        iterate_R2xy_from_five_neg_two (m := m) n hn

theorem iterate_to_m_sub_one_four_from_five_neg_two [Fact (Even m)] [Fact (7 < m)] :
    (R2xy (m := m)^[m - 6]) ((5 : ZMod m), (-2 : ZMod m)) =
      ((((m - 1 : ℕ) : ZMod m)), (4 : ZMod m)) := by
  have hm7 : 7 < m := Fact.out
  rw [iterate_R2xy_from_five_neg_two (m := m) (m - 6) le_rfl]
  ext
  · change ((((5 : ℕ) : ZMod m)) + (((m - 6 : ℕ) : ZMod m))) = (((m - 1 : ℕ) : ZMod m))
    calc
      ((((5 : ℕ) : ZMod m)) + (((m - 6 : ℕ) : ZMod m))) = (((5 + (m - 6) : ℕ) : ZMod m)) := by
        rw [Nat.cast_add]
      _ = (((m - 1 : ℕ) : ZMod m)) := by congr; omega
  · have hm2le : 2 ≤ m := by omega
    have hnle : m - 6 ≤ m - 2 := by omega
    have hnat : m - 2 - (m - 6) = 4 := by omega
    change (-2 : ZMod m) - (((m - 6 : ℕ) : ZMod m)) = (4 : ZMod m)
    calc
      (-2 : ZMod m) - (((m - 6 : ℕ) : ZMod m))
          = (((m - 2 : ℕ) : ZMod m)) - (((m - 6 : ℕ) : ZMod m)) := by
              rw [cast_sub_two_eq_neg_two (m := m) hm2le]
      _ = (((m - 2 - (m - 6) : ℕ) : ZMod m)) := by rw [Nat.cast_sub hnle]
      _ = (((4 : ℕ) : ZMod m)) := by rw [hnat]
      _ = (4 : ZMod m) := by norm_num

theorem R2xy_m_sub_one_four [Fact (7 < m)] :
    R2xy (m := m) ((((m - 1 : ℕ) : ZMod m)), (4 : ZMod m)) = ((0 : ZMod m), (4 : ZMod m)) := by
  have hm7 : 7 < m := Fact.out
  have hm1le : 1 ≤ m := by omega
  have hneg1 : (((m - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) := cast_sub_one_eq_neg_one (m := m) hm1le
  letI : Fact (5 < m) := ⟨by omega⟩
  calc
    R2xy (m := m) ((((m - 1 : ℕ) : ZMod m)), (4 : ZMod m))
        = R2xy (m := m) ((-1 : ZMod m), (4 : ZMod m)) := by rw [hneg1]
    _ = ((0 : ZMod m), (4 : ZMod m)) := by
          simpa using R2xy_eq_E_of (m := m) (y := (4 : ZMod m))
            (four_ne_zero (m := m)) (four_ne_neg_two (m := m))

theorem R2xy_zero_four [Fact (5 < m)] :
    R2xy (m := m) ((0 : ZMod m), (4 : ZMod m)) = ((1 : ZMod m), (3 : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm1 : 1 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (1 < m) := ⟨hm1⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  have hA : ((0 : ZMod m), (4 : ZMod m)) ≠ ((2 : ZMod m), (2 : ZMod m)) := by
    intro h
    exact two_ne_zero (m := m) (congrArg Prod.fst h).symm
  have hy1 : (4 : ZMod m) ≠ (1 : ZMod m) := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := 4) (by omega) (by omega)
  have hyneg1 : (4 : ZMod m) ≠ (-1 : ZMod m) :=
    natCast_ne_neg_one_of_lt (m := m) (n := 4) (by omega)
  have hdiag : (4 : ZMod m) ≠ (0 : ZMod m) := by
    intro h
    exact four_ne_zero (m := m) h
  have hxneg1 : (0 : ZMod m) ≠ (-1 : ZMod m) := by
    intro h
    exact neg_ne_zero.mpr (one_ne_zero (m := m)) h.symm
  have h00 : ((0 : ZMod m), (4 : ZMod m)) ≠ ((0 : ZMod m), (0 : ZMod m)) := by
    intro h
    exact four_ne_zero (m := m) (congrArg Prod.snd h)
  calc
    R2xy (m := m) ((0 : ZMod m), (4 : ZMod m))
        = G (m := m) ((0 : ZMod m), (4 : ZMod m)) := by
            exact R2xy_eq_G_of (m := m) hA hy1 hyneg1 hdiag hxneg1 h00
    _ = ((1 : ZMod m), (3 : ZMod m)) := by
          ext <;> simp [G] <;> ring

theorem R2xy_one_three [Fact (5 < m)] :
    R2xy (m := m) ((1 : ZMod m), (3 : ZMod m)) = ((2 : ZMod m), (2 : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm1 : 1 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (1 < m) := ⟨hm1⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  have hA : ((1 : ZMod m), (3 : ZMod m)) ≠ ((2 : ZMod m), (2 : ZMod m)) := by
    intro h
    exact two_ne_one (m := m) (congrArg Prod.fst h).symm
  have hy1 : (3 : ZMod m) ≠ (1 : ZMod m) := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := 3) (by omega) (by omega)
  have hyneg1 : (3 : ZMod m) ≠ (-1 : ZMod m) :=
    natCast_ne_neg_one_of_lt (m := m) (n := 3) (by omega)
  have hdiag : (3 : ZMod m) ≠ (1 : ZMod m) := hy1
  have hxneg1 : (1 : ZMod m) ≠ (-1 : ZMod m) := one_ne_neg_one (m := m)
  have h00 : ((1 : ZMod m), (3 : ZMod m)) ≠ ((0 : ZMod m), (0 : ZMod m)) := by
    intro h
    exact one_ne_zero (m := m) (congrArg Prod.fst h)
  calc
    R2xy (m := m) ((1 : ZMod m), (3 : ZMod m))
        = G (m := m) ((1 : ZMod m), (3 : ZMod m)) := by
            exact R2xy_eq_G_of (m := m) hA hy1 hyneg1 hdiag hxneg1 h00
    _ = ((2 : ZMod m), (2 : ZMod m)) := by
          ext <;> simp [G] <;> ring

theorem iterate_two_from_zero_four [Fact (5 < m)] :
    (R2xy (m := m)^[2]) ((0 : ZMod m), (4 : ZMod m)) = ((2 : ZMod m), (2 : ZMod m)) := by
  calc
    (R2xy (m := m)^[2]) ((0 : ZMod m), (4 : ZMod m))
        = R2xy (m := m) (R2xy (m := m) ((0 : ZMod m), (4 : ZMod m))) := by simp
    _ = R2xy (m := m) ((1 : ZMod m), (3 : ZMod m)) := by rw [R2xy_zero_four (m := m)]
    _ = ((2 : ZMod m), (2 : ZMod m)) := R2xy_one_three (m := m)

theorem firstReturn_four_of_ge_eight [Fact (Even m)] [Fact (7 < m)] :
    (R2xy (m := m)^[rho2 (m := m) (4 : ZMod m)]) (linePoint (m := m) (4 : ZMod m)) =
      linePoint (m := m) (T2 (m := m) (4 : ZMod m)) := by
  have hm7 : 7 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm1 : 1 < m := by omega
  have hm2 : 2 < m := by omega
  have hm5 : 5 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (1 < m) := ⟨hm1⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  letI : Fact (5 < m) := ⟨hm5⟩
  have hx0 : (4 : ZMod m) ≠ 0 := four_ne_zero (m := m)
  have hx1 : (4 : ZMod m) ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := 4) (by omega) (by omega)
  have hx2 : (4 : ZMod m) ≠ 2 := by
    exact natCast_ne_two_of_three_le_lt (m := m) (n := 4) (by omega) (by omega)
  have hrho : rho2 (m := m) (4 : ZMod m) = m := by
    simp [rho2, hx0, hx1, hx2]
  have hT : T2 (m := m) (4 : ZMod m) = (3 : ZMod m) := by
    simp [T2, hx0, hx1, hx2]
    norm_num
  have hstepMSubOneFour :
      (R2xy (m := m)^[m - 4]) (linePoint (m := m) (4 : ZMod m)) =
        ((((m - 1 : ℕ) : ZMod m)), (4 : ZMod m)) := by
    rw [show m - 4 = (m - 6) + 2 by omega, Function.iterate_add_apply]
    rw [iterate_two_from_linePoint_four (m := m)]
    exact iterate_to_m_sub_one_four_from_five_neg_two (m := m)
  have hstepZeroFour :
      (R2xy (m := m)^[m - 3]) (linePoint (m := m) (4 : ZMod m)) =
        ((0 : ZMod m), (4 : ZMod m)) := by
    rw [show m - 3 = 1 + (m - 4) by omega, Function.iterate_add_apply]
    simp [Function.iterate_one]
    rw [hstepMSubOneFour]
    exact R2xy_m_sub_one_four (m := m)
  have hstepTwoTwo :
      (R2xy (m := m)^[m - 1]) (linePoint (m := m) (4 : ZMod m)) =
        ((2 : ZMod m), (2 : ZMod m)) := by
    rw [show m - 1 = 2 + (m - 3) by omega, Function.iterate_add_apply]
    simpa [hstepZeroFour] using iterate_two_from_zero_four (m := m)
  have hstepFinal :
      (R2xy (m := m)^[m]) (linePoint (m := m) (4 : ZMod m)) =
        linePoint (m := m) (3 : ZMod m) := by
    calc
      (R2xy (m := m)^[m]) (linePoint (m := m) (4 : ZMod m))
          = R2xy (m := m) ((R2xy (m := m)^[m - 1]) (linePoint (m := m) (4 : ZMod m))) := by
              rw [show m = 1 + (m - 1) by omega, Function.iterate_add_apply]
              simp
      _ = R2xy (m := m) ((2 : ZMod m), (2 : ZMod m)) := by rw [hstepTwoTwo]
      _ = linePoint (m := m) (3 : ZMod m) := by simpa [linePoint] using R2xy_eq_A (m := m)
  calc
    (R2xy (m := m)^[rho2 (m := m) (4 : ZMod m)]) (linePoint (m := m) (4 : ZMod m))
        = (R2xy (m := m)^[m]) (linePoint (m := m) (4 : ZMod m)) := by rw [hrho]
    _ = linePoint (m := m) (3 : ZMod m) := hstepFinal
    _ = linePoint (m := m) (T2 (m := m) (4 : ZMod m)) := by rw [hT]

theorem hfirst_four_of_ge_eight [Fact (Even m)] [Fact (7 < m)] :
    ∀ n, 0 < n → n < rho2 (m := m) (4 : ZMod m) →
      (R2xy (m := m)^[n]) (linePoint (m := m) (4 : ZMod m)) ∉ Set.range (linePoint (m := m))
  | n, hn0, hnlt => by
      have hm7 : 7 < m := Fact.out
      have hm0 : 0 < m := by omega
      have hm1 : 1 < m := by omega
      have hm2 : 2 < m := by omega
      have hm5 : 5 < m := by omega
      letI : Fact (0 < m) := ⟨hm0⟩
      letI : Fact (1 < m) := ⟨hm1⟩
      letI : Fact (2 < m) := ⟨hm2⟩
      letI : Fact (5 < m) := ⟨hm5⟩
      have hx0 : (4 : ZMod m) ≠ 0 := four_ne_zero (m := m)
      have hx1 : (4 : ZMod m) ≠ 1 := by
        exact natCast_ne_one_of_two_le_lt (m := m) (n := 4) (by omega) (by omega)
      have hx2 : (4 : ZMod m) ≠ 2 := by
        exact natCast_ne_two_of_three_le_lt (m := m) (n := 4) (by omega) (by omega)
      have hrho : rho2 (m := m) (4 : ZMod m) = m := by
        simp [rho2, hx0, hx1, hx2]
      have hnm : n < m := by rwa [hrho] at hnlt
      by_cases h1 : n = 1
      · apply not_mem_range_linePoint_of_snd_ne_zero
        rw [h1]
        simpa [Function.iterate_one, R2xy_linePoint_four (m := m)] using
          (neg_ne_zero.mpr (one_ne_zero (m := m)))
      · by_cases hfront : n ≤ m - 4
        · let t : ℕ := n - 2
          have ht : t ≤ m - 6 := by
            dsimp [t]
            omega
          have hnEq : n = t + 2 := by
            dsimp [t]
            omega
          have hiter :
              (R2xy (m := m)^[n]) (linePoint (m := m) (4 : ZMod m)) =
                ((5 : ZMod m) + t, (-2 : ZMod m) - t) := by
            rw [hnEq]
            simpa using iterate_R2xy_from_linePoint_four_after_two (m := m) t ht
          apply not_mem_range_linePoint_of_snd_ne_zero
          rw [hiter]
          exact neg_two_sub_nat_ne_zero (m := m) (n := t) (by omega)
        · have hstepZeroFour :
            (R2xy (m := m)^[m - 3]) (linePoint (m := m) (4 : ZMod m)) =
              ((0 : ZMod m), (4 : ZMod m)) := by
            have hstepMSubOneFour :
                (R2xy (m := m)^[m - 4]) (linePoint (m := m) (4 : ZMod m)) =
                  ((((m - 1 : ℕ) : ZMod m)), (4 : ZMod m)) := by
              rw [show m - 4 = (m - 6) + 2 by omega, Function.iterate_add_apply]
              rw [iterate_two_from_linePoint_four (m := m)]
              exact iterate_to_m_sub_one_four_from_five_neg_two (m := m)
            rw [show m - 3 = 1 + (m - 4) by omega, Function.iterate_add_apply]
            simp [Function.iterate_one]
            rw [hstepMSubOneFour]
            exact R2xy_m_sub_one_four (m := m)
          by_cases hm3case : n = m - 3
          · apply not_mem_range_linePoint_of_snd_ne_zero
            rw [hm3case, hstepZeroFour]
            exact four_ne_zero (m := m)
          · by_cases hm2case : n = m - 2
            · apply not_mem_range_linePoint_of_snd_ne_zero
              rw [hm2case]
              have hstepOneThree :
                  (R2xy (m := m)^[m - 2]) (linePoint (m := m) (4 : ZMod m)) =
                    ((1 : ZMod m), (3 : ZMod m)) := by
                calc
                  (R2xy (m := m)^[m - 2]) (linePoint (m := m) (4 : ZMod m))
                      = R2xy (m := m) ((R2xy (m := m)^[m - 3]) (linePoint (m := m) (4 : ZMod m))) := by
                          rw [show m - 2 = 1 + (m - 3) by omega, Function.iterate_add_apply]
                          simp
                  _ = R2xy (m := m) ((0 : ZMod m), (4 : ZMod m)) := by rw [hstepZeroFour]
                  _ = ((1 : ZMod m), (3 : ZMod m)) := R2xy_zero_four (m := m)
              rw [hstepOneThree]
              exact three_ne_zero (m := m)
            · have hm1case : n = m - 1 := by omega
              apply not_mem_range_linePoint_of_snd_ne_zero
              rw [hm1case]
              have hstepTwoTwo :
                  (R2xy (m := m)^[m - 1]) (linePoint (m := m) (4 : ZMod m)) =
                    ((2 : ZMod m), (2 : ZMod m)) := by
                rw [show m - 1 = 2 + (m - 3) by omega, Function.iterate_add_apply]
                simpa [hstepZeroFour] using iterate_two_from_zero_four (m := m)
              rw [hstepTwoTwo]
              exact two_ne_zero (m := m)

theorem firstReturn_four [Fact (Even m)] [Fact (5 < m)] :
    (R2xy (m := m)^[rho2 (m := m) (4 : ZMod m)]) (linePoint (m := m) (4 : ZMod m)) =
      linePoint (m := m) (T2 (m := m) (4 : ZMod m)) := by
  by_cases hm6 : m = 6
  · subst hm6
    exact firstReturn_four_m6
  · have hmEven : Even m := by
      have hinst : Fact (Even m) := inferInstance
      exact hinst.out
    have hm5 : 5 < m := by
      have hinst : Fact (5 < m) := inferInstance
      exact hinst.out
    have hm8 : 7 < m := by
      rcases hmEven with ⟨k, hk⟩
      omega
    letI : Fact (7 < m) := ⟨hm8⟩
    exact firstReturn_four_of_ge_eight (m := m)

theorem hfirst_four [Fact (Even m)] [Fact (5 < m)] :
    ∀ n, 0 < n → n < rho2 (m := m) (4 : ZMod m) →
      (R2xy (m := m)^[n]) (linePoint (m := m) (4 : ZMod m)) ∉ Set.range (linePoint (m := m))
  | n, hn0, hnlt => by
      by_cases hm6 : m = 6
      · subst hm6
        exact hfirst_four_m6 n hn0 (by simpa using hnlt)
      · have hmEven : Even m := by
          have hinst : Fact (Even m) := inferInstance
          exact hinst.out
        have hm5 : 5 < m := by
          have hinst : Fact (5 < m) := inferInstance
          exact hinst.out
        have hm8 : 7 < m := by
          rcases hmEven with ⟨k, hk⟩
          omega
        letI : Fact (7 < m) := ⟨hm8⟩
        exact hfirst_four_of_ge_eight (m := m) n hn0 hnlt

theorem firstReturn_six_m8 :
    (R2xy (m := 8)^[rho2 (m := 8) (6 : ZMod 8)]) (linePoint (m := 8) (6 : ZMod 8)) =
      linePoint (m := 8) (T2 (m := 8) (6 : ZMod 8)) := by
  native_decide

theorem hfirst_six_m8 :
    ∀ n, 0 < n → n < rho2 (m := 8) (6 : ZMod 8) →
      (R2xy (m := 8)^[n]) (linePoint (m := 8) (6 : ZMod 8)) ∉ Set.range (linePoint (m := 8))
  | n, hn0, hnlt => by
      have hn : n < 8 := by simpa [rho2] using hnlt
      interval_cases n <;> native_decide

theorem R2xy_linePoint_six [Fact (7 < m)] :
    R2xy (m := m) (linePoint (m := m) (6 : ZMod m)) = ((7 : ZMod m), (-1 : ZMod m)) := by
  have hm7 : 7 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm1 : 1 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (1 < m) := ⟨hm1⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  have hA : linePoint (m := m) (6 : ZMod m) ≠ ((2 : ZMod m), (2 : ZMod m)) := by
    intro h
    exact two_ne_zero (m := m) (by simpa [linePoint] using (congrArg Prod.snd h).symm)
  have hy1 : (0 : ZMod m) ≠ (1 : ZMod m) := (one_ne_zero (m := m)).symm
  have hyneg1 : (0 : ZMod m) ≠ (-1 : ZMod m) := by
    intro h
    exact neg_ne_zero.mpr (one_ne_zero (m := m)) h.symm
  have hdiag : (0 : ZMod m) ≠ (6 : ZMod m) := by
    intro h
    exact six_ne_zero (m := m) h.symm
  have hxneg1 : (6 : ZMod m) ≠ (-1 : ZMod m) :=
    natCast_ne_neg_one_of_lt (m := m) (n := 6) (by omega)
  have h00 : linePoint (m := m) (6 : ZMod m) ≠ ((0 : ZMod m), (0 : ZMod m)) := by
    intro h
    exact six_ne_zero (m := m) (by simpa [linePoint] using congrArg Prod.fst h)
  calc
    R2xy (m := m) (linePoint (m := m) (6 : ZMod m))
        = G (m := m) (linePoint (m := m) (6 : ZMod m)) := by
            simpa [linePoint] using R2xy_eq_G_of (m := m) hA hy1 hyneg1 hdiag hxneg1 h00
    _ = ((7 : ZMod m), (-1 : ZMod m)) := by
          ext <;> simp [linePoint, G] <;> ring

theorem R2xy_seven_neg_one [Fact (9 < m)] :
    R2xy (m := m) ((7 : ZMod m), (-1 : ZMod m)) = ((7 : ZMod m), (-2 : ZMod m)) := by
  have hm9 : 9 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  simpa using R2xy_eq_C_of (m := m) (x := 7) (seven_ne_neg_one (m := m))

theorem iterate_two_from_linePoint_six [Fact (9 < m)] :
    (R2xy (m := m)^[2]) (linePoint (m := m) (6 : ZMod m)) =
      ((7 : ZMod m), (-2 : ZMod m)) := by
  have hm9 : 9 < m := Fact.out
  have hm7 : 7 < m := by omega
  letI : Fact (7 < m) := ⟨hm7⟩
  calc
    (R2xy (m := m)^[2]) (linePoint (m := m) (6 : ZMod m))
        = R2xy (m := m) (R2xy (m := m) (linePoint (m := m) (6 : ZMod m))) := by simp
    _ = R2xy (m := m) ((7 : ZMod m), (-1 : ZMod m)) := by rw [R2xy_linePoint_six (m := m)]
    _ = ((7 : ZMod m), (-2 : ZMod m)) := R2xy_seven_neg_one (m := m)

theorem iterate_R2xy_from_seven_neg_two [Fact (Even m)] [Fact (9 < m)] :
    ∀ n, n ≤ m - 8 →
      (R2xy (m := m)^[n]) ((7 : ZMod m), (-2 : ZMod m)) =
        ((7 : ZMod m) + n, (-2 : ZMod m) - n)
  | 0, _ => by simp
  | n + 1, hn => by
      have hmEven : Even m := Fact.out
      have hm9 : 9 < m := Fact.out
      have hm0 : 0 < m := by omega
      have hm1 : 1 < m := by omega
      have hm2 : 2 < m := by omega
      letI : Fact (0 < m) := ⟨hm0⟩
      letI : Fact (1 < m) := ⟨hm1⟩
      letI : Fact (2 < m) := ⟨hm2⟩
      have hn' : n < m - 8 := Nat.lt_of_succ_le hn
      have hx_lt : 7 + n < m := by omega
      have hy_lt : m - 2 - n < m := by omega
      have xcast : ((7 : ZMod m) + n) = (((7 + n : ℕ) : ZMod m)) := by
        simpa using (Nat.cast_add 7 n).symm
      have ycast : ((-2 : ZMod m) - n) = (((m - 2 - n : ℕ) : ZMod m)) := by
        have hm2le : 2 ≤ m := by omega
        have hnle : n ≤ m - 2 := by omega
        calc
          (-2 : ZMod m) - n = (((m - 2 : ℕ) : ZMod m)) - n := by
            rw [cast_sub_two_eq_neg_two (m := m) hm2le]
          _ = (((m - 2 - n : ℕ) : ZMod m)) := by rw [Nat.cast_sub hnle]
      have hA : ((7 : ZMod m) + n, (-2 : ZMod m) - n) ≠ ((2 : ZMod m), (2 : ZMod m)) := by
        intro hEq
        have hfst : (((7 + n : ℕ) : ZMod m)) = ((2 : ℕ) : ZMod m) := by
          calc
            (((7 + n : ℕ) : ZMod m)) = ((7 : ZMod m) + n) := by rw [xcast]
            _ = (2 : ZMod m) := congrArg Prod.fst hEq
            _ = ((2 : ℕ) : ZMod m) := by norm_num
        exact natCast_ne_two_of_three_le_lt (m := m) (n := 7 + n) (by omega) hx_lt hfst
      have hy1 : (-2 : ZMod m) - n ≠ (1 : ZMod m) := by
        rw [ycast]
        exact natCast_ne_one_of_two_le_lt (m := m) (n := m - 2 - n) (by omega) hy_lt
      have hyneg1 : (-2 : ZMod m) - n ≠ (-1 : ZMod m) := by
        rw [ycast]
        exact natCast_ne_neg_one_of_lt (m := m) (n := m - 2 - n) (by omega)
      have hdiag : (-2 : ZMod m) - n ≠ (7 : ZMod m) + n := by
        intro hEq
        have hnatEq : m - 2 - n = 7 + n := by
          have hcast : (((m - 2 - n : ℕ) : ZMod m)) = (((7 + n : ℕ) : ZMod m)) := by
            rw [ycast, xcast] at hEq
            exact hEq
          exact (natCast_eq_natCast_iff_of_lt (m := m) (a := m - 2 - n) (b := 7 + n)
            hy_lt hx_lt).1 hcast
        rcases hmEven with ⟨k, hk⟩
        omega
      have hxneg1 : (7 : ZMod m) + n ≠ (-1 : ZMod m) := by
        rw [xcast]
        exact natCast_ne_neg_one_of_lt (m := m) (n := 7 + n) (by omega)
      have h00 : ((7 : ZMod m) + n, (-2 : ZMod m) - n) ≠ ((0 : ZMod m), (0 : ZMod m)) := by
        intro hEq
        have hfst : (((7 + n : ℕ) : ZMod m)) = 0 := by
          calc
            (((7 + n : ℕ) : ZMod m)) = ((7 : ZMod m) + n) := by rw [xcast]
            _ = 0 := congrArg Prod.fst hEq
        exact natCast_ne_zero_of_pos_lt (m := m) (n := 7 + n) (by omega) hx_lt hfst
      rw [Function.iterate_succ_apply',
        iterate_R2xy_from_seven_neg_two (m := m) n (Nat.le_of_succ_le hn)]
      rw [R2xy_eq_G_of (m := m) hA hy1 hyneg1 hdiag hxneg1 h00]
      ext <;> simp [G, Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] <;> ring

theorem iterate_R2xy_from_linePoint_six_after_two [Fact (Even m)] [Fact (9 < m)] :
    ∀ n, n ≤ m - 8 →
      (R2xy (m := m)^[n + 2]) (linePoint (m := m) (6 : ZMod m)) =
        ((7 : ZMod m) + n, (-2 : ZMod m) - n)
  | n, hn => by
      rw [Function.iterate_add_apply]
      simpa [iterate_two_from_linePoint_six (m := m)] using
        iterate_R2xy_from_seven_neg_two (m := m) n hn

theorem iterate_to_m_sub_one_six_from_seven_neg_two [Fact (Even m)] [Fact (9 < m)] :
    (R2xy (m := m)^[m - 8]) ((7 : ZMod m), (-2 : ZMod m)) =
      ((((m - 1 : ℕ) : ZMod m)), (6 : ZMod m)) := by
  have hm9 : 9 < m := Fact.out
  rw [iterate_R2xy_from_seven_neg_two (m := m) (m - 8) le_rfl]
  ext
  · change ((((7 : ℕ) : ZMod m)) + (((m - 8 : ℕ) : ZMod m))) = (((m - 1 : ℕ) : ZMod m))
    calc
      ((((7 : ℕ) : ZMod m)) + (((m - 8 : ℕ) : ZMod m))) = (((7 + (m - 8) : ℕ) : ZMod m)) := by
        rw [Nat.cast_add]
      _ = (((m - 1 : ℕ) : ZMod m)) := by congr; omega
  · have hm2le : 2 ≤ m := by omega
    have hnle : m - 8 ≤ m - 2 := by omega
    have hnat : m - 2 - (m - 8) = 6 := by omega
    change (-2 : ZMod m) - (((m - 8 : ℕ) : ZMod m)) = (6 : ZMod m)
    calc
      (-2 : ZMod m) - (((m - 8 : ℕ) : ZMod m))
          = (((m - 2 : ℕ) : ZMod m)) - (((m - 8 : ℕ) : ZMod m)) := by
              rw [cast_sub_two_eq_neg_two (m := m) hm2le]
      _ = (((m - 2 - (m - 8) : ℕ) : ZMod m)) := by rw [Nat.cast_sub hnle]
      _ = (((6 : ℕ) : ZMod m)) := by rw [hnat]
      _ = (6 : ZMod m) := by norm_num

theorem R2xy_m_sub_one_six [Fact (9 < m)] :
    R2xy (m := m) ((((m - 1 : ℕ) : ZMod m)), (6 : ZMod m)) = ((0 : ZMod m), (6 : ZMod m)) := by
  have hm9 : 9 < m := Fact.out
  have hm1le : 1 ≤ m := by omega
  have hneg1 : (((m - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) := cast_sub_one_eq_neg_one (m := m) hm1le
  letI : Fact (5 < m) := ⟨by omega⟩
  letI : Fact (7 < m) := ⟨by omega⟩
  calc
    R2xy (m := m) ((((m - 1 : ℕ) : ZMod m)), (6 : ZMod m))
        = R2xy (m := m) ((-1 : ZMod m), (6 : ZMod m)) := by rw [hneg1]
    _ = ((0 : ZMod m), (6 : ZMod m)) := by
          simpa using R2xy_eq_E_of (m := m) (y := (6 : ZMod m))
            (six_ne_zero (m := m)) (six_ne_neg_two (m := m))

theorem R2xy_zero_six [Fact (7 < m)] :
    R2xy (m := m) ((0 : ZMod m), (6 : ZMod m)) = ((1 : ZMod m), (5 : ZMod m)) := by
  have hm7 : 7 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm1 : 1 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (1 < m) := ⟨hm1⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  have hA : ((0 : ZMod m), (6 : ZMod m)) ≠ ((2 : ZMod m), (2 : ZMod m)) := by
    intro h
    have hsnd : (6 : ZMod m) = (2 : ZMod m) := congrArg Prod.snd h
    exact natCast_ne_two_of_three_le_lt (m := m) (n := 6) (by omega) (by omega) hsnd
  have hy1 : (6 : ZMod m) ≠ (1 : ZMod m) := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := 6) (by omega) (by omega)
  have hyneg1 : (6 : ZMod m) ≠ (-1 : ZMod m) :=
    natCast_ne_neg_one_of_lt (m := m) (n := 6) (by omega)
  have hdiag : (6 : ZMod m) ≠ (0 : ZMod m) := by
    intro h
    exact six_ne_zero (m := m) h
  have hxneg1 : (0 : ZMod m) ≠ (-1 : ZMod m) := by
    intro h
    exact neg_ne_zero.mpr (one_ne_zero (m := m)) h.symm
  have h00 : ((0 : ZMod m), (6 : ZMod m)) ≠ ((0 : ZMod m), (0 : ZMod m)) := by
    intro h
    exact six_ne_zero (m := m) (congrArg Prod.snd h)
  calc
    R2xy (m := m) ((0 : ZMod m), (6 : ZMod m))
        = G (m := m) ((0 : ZMod m), (6 : ZMod m)) := by
            exact R2xy_eq_G_of (m := m) hA hy1 hyneg1 hdiag hxneg1 h00
    _ = ((1 : ZMod m), (5 : ZMod m)) := by
          ext <;> simp [G] <;> ring

theorem R2xy_one_five [Fact (7 < m)] :
    R2xy (m := m) ((1 : ZMod m), (5 : ZMod m)) = ((2 : ZMod m), (4 : ZMod m)) := by
  have hm7 : 7 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm1 : 1 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (1 < m) := ⟨hm1⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  have hA : ((1 : ZMod m), (5 : ZMod m)) ≠ ((2 : ZMod m), (2 : ZMod m)) := by
    intro h
    exact two_ne_one (m := m) (congrArg Prod.fst h).symm
  have hy1 : (5 : ZMod m) ≠ (1 : ZMod m) := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := 5) (by omega) (by omega)
  have hyneg1 : (5 : ZMod m) ≠ (-1 : ZMod m) := five_ne_neg_one (m := m)
  have hdiag : (5 : ZMod m) ≠ (1 : ZMod m) := hy1
  have hxneg1 : (1 : ZMod m) ≠ (-1 : ZMod m) := one_ne_neg_one (m := m)
  have h00 : ((1 : ZMod m), (5 : ZMod m)) ≠ ((0 : ZMod m), (0 : ZMod m)) := by
    intro h
    exact one_ne_zero (m := m) (congrArg Prod.fst h)
  calc
    R2xy (m := m) ((1 : ZMod m), (5 : ZMod m))
        = G (m := m) ((1 : ZMod m), (5 : ZMod m)) := by
            exact R2xy_eq_G_of (m := m) hA hy1 hyneg1 hdiag hxneg1 h00
    _ = ((2 : ZMod m), (4 : ZMod m)) := by
          ext <;> simp [G] <;> ring

theorem R2xy_two_four [Fact (7 < m)] :
    R2xy (m := m) ((2 : ZMod m), (4 : ZMod m)) = ((3 : ZMod m), (3 : ZMod m)) := by
  have hm7 : 7 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm1 : 1 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (1 < m) := ⟨hm1⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  have hA : ((2 : ZMod m), (4 : ZMod m)) ≠ ((2 : ZMod m), (2 : ZMod m)) := by
    intro h
    have hsnd : (4 : ZMod m) = (2 : ZMod m) := congrArg Prod.snd h
    exact natCast_ne_two_of_three_le_lt (m := m) (n := 4) (by omega) (by omega) hsnd
  have hy1 : (4 : ZMod m) ≠ (1 : ZMod m) := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := 4) (by omega) (by omega)
  have hyneg1 : (4 : ZMod m) ≠ (-1 : ZMod m) :=
    natCast_ne_neg_one_of_lt (m := m) (n := 4) (by omega)
  have hdiag : (4 : ZMod m) ≠ (2 : ZMod m) := by
    exact natCast_ne_two_of_three_le_lt (m := m) (n := 4) (by omega) (by omega)
  have hxneg1 : (2 : ZMod m) ≠ (-1 : ZMod m) :=
    natCast_ne_neg_one_of_lt (m := m) (n := 2) (by omega)
  have h00 : ((2 : ZMod m), (4 : ZMod m)) ≠ ((0 : ZMod m), (0 : ZMod m)) := by
    intro h
    exact two_ne_zero (m := m) (congrArg Prod.fst h)
  calc
    R2xy (m := m) ((2 : ZMod m), (4 : ZMod m))
        = G (m := m) ((2 : ZMod m), (4 : ZMod m)) := by
            exact R2xy_eq_G_of (m := m) hA hy1 hyneg1 hdiag hxneg1 h00
    _ = ((3 : ZMod m), (3 : ZMod m)) := by
          ext <;> simp [G] <;> ring

theorem iterate_two_from_zero_six [Fact (7 < m)] :
    (R2xy (m := m)^[2]) ((0 : ZMod m), (6 : ZMod m)) = ((2 : ZMod m), (4 : ZMod m)) := by
  calc
    (R2xy (m := m)^[2]) ((0 : ZMod m), (6 : ZMod m))
        = R2xy (m := m) (R2xy (m := m) ((0 : ZMod m), (6 : ZMod m))) := by simp
    _ = R2xy (m := m) ((1 : ZMod m), (5 : ZMod m)) := by rw [R2xy_zero_six (m := m)]
    _ = ((2 : ZMod m), (4 : ZMod m)) := R2xy_one_five (m := m)

theorem iterate_three_from_zero_six [Fact (7 < m)] :
    (R2xy (m := m)^[3]) ((0 : ZMod m), (6 : ZMod m)) = ((3 : ZMod m), (3 : ZMod m)) := by
  calc
    (R2xy (m := m)^[3]) ((0 : ZMod m), (6 : ZMod m))
        = R2xy (m := m) ((R2xy (m := m)^[2]) ((0 : ZMod m), (6 : ZMod m))) := by
            rw [show 3 = 1 + 2 by decide, Function.iterate_add_apply]
            simp
    _ = R2xy (m := m) ((2 : ZMod m), (4 : ZMod m)) := by rw [iterate_two_from_zero_six (m := m)]
    _ = ((3 : ZMod m), (3 : ZMod m)) := R2xy_two_four (m := m)

theorem R2xy_three_three [Fact (5 < m)] :
    R2xy (m := m) ((3 : ZMod m), (3 : ZMod m)) = ((3 : ZMod m), (1 : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  have hx0 : (3 : ZMod m) ≠ 0 := three_ne_zero (m := m)
  have hx2 : (3 : ZMod m) ≠ 2 := by
    exact natCast_ne_two_of_three_le_lt (m := m) (n := 3) (by omega) (by omega)
  have hxneg1 : (3 : ZMod m) ≠ (-1 : ZMod m) :=
    natCast_ne_neg_one_of_lt (m := m) (n := 3) (by omega)
  calc
    R2xy (m := m) ((3 : ZMod m), (3 : ZMod m))
        = ((3 : ZMod m), (3 : ZMod m) - 2) := R2xy_eq_D_of (m := m) hx0 hx2 hxneg1
    _ = ((3 : ZMod m), (1 : ZMod m)) := by
          ext <;> ring

theorem R2xy_three_one [Fact (5 < m)] :
    R2xy (m := m) ((3 : ZMod m), (1 : ZMod m)) = ((5 : ZMod m), (0 : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm1 : 1 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (1 < m) := ⟨hm1⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  have hx1 : (3 : ZMod m) ≠ (1 : ZMod m) := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := 3) (by omega) (by omega)
  have hxneg1 : (3 : ZMod m) ≠ (-1 : ZMod m) :=
    natCast_ne_neg_one_of_lt (m := m) (n := 3) (by omega)
  calc
    R2xy (m := m) ((3 : ZMod m), (1 : ZMod m))
        = ((3 : ZMod m) + 2, (0 : ZMod m)) := R2xy_eq_B_of (m := m) (x := (3 : ZMod m)) hx1 hxneg1
    _ = ((5 : ZMod m), (0 : ZMod m)) := by
          ext <;> ring

theorem firstReturn_six_of_ge_ten [Fact (Even m)] [Fact (9 < m)] :
    (R2xy (m := m)^[rho2 (m := m) (6 : ZMod m)]) (linePoint (m := m) (6 : ZMod m)) =
      linePoint (m := m) (T2 (m := m) (6 : ZMod m)) := by
  have hm9 : 9 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm1 : 1 < m := by omega
  have hm2 : 2 < m := by omega
  have hm5 : 5 < m := by omega
  have hm7 : 7 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (1 < m) := ⟨hm1⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  letI : Fact (5 < m) := ⟨hm5⟩
  letI : Fact (7 < m) := ⟨hm7⟩
  have hx0 : (6 : ZMod m) ≠ 0 := six_ne_zero (m := m)
  have hx1 : (6 : ZMod m) ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := 6) (by omega) (by omega)
  have hx2 : (6 : ZMod m) ≠ 2 := by
    exact natCast_ne_two_of_three_le_lt (m := m) (n := 6) (by omega) (by omega)
  have hrho : rho2 (m := m) (6 : ZMod m) = m := by
    simp [rho2, hx0, hx1, hx2]
  have hT : T2 (m := m) (6 : ZMod m) = (5 : ZMod m) := by
    simp [T2, hx0, hx1, hx2]
    norm_num
  have hstepMSubOneSix :
      (R2xy (m := m)^[m - 6]) (linePoint (m := m) (6 : ZMod m)) =
        ((((m - 1 : ℕ) : ZMod m)), (6 : ZMod m)) := by
    rw [show m - 6 = (m - 8) + 2 by omega, Function.iterate_add_apply]
    rw [iterate_two_from_linePoint_six (m := m)]
    exact iterate_to_m_sub_one_six_from_seven_neg_two (m := m)
  have hstepZeroSix :
      (R2xy (m := m)^[m - 5]) (linePoint (m := m) (6 : ZMod m)) =
        ((0 : ZMod m), (6 : ZMod m)) := by
    rw [show m - 5 = 1 + (m - 6) by omega, Function.iterate_add_apply]
    simp
    rw [hstepMSubOneSix]
    exact R2xy_m_sub_one_six (m := m)
  have hstepThreeThree :
      (R2xy (m := m)^[m - 2]) (linePoint (m := m) (6 : ZMod m)) =
        ((3 : ZMod m), (3 : ZMod m)) := by
    rw [show m - 2 = 3 + (m - 5) by omega, Function.iterate_add_apply]
    simpa [hstepZeroSix] using iterate_three_from_zero_six (m := m)
  have hstepThreeOne :
      (R2xy (m := m)^[m - 1]) (linePoint (m := m) (6 : ZMod m)) =
        ((3 : ZMod m), (1 : ZMod m)) := by
    rw [show m - 1 = 1 + (m - 2) by omega, Function.iterate_add_apply]
    simp
    rw [hstepThreeThree]
    exact R2xy_three_three (m := m)
  have hstepFinal :
      (R2xy (m := m)^[m]) (linePoint (m := m) (6 : ZMod m)) =
        linePoint (m := m) (5 : ZMod m) := by
    calc
      (R2xy (m := m)^[m]) (linePoint (m := m) (6 : ZMod m))
          = R2xy (m := m) ((R2xy (m := m)^[m - 1]) (linePoint (m := m) (6 : ZMod m))) := by
              rw [show m = 1 + (m - 1) by omega, Function.iterate_add_apply]
              simp
      _ = R2xy (m := m) ((3 : ZMod m), (1 : ZMod m)) := by rw [hstepThreeOne]
      _ = linePoint (m := m) (5 : ZMod m) := by simpa [linePoint] using R2xy_three_one (m := m)
  calc
    (R2xy (m := m)^[rho2 (m := m) (6 : ZMod m)]) (linePoint (m := m) (6 : ZMod m))
        = (R2xy (m := m)^[m]) (linePoint (m := m) (6 : ZMod m)) := by rw [hrho]
    _ = linePoint (m := m) (5 : ZMod m) := hstepFinal
    _ = linePoint (m := m) (T2 (m := m) (6 : ZMod m)) := by rw [hT]

theorem hfirst_six_of_ge_ten [Fact (Even m)] [Fact (9 < m)] :
    ∀ n, 0 < n → n < rho2 (m := m) (6 : ZMod m) →
      (R2xy (m := m)^[n]) (linePoint (m := m) (6 : ZMod m)) ∉ Set.range (linePoint (m := m))
  | n, hn0, hnlt => by
      have hm9 : 9 < m := Fact.out
      have hm0 : 0 < m := by omega
      have hm1 : 1 < m := by omega
      have hm2 : 2 < m := by omega
      have hm5 : 5 < m := by omega
      have hm7 : 7 < m := by omega
      letI : Fact (0 < m) := ⟨hm0⟩
      letI : Fact (1 < m) := ⟨hm1⟩
      letI : Fact (2 < m) := ⟨hm2⟩
      letI : Fact (5 < m) := ⟨hm5⟩
      letI : Fact (7 < m) := ⟨hm7⟩
      have hx0 : (6 : ZMod m) ≠ 0 := six_ne_zero (m := m)
      have hx1 : (6 : ZMod m) ≠ 1 := by
        exact natCast_ne_one_of_two_le_lt (m := m) (n := 6) (by omega) (by omega)
      have hx2 : (6 : ZMod m) ≠ 2 := by
        exact natCast_ne_two_of_three_le_lt (m := m) (n := 6) (by omega) (by omega)
      have hrho : rho2 (m := m) (6 : ZMod m) = m := by
        simp [rho2, hx0, hx1, hx2]
      have hnm : n < m := by rwa [hrho] at hnlt
      by_cases h1 : n = 1
      · apply not_mem_range_linePoint_of_snd_ne_zero
        rw [h1]
        simpa [Function.iterate_one, R2xy_linePoint_six (m := m)] using
          (neg_ne_zero.mpr (one_ne_zero (m := m)))
      · by_cases hfront : n ≤ m - 6
        · let t : ℕ := n - 2
          have ht : t ≤ m - 8 := by
            dsimp [t]
            omega
          have hnEq : n = t + 2 := by
            dsimp [t]
            omega
          have hiter :
              (R2xy (m := m)^[n]) (linePoint (m := m) (6 : ZMod m)) =
                ((7 : ZMod m) + t, (-2 : ZMod m) - t) := by
            rw [hnEq]
            simpa using iterate_R2xy_from_linePoint_six_after_two (m := m) t ht
          apply not_mem_range_linePoint_of_snd_ne_zero
          rw [hiter]
          exact neg_two_sub_nat_ne_zero (m := m) (n := t) (by omega)
        · have hstepZeroSix :
            (R2xy (m := m)^[m - 5]) (linePoint (m := m) (6 : ZMod m)) =
              ((0 : ZMod m), (6 : ZMod m)) := by
            have hstepMSubOneSix :
                (R2xy (m := m)^[m - 6]) (linePoint (m := m) (6 : ZMod m)) =
                  ((((m - 1 : ℕ) : ZMod m)), (6 : ZMod m)) := by
              rw [show m - 6 = (m - 8) + 2 by omega, Function.iterate_add_apply]
              rw [iterate_two_from_linePoint_six (m := m)]
              exact iterate_to_m_sub_one_six_from_seven_neg_two (m := m)
            rw [show m - 5 = 1 + (m - 6) by omega, Function.iterate_add_apply]
            simp
            rw [hstepMSubOneSix]
            exact R2xy_m_sub_one_six (m := m)
          by_cases hm5case : n = m - 5
          · apply not_mem_range_linePoint_of_snd_ne_zero
            rw [hm5case, hstepZeroSix]
            exact six_ne_zero (m := m)
          · by_cases hm4case : n = m - 4
            · apply not_mem_range_linePoint_of_snd_ne_zero
              rw [hm4case]
              have hstepOneFive :
                  (R2xy (m := m)^[m - 4]) (linePoint (m := m) (6 : ZMod m)) =
                    ((1 : ZMod m), (5 : ZMod m)) := by
                rw [show m - 4 = 1 + (m - 5) by omega, Function.iterate_add_apply]
                simpa [hstepZeroSix] using R2xy_zero_six (m := m)
              rw [hstepOneFive]
              exact five_ne_zero (m := m)
            · by_cases hm3case : n = m - 3
              · apply not_mem_range_linePoint_of_snd_ne_zero
                rw [hm3case]
                have hstepTwoFour :
                    (R2xy (m := m)^[m - 3]) (linePoint (m := m) (6 : ZMod m)) =
                      ((2 : ZMod m), (4 : ZMod m)) := by
                  rw [show m - 3 = 2 + (m - 5) by omega, Function.iterate_add_apply]
                  simpa [hstepZeroSix] using iterate_two_from_zero_six (m := m)
                rw [hstepTwoFour]
                exact four_ne_zero (m := m)
              · by_cases hm2case : n = m - 2
                · apply not_mem_range_linePoint_of_snd_ne_zero
                  rw [hm2case]
                  have hstepThreeThree :
                      (R2xy (m := m)^[m - 2]) (linePoint (m := m) (6 : ZMod m)) =
                        ((3 : ZMod m), (3 : ZMod m)) := by
                    rw [show m - 2 = 3 + (m - 5) by omega, Function.iterate_add_apply]
                    simpa [hstepZeroSix] using iterate_three_from_zero_six (m := m)
                  rw [hstepThreeThree]
                  exact three_ne_zero (m := m)
                · have hm1case : n = m - 1 := by omega
                  apply not_mem_range_linePoint_of_snd_ne_zero
                  rw [hm1case]
                  have hstepThreeThree :
                      (R2xy (m := m)^[m - 2]) (linePoint (m := m) (6 : ZMod m)) =
                        ((3 : ZMod m), (3 : ZMod m)) := by
                    rw [show m - 2 = 3 + (m - 5) by omega, Function.iterate_add_apply]
                    simpa [hstepZeroSix] using iterate_three_from_zero_six (m := m)
                  have hstepThreeOne :
                      (R2xy (m := m)^[m - 1]) (linePoint (m := m) (6 : ZMod m)) =
                        ((3 : ZMod m), (1 : ZMod m)) := by
                    rw [show m - 1 = 1 + (m - 2) by omega, Function.iterate_add_apply]
                    simp
                    rw [hstepThreeThree]
                    exact R2xy_three_three (m := m)
                  rw [hstepThreeOne]
                  exact one_ne_zero (m := m)

theorem firstReturn_six [Fact (Even m)] [Fact (7 < m)] :
    (R2xy (m := m)^[rho2 (m := m) (6 : ZMod m)]) (linePoint (m := m) (6 : ZMod m)) =
      linePoint (m := m) (T2 (m := m) (6 : ZMod m)) := by
  by_cases hm8 : m = 8
  · subst hm8
    exact firstReturn_six_m8
  · have hmEven : Even m := by
      have hinst : Fact (Even m) := inferInstance
      exact hinst.out
    have hm7 : 7 < m := by
      have hinst : Fact (7 < m) := inferInstance
      exact hinst.out
    have hm10 : 9 < m := by
      rcases hmEven with ⟨k, hk⟩
      omega
    letI : Fact (9 < m) := ⟨hm10⟩
    exact firstReturn_six_of_ge_ten (m := m)

theorem hfirst_six [Fact (Even m)] [Fact (7 < m)] :
    ∀ n, 0 < n → n < rho2 (m := m) (6 : ZMod m) →
      (R2xy (m := m)^[n]) (linePoint (m := m) (6 : ZMod m)) ∉ Set.range (linePoint (m := m))
  | n, hn0, hnlt => by
      by_cases hm8 : m = 8
      · subst hm8
        exact hfirst_six_m8 n hn0 (by simpa using hnlt)
      · have hmEven : Even m := by
          have hinst : Fact (Even m) := inferInstance
          exact hinst.out
        have hm7 : 7 < m := by
          have hinst : Fact (7 < m) := inferInstance
          exact hinst.out
        have hm10 : 9 < m := by
          rcases hmEven with ⟨k, hk⟩
          omega
        letI : Fact (9 < m) := ⟨hm10⟩
        exact hfirst_six_of_ge_ten (m := m) n hn0 hnlt

theorem R2xy_linePoint_even_generic_start [Fact (7 < m)] {x : ℕ}
    (hx8 : 8 ≤ x) (hxle : x ≤ m - 4) :
    R2xy (m := m) (linePoint (m := m) (((x : ℕ) : ZMod m))) =
      ((((x + 1 : ℕ) : ZMod m)), (-1 : ZMod m)) := by
  have hm7 : 7 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm1 : 1 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (1 < m) := ⟨hm1⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  have hA : linePoint (m := m) (((x : ℕ) : ZMod m)) ≠ ((2 : ZMod m), (2 : ZMod m)) := by
    intro h
    exact two_ne_zero (m := m) (by simpa [linePoint] using (congrArg Prod.snd h).symm)
  have hy1 : (0 : ZMod m) ≠ (1 : ZMod m) := (one_ne_zero (m := m)).symm
  have hyneg1 : (0 : ZMod m) ≠ (-1 : ZMod m) := by
    intro h
    exact neg_ne_zero.mpr (one_ne_zero (m := m)) h.symm
  have hdiag : (0 : ZMod m) ≠ (((x : ℕ) : ZMod m)) := by
    intro h
    exact natCast_ne_zero_of_pos_lt (m := m) (n := x) (by omega) (by omega) h.symm
  have hxneg1 : (((x : ℕ) : ZMod m)) ≠ (-1 : ZMod m) :=
    natCast_ne_neg_one_of_lt (m := m) (n := x) (by omega)
  have h00 : linePoint (m := m) (((x : ℕ) : ZMod m)) ≠ ((0 : ZMod m), (0 : ZMod m)) := by
    intro h
    exact natCast_ne_zero_of_pos_lt (m := m) (n := x) (by omega) (by omega)
      (by simpa [linePoint] using congrArg Prod.fst h)
  calc
    R2xy (m := m) (linePoint (m := m) (((x : ℕ) : ZMod m)))
        = G (m := m) (linePoint (m := m) (((x : ℕ) : ZMod m))) := by
            simpa [linePoint] using R2xy_eq_G_of (m := m) hA hy1 hyneg1 hdiag hxneg1 h00
    _ = ((((x + 1 : ℕ) : ZMod m)), (-1 : ZMod m)) := by
          ext <;> simp [linePoint, G, Nat.cast_add] <;> ring

theorem R2xy_even_generic_succ_neg_one [Fact (7 < m)] {x : ℕ}
    (hx8 : 8 ≤ x) (hxle : x ≤ m - 4) :
    R2xy (m := m) ((((x + 1 : ℕ) : ZMod m)), (-1 : ZMod m)) =
      ((((x + 1 : ℕ) : ZMod m)), (-2 : ZMod m)) := by
  have hm7 : 7 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  have hxneg1 : (((x + 1 : ℕ) : ZMod m)) ≠ (-1 : ZMod m) :=
    natCast_ne_neg_one_of_lt (m := m) (n := x + 1) (by omega)
  simpa using R2xy_eq_C_of (m := m) (x := (((x + 1 : ℕ) : ZMod m))) hxneg1

theorem iterate_R2xy_from_even_generic_succ_neg_two
    [Fact (Even m)] [Fact (7 < m)] {x : ℕ} (hxEven : Even x)
    (hx8 : 8 ≤ x) (hxle : x ≤ m - 4) :
    ∀ n, n ≤ m - x - 2 →
      (R2xy (m := m)^[n]) ((((x + 1 : ℕ) : ZMod m)), (-2 : ZMod m)) =
        ((((x + 1 : ℕ) : ZMod m)) + n, (-2 : ZMod m) - n)
  | 0, _ => by simp
  | n + 1, hn => by
      have hmEven : Even m := Fact.out
      have hm7 : 7 < m := Fact.out
      have hm0 : 0 < m := by omega
      have hm1 : 1 < m := by omega
      have hm2 : 2 < m := by omega
      letI : Fact (0 < m) := ⟨hm0⟩
      letI : Fact (1 < m) := ⟨hm1⟩
      letI : Fact (2 < m) := ⟨hm2⟩
      have hn' : n < m - x - 2 := Nat.lt_of_succ_le hn
      have hx_lt : x + 1 + n < m := by omega
      have hy_lt : m - 2 - n < m := by omega
      have xcast : ((((x + 1 : ℕ) : ZMod m)) + n) = (((x + 1 + n : ℕ) : ZMod m)) := by
        simpa [Nat.cast_add, add_assoc] using (Nat.cast_add (x + 1) n).symm
      have ycast : ((-2 : ZMod m) - n) = (((m - 2 - n : ℕ) : ZMod m)) := by
        have hm2le : 2 ≤ m := by omega
        have hnle : n ≤ m - 2 := by omega
        calc
          (-2 : ZMod m) - n = (((m - 2 : ℕ) : ZMod m)) - n := by
            rw [cast_sub_two_eq_neg_two (m := m) hm2le]
          _ = (((m - 2 - n : ℕ) : ZMod m)) := by rw [Nat.cast_sub hnle]
      have hA : ((((x + 1 : ℕ) : ZMod m)) + n, (-2 : ZMod m) - n) ≠ ((2 : ZMod m), (2 : ZMod m)) := by
        intro hEq
        have hfst : (((x + 1 + n : ℕ) : ZMod m)) = ((2 : ℕ) : ZMod m) := by
          calc
            (((x + 1 + n : ℕ) : ZMod m)) = ((((x + 1 : ℕ) : ZMod m)) + n) := by rw [xcast]
            _ = (2 : ZMod m) := congrArg Prod.fst hEq
            _ = ((2 : ℕ) : ZMod m) := by norm_num
        exact natCast_ne_two_of_three_le_lt (m := m) (n := x + 1 + n) (by omega) hx_lt hfst
      have hy1 : (-2 : ZMod m) - n ≠ (1 : ZMod m) := by
        rw [ycast]
        exact natCast_ne_one_of_two_le_lt (m := m) (n := m - 2 - n) (by omega) hy_lt
      have hyneg1 : (-2 : ZMod m) - n ≠ (-1 : ZMod m) := by
        rw [ycast]
        exact natCast_ne_neg_one_of_lt (m := m) (n := m - 2 - n) (by omega)
      have hdiag : (-2 : ZMod m) - n ≠ ((((x + 1 : ℕ) : ZMod m)) + n) := by
        intro hEq
        have hnatEq : m - 2 - n = x + 1 + n := by
          have hcast : (((m - 2 - n : ℕ) : ZMod m)) = (((x + 1 + n : ℕ) : ZMod m)) := by
            rw [ycast, xcast] at hEq
            exact hEq
          exact (natCast_eq_natCast_iff_of_lt (m := m) (a := m - 2 - n) (b := x + 1 + n)
            hy_lt hx_lt).1 hcast
        rcases hmEven with ⟨k, hk⟩
        rcases hxEven with ⟨j, hj⟩
        omega
      have hxneg1 : (((x + 1 + n : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
        exact natCast_ne_neg_one_of_lt (m := m) (n := x + 1 + n) (by omega)
      have hxneg1' : ((((x + 1 : ℕ) : ZMod m)) + n) ≠ (-1 : ZMod m) := by
        rw [xcast]
        exact hxneg1
      have h00 : ((((x + 1 : ℕ) : ZMod m)) + n, (-2 : ZMod m) - n) ≠ ((0 : ZMod m), (0 : ZMod m)) := by
        intro hEq
        have hfst : (((x + 1 + n : ℕ) : ZMod m)) = 0 := by
          calc
            (((x + 1 + n : ℕ) : ZMod m)) = ((((x + 1 : ℕ) : ZMod m)) + n) := by rw [xcast]
            _ = 0 := congrArg Prod.fst hEq
        exact natCast_ne_zero_of_pos_lt (m := m) (n := x + 1 + n) (by omega) hx_lt hfst
      rw [Function.iterate_succ_apply',
        iterate_R2xy_from_even_generic_succ_neg_two (m := m) hxEven hx8 hxle n (Nat.le_of_succ_le hn)]
      rw [R2xy_eq_G_of (m := m) hA hy1 hyneg1 hdiag hxneg1' h00]
      ext <;> simp [G, Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] <;> ring

theorem iterate_R2xy_from_linePoint_even_generic_after_two
    [Fact (Even m)] [Fact (7 < m)] {x : ℕ} (hxEven : Even x)
    (hx8 : 8 ≤ x) (hxle : x ≤ m - 4) :
    ∀ n, n ≤ m - x - 2 →
      (R2xy (m := m)^[n + 2]) (linePoint (m := m) (((x : ℕ) : ZMod m))) =
        ((((x + 1 : ℕ) : ZMod m)) + n, (-2 : ZMod m) - n)
  | n, hn => by
      have htwo :
          (R2xy (m := m)^[2]) (linePoint (m := m) (((x : ℕ) : ZMod m))) =
            ((((x + 1 : ℕ) : ZMod m)), (-2 : ZMod m)) := by
        calc
          (R2xy (m := m)^[2]) (linePoint (m := m) (((x : ℕ) : ZMod m)))
              = R2xy (m := m) (R2xy (m := m) (linePoint (m := m) (((x : ℕ) : ZMod m)))) := by simp
          _ = R2xy (m := m) ((((x + 1 : ℕ) : ZMod m)), (-1 : ZMod m)) := by
                rw [R2xy_linePoint_even_generic_start (m := m) hx8 hxle]
          _ = ((((x + 1 : ℕ) : ZMod m)), (-2 : ZMod m)) := by
                rw [R2xy_even_generic_succ_neg_one (m := m) hx8 hxle]
      rw [Function.iterate_add_apply]
      simpa [htwo] using
        iterate_R2xy_from_even_generic_succ_neg_two (m := m) hxEven hx8 hxle n hn

theorem iterate_to_m_sub_one_even_generic
    [Fact (Even m)] [Fact (7 < m)] {x : ℕ} (hxEven : Even x)
    (hx8 : 8 ≤ x) (hxle : x ≤ m - 4) :
    (R2xy (m := m)^[m - x]) (linePoint (m := m) (((x : ℕ) : ZMod m))) =
      ((((m - 1 : ℕ) : ZMod m)), (((x : ℕ) : ZMod m))) := by
  rw [show m - x = (m - x - 2) + 2 by omega, Function.iterate_add_apply]
  have htwo :
      (R2xy (m := m)^[2]) (linePoint (m := m) (((x : ℕ) : ZMod m))) =
        ((((x + 1 : ℕ) : ZMod m)), (-2 : ZMod m)) := by
    calc
      (R2xy (m := m)^[2]) (linePoint (m := m) (((x : ℕ) : ZMod m)))
          = R2xy (m := m) (R2xy (m := m) (linePoint (m := m) (((x : ℕ) : ZMod m)))) := by simp
      _ = R2xy (m := m) ((((x + 1 : ℕ) : ZMod m)), (-1 : ZMod m)) := by
            rw [R2xy_linePoint_even_generic_start (m := m) hx8 hxle]
      _ = ((((x + 1 : ℕ) : ZMod m)), (-2 : ZMod m)) := by
            rw [R2xy_even_generic_succ_neg_one (m := m) hx8 hxle]
  rw [htwo]
  have hmain := iterate_R2xy_from_even_generic_succ_neg_two
    (m := m) hxEven hx8 hxle (m - x - 2) le_rfl
  rw [hmain]
  ext
  · calc
      ((((x + 1 : ℕ) : ZMod m)) + (((m - x - 2 : ℕ) : ZMod m)))
          = (((x + 1 + (m - x - 2) : ℕ) : ZMod m)) := by
              simp [Nat.cast_add, add_assoc, add_left_comm, add_comm]
      _ = (((m - 1 : ℕ) : ZMod m)) := by congr; omega
  · have hm2le : 2 ≤ m := by omega
    have hnle : m - x - 2 ≤ m - 2 := by omega
    change (-2 : ZMod m) - (((m - x - 2 : ℕ) : ZMod m)) = (((x : ℕ) : ZMod m))
    calc
      (-2 : ZMod m) - (((m - x - 2 : ℕ) : ZMod m))
          = (((m - 2 : ℕ) : ZMod m)) - (((m - x - 2 : ℕ) : ZMod m)) := by
              rw [cast_sub_two_eq_neg_two (m := m) hm2le]
      _ = (((m - 2 - (m - x - 2) : ℕ) : ZMod m)) := by rw [Nat.cast_sub hnle]
      _ = (((x : ℕ) : ZMod m)) := by congr; omega

theorem R2xy_m_sub_one_even_generic [Fact (7 < m)] {x : ℕ}
    (hx8 : 8 ≤ x) (hxle : x ≤ m - 4) :
    R2xy (m := m) ((((m - 1 : ℕ) : ZMod m)), (((x : ℕ) : ZMod m))) =
      ((0 : ZMod m), (((x : ℕ) : ZMod m))) := by
  have hm7 : 7 < m := Fact.out
  have hm0 : 0 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (5 < m) := ⟨by omega⟩
  have hm1le : 1 ≤ m := by omega
  have hneg1 : (((m - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) := cast_sub_one_eq_neg_one (m := m) hm1le
  have hx0 : (((x : ℕ) : ZMod m)) ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := x) (by omega) (by omega)
  have hxneg2 : (((x : ℕ) : ZMod m)) ≠ (-2 : ZMod m) := by
    exact natCast_ne_neg_two_of_lt (m := m) (n := x) (by omega)
  calc
    R2xy (m := m) ((((m - 1 : ℕ) : ZMod m)), (((x : ℕ) : ZMod m)))
        = R2xy (m := m) ((-1 : ZMod m), (((x : ℕ) : ZMod m))) := by rw [hneg1]
    _ = ((0 : ZMod m), (((x : ℕ) : ZMod m))) := by
          simpa using R2xy_eq_E_of (m := m) (y := (((x : ℕ) : ZMod m))) hx0 hxneg2

theorem iterate_R2xy_from_zero_even_generic
    [Fact (Even m)] [Fact (7 < m)] {x : ℕ} (hxEven : Even x)
    (hx8 : 8 ≤ x) (hxle : x ≤ m - 2) :
    ∀ n, n ≤ x / 2 →
      (R2xy (m := m)^[n]) ((0 : ZMod m), (((x : ℕ) : ZMod m))) =
        ((((n : ℕ) : ZMod m)), (((x : ℕ) : ZMod m)) - n)
  | 0, _ => by simp
  | n + 1, hn => by
      have hm7 : 7 < m := Fact.out
      have hm0 : 0 < m := by omega
      have hm1 : 1 < m := by omega
      have hm2 : 2 < m := by omega
      letI : Fact (0 < m) := ⟨hm0⟩
      letI : Fact (1 < m) := ⟨hm1⟩
      letI : Fact (2 < m) := ⟨hm2⟩
      have hn' : n < x / 2 := Nat.lt_of_succ_le hn
      have hdouble : x / 2 + x / 2 = x := by
        simpa [two_mul] using (Nat.two_mul_div_two_of_even hxEven)
      have hnleX : n ≤ x := by omega
      have hx_lt : n < m := by omega
      have hy_lt : x - n < m := by omega
      have ycast : ((((x : ℕ) : ZMod m)) - n) = (((x - n : ℕ) : ZMod m)) := by
        rw [Nat.cast_sub hnleX]
      have hA : ((((n : ℕ) : ZMod m)), (((x : ℕ) : ZMod m)) - n) ≠
          ((2 : ZMod m), (2 : ZMod m)) := by
        intro hEq
        have hsnd : (((x - n : ℕ) : ZMod m)) = ((2 : ℕ) : ZMod m) := by
          calc
            (((x - n : ℕ) : ZMod m)) = ((((x : ℕ) : ZMod m)) - n) := by rw [← ycast]
            _ = (2 : ZMod m) := congrArg Prod.snd hEq
            _ = ((2 : ℕ) : ZMod m) := by norm_num
        exact natCast_ne_two_of_three_le_lt (m := m) (n := x - n) (by omega) hy_lt hsnd
      have hy1 : (((x : ℕ) : ZMod m)) - n ≠ (1 : ZMod m) := by
        rw [ycast]
        exact natCast_ne_one_of_two_le_lt (m := m) (n := x - n) (by omega) hy_lt
      have hyneg1 : (((x : ℕ) : ZMod m)) - n ≠ (-1 : ZMod m) := by
        rw [ycast]
        exact natCast_ne_neg_one_of_lt (m := m) (n := x - n) (by omega)
      have hdiag : (((x : ℕ) : ZMod m)) - n ≠ (((n : ℕ) : ZMod m)) := by
        intro hEq
        have hnatEq : x - n = n := by
          have hcast : (((x - n : ℕ) : ZMod m)) = (((n : ℕ) : ZMod m)) := by
            rw [ycast] at hEq
            exact hEq
          exact (natCast_eq_natCast_iff_of_lt (m := m) (a := x - n) (b := n) hy_lt hx_lt).1 hcast
        omega
      have hxneg1 : (n : ZMod m) ≠ (-1 : ZMod m) := by
        exact natCast_ne_neg_one_of_lt (m := m) (n := n) (by omega)
      have h00 : ((((n : ℕ) : ZMod m)), (((x : ℕ) : ZMod m)) - n) ≠
          ((0 : ZMod m), (0 : ZMod m)) := by
        intro hEq
        have hsnd : (((x - n : ℕ) : ZMod m)) = 0 := by
          calc
            (((x - n : ℕ) : ZMod m)) = ((((x : ℕ) : ZMod m)) - n) := by rw [← ycast]
            _ = 0 := congrArg Prod.snd hEq
        exact natCast_ne_zero_of_pos_lt (m := m) (n := x - n) (by omega) hy_lt hsnd
      rw [Function.iterate_succ_apply',
        iterate_R2xy_from_zero_even_generic (m := m) hxEven hx8 hxle n (Nat.le_of_succ_le hn)]
      rw [R2xy_eq_G_of (m := m) hA hy1 hyneg1 hdiag hxneg1 h00]
      ext <;> simp [G, Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] <;> ring

theorem iterate_to_half_half_even_generic
    [Fact (Even m)] [Fact (7 < m)] {x : ℕ} (hxEven : Even x)
    (hx8 : 8 ≤ x) (hxle : x ≤ m - 2) :
    (R2xy (m := m)^[x / 2]) ((0 : ZMod m), (((x : ℕ) : ZMod m))) =
      ((((x / 2 : ℕ) : ZMod m)), (((x / 2 : ℕ) : ZMod m))) := by
  have hdouble : x / 2 + x / 2 = x := by
    simpa [two_mul] using (Nat.two_mul_div_two_of_even hxEven)
  rw [iterate_R2xy_from_zero_even_generic (m := m) hxEven hx8 hxle (x / 2) le_rfl]
  ext
  · rfl
  · change (((x : ℕ) : ZMod m) - (((x / 2 : ℕ) : ZMod m))) = (((x / 2 : ℕ) : ZMod m))
    have hhalfle : x / 2 ≤ x := by omega
    calc
      (((x : ℕ) : ZMod m) - (((x / 2 : ℕ) : ZMod m))) = (((x - x / 2 : ℕ) : ZMod m)) := by
        rw [Nat.cast_sub hhalfle]
      _ = (((x / 2 : ℕ) : ZMod m)) := by congr; omega

theorem R2xy_half_half_even_generic
    [Fact (Even m)] [Fact (7 < m)] {x : ℕ} (hxEven : Even x)
    (hx8 : 8 ≤ x) (hxle : x ≤ m - 2) :
    R2xy (m := m) ((((x / 2 : ℕ) : ZMod m)), (((x / 2 : ℕ) : ZMod m))) =
      ((((x / 2 : ℕ) : ZMod m)), (((x / 2 : ℕ) : ZMod m)) - 2) := by
  have hm7 : 7 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  have hx0 : (((x / 2 : ℕ) : ZMod m)) ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := x / 2) (by omega) (by omega)
  have hx2 : (((x / 2 : ℕ) : ZMod m)) ≠ 2 := by
    exact natCast_ne_two_of_three_le_lt (m := m) (n := x / 2) (by omega) (by omega)
  have hxneg1 : (((x / 2 : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := x / 2) (by omega)
  simpa using R2xy_eq_D_of (m := m) hx0 hx2 hxneg1

theorem iterate_R2xy_from_half_half_sub_two_even_generic
    [Fact (Even m)] [Fact (7 < m)] {x : ℕ} (hxEven : Even x)
    (hx8 : 8 ≤ x) (hxle : x ≤ m - 2) :
    ∀ n, n ≤ x / 2 - 3 →
      (R2xy (m := m)^[n])
          ((((x / 2 : ℕ) : ZMod m)), (((x / 2 : ℕ) : ZMod m)) - 2) =
        ((((x / 2 : ℕ) : ZMod m)) + n, (((x / 2 : ℕ) : ZMod m)) - 2 - n)
  | 0, _ => by simp
  | n + 1, hn => by
      have hm7 : 7 < m := Fact.out
      have hm0 : 0 < m := by omega
      have hm1 : 1 < m := by omega
      have hm2 : 2 < m := by omega
      letI : Fact (0 < m) := ⟨hm0⟩
      letI : Fact (1 < m) := ⟨hm1⟩
      letI : Fact (2 < m) := ⟨hm2⟩
      have hn' : n < x / 2 - 3 := Nat.lt_of_succ_le hn
      have hdouble : x / 2 + x / 2 = x := by
        simpa [two_mul] using (Nat.two_mul_div_two_of_even hxEven)
      have hhalf_lt : x / 2 + n < m := by omega
      have hy_lt : x / 2 - 2 - n < m := by omega
      have xcast : ((((x / 2 : ℕ) : ZMod m)) + n) = (((x / 2 + n : ℕ) : ZMod m)) := by
        simpa [Nat.cast_add, add_assoc] using (Nat.cast_add (x / 2) n).symm
      have ycast : ((((x / 2 : ℕ) : ZMod m)) - 2 - n) = (((x / 2 - 2 - n : ℕ) : ZMod m)) := by
        have h2n : 2 + n ≤ x / 2 := by omega
        have hsub : x / 2 - n - 2 = x / 2 - 2 - n := by omega
        calc
          ((((x / 2 : ℕ) : ZMod m)) - 2 - n)
              = ((((x / 2 : ℕ) : ZMod m)) - (((2 + n : ℕ) : ZMod m))) := by
                  simp [Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          _ = (((x / 2 - (2 + n) : ℕ) : ZMod m)) := by rw [Nat.cast_sub h2n]
          _ = (((x / 2 - n - 2 : ℕ) : ZMod m)) := by rw [Nat.add_comm 2 n, ← Nat.sub_sub]
          _ = (((x / 2 - 2 - n : ℕ) : ZMod m)) := by
                simpa using congrArg (fun t : ℕ => ((t : ℕ) : ZMod m)) hsub
      have hA :
          ((((x / 2 : ℕ) : ZMod m)) + n, (((x / 2 : ℕ) : ZMod m)) - 2 - n) ≠
            ((2 : ZMod m), (2 : ZMod m)) := by
        intro hEq
        have hfst : (((x / 2 + n : ℕ) : ZMod m)) = ((2 : ℕ) : ZMod m) := by
          calc
            (((x / 2 + n : ℕ) : ZMod m)) = ((((x / 2 : ℕ) : ZMod m)) + n) := by rw [xcast]
            _ = (2 : ZMod m) := congrArg Prod.fst hEq
            _ = ((2 : ℕ) : ZMod m) := by norm_num
        exact natCast_ne_two_of_three_le_lt (m := m) (n := x / 2 + n) (by omega) hhalf_lt hfst
      have hy1 : (((x / 2 : ℕ) : ZMod m)) - 2 - n ≠ (1 : ZMod m) := by
        rw [ycast]
        exact natCast_ne_one_of_two_le_lt (m := m) (n := x / 2 - 2 - n) (by omega) hy_lt
      have hyneg1 : (((x / 2 : ℕ) : ZMod m)) - 2 - n ≠ (-1 : ZMod m) := by
        rw [ycast]
        exact natCast_ne_neg_one_of_lt (m := m) (n := x / 2 - 2 - n) (by omega)
      have hdiag : (((x / 2 : ℕ) : ZMod m)) - 2 - n ≠ (((x / 2 : ℕ) : ZMod m)) + n := by
        intro hEq
        have hnatEq : x / 2 - 2 - n = x / 2 + n := by
          have hcast : (((x / 2 - 2 - n : ℕ) : ZMod m)) = (((x / 2 + n : ℕ) : ZMod m)) := by
            rw [ycast, xcast] at hEq
            exact hEq
          exact (natCast_eq_natCast_iff_of_lt (m := m) (a := x / 2 - 2 - n) (b := x / 2 + n)
            hy_lt hhalf_lt).1 hcast
        omega
      have hxneg1 : (((x / 2 : ℕ) : ZMod m)) + n ≠ (-1 : ZMod m) := by
        rw [xcast]
        exact natCast_ne_neg_one_of_lt (m := m) (n := x / 2 + n) (by omega)
      have h00 :
          ((((x / 2 : ℕ) : ZMod m)) + n, (((x / 2 : ℕ) : ZMod m)) - 2 - n) ≠
            ((0 : ZMod m), (0 : ZMod m)) := by
        intro hEq
        have hfst : (((x / 2 + n : ℕ) : ZMod m)) = 0 := by
          calc
            (((x / 2 + n : ℕ) : ZMod m)) = ((((x / 2 : ℕ) : ZMod m)) + n) := by rw [xcast]
            _ = 0 := congrArg Prod.fst hEq
        exact natCast_ne_zero_of_pos_lt (m := m) (n := x / 2 + n) (by omega) hhalf_lt hfst
      rw [Function.iterate_succ_apply',
        iterate_R2xy_from_half_half_sub_two_even_generic (m := m) hxEven hx8 hxle n
          (Nat.le_of_succ_le hn)]
      rw [R2xy_eq_G_of (m := m) hA hy1 hyneg1 hdiag hxneg1 h00]
      ext <;> simp [G, Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] <;> ring

theorem iterate_to_x_sub_three_one_even_generic
    [Fact (Even m)] [Fact (7 < m)] {x : ℕ} (hxEven : Even x)
    (hx8 : 8 ≤ x) (hxle : x ≤ m - 2) :
    (R2xy (m := m)^[x / 2 - 3])
        ((((x / 2 : ℕ) : ZMod m)), (((x / 2 : ℕ) : ZMod m)) - 2) =
      ((((x - 3 : ℕ) : ZMod m)), (1 : ZMod m)) := by
  have hdouble : x / 2 + x / 2 = x := by
    simpa [two_mul] using (Nat.two_mul_div_two_of_even hxEven)
  rw [iterate_R2xy_from_half_half_sub_two_even_generic (m := m) hxEven hx8 hxle (x / 2 - 3) le_rfl]
  ext
  · calc
      ((((x / 2 : ℕ) : ZMod m)) + (((x / 2 - 3 : ℕ) : ZMod m)))
          = (((x / 2 + (x / 2 - 3) : ℕ) : ZMod m)) := by rw [Nat.cast_add]
      _ = (((x - 3 : ℕ) : ZMod m)) := by congr; omega
  · change (((x / 2 : ℕ) : ZMod m) - 2 - (((x / 2 - 3 : ℕ) : ZMod m))) = (1 : ZMod m)
    have h2n : 2 + (x / 2 - 3) ≤ x / 2 := by omega
    have hsub : x / 2 - (x / 2 - 3) - 2 = x / 2 - 2 - (x / 2 - 3) := by omega
    calc
      (((x / 2 : ℕ) : ZMod m) - 2 - (((x / 2 - 3 : ℕ) : ZMod m)))
          = (((x / 2 : ℕ) : ZMod m) - (((2 + (x / 2 - 3) : ℕ) : ZMod m))) := by
              simp [Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = (((x / 2 - (2 + (x / 2 - 3)) : ℕ) : ZMod m)) := by rw [Nat.cast_sub h2n]
      _ = (((x / 2 - (x / 2 - 3) - 2 : ℕ) : ZMod m)) := by
            rw [Nat.add_comm 2 (x / 2 - 3), ← Nat.sub_sub]
      _ = (((x / 2 - 2 - (x / 2 - 3) : ℕ) : ZMod m)) := by
            simpa using congrArg (fun t : ℕ => ((t : ℕ) : ZMod m)) hsub
      _ = (((1 : ℕ) : ZMod m)) := by congr; omega
      _ = (1 : ZMod m) := by norm_num

theorem R2xy_x_sub_three_one_even_generic [Fact (7 < m)] {x : ℕ}
    (hx8 : 8 ≤ x) (hxle : x ≤ m - 2) :
    R2xy (m := m) ((((x - 3 : ℕ) : ZMod m)), (1 : ZMod m)) =
      linePoint (m := m) (((x - 1 : ℕ) : ZMod m)) := by
  have hm7 : 7 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm1 : 1 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (1 < m) := ⟨hm1⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  have hx1 : (((x - 3 : ℕ) : ZMod m)) ≠ (1 : ZMod m) := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := x - 3) (by omega) (by omega)
  have hxneg1 : (((x - 3 : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := x - 3) (by omega)
  have hcoord : (((x - 3 : ℕ) : ZMod m) + 2) = (((x - 1 : ℕ) : ZMod m)) := by
    change (((x - 3 : ℕ) : ZMod m) + (((2 : ℕ) : ZMod m))) = (((x - 1 : ℕ) : ZMod m))
    rw [← Nat.cast_add]
    congr
    omega
  calc
    R2xy (m := m) ((((x - 3 : ℕ) : ZMod m)), (1 : ZMod m))
        = ((((x - 3 : ℕ) : ZMod m)) + 2, (0 : ZMod m)) := by
            simpa using R2xy_eq_B_of (m := m) (x := (((x - 3 : ℕ) : ZMod m))) hx1 hxneg1
    _ = linePoint (m := m) (((x - 1 : ℕ) : ZMod m)) := by
          simp [linePoint, hcoord]

theorem firstReturn_even_generic
    [Fact (Even m)] [Fact (7 < m)] {x : ℕ} (hxEven : Even x)
    (hx8 : 8 ≤ x) (hxle : x ≤ m - 4) :
    (R2xy (m := m)^[rho2 (m := m) (((x : ℕ) : ZMod m))])
        (linePoint (m := m) (((x : ℕ) : ZMod m))) =
      linePoint (m := m) (T2 (m := m) (((x : ℕ) : ZMod m))) := by
  have hm7 : 7 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm1 : 1 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (1 < m) := ⟨hm1⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  have hx0 : (((x : ℕ) : ZMod m)) ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := x) (by omega) (by omega)
  have hx1 : (((x : ℕ) : ZMod m)) ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := x) (by omega) (by omega)
  have hx2 : (((x : ℕ) : ZMod m)) ≠ 2 := by
    exact natCast_ne_two_of_three_le_lt (m := m) (n := x) (by omega) (by omega)
  have hrho : rho2 (m := m) (((x : ℕ) : ZMod m)) = m := by
    simp [rho2, hx0, hx1, hx2]
  have hT : T2 (m := m) (((x : ℕ) : ZMod m)) = (((x - 1 : ℕ) : ZMod m)) := by
    calc
      T2 (m := m) (((x : ℕ) : ZMod m)) = (((x : ℕ) : ZMod m)) - 1 := by
        simp [T2, hx0, hx1, hx2]
      _ = (((x - 1 : ℕ) : ZMod m)) := by
        symm
        simpa using (Nat.cast_sub (R := ZMod m) (m := 1) (n := x) (by omega))
  have hxle2 : x ≤ m - 2 := by
    omega
  have hdouble : x / 2 + x / 2 = x := by
    simpa [two_mul] using (Nat.two_mul_div_two_of_even hxEven)
  have hstepMSubOne :
      (R2xy (m := m)^[m - x]) (linePoint (m := m) (((x : ℕ) : ZMod m))) =
        ((((m - 1 : ℕ) : ZMod m)), (((x : ℕ) : ZMod m))) := by
    exact iterate_to_m_sub_one_even_generic (m := m) hxEven hx8 hxle
  have hstepZeroX :
      (R2xy (m := m)^[m - x + 1]) (linePoint (m := m) (((x : ℕ) : ZMod m))) =
        ((0 : ZMod m), (((x : ℕ) : ZMod m))) := by
    rw [show m - x + 1 = 1 + (m - x) by omega, Function.iterate_add_apply]
    simp
    rw [hstepMSubOne]
    exact R2xy_m_sub_one_even_generic (m := m) hx8 hxle
  have hstepHalfHalf :
      (R2xy (m := m)^[m - x + 1 + x / 2]) (linePoint (m := m) (((x : ℕ) : ZMod m))) =
        ((((x / 2 : ℕ) : ZMod m)), (((x / 2 : ℕ) : ZMod m))) := by
    rw [show m - x + 1 + x / 2 = x / 2 + (m - x + 1) by omega, Function.iterate_add_apply]
    simpa [hstepZeroX] using iterate_to_half_half_even_generic (m := m) hxEven hx8 hxle2
  have hstepHalfSubTwo :
      (R2xy (m := m)^[m - x + 1 + x / 2 + 1]) (linePoint (m := m) (((x : ℕ) : ZMod m))) =
        ((((x / 2 : ℕ) : ZMod m)), (((x / 2 : ℕ) : ZMod m)) - 2) := by
    rw [show m - x + 1 + x / 2 + 1 = 1 + (m - x + 1 + x / 2) by omega, Function.iterate_add_apply]
    simpa [hstepHalfHalf] using R2xy_half_half_even_generic (m := m) hxEven hx8 hxle2
  have hstepXSubThreeOne :
      (R2xy (m := m)^[m - x + 1 + x / 2 + 1 + (x / 2 - 3)])
          (linePoint (m := m) (((x : ℕ) : ZMod m))) =
        ((((x - 3 : ℕ) : ZMod m)), (1 : ZMod m)) := by
    rw [show m - x + 1 + x / 2 + 1 + (x / 2 - 3) =
      (x / 2 - 3) + (m - x + 1 + x / 2 + 1) by omega, Function.iterate_add_apply]
    simpa [hstepHalfSubTwo] using
      iterate_to_x_sub_three_one_even_generic (m := m) hxEven hx8 hxle2
  have hstepFinal :
      (R2xy (m := m)^[m - x + 1 + x / 2 + 1 + (x / 2 - 3) + 1])
          (linePoint (m := m) (((x : ℕ) : ZMod m))) =
        linePoint (m := m) (((x - 1 : ℕ) : ZMod m)) := by
    rw [show m - x + 1 + x / 2 + 1 + (x / 2 - 3) + 1 =
      1 + (m - x + 1 + x / 2 + 1 + (x / 2 - 3)) by omega, Function.iterate_add_apply]
    simpa [hstepXSubThreeOne] using R2xy_x_sub_three_one_even_generic (m := m) hx8 hxle2
  have hsplit : m = m - x + 1 + x / 2 + 1 + (x / 2 - 3) + 1 := by
    rw [← hdouble]
    omega
  calc
    (R2xy (m := m)^[rho2 (m := m) (((x : ℕ) : ZMod m))])
        (linePoint (m := m) (((x : ℕ) : ZMod m)))
        = (R2xy (m := m)^[m]) (linePoint (m := m) (((x : ℕ) : ZMod m))) := by rw [hrho]
    _ = (R2xy (m := m)^[m - x + 1 + x / 2 + 1 + (x / 2 - 3) + 1])
          (linePoint (m := m) (((x : ℕ) : ZMod m))) := by
            exact congrArg
              (fun n => (R2xy (m := m)^[n]) (linePoint (m := m) (((x : ℕ) : ZMod m))))
              hsplit
    _ = linePoint (m := m) (((x - 1 : ℕ) : ZMod m)) := hstepFinal
    _ = linePoint (m := m) (T2 (m := m) (((x : ℕ) : ZMod m))) := by rw [hT]

theorem hfirst_even_generic
    [Fact (Even m)] [Fact (7 < m)] {x : ℕ} (hxEven : Even x)
    (hx8 : 8 ≤ x) (hxle : x ≤ m - 4) :
    ∀ n, 0 < n → n < rho2 (m := m) (((x : ℕ) : ZMod m)) →
      (R2xy (m := m)^[n]) (linePoint (m := m) (((x : ℕ) : ZMod m))) ∉
        Set.range (linePoint (m := m))
  | n, hn0, hnlt => by
      have hm7 : 7 < m := Fact.out
      have hm0 : 0 < m := by omega
      have hm1 : 1 < m := by omega
      have hm2 : 2 < m := by omega
      letI : Fact (0 < m) := ⟨hm0⟩
      letI : Fact (1 < m) := ⟨hm1⟩
      letI : Fact (2 < m) := ⟨hm2⟩
      have hx0 : (((x : ℕ) : ZMod m)) ≠ 0 := by
        exact natCast_ne_zero_of_pos_lt (m := m) (n := x) (by omega) (by omega)
      have hx1 : (((x : ℕ) : ZMod m)) ≠ 1 := by
        exact natCast_ne_one_of_two_le_lt (m := m) (n := x) (by omega) (by omega)
      have hx2 : (((x : ℕ) : ZMod m)) ≠ 2 := by
        exact natCast_ne_two_of_three_le_lt (m := m) (n := x) (by omega) (by omega)
      have hrho : rho2 (m := m) (((x : ℕ) : ZMod m)) = m := by
        simp [rho2, hx0, hx1, hx2]
      have hnm : n < m := by rwa [hrho] at hnlt
      have hxle2 : x ≤ m - 2 := by
        omega
      by_cases h1 : n = 1
      · apply not_mem_range_linePoint_of_snd_ne_zero
        rw [h1]
        simpa [Function.iterate_one, R2xy_linePoint_even_generic_start (m := m) hx8 hxle] using
          (neg_ne_zero.mpr (one_ne_zero (m := m)))
      · by_cases hfront : n ≤ m - x
        · let t : ℕ := n - 2
          have ht : t ≤ m - x - 2 := by
            dsimp [t]
            omega
          have hnEq : n = t + 2 := by
            dsimp [t]
            omega
          have hiter :
              (R2xy (m := m)^[n]) (linePoint (m := m) (((x : ℕ) : ZMod m))) =
                ((((x + 1 : ℕ) : ZMod m)) + t, (-2 : ZMod m) - t) := by
            rw [hnEq]
            simpa using
              iterate_R2xy_from_linePoint_even_generic_after_two (m := m) hxEven hx8 hxle t ht
          apply not_mem_range_linePoint_of_snd_ne_zero
          rw [hiter]
          exact neg_two_sub_nat_ne_zero (m := m) (n := t) (by omega)
        · have hstepZeroX :
            (R2xy (m := m)^[m - x + 1]) (linePoint (m := m) (((x : ℕ) : ZMod m))) =
              ((0 : ZMod m), (((x : ℕ) : ZMod m))) := by
            have hstepMSubOne :
                (R2xy (m := m)^[m - x]) (linePoint (m := m) (((x : ℕ) : ZMod m))) =
                  ((((m - 1 : ℕ) : ZMod m)), (((x : ℕ) : ZMod m))) := by
              exact iterate_to_m_sub_one_even_generic (m := m) hxEven hx8 hxle
            rw [show m - x + 1 = 1 + (m - x) by omega, Function.iterate_add_apply]
            simp
            rw [hstepMSubOne]
            exact R2xy_m_sub_one_even_generic (m := m) hx8 hxle
          by_cases hzeroX : n = m - x + 1
          · apply not_mem_range_linePoint_of_snd_ne_zero
            rw [hzeroX, hstepZeroX]
            exact hx0
          · by_cases hmid : n ≤ m - x + 1 + x / 2
            · let t : ℕ := n - (m - x + 1)
              have ht : t ≤ x / 2 := by
                dsimp [t]
                omega
              have ht0 : 0 < t := by
                dsimp [t]
                omega
              have hnEq : n = m - x + 1 + t := by
                dsimp [t]
                omega
              have hiter :
                  (R2xy (m := m)^[n]) (linePoint (m := m) (((x : ℕ) : ZMod m))) =
                    ((((t : ℕ) : ZMod m)), (((x : ℕ) : ZMod m)) - t) := by
                rw [hnEq]
                rw [show m - x + 1 + t = t + (m - x + 1) by omega, Function.iterate_add_apply]
                simpa [hstepZeroX] using
                  iterate_R2xy_from_zero_even_generic (m := m) hxEven hx8 hxle2 t ht
              have hycast : (((x : ℕ) : ZMod m) - t) = (((x - t : ℕ) : ZMod m)) := by
                have htleX : t ≤ x := by omega
                rw [Nat.cast_sub htleX]
              have hy : (((x : ℕ) : ZMod m) - t) ≠ 0 := by
                rw [hycast]
                exact natCast_ne_zero_of_pos_lt (m := m) (n := x - t) (by omega) (by omega)
              apply not_mem_range_linePoint_of_snd_ne_zero
              rw [hiter]
              exact hy
            · have hstepHalfHalf :
                (R2xy (m := m)^[m - x + 1 + x / 2])
                    (linePoint (m := m) (((x : ℕ) : ZMod m))) =
                  ((((x / 2 : ℕ) : ZMod m)), (((x / 2 : ℕ) : ZMod m))) := by
                rw [show m - x + 1 + x / 2 = x / 2 + (m - x + 1) by omega,
                  Function.iterate_add_apply]
                simpa [hstepZeroX] using
                  iterate_to_half_half_even_generic (m := m) hxEven hx8 hxle2
              have hstepHalfSubTwo :
                  (R2xy (m := m)^[m - x + 1 + x / 2 + 1])
                      (linePoint (m := m) (((x : ℕ) : ZMod m))) =
                    ((((x / 2 : ℕ) : ZMod m)), (((x / 2 : ℕ) : ZMod m)) - 2) := by
                rw [show m - x + 1 + x / 2 + 1 = 1 + (m - x + 1 + x / 2) by omega,
                  Function.iterate_add_apply]
                simpa [hstepHalfHalf] using
                  R2xy_half_half_even_generic (m := m) hxEven hx8 hxle2
              have hdouble : x / 2 + x / 2 = x := by
                simpa [two_mul] using (Nat.two_mul_div_two_of_even hxEven)
              let t : ℕ := n - (m - x + 1 + x / 2 + 1)
              have ht : t ≤ x / 2 - 3 := by
                dsimp [t]
                omega
              have hnEq : n = m - x + 1 + x / 2 + 1 + t := by
                dsimp [t]
                omega
              have hiter :
                  (R2xy (m := m)^[n]) (linePoint (m := m) (((x : ℕ) : ZMod m))) =
                    ((((x / 2 : ℕ) : ZMod m)) + t, (((x / 2 : ℕ) : ZMod m)) - 2 - t) := by
                rw [hnEq]
                rw [show m - x + 1 + x / 2 + 1 + t =
                  t + (m - x + 1 + x / 2 + 1) by omega, Function.iterate_add_apply]
                simpa [hstepHalfSubTwo] using
                  iterate_R2xy_from_half_half_sub_two_even_generic (m := m) hxEven hx8 hxle2 t ht
              have hycast :
                  (((x / 2 : ℕ) : ZMod m) - 2 - t) = (((x / 2 - 2 - t : ℕ) : ZMod m)) := by
                have h2t : 2 + t ≤ x / 2 := by omega
                have hsub : x / 2 - t - 2 = x / 2 - 2 - t := by omega
                calc
                  (((x / 2 : ℕ) : ZMod m) - 2 - t)
                      = (((x / 2 : ℕ) : ZMod m) - (((2 + t : ℕ) : ZMod m))) := by
                          simp [Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
                  _ = (((x / 2 - (2 + t) : ℕ) : ZMod m)) := by rw [Nat.cast_sub h2t]
                  _ = (((x / 2 - t - 2 : ℕ) : ZMod m)) := by rw [Nat.add_comm 2 t, ← Nat.sub_sub]
                  _ = (((x / 2 - 2 - t : ℕ) : ZMod m)) := by
                        simpa using congrArg (fun s : ℕ => ((s : ℕ) : ZMod m)) hsub
              have hy : (((x / 2 : ℕ) : ZMod m) - 2 - t) ≠ 0 := by
                rw [hycast]
                exact natCast_ne_zero_of_pos_lt (m := m) (n := x / 2 - 2 - t) (by omega) (by omega)
              apply not_mem_range_linePoint_of_snd_ne_zero
              rw [hiter]
              exact hy

theorem R2xy_linePoint_m_sub_two [Fact (7 < m)] :
    R2xy (m := m) (linePoint (m := m) (((m - 2 : ℕ) : ZMod m))) =
      ((((m - 1 : ℕ) : ZMod m)), (-1 : ZMod m)) := by
  have hm7 : 7 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm1 : 1 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (1 < m) := ⟨hm1⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  have hA : linePoint (m := m) (((m - 2 : ℕ) : ZMod m)) ≠ ((2 : ZMod m), (2 : ZMod m)) := by
    intro h
    exact two_ne_zero (m := m) (by simpa [linePoint] using (congrArg Prod.snd h).symm)
  have hy1 : (0 : ZMod m) ≠ (1 : ZMod m) := (one_ne_zero (m := m)).symm
  have hyneg1 : (0 : ZMod m) ≠ (-1 : ZMod m) := by
    intro h
    exact neg_ne_zero.mpr (one_ne_zero (m := m)) h.symm
  have hdiag : (0 : ZMod m) ≠ (((m - 2 : ℕ) : ZMod m)) := by
    intro h
    exact natCast_ne_zero_of_pos_lt (m := m) (n := m - 2) (by omega) (by omega) h.symm
  have hxneg1 : (((m - 2 : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := m - 2) (by omega)
  have h00 : linePoint (m := m) (((m - 2 : ℕ) : ZMod m)) ≠ ((0 : ZMod m), (0 : ZMod m)) := by
    intro h
    exact natCast_ne_zero_of_pos_lt (m := m) (n := m - 2) (by omega) (by omega)
      (by simpa [linePoint] using congrArg Prod.fst h)
  calc
    R2xy (m := m) (linePoint (m := m) (((m - 2 : ℕ) : ZMod m)))
        = G (m := m) (linePoint (m := m) (((m - 2 : ℕ) : ZMod m))) := by
            simpa [linePoint] using R2xy_eq_G_of (m := m) hA hy1 hyneg1 hdiag hxneg1 h00
    _ = ((((m - 1 : ℕ) : ZMod m)), (-1 : ZMod m)) := by
          ext
          · calc
              (((m - 2 : ℕ) : ZMod m) + 1) = (((m - 2 : ℕ) : ZMod m) + (((1 : ℕ) : ZMod m))) := by
                  norm_num
              _ = (((m - 1 : ℕ) : ZMod m)) := by
                    rw [← Nat.cast_add]
                    congr
                    omega
          · simp [linePoint, G]

theorem R2xy_m_sub_one_neg_one [Fact (5 < m)] :
    R2xy (m := m) ((((m - 1 : ℕ) : ZMod m)), (-1 : ZMod m)) =
      ((0 : ZMod m), (-1 : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  have hm1 : 1 < m := by omega
  have hm1le : 1 ≤ m := by omega
  letI : Fact (1 < m) := ⟨hm1⟩
  have hneg1 : (((m - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) := cast_sub_one_eq_neg_one (m := m) hm1le
  have hy0 : (-1 : ZMod m) ≠ (0 : ZMod m) := neg_ne_zero.mpr (one_ne_zero (m := m))
  have hyneg2 : (-1 : ZMod m) ≠ (-2 : ZMod m) := by
    intro h
    have hzero : (1 : ZMod m) = 0 := by
      calc
        (1 : ZMod m) = (-1 : ZMod m) + 2 := by ring
        _ = (-2 : ZMod m) + 2 := by rw [h]
        _ = 0 := by ring
    exact one_ne_zero (m := m) hzero
  calc
    R2xy (m := m) ((((m - 1 : ℕ) : ZMod m)), (-1 : ZMod m))
        = R2xy (m := m) ((-1 : ZMod m), (-1 : ZMod m)) := by rw [hneg1]
    _ = ((0 : ZMod m), (-1 : ZMod m)) := by
          simpa using R2xy_eq_E_of (m := m) (y := (-1 : ZMod m)) hy0 hyneg2

theorem R2xy_zero_neg_one [Fact (2 < m)] :
    R2xy (m := m) ((0 : ZMod m), (-1 : ZMod m)) = ((0 : ZMod m), (-2 : ZMod m)) := by
  have hm2 : 2 < m := Fact.out
  have hm1 : 1 < m := by omega
  letI : Fact (1 < m) := ⟨hm1⟩
  have h0neg1 : (0 : ZMod m) ≠ (-1 : ZMod m) := by
    intro h
    exact neg_ne_zero.mpr (one_ne_zero (m := m)) h.symm
  simpa using R2xy_eq_C_of (m := m) (x := (0 : ZMod m)) h0neg1

theorem iterate_three_to_zero_m_sub_two [Fact (7 < m)] :
    (R2xy (m := m)^[3]) (linePoint (m := m) (((m - 2 : ℕ) : ZMod m))) =
      ((0 : ZMod m), (((m - 2 : ℕ) : ZMod m))) := by
  have hm7 : 7 < m := Fact.out
  have hm5 : 5 < m := by omega
  have hm2 : 2 < m := by omega
  have hm2le : 2 ≤ m := by omega
  letI : Fact (5 < m) := ⟨hm5⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  calc
    (R2xy (m := m)^[3]) (linePoint (m := m) (((m - 2 : ℕ) : ZMod m)))
        = R2xy (m := m)
            (R2xy (m := m)
              (R2xy (m := m) (linePoint (m := m) (((m - 2 : ℕ) : ZMod m))))) := by simp
    _ = R2xy (m := m) (R2xy (m := m) ((((m - 1 : ℕ) : ZMod m)), (-1 : ZMod m))) := by
          rw [R2xy_linePoint_m_sub_two (m := m)]
    _ = R2xy (m := m) ((0 : ZMod m), (-1 : ZMod m)) := by rw [R2xy_m_sub_one_neg_one (m := m)]
    _ = ((0 : ZMod m), (-2 : ZMod m)) := R2xy_zero_neg_one (m := m)
    _ = ((0 : ZMod m), (((m - 2 : ℕ) : ZMod m))) := by rw [cast_sub_two_eq_neg_two (m := m) hm2le]

theorem firstReturn_m_sub_two_of_ge_ten [Fact (Even m)] [Fact (9 < m)] :
    (R2xy (m := m)^[rho2 (m := m) (((m - 2 : ℕ) : ZMod m))])
        (linePoint (m := m) (((m - 2 : ℕ) : ZMod m))) =
      linePoint (m := m) (T2 (m := m) (((m - 2 : ℕ) : ZMod m))) := by
  have hm9 : 9 < m := Fact.out
  have hm7 : 7 < m := by omega
  have hm0 : 0 < m := by omega
  have hm1 : 1 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (7 < m) := ⟨hm7⟩
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (1 < m) := ⟨hm1⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  have hmEven : Even m := Fact.out
  have hxEven : Even (m - 2) := by
    rcases hmEven with ⟨k, hk⟩
    use k - 1
    omega
  have hx8 : 8 ≤ m - 2 := by omega
  have hx0 : (((m - 2 : ℕ) : ZMod m)) ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := m - 2) (by omega) (by omega)
  have hx1 : (((m - 2 : ℕ) : ZMod m)) ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := m - 2) (by omega) (by omega)
  have hx2 : (((m - 2 : ℕ) : ZMod m)) ≠ 2 := by
    exact natCast_ne_two_of_three_le_lt (m := m) (n := m - 2) (by omega) (by omega)
  have hrho : rho2 (m := m) (((m - 2 : ℕ) : ZMod m)) = m := by
    simp [rho2, hx0, hx1, hx2]
  have hT : T2 (m := m) (((m - 2 : ℕ) : ZMod m)) = (((m - 3 : ℕ) : ZMod m)) := by
    calc
      T2 (m := m) (((m - 2 : ℕ) : ZMod m)) = (((m - 2 : ℕ) : ZMod m)) - 1 := by
        simp [T2, hx0, hx1, hx2]
      _ = (((m - 3 : ℕ) : ZMod m)) := by
        symm
        simpa using (Nat.cast_sub (R := ZMod m) (m := 1) (n := m - 2) (by omega))
  have hdouble : (m - 2) / 2 + (m - 2) / 2 = m - 2 := by
    simpa [two_mul] using (Nat.two_mul_div_two_of_even hxEven)
  have hstepZero :
      (R2xy (m := m)^[3]) (linePoint (m := m) (((m - 2 : ℕ) : ZMod m))) =
        ((0 : ZMod m), (((m - 2 : ℕ) : ZMod m))) := by
    exact iterate_three_to_zero_m_sub_two (m := m)
  have hstepHalfHalf :
      (R2xy (m := m)^[3 + (m - 2) / 2]) (linePoint (m := m) (((m - 2 : ℕ) : ZMod m))) =
        ((((m - 2) / 2 : ℕ) : ZMod m), ((((m - 2) / 2 : ℕ) : ZMod m))) := by
    rw [show 3 + (m - 2) / 2 = (m - 2) / 2 + 3 by omega, Function.iterate_add_apply]
    simpa [hstepZero] using
      iterate_to_half_half_even_generic (m := m) (x := m - 2) hxEven hx8 le_rfl
  have hstepHalfSubTwo :
      (R2xy (m := m)^[3 + (m - 2) / 2 + 1]) (linePoint (m := m) (((m - 2 : ℕ) : ZMod m))) =
        ((((m - 2) / 2 : ℕ) : ZMod m), ((((m - 2) / 2 : ℕ) : ZMod m)) - 2) := by
    rw [show 3 + (m - 2) / 2 + 1 = 1 + (3 + (m - 2) / 2) by omega, Function.iterate_add_apply]
    simpa [hstepHalfHalf] using
      R2xy_half_half_even_generic (m := m) (x := m - 2) hxEven hx8 le_rfl
  have hstepMSubFiveOne :
      (R2xy (m := m)^[3 + (m - 2) / 2 + 1 + ((m - 2) / 2 - 3)])
          (linePoint (m := m) (((m - 2 : ℕ) : ZMod m))) =
        ((((m - 5 : ℕ) : ZMod m)), (1 : ZMod m)) := by
    rw [show 3 + (m - 2) / 2 + 1 + ((m - 2) / 2 - 3) =
      ((m - 2) / 2 - 3) + (3 + (m - 2) / 2 + 1) by omega, Function.iterate_add_apply]
    simpa [hstepHalfSubTwo] using
      iterate_to_x_sub_three_one_even_generic (m := m) (x := m - 2) hxEven hx8 le_rfl
  have hstepFinal :
      (R2xy (m := m)^[3 + (m - 2) / 2 + 1 + ((m - 2) / 2 - 3) + 1])
          (linePoint (m := m) (((m - 2 : ℕ) : ZMod m))) =
        linePoint (m := m) (((m - 3 : ℕ) : ZMod m)) := by
    rw [show 3 + (m - 2) / 2 + 1 + ((m - 2) / 2 - 3) + 1 =
      1 + (3 + (m - 2) / 2 + 1 + ((m - 2) / 2 - 3)) by omega, Function.iterate_add_apply]
    simpa [hstepMSubFiveOne] using
      R2xy_x_sub_three_one_even_generic (m := m) (x := m - 2) hx8 le_rfl
  have hsplit : m = 3 + (m - 2) / 2 + 1 + ((m - 2) / 2 - 3) + 1 := by
    rw [← hdouble]
    omega
  calc
    (R2xy (m := m)^[rho2 (m := m) (((m - 2 : ℕ) : ZMod m))])
        (linePoint (m := m) (((m - 2 : ℕ) : ZMod m)))
        = (R2xy (m := m)^[m]) (linePoint (m := m) (((m - 2 : ℕ) : ZMod m))) := by rw [hrho]
    _ = (R2xy (m := m)^[3 + (m - 2) / 2 + 1 + ((m - 2) / 2 - 3) + 1])
          (linePoint (m := m) (((m - 2 : ℕ) : ZMod m))) := by
            exact congrArg
              (fun n => (R2xy (m := m)^[n]) (linePoint (m := m) (((m - 2 : ℕ) : ZMod m))))
              hsplit
    _ = linePoint (m := m) (((m - 3 : ℕ) : ZMod m)) := hstepFinal
    _ = linePoint (m := m) (T2 (m := m) (((m - 2 : ℕ) : ZMod m))) := by rw [hT]

theorem hfirst_m_sub_two_of_ge_ten [Fact (Even m)] [Fact (9 < m)] :
    ∀ n, 0 < n → n < rho2 (m := m) (((m - 2 : ℕ) : ZMod m)) →
      (R2xy (m := m)^[n]) (linePoint (m := m) (((m - 2 : ℕ) : ZMod m))) ∉
        Set.range (linePoint (m := m))
  | n, hn0, hnlt => by
      have hm9 : 9 < m := Fact.out
      have hm7 : 7 < m := by omega
      have hm5 : 5 < m := by omega
      have hm0 : 0 < m := by omega
      have hm1 : 1 < m := by omega
      have hm2 : 2 < m := by omega
      letI : Fact (7 < m) := ⟨hm7⟩
      letI : Fact (5 < m) := ⟨hm5⟩
      letI : Fact (0 < m) := ⟨hm0⟩
      letI : Fact (1 < m) := ⟨hm1⟩
      letI : Fact (2 < m) := ⟨hm2⟩
      have hmEven : Even m := Fact.out
      have hxEven : Even (m - 2) := by
        rcases hmEven with ⟨k, hk⟩
        use k - 1
        omega
      have hx8 : 8 ≤ m - 2 := by omega
      have hx0 : (((m - 2 : ℕ) : ZMod m)) ≠ 0 := by
        exact natCast_ne_zero_of_pos_lt (m := m) (n := m - 2) (by omega) (by omega)
      have hx1 : (((m - 2 : ℕ) : ZMod m)) ≠ 1 := by
        exact natCast_ne_one_of_two_le_lt (m := m) (n := m - 2) (by omega) (by omega)
      have hx2 : (((m - 2 : ℕ) : ZMod m)) ≠ 2 := by
        exact natCast_ne_two_of_three_le_lt (m := m) (n := m - 2) (by omega) (by omega)
      have hrho : rho2 (m := m) (((m - 2 : ℕ) : ZMod m)) = m := by
        simp [rho2, hx0, hx1, hx2]
      have hnm : n < m := by rwa [hrho] at hnlt
      by_cases h1 : n = 1
      · apply not_mem_range_linePoint_of_snd_ne_zero
        rw [h1]
        simpa [Function.iterate_one, R2xy_linePoint_m_sub_two (m := m)] using
          (neg_ne_zero.mpr (one_ne_zero (m := m)))
      · by_cases h2 : n = 2
        · apply not_mem_range_linePoint_of_snd_ne_zero
          rw [h2]
          have hiter :
              (R2xy (m := m)^[2]) (linePoint (m := m) (((m - 2 : ℕ) : ZMod m))) =
                ((0 : ZMod m), (-1 : ZMod m)) := by
            calc
            (R2xy (m := m)^[2]) (linePoint (m := m) (((m - 2 : ℕ) : ZMod m)))
                = R2xy (m := m)
                    (R2xy (m := m) (linePoint (m := m) (((m - 2 : ℕ) : ZMod m)))) := by simp
            _ = R2xy (m := m) ((((m - 1 : ℕ) : ZMod m)), (-1 : ZMod m)) := by
                  rw [R2xy_linePoint_m_sub_two (m := m)]
            _ = ((0 : ZMod m), (-1 : ZMod m)) := R2xy_m_sub_one_neg_one (m := m)
          rw [hiter]
          exact neg_ne_zero.mpr (one_ne_zero (m := m))
        · have hstepZero :
            (R2xy (m := m)^[3]) (linePoint (m := m) (((m - 2 : ℕ) : ZMod m))) =
              ((0 : ZMod m), (((m - 2 : ℕ) : ZMod m))) := by
            exact iterate_three_to_zero_m_sub_two (m := m)
          by_cases hmid : n ≤ 3 + (m - 2) / 2
          · let t : ℕ := n - 3
            have ht : t ≤ (m - 2) / 2 := by
              dsimp [t]
              omega
            have hnEq : n = 3 + t := by
              dsimp [t]
              omega
            have hiter :
                (R2xy (m := m)^[n]) (linePoint (m := m) (((m - 2 : ℕ) : ZMod m))) =
                  ((((t : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m)) - t) := by
              rw [hnEq]
              rw [show 3 + t = t + 3 by omega, Function.iterate_add_apply]
              simpa [hstepZero] using
                iterate_R2xy_from_zero_even_generic (m := m) (x := m - 2) hxEven hx8 le_rfl t ht
            have hycast :
                (((m - 2 : ℕ) : ZMod m) - t) = (((m - 2 - t : ℕ) : ZMod m)) := by
              have htle : t ≤ m - 2 := by omega
              rw [Nat.cast_sub htle]
            have hy : (((m - 2 : ℕ) : ZMod m) - t) ≠ 0 := by
              rw [hycast]
              exact natCast_ne_zero_of_pos_lt (m := m) (n := m - 2 - t) (by omega) (by omega)
            apply not_mem_range_linePoint_of_snd_ne_zero
            rw [hiter]
            exact hy
          · have hstepHalfHalf :
                (R2xy (m := m)^[3 + (m - 2) / 2]) (linePoint (m := m) (((m - 2 : ℕ) : ZMod m))) =
                  ((((m - 2) / 2 : ℕ) : ZMod m), ((((m - 2) / 2 : ℕ) : ZMod m))) := by
              rw [show 3 + (m - 2) / 2 = (m - 2) / 2 + 3 by omega, Function.iterate_add_apply]
              simpa [hstepZero] using
                iterate_to_half_half_even_generic (m := m) (x := m - 2) hxEven hx8 le_rfl
            have hstepHalfSubTwo :
                (R2xy (m := m)^[3 + (m - 2) / 2 + 1])
                    (linePoint (m := m) (((m - 2 : ℕ) : ZMod m))) =
                  ((((m - 2) / 2 : ℕ) : ZMod m), ((((m - 2) / 2 : ℕ) : ZMod m)) - 2) := by
              rw [show 3 + (m - 2) / 2 + 1 = 1 + (3 + (m - 2) / 2) by omega,
                Function.iterate_add_apply]
              simpa [hstepHalfHalf] using
                R2xy_half_half_even_generic (m := m) (x := m - 2) hxEven hx8 le_rfl
            have hdouble : (m - 2) / 2 + (m - 2) / 2 = m - 2 := by
              simpa [two_mul] using (Nat.two_mul_div_two_of_even hxEven)
            let t : ℕ := n - (3 + (m - 2) / 2 + 1)
            have ht : t ≤ (m - 2) / 2 - 3 := by
              dsimp [t]
              omega
            have hnEq : n = 3 + (m - 2) / 2 + 1 + t := by
              dsimp [t]
              omega
            have hiter :
                (R2xy (m := m)^[n]) (linePoint (m := m) (((m - 2 : ℕ) : ZMod m))) =
                  ((((m - 2) / 2 : ℕ) : ZMod m) + t,
                    ((((m - 2) / 2 : ℕ) : ZMod m)) - 2 - t) := by
              rw [hnEq]
              rw [show 3 + (m - 2) / 2 + 1 + t = t + (3 + (m - 2) / 2 + 1) by omega,
                Function.iterate_add_apply]
              simpa [hstepHalfSubTwo] using
                iterate_R2xy_from_half_half_sub_two_even_generic (m := m)
                  (x := m - 2) hxEven hx8 le_rfl t ht
            have hycast :
                ((((m - 2) / 2 : ℕ) : ZMod m) - 2 - t) =
                  (((((m - 2) / 2) - 2 - t : ℕ) : ZMod m)) := by
              have h2t : 2 + t ≤ (m - 2) / 2 := by omega
              have hsub : (m - 2) / 2 - t - 2 = (m - 2) / 2 - 2 - t := by omega
              calc
                ((((m - 2) / 2 : ℕ) : ZMod m) - 2 - t)
                    = ((((m - 2) / 2 : ℕ) : ZMod m) - (((2 + t : ℕ) : ZMod m))) := by
                        simp [Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
                _ = (((((m - 2) / 2) - (2 + t) : ℕ) : ZMod m)) := by rw [Nat.cast_sub h2t]
                _ = (((((m - 2) / 2) - t - 2 : ℕ) : ZMod m)) := by rw [Nat.add_comm 2 t, ← Nat.sub_sub]
                _ = (((((m - 2) / 2) - 2 - t : ℕ) : ZMod m)) := by
                      simpa using congrArg (fun s : ℕ => ((s : ℕ) : ZMod m)) hsub
            have hy : ((((m - 2) / 2 : ℕ) : ZMod m) - 2 - t) ≠ 0 := by
              rw [hycast]
              exact natCast_ne_zero_of_pos_lt (m := m) (n := ((m - 2) / 2) - 2 - t) (by omega) (by omega)
            apply not_mem_range_linePoint_of_snd_ne_zero
            rw [hiter]
            exact hy

theorem firstReturn_m_sub_two [Fact (Even m)] [Fact (7 < m)] :
    (R2xy (m := m)^[rho2 (m := m) (((m - 2 : ℕ) : ZMod m))])
        (linePoint (m := m) (((m - 2 : ℕ) : ZMod m))) =
      linePoint (m := m) (T2 (m := m) (((m - 2 : ℕ) : ZMod m))) := by
  by_cases hm8 : m = 8
  · subst hm8
    simpa using firstReturn_six_m8
  · have hmEven : Even m := by
      have hinst : Fact (Even m) := inferInstance
      exact hinst.out
    have hm7 : 7 < m := by
      have hinst : Fact (7 < m) := inferInstance
      exact hinst.out
    have hm10 : 9 < m := by
      rcases hmEven with ⟨k, hk⟩
      omega
    letI : Fact (9 < m) := ⟨hm10⟩
    exact firstReturn_m_sub_two_of_ge_ten (m := m)

theorem hfirst_m_sub_two [Fact (Even m)] [Fact (7 < m)] :
    ∀ n, 0 < n → n < rho2 (m := m) (((m - 2 : ℕ) : ZMod m)) →
      (R2xy (m := m)^[n]) (linePoint (m := m) (((m - 2 : ℕ) : ZMod m))) ∉
        Set.range (linePoint (m := m))
  | n, hn0, hnlt => by
      by_cases hm8 : m = 8
      · subst hm8
        exact hfirst_six_m8 n hn0 (by simpa using hnlt)
      · have hmEven : Even m := by
          have hinst : Fact (Even m) := inferInstance
          exact hinst.out
        have hm7 : 7 < m := by
          have hinst : Fact (7 < m) := inferInstance
          exact hinst.out
        have hm10 : 9 < m := by
          rcases hmEven with ⟨k, hk⟩
          omega
        letI : Fact (9 < m) := ⟨hm10⟩
        exact hfirst_m_sub_two_of_ge_ten (m := m) n hn0 hnlt

theorem R2xy_linePoint_odd_generic_start [Fact (5 < m)] {x : ℕ}
    (hx3 : 3 ≤ x) (hxle : x ≤ m - 3) :
    R2xy (m := m) (linePoint (m := m) (((x : ℕ) : ZMod m))) =
      ((((x + 1 : ℕ) : ZMod m)), (-1 : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm1 : 1 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (1 < m) := ⟨hm1⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  have hA : linePoint (m := m) (((x : ℕ) : ZMod m)) ≠ ((2 : ZMod m), (2 : ZMod m)) := by
    intro h
    exact two_ne_zero (m := m) (by simpa [linePoint] using (congrArg Prod.snd h).symm)
  have hy1 : (0 : ZMod m) ≠ (1 : ZMod m) := (one_ne_zero (m := m)).symm
  have hyneg1 : (0 : ZMod m) ≠ (-1 : ZMod m) := by
    intro h
    exact neg_ne_zero.mpr (one_ne_zero (m := m)) h.symm
  have hdiag : (0 : ZMod m) ≠ (((x : ℕ) : ZMod m)) := by
    intro h
    exact natCast_ne_zero_of_pos_lt (m := m) (n := x) (by omega) (by omega) h.symm
  have hxneg1 : (((x : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := x) (by omega)
  have h00 : linePoint (m := m) (((x : ℕ) : ZMod m)) ≠ ((0 : ZMod m), (0 : ZMod m)) := by
    intro h
    exact natCast_ne_zero_of_pos_lt (m := m) (n := x) (by omega) (by omega)
      (by simpa [linePoint] using congrArg Prod.fst h)
  calc
    R2xy (m := m) (linePoint (m := m) (((x : ℕ) : ZMod m)))
        = G (m := m) (linePoint (m := m) (((x : ℕ) : ZMod m))) := by
            simpa [linePoint] using R2xy_eq_G_of (m := m) hA hy1 hyneg1 hdiag hxneg1 h00
    _ = ((((x + 1 : ℕ) : ZMod m)), (-1 : ZMod m)) := by
          ext <;> simp [linePoint, G, Nat.cast_add] <;> ring

theorem R2xy_odd_generic_succ_neg_one [Fact (5 < m)] {x : ℕ}
    (hx3 : 3 ≤ x) (hxle : x ≤ m - 3) :
    R2xy (m := m) ((((x + 1 : ℕ) : ZMod m)), (-1 : ZMod m)) =
      ((((x + 1 : ℕ) : ZMod m)), (-2 : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  have hxneg1 : (((x + 1 : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := x + 1) (by omega)
  simpa using R2xy_eq_C_of (m := m) (x := (((x + 1 : ℕ) : ZMod m))) hxneg1

theorem iterate_two_from_linePoint_odd_generic [Fact (5 < m)] {x : ℕ}
    (hx3 : 3 ≤ x) (hxle : x ≤ m - 3) :
    (R2xy (m := m)^[2]) (linePoint (m := m) (((x : ℕ) : ZMod m))) =
      ((((x + 1 : ℕ) : ZMod m)), (-2 : ZMod m)) := by
  calc
    (R2xy (m := m)^[2]) (linePoint (m := m) (((x : ℕ) : ZMod m)))
        = R2xy (m := m) (R2xy (m := m) (linePoint (m := m) (((x : ℕ) : ZMod m)))) := by simp
    _ = R2xy (m := m) ((((x + 1 : ℕ) : ZMod m)), (-1 : ZMod m)) := by
          rw [R2xy_linePoint_odd_generic_start (m := m) hx3 hxle]
    _ = ((((x + 1 : ℕ) : ZMod m)), (-2 : ZMod m)) := by
          rw [R2xy_odd_generic_succ_neg_one (m := m) hx3 hxle]

theorem iterate_R2xy_from_odd_generic_succ_neg_two
    [Fact (Even m)] [Fact (5 < m)] {x : ℕ} (hx3 : 3 ≤ x) (hxle : x ≤ m - 3) :
    ∀ n, n ≤ (m - x - 3) / 2 →
      (R2xy (m := m)^[n]) ((((x + 1 : ℕ) : ZMod m)), (-2 : ZMod m)) =
        ((((x + 1 : ℕ) : ZMod m)) + n, (-2 : ZMod m) - n)
  | 0, _ => by simp
  | n + 1, hn => by
      have hm5 : 5 < m := Fact.out
      have hm0 : 0 < m := by omega
      have hm1 : 1 < m := by omega
      have hm2 : 2 < m := by omega
      letI : Fact (0 < m) := ⟨hm0⟩
      letI : Fact (1 < m) := ⟨hm1⟩
      letI : Fact (2 < m) := ⟨hm2⟩
      have hn' : n < (m - x - 3) / 2 := Nat.lt_of_succ_le hn
      have hx_lt : x + 1 + n < m := by omega
      have hy_lt : m - 2 - n < m := by omega
      have xcast : ((((x + 1 : ℕ) : ZMod m)) + n) = (((x + 1 + n : ℕ) : ZMod m)) := by
        simpa [Nat.cast_add, add_assoc] using (Nat.cast_add (x + 1) n).symm
      have ycast : ((-2 : ZMod m) - n) = (((m - 2 - n : ℕ) : ZMod m)) := by
        have hnle : n ≤ m - 2 := by omega
        have hm2le : 2 ≤ m := by omega
        calc
          (-2 : ZMod m) - n = (((m - 2 : ℕ) : ZMod m)) - n := by
            rw [cast_sub_two_eq_neg_two (m := m) hm2le]
          _ = (((m - 2 - n : ℕ) : ZMod m)) := by rw [Nat.cast_sub hnle]
      have hA :
          ((((x + 1 : ℕ) : ZMod m)) + n, (-2 : ZMod m) - n) ≠ ((2 : ZMod m), (2 : ZMod m)) := by
        intro hEq
        have hfst : (((x + 1 + n : ℕ) : ZMod m)) = ((2 : ℕ) : ZMod m) := by
          calc
            (((x + 1 + n : ℕ) : ZMod m)) = ((((x + 1 : ℕ) : ZMod m)) + n) := by rw [xcast]
            _ = (2 : ZMod m) := congrArg Prod.fst hEq
            _ = ((2 : ℕ) : ZMod m) := by norm_num
        exact natCast_ne_two_of_three_le_lt (m := m) (n := x + 1 + n) (by omega) hx_lt hfst
      have hy1 : (-2 : ZMod m) - n ≠ (1 : ZMod m) := by
        rw [ycast]
        exact natCast_ne_one_of_two_le_lt (m := m) (n := m - 2 - n) (by omega) hy_lt
      have hyneg1 : (-2 : ZMod m) - n ≠ (-1 : ZMod m) := by
        rw [ycast]
        exact natCast_ne_neg_one_of_lt (m := m) (n := m - 2 - n) (by omega)
      have hdiag : (-2 : ZMod m) - n ≠ ((((x + 1 : ℕ) : ZMod m)) + n) := by
        intro hEq
        have hnatEq : m - 2 - n = x + 1 + n := by
          have hcast : (((m - 2 - n : ℕ) : ZMod m)) = (((x + 1 + n : ℕ) : ZMod m)) := by
            rw [ycast, xcast] at hEq
            exact hEq
          exact (natCast_eq_natCast_iff_of_lt (m := m) (a := m - 2 - n) (b := x + 1 + n)
            hy_lt hx_lt).1 hcast
        omega
      have hxneg1 : ((((x + 1 : ℕ) : ZMod m)) + n) ≠ (-1 : ZMod m) := by
        rw [xcast]
        exact natCast_ne_neg_one_of_lt (m := m) (n := x + 1 + n) (by omega)
      have h00 :
          ((((x + 1 : ℕ) : ZMod m)) + n, (-2 : ZMod m) - n) ≠ ((0 : ZMod m), (0 : ZMod m)) := by
        intro hEq
        have hfst : (((x + 1 + n : ℕ) : ZMod m)) = 0 := by
          calc
            (((x + 1 + n : ℕ) : ZMod m)) = ((((x + 1 : ℕ) : ZMod m)) + n) := by rw [xcast]
            _ = 0 := congrArg Prod.fst hEq
        exact natCast_ne_zero_of_pos_lt (m := m) (n := x + 1 + n) (by omega) hx_lt hfst
      rw [Function.iterate_succ_apply',
        iterate_R2xy_from_odd_generic_succ_neg_two (m := m) hx3 hxle n (Nat.le_of_succ_le hn)]
      rw [R2xy_eq_G_of (m := m) hA hy1 hyneg1 hdiag hxneg1 h00]
      ext <;> simp [G, Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] <;> ring

theorem iterate_to_diag_odd_generic
    [Fact (Even m)] [Fact (5 < m)] {x : ℕ} (hxOdd : Odd x) (hx3 : 3 ≤ x) (hxle : x ≤ m - 3) :
    (R2xy (m := m)^[(m - x - 3) / 2]) ((((x + 1 : ℕ) : ZMod m)), (-2 : ZMod m)) =
      (((((x + m - 1) / 2 : ℕ) : ZMod m)), ((((x + m - 1) / 2 : ℕ) : ZMod m))) := by
  have hm5 : 5 < m := Fact.out
  have hm2le : 2 ≤ m := by omega
  rw [iterate_R2xy_from_odd_generic_succ_neg_two (m := m) hx3 hxle ((m - x - 3) / 2) le_rfl]
  ext
  · calc
      ((((x + 1 : ℕ) : ZMod m)) + ((((m - x - 3) / 2 : ℕ) : ZMod m)))
          = (((x + 1 + (m - x - 3) / 2 : ℕ) : ZMod m)) := by rw [← Nat.cast_add]
      _ = (((((x + m - 1) / 2 : ℕ) : ℕ) : ZMod m)) := by
            rcases hxOdd with ⟨k, hk⟩
            congr
            omega
  · have hmEven : Even m := Fact.out
    have hnle : (m - x - 3) / 2 ≤ m - 2 := by omega
    have hdiagNat : m - 2 - (m - x - 3) / 2 = x + 1 + (m - x - 3) / 2 := by
      rcases hmEven with ⟨j, hj⟩
      rcases hxOdd with ⟨k, hk⟩
      omega
    calc
      (-2 : ZMod m) - ((((m - x - 3) / 2 : ℕ) : ZMod m))
          = (((m - 2 : ℕ) : ZMod m)) - ((((m - x - 3) / 2 : ℕ) : ZMod m)) := by
              rw [cast_sub_two_eq_neg_two (m := m) hm2le]
      _ = (((m - 2 - (m - x - 3) / 2 : ℕ) : ZMod m)) := by rw [Nat.cast_sub hnle]
      _ = (((x + 1 + (m - x - 3) / 2 : ℕ) : ZMod m)) := by
            simpa using congrArg (fun t : ℕ => ((t : ℕ) : ZMod m)) hdiagNat
      _ = (((((x + m - 1) / 2 : ℕ) : ℕ) : ZMod m)) := by
            rcases hxOdd with ⟨k, hk⟩
            congr
            omega

theorem R2xy_diag_odd_generic
    [Fact (Even m)] [Fact (5 < m)] {x : ℕ} (hxOdd : Odd x) (hx3 : 3 ≤ x) (hxle : x ≤ m - 3) :
    R2xy (m := m)
        (((((x + m - 1) / 2 : ℕ) : ZMod m)), ((((x + m - 1) / 2 : ℕ) : ZMod m))) =
      (((((x + m - 1) / 2 : ℕ) : ZMod m)), ((((x + m - 1) / 2 : ℕ) : ZMod m)) - 2) := by
  have hm5 : 5 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  have hd0 : (((((x + m - 1) / 2 : ℕ) : ℕ) : ZMod m)) ≠ 0 := by
    rcases hxOdd with ⟨k, hk⟩
    exact natCast_ne_zero_of_pos_lt (m := m) (n := (x + m - 1) / 2) (by omega) (by omega)
  have hd2 : (((((x + m - 1) / 2 : ℕ) : ℕ) : ZMod m)) ≠ 2 := by
    rcases hxOdd with ⟨k, hk⟩
    exact natCast_ne_two_of_three_le_lt (m := m) (n := (x + m - 1) / 2) (by omega) (by omega)
  have hdneg1 : (((((x + m - 1) / 2 : ℕ) : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
    rcases hxOdd with ⟨k, hk⟩
    exact natCast_ne_neg_one_of_lt (m := m) (n := (x + m - 1) / 2) (by omega)
  simpa using R2xy_eq_D_of (m := m) hd0 hd2 hdneg1

theorem iterate_R2xy_from_diag_odd_generic_sub_two
    [Fact (Even m)] [Fact (5 < m)] {x : ℕ} (hxOdd : Odd x) (hx3 : 3 ≤ x) (hxle : x ≤ m - 3) :
    ∀ n, n ≤ (m - x - 1) / 2 →
      (R2xy (m := m)^[n])
          (((((x + m - 1) / 2 : ℕ) : ZMod m)), ((((x + m - 1) / 2 : ℕ) : ZMod m)) - 2) =
        (((((x + m - 1) / 2 : ℕ) : ZMod m)) + n,
          ((((x + m - 1) / 2 : ℕ) : ZMod m)) - 2 - n)
  | 0, _ => by simp
  | n + 1, hn => by
      have hm5 : 5 < m := Fact.out
      have hmEven : Even m := Fact.out
      have hm0 : 0 < m := by omega
      have hm1 : 1 < m := by omega
      have hm2 : 2 < m := by omega
      letI : Fact (0 < m) := ⟨hm0⟩
      letI : Fact (1 < m) := ⟨hm1⟩
      letI : Fact (2 < m) := ⟨hm2⟩
      let d : ℕ := (x + m - 1) / 2
      have hn' : n < (m - x - 1) / 2 := Nat.lt_of_succ_le hn
      have hd_lt : d + n < m := by
        dsimp [d]
        rcases hmEven with ⟨j, hj⟩
        rcases hxOdd with ⟨k, hk⟩
        omega
      have hdn1_lt : d + n + 1 < m := by
        dsimp [d]
        rcases hmEven with ⟨j, hj⟩
        rcases hxOdd with ⟨k, hk⟩
        omega
      have hy_lt : d - 2 - n < m := by
        dsimp [d]
        omega
      have xcast :
          ((((d : ℕ) : ZMod m)) + n) = (((d + n : ℕ) : ZMod m)) := by
        simpa [Nat.cast_add, add_assoc] using (Nat.cast_add d n).symm
      have ycast :
          ((((d : ℕ) : ZMod m)) - 2 - n) = (((d - 2 - n : ℕ) : ZMod m)) := by
        have h2n : 2 + n ≤ d := by
          dsimp [d]
          rcases hmEven with ⟨j, hj⟩
          rcases hxOdd with ⟨k, hk⟩
          omega
        have hsub : d - n - 2 = d - 2 - n := by omega
        calc
          ((((d : ℕ) : ZMod m)) - 2 - n)
              = ((((d : ℕ) : ZMod m)) - (((2 + n : ℕ) : ZMod m))) := by
                  simp [Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          _ = (((d - (2 + n) : ℕ) : ZMod m)) := by rw [Nat.cast_sub h2n]
          _ = (((d - n - 2 : ℕ) : ZMod m)) := by rw [Nat.add_comm 2 n, ← Nat.sub_sub]
          _ = (((d - 2 - n : ℕ) : ZMod m)) := by
                simpa using congrArg (fun s : ℕ => ((s : ℕ) : ZMod m)) hsub
      have hA :
          ((((d : ℕ) : ZMod m)) + n, ((((d : ℕ) : ZMod m)) - 2 - n)) ≠
            ((2 : ZMod m), (2 : ZMod m)) := by
        intro hEq
        have hfst : (((d + n : ℕ) : ZMod m)) = ((2 : ℕ) : ZMod m) := by
          calc
            (((d + n : ℕ) : ZMod m)) = ((((d : ℕ) : ZMod m)) + n) := by rw [xcast]
            _ = (2 : ZMod m) := congrArg Prod.fst hEq
            _ = ((2 : ℕ) : ZMod m) := by norm_num
        exact natCast_ne_two_of_three_le_lt (m := m) (n := d + n) (by omega) hd_lt hfst
      have hy1 : ((((d : ℕ) : ZMod m)) - 2 - n) ≠ (1 : ZMod m) := by
        rw [ycast]
        exact natCast_ne_one_of_two_le_lt (m := m) (n := d - 2 - n) (by omega) hy_lt
      have hyneg1 : ((((d : ℕ) : ZMod m)) - 2 - n) ≠ (-1 : ZMod m) := by
        rw [ycast]
        exact natCast_ne_neg_one_of_lt (m := m) (n := d - 2 - n) (by omega)
      have hdiag : ((((d : ℕ) : ZMod m)) - 2 - n) ≠ ((((d : ℕ) : ZMod m)) + n) := by
        intro hEq
        have hnatEq : d - 2 - n = d + n := by
          have hcast : (((d - 2 - n : ℕ) : ZMod m)) = (((d + n : ℕ) : ZMod m)) := by
            rw [ycast, xcast] at hEq
            exact hEq
          exact (natCast_eq_natCast_iff_of_lt (m := m) (a := d - 2 - n) (b := d + n)
            hy_lt hd_lt).1 hcast
        omega
      have hxneg1 : ((((d : ℕ) : ZMod m)) + n) ≠ (-1 : ZMod m) := by
        rw [xcast]
        exact natCast_ne_neg_one_of_lt (m := m) (n := d + n) hdn1_lt
      have h00 :
          ((((d : ℕ) : ZMod m)) + n, ((((d : ℕ) : ZMod m)) - 2 - n)) ≠
            ((0 : ZMod m), (0 : ZMod m)) := by
        intro hEq
        have hsnd : (((d - 2 - n : ℕ) : ZMod m)) = 0 := by
          calc
            (((d - 2 - n : ℕ) : ZMod m)) = ((((d : ℕ) : ZMod m)) - 2 - n) := by rw [← ycast]
            _ = 0 := congrArg Prod.snd hEq
        exact natCast_ne_zero_of_pos_lt (m := m) (n := d - 2 - n) (by omega) hy_lt hsnd
      rw [Function.iterate_succ_apply',
        iterate_R2xy_from_diag_odd_generic_sub_two (m := m) hxOdd hx3 hxle n (Nat.le_of_succ_le hn)]
      rw [R2xy_eq_G_of (m := m) hA hy1 hyneg1 hdiag hxneg1 h00]
      have hd : d = (m + x - 1) / 2 := by
        dsimp [d]
        omega
      ext <;> simp [G, Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, hd] <;> ring

theorem iterate_to_m_sub_one_x_sub_two_odd_generic
    [Fact (Even m)] [Fact (5 < m)] {x : ℕ} (hxOdd : Odd x) (hx3 : 3 ≤ x) (hxle : x ≤ m - 3) :
    (R2xy (m := m)^[(m - x - 1) / 2])
        (((((x + m - 1) / 2 : ℕ) : ZMod m)), ((((x + m - 1) / 2 : ℕ) : ZMod m)) - 2) =
      ((((m - 1 : ℕ) : ZMod m)), (((x - 2 : ℕ) : ZMod m))) := by
  have hmEven : Even m := Fact.out
  rw [iterate_R2xy_from_diag_odd_generic_sub_two (m := m) hxOdd hx3 hxle ((m - x - 1) / 2) le_rfl]
  ext
  · calc
      (((((x + m - 1) / 2 : ℕ) : ZMod m)) + ((((m - x - 1) / 2 : ℕ) : ZMod m)))
          = (((((x + m - 1) / 2) + (m - x - 1) / 2 : ℕ) : ZMod m)) := by rw [Nat.cast_add]
      _ = ((((m - 1 : ℕ) : ℕ) : ZMod m)) := by
            rcases hmEven with ⟨j, hj⟩
            rcases hxOdd with ⟨k, hk⟩
            congr
            omega
  · have hm2le : 2 ≤ (x + m - 1) / 2 := by
      rcases hmEven with ⟨j, hj⟩
      rcases hxOdd with ⟨k, hk⟩
      omega
    have hsub : (x + m - 1) / 2 - (m - x - 1) / 2 - 2 = (x + m - 1) / 2 - 2 - (m - x - 1) / 2 := by
      omega
    calc
      (((((x + m - 1) / 2 : ℕ) : ZMod m)) - 2 - ((((m - x - 1) / 2 : ℕ) : ZMod m)))
          = (((((x + m - 1) / 2 : ℕ) : ZMod m)) - ((((2 + (m - x - 1) / 2 : ℕ) : ℕ) : ZMod m))) := by
              simp [Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = (((((x + m - 1) / 2 - (2 + (m - x - 1) / 2) : ℕ) : ℕ) : ZMod m)) := by
            rw [Nat.cast_sub]
            omega
      _ = (((((x + m - 1) / 2 - (m - x - 1) / 2 - 2 : ℕ) : ℕ) : ZMod m)) := by
            rw [Nat.add_comm 2 ((m - x - 1) / 2), ← Nat.sub_sub]
      _ = (((((x + m - 1) / 2 - 2 - (m - x - 1) / 2 : ℕ) : ℕ) : ZMod m)) := by
            simpa using congrArg (fun s : ℕ => ((s : ℕ) : ZMod m)) hsub
      _ = (((x - 2 : ℕ) : ZMod m)) := by
            have htailNat : (x + m - 1) / 2 - 2 - (m - x - 1) / 2 = x - 2 := by
              rcases hmEven with ⟨j, hj⟩
              rcases hxOdd with ⟨k, hk⟩
              omega
            simpa using congrArg (fun s : ℕ => ((s : ℕ) : ZMod m)) htailNat

theorem R2xy_m_sub_one_odd_generic [Fact (5 < m)] {x : ℕ}
    (hx3 : 3 ≤ x) (hxle : x ≤ m - 3) :
    R2xy (m := m) ((((m - 1 : ℕ) : ZMod m)), (((x - 2 : ℕ) : ZMod m))) =
      ((0 : ZMod m), (((x - 2 : ℕ) : ZMod m))) := by
  have hm5 : 5 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm1le : 1 ≤ m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  have hneg1 : (((m - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) := cast_sub_one_eq_neg_one (m := m) hm1le
  have hy0 : (((x - 2 : ℕ) : ZMod m)) ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := x - 2) (by omega) (by omega)
  have hyneg2 : (((x - 2 : ℕ) : ZMod m)) ≠ (-2 : ZMod m) := by
    exact natCast_ne_neg_two_of_lt (m := m) (n := x - 2) (by omega)
  calc
    R2xy (m := m) ((((m - 1 : ℕ) : ZMod m)), (((x - 2 : ℕ) : ZMod m)))
        = R2xy (m := m) ((-1 : ZMod m), (((x - 2 : ℕ) : ZMod m))) := by rw [hneg1]
    _ = ((0 : ZMod m), (((x - 2 : ℕ) : ZMod m))) := by
          simpa using R2xy_eq_E_of (m := m) (y := (((x - 2 : ℕ) : ZMod m))) hy0 hyneg2

theorem iterate_R2xy_from_zero_odd_generic
    [Fact (Even m)] [Fact (5 < m)] {x : ℕ} (hxOdd : Odd x) (hx3 : 3 ≤ x) (hxle : x ≤ m - 3) :
    ∀ n, n ≤ x - 3 →
      (R2xy (m := m)^[n]) ((0 : ZMod m), (((x - 2 : ℕ) : ZMod m))) =
        ((((n : ℕ) : ZMod m)), (((x - 2 : ℕ) : ZMod m)) - n)
  | 0, _ => by simp
  | n + 1, hn => by
      have hmEven : Even m := Fact.out
      have hm5 : 5 < m := Fact.out
      have hm0 : 0 < m := by omega
      have hm1 : 1 < m := by omega
      have hm2 : 2 < m := by omega
      letI : Fact (0 < m) := ⟨hm0⟩
      letI : Fact (1 < m) := ⟨hm1⟩
      letI : Fact (2 < m) := ⟨hm2⟩
      have hn' : n < x - 3 := Nat.lt_of_succ_le hn
      have hx_lt : n < m := by omega
      have hy_lt : x - 2 - n < m := by omega
      have ycast : (((x - 2 : ℕ) : ZMod m) - n) = (((x - 2 - n : ℕ) : ZMod m)) := by
        have hnle : n ≤ x - 2 := by omega
        rw [Nat.cast_sub hnle]
      have hA : ((((n : ℕ) : ZMod m)), (((x - 2 : ℕ) : ZMod m)) - n) ≠ ((2 : ZMod m), (2 : ZMod m)) := by
        intro hEq
        have hfst : n = 2 := by
          have hcast : (((n : ℕ) : ZMod m)) = ((2 : ℕ) : ZMod m) := by
            calc
              (((n : ℕ) : ZMod m)) = (2 : ZMod m) := congrArg Prod.fst hEq
              _ = ((2 : ℕ) : ZMod m) := by norm_num
          exact (natCast_eq_natCast_iff_of_lt (m := m) (a := n) (b := 2) hx_lt (by omega)).1 hcast
        have hsnd : x - 2 - n = 2 := by
          have hcast : (((x - 2 - n : ℕ) : ZMod m)) = ((2 : ℕ) : ZMod m) := by
            calc
              (((x - 2 - n : ℕ) : ZMod m)) = (((x - 2 : ℕ) : ZMod m) - n) := by rw [← ycast]
              _ = (2 : ZMod m) := congrArg Prod.snd hEq
              _ = ((2 : ℕ) : ZMod m) := by norm_num
          exact (natCast_eq_natCast_iff_of_lt (m := m) (a := x - 2 - n) (b := 2) hy_lt (by omega)).1 hcast
        rcases hxOdd with ⟨k, hk⟩
        omega
      have hy1 : (((x - 2 : ℕ) : ZMod m) - n) ≠ (1 : ZMod m) := by
        rw [ycast]
        exact natCast_ne_one_of_two_le_lt (m := m) (n := x - 2 - n) (by omega) hy_lt
      have hyneg1 : (((x - 2 : ℕ) : ZMod m) - n) ≠ (-1 : ZMod m) := by
        rw [ycast]
        exact natCast_ne_neg_one_of_lt (m := m) (n := x - 2 - n) (by omega)
      have hdiag : (((x - 2 : ℕ) : ZMod m) - n) ≠ (((n : ℕ) : ZMod m)) := by
        intro hEq
        have hnatEq : x - 2 - n = n := by
          have hcast : (((x - 2 - n : ℕ) : ZMod m)) = (((n : ℕ) : ZMod m)) := by
            rw [ycast] at hEq
            exact hEq
          exact (natCast_eq_natCast_iff_of_lt (m := m) (a := x - 2 - n) (b := n) hy_lt hx_lt).1 hcast
        rcases hxOdd with ⟨k, hk⟩
        omega
      have hxneg1 : (n : ZMod m) ≠ (-1 : ZMod m) := by
        exact natCast_ne_neg_one_of_lt (m := m) (n := n) (by omega)
      have h00 : ((((n : ℕ) : ZMod m)), (((x - 2 : ℕ) : ZMod m) - n)) ≠ ((0 : ZMod m), (0 : ZMod m)) := by
        intro hEq
        have hsnd : (((x - 2 - n : ℕ) : ZMod m)) = 0 := by
          calc
            (((x - 2 - n : ℕ) : ZMod m)) = (((x - 2 : ℕ) : ZMod m) - n) := by rw [← ycast]
            _ = 0 := congrArg Prod.snd hEq
        exact natCast_ne_zero_of_pos_lt (m := m) (n := x - 2 - n) (by omega) hy_lt hsnd
      rw [Function.iterate_succ_apply',
        iterate_R2xy_from_zero_odd_generic (m := m) hxOdd hx3 hxle n (Nat.le_of_succ_le hn)]
      rw [R2xy_eq_G_of (m := m) hA hy1 hyneg1 hdiag hxneg1 h00]
      ext <;> simp [G, Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] <;> ring

theorem iterate_to_x_sub_three_one_odd_generic
    [Fact (Even m)] [Fact (5 < m)] {x : ℕ} (hxOdd : Odd x) (hx3 : 3 ≤ x) (hxle : x ≤ m - 3) :
    (R2xy (m := m)^[x - 3]) ((0 : ZMod m), (((x - 2 : ℕ) : ZMod m))) =
      ((((x - 3 : ℕ) : ZMod m)), (1 : ZMod m)) := by
  rw [iterate_R2xy_from_zero_odd_generic (m := m) hxOdd hx3 hxle (x - 3) le_rfl]
  ext
  · rfl
  · change (((x - 2 : ℕ) : ZMod m) - (((x - 3 : ℕ) : ZMod m))) = (1 : ZMod m)
    have hle : x - 3 ≤ x - 2 := by omega
    calc
      (((x - 2 : ℕ) : ZMod m) - (((x - 3 : ℕ) : ZMod m))) = (((x - 2 - (x - 3) : ℕ) : ZMod m)) := by
        rw [Nat.cast_sub hle]
      _ = (((1 : ℕ) : ZMod m)) := by congr; omega
      _ = (1 : ZMod m) := by norm_num

theorem R2xy_x_sub_three_one_odd_generic [Fact (5 < m)] {x : ℕ}
    (hxOdd : Odd x) (hx3 : 3 ≤ x) (hxle : x ≤ m - 3) :
    R2xy (m := m) ((((x - 3 : ℕ) : ZMod m)), (1 : ZMod m)) =
      linePoint (m := m) (((x - 1 : ℕ) : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm1 : 1 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (1 < m) := ⟨hm1⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  have hx1 : (((x - 3 : ℕ) : ZMod m)) ≠ (1 : ZMod m) := by
    intro h
    have hnat : x - 3 = 1 := by
      have hcast : (((x - 3 : ℕ) : ZMod m)) = (((1 : ℕ) : ZMod m)) := by
        simpa using h
      exact (natCast_eq_natCast_iff_of_lt (m := m) (a := x - 3) (b := 1) (by omega) (by omega)).1 hcast
    rcases hxOdd with ⟨k, hk⟩
    omega
  have hxneg1 : (((x - 3 : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := x - 3) (by omega)
  have hcoord : (((x - 3 : ℕ) : ZMod m) + 2) = (((x - 1 : ℕ) : ZMod m)) := by
    change (((x - 3 : ℕ) : ZMod m) + (((2 : ℕ) : ZMod m))) = (((x - 1 : ℕ) : ZMod m))
    rw [← Nat.cast_add]
    congr
    omega
  calc
    R2xy (m := m) ((((x - 3 : ℕ) : ZMod m)), (1 : ZMod m))
        = ((((x - 3 : ℕ) : ZMod m)) + 2, (0 : ZMod m)) := by
            simpa using R2xy_eq_B_of (m := m) (x := (((x - 3 : ℕ) : ZMod m))) hx1 hxneg1
    _ = linePoint (m := m) (((x - 1 : ℕ) : ZMod m)) := by
          ext <;> simp [linePoint, hcoord]

theorem iterate_R2xy_from_linePoint_odd_generic_after_two
    [Fact (Even m)] [Fact (5 < m)] {x : ℕ} (hxOdd : Odd x) (hx3 : 3 ≤ x) (hxle : x ≤ m - 3) :
    ∀ n, n ≤ (m - x - 3) / 2 →
      (R2xy (m := m)^[n + 2]) (linePoint (m := m) (((x : ℕ) : ZMod m))) =
        ((((x + 1 : ℕ) : ZMod m)) + n, (-2 : ZMod m) - n)
  | n, hn => by
      rw [Function.iterate_add_apply]
      simpa [iterate_two_from_linePoint_odd_generic (m := m) hx3 hxle] using
        iterate_R2xy_from_odd_generic_succ_neg_two (m := m) hx3 hxle n hn

theorem iterate_to_diag_from_linePoint_odd_generic
    [Fact (Even m)] [Fact (5 < m)] {x : ℕ} (hxOdd : Odd x) (hx3 : 3 ≤ x) (hxle : x ≤ m - 3) :
    (R2xy (m := m)^[2 + (m - x - 3) / 2]) (linePoint (m := m) (((x : ℕ) : ZMod m))) =
      (((((x + m - 1) / 2 : ℕ) : ZMod m)), ((((x + m - 1) / 2 : ℕ) : ZMod m))) := by
  rw [show 2 + (m - x - 3) / 2 = (m - x - 3) / 2 + 2 by omega, Function.iterate_add_apply]
  simpa [iterate_two_from_linePoint_odd_generic (m := m) hx3 hxle] using
    iterate_to_diag_odd_generic (m := m) hxOdd hx3 hxle

theorem iterate_to_diag_sub_two_from_linePoint_odd_generic
    [Fact (Even m)] [Fact (5 < m)] {x : ℕ} (hxOdd : Odd x) (hx3 : 3 ≤ x) (hxle : x ≤ m - 3) :
    (R2xy (m := m)^[2 + (m - x - 3) / 2 + 1]) (linePoint (m := m) (((x : ℕ) : ZMod m))) =
      (((((x + m - 1) / 2 : ℕ) : ZMod m)), ((((x + m - 1) / 2 : ℕ) : ZMod m)) - 2) := by
  rw [show 2 + (m - x - 3) / 2 + 1 = 1 + (2 + (m - x - 3) / 2) by omega, Function.iterate_add_apply]
  simpa [iterate_to_diag_from_linePoint_odd_generic (m := m) hxOdd hx3 hxle] using
    R2xy_diag_odd_generic (m := m) hxOdd hx3 hxle

theorem iterate_R2xy_from_linePoint_odd_generic_after_diag_sub_two
    [Fact (Even m)] [Fact (5 < m)] {x : ℕ} (hxOdd : Odd x) (hx3 : 3 ≤ x) (hxle : x ≤ m - 3) :
    ∀ n, n ≤ (m - x - 1) / 2 →
      (R2xy (m := m)^[2 + (m - x - 3) / 2 + 1 + n]) (linePoint (m := m) (((x : ℕ) : ZMod m))) =
        (((((x + m - 1) / 2 : ℕ) : ZMod m)) + n,
          ((((x + m - 1) / 2 : ℕ) : ZMod m)) - 2 - n)
  | n, hn => by
      rw [show 2 + (m - x - 3) / 2 + 1 + n = n + (2 + (m - x - 3) / 2 + 1) by omega,
        Function.iterate_add_apply]
      simpa [iterate_to_diag_sub_two_from_linePoint_odd_generic (m := m) hxOdd hx3 hxle] using
        iterate_R2xy_from_diag_odd_generic_sub_two (m := m) hxOdd hx3 hxle n hn

theorem iterate_to_m_sub_one_x_sub_two_from_linePoint_odd_generic
    [Fact (Even m)] [Fact (5 < m)] {x : ℕ} (hxOdd : Odd x) (hx3 : 3 ≤ x) (hxle : x ≤ m - 3) :
    (R2xy (m := m)^[2 + (m - x - 3) / 2 + 1 + (m - x - 1) / 2])
        (linePoint (m := m) (((x : ℕ) : ZMod m))) =
      ((((m - 1 : ℕ) : ZMod m)), (((x - 2 : ℕ) : ZMod m))) := by
  rw [show 2 + (m - x - 3) / 2 + 1 + (m - x - 1) / 2 =
    (m - x - 1) / 2 + (2 + (m - x - 3) / 2 + 1) by omega, Function.iterate_add_apply]
  simpa [iterate_to_diag_sub_two_from_linePoint_odd_generic (m := m) hxOdd hx3 hxle] using
    iterate_to_m_sub_one_x_sub_two_odd_generic (m := m) hxOdd hx3 hxle

theorem iterate_to_zero_x_sub_two_from_linePoint_odd_generic
    [Fact (Even m)] [Fact (5 < m)] {x : ℕ} (hxOdd : Odd x) (hx3 : 3 ≤ x) (hxle : x ≤ m - 3) :
    (R2xy (m := m)^[2 + (m - x - 3) / 2 + 1 + (m - x - 1) / 2 + 1])
        (linePoint (m := m) (((x : ℕ) : ZMod m))) =
      ((0 : ZMod m), (((x - 2 : ℕ) : ZMod m))) := by
  rw [show 2 + (m - x - 3) / 2 + 1 + (m - x - 1) / 2 + 1 =
    1 + (2 + (m - x - 3) / 2 + 1 + (m - x - 1) / 2) by omega, Function.iterate_add_apply]
  simpa [iterate_to_m_sub_one_x_sub_two_from_linePoint_odd_generic (m := m) hxOdd hx3 hxle] using
    R2xy_m_sub_one_odd_generic (m := m) hx3 hxle

theorem iterate_R2xy_from_linePoint_odd_generic_after_zero_x_sub_two
    [Fact (Even m)] [Fact (5 < m)] {x : ℕ} (hxOdd : Odd x) (hx3 : 3 ≤ x) (hxle : x ≤ m - 3) :
    ∀ n, n ≤ x - 3 →
      (R2xy (m := m)^[2 + (m - x - 3) / 2 + 1 + (m - x - 1) / 2 + 1 + n])
          (linePoint (m := m) (((x : ℕ) : ZMod m))) =
        ((((n : ℕ) : ZMod m)), (((x - 2 : ℕ) : ZMod m)) - n)
  | n, hn => by
      rw [show 2 + (m - x - 3) / 2 + 1 + (m - x - 1) / 2 + 1 + n =
        n + (2 + (m - x - 3) / 2 + 1 + (m - x - 1) / 2 + 1) by omega, Function.iterate_add_apply]
      simpa [iterate_to_zero_x_sub_two_from_linePoint_odd_generic (m := m) hxOdd hx3 hxle] using
        iterate_R2xy_from_zero_odd_generic (m := m) hxOdd hx3 hxle n hn

theorem iterate_to_x_sub_three_one_from_linePoint_odd_generic
    [Fact (Even m)] [Fact (5 < m)] {x : ℕ} (hxOdd : Odd x) (hx3 : 3 ≤ x) (hxle : x ≤ m - 3) :
    (R2xy (m := m)^[2 + (m - x - 3) / 2 + 1 + (m - x - 1) / 2 + 1 + (x - 3)])
        (linePoint (m := m) (((x : ℕ) : ZMod m))) =
      ((((x - 3 : ℕ) : ZMod m)), (1 : ZMod m)) := by
  rw [show 2 + (m - x - 3) / 2 + 1 + (m - x - 1) / 2 + 1 + (x - 3) =
    (x - 3) + (2 + (m - x - 3) / 2 + 1 + (m - x - 1) / 2 + 1) by omega, Function.iterate_add_apply]
  simpa [iterate_to_zero_x_sub_two_from_linePoint_odd_generic (m := m) hxOdd hx3 hxle] using
    iterate_to_x_sub_three_one_odd_generic (m := m) hxOdd hx3 hxle

theorem firstReturn_odd_generic
    [Fact (Even m)] [Fact (5 < m)] {x : ℕ} (hxOdd : Odd x)
    (hx3 : 3 ≤ x) (hxle : x ≤ m - 3) :
    (R2xy (m := m)^[rho2 (m := m) (((x : ℕ) : ZMod m))])
        (linePoint (m := m) (((x : ℕ) : ZMod m))) =
      linePoint (m := m) (T2 (m := m) (((x : ℕ) : ZMod m))) := by
  have hm5 : 5 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm1 : 1 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (1 < m) := ⟨hm1⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  have hx0 : (((x : ℕ) : ZMod m)) ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := x) (by omega) (by omega)
  have hx1 : (((x : ℕ) : ZMod m)) ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := x) (by omega) (by omega)
  have hx2 : (((x : ℕ) : ZMod m)) ≠ 2 := by
    exact natCast_ne_two_of_three_le_lt (m := m) (n := x) hx3 (by omega)
  have hrho : rho2 (m := m) (((x : ℕ) : ZMod m)) = m := by
    simp [rho2, hx0, hx1, hx2]
  have hT : T2 (m := m) (((x : ℕ) : ZMod m)) = (((x - 1 : ℕ) : ZMod m)) := by
    calc
      T2 (m := m) (((x : ℕ) : ZMod m)) = (((x : ℕ) : ZMod m)) - 1 := by
        simp [T2, hx0, hx1, hx2]
      _ = (((x - 1 : ℕ) : ZMod m)) := by
        symm
        simpa using (Nat.cast_sub (R := ZMod m) (m := 1) (n := x) (by omega))
  have hstepFinal :
      (R2xy (m := m)^[2 + (m - x - 3) / 2 + 1 + (m - x - 1) / 2 + 1 + (x - 3) + 1])
          (linePoint (m := m) (((x : ℕ) : ZMod m))) =
        linePoint (m := m) (((x - 1 : ℕ) : ZMod m)) := by
    rw [show 2 + (m - x - 3) / 2 + 1 + (m - x - 1) / 2 + 1 + (x - 3) + 1 =
      1 + (2 + (m - x - 3) / 2 + 1 + (m - x - 1) / 2 + 1 + (x - 3)) by omega,
      Function.iterate_add_apply]
    simpa [iterate_to_x_sub_three_one_from_linePoint_odd_generic (m := m) hxOdd hx3 hxle] using
      R2xy_x_sub_three_one_odd_generic (m := m) hxOdd hx3 hxle
  have hsplit : m = 2 + (m - x - 3) / 2 + 1 + (m - x - 1) / 2 + 1 + (x - 3) + 1 := by
    have hmEven : Even m := Fact.out
    rcases hmEven with ⟨j, hj⟩
    rcases hxOdd with ⟨k, hk⟩
    omega
  calc
    (R2xy (m := m)^[rho2 (m := m) (((x : ℕ) : ZMod m))])
        (linePoint (m := m) (((x : ℕ) : ZMod m)))
        = (R2xy (m := m)^[m]) (linePoint (m := m) (((x : ℕ) : ZMod m))) := by rw [hrho]
    _ = (R2xy (m := m)^[2 + (m - x - 3) / 2 + 1 + (m - x - 1) / 2 + 1 + (x - 3) + 1])
          (linePoint (m := m) (((x : ℕ) : ZMod m))) := by
            exact congrArg
              (fun n => (R2xy (m := m)^[n]) (linePoint (m := m) (((x : ℕ) : ZMod m))))
              hsplit
    _ = linePoint (m := m) (((x - 1 : ℕ) : ZMod m)) := hstepFinal
    _ = linePoint (m := m) (T2 (m := m) (((x : ℕ) : ZMod m))) := by rw [hT]

theorem hfirst_odd_generic
    [Fact (Even m)] [Fact (5 < m)] {x : ℕ} (hxOdd : Odd x)
    (hx3 : 3 ≤ x) (hxle : x ≤ m - 3) :
    ∀ n, 0 < n → n < rho2 (m := m) (((x : ℕ) : ZMod m)) →
      (R2xy (m := m)^[n]) (linePoint (m := m) (((x : ℕ) : ZMod m))) ∉
        Set.range (linePoint (m := m))
  | n, hn0, hnlt => by
      have hm5 : 5 < m := Fact.out
      have hmEven : Even m := Fact.out
      have hm0 : 0 < m := by omega
      have hm1 : 1 < m := by omega
      have hm2 : 2 < m := by omega
      letI : Fact (0 < m) := ⟨hm0⟩
      letI : Fact (1 < m) := ⟨hm1⟩
      letI : Fact (2 < m) := ⟨hm2⟩
      have hx0 : (((x : ℕ) : ZMod m)) ≠ 0 := by
        exact natCast_ne_zero_of_pos_lt (m := m) (n := x) (by omega) (by omega)
      have hx1 : (((x : ℕ) : ZMod m)) ≠ 1 := by
        exact natCast_ne_one_of_two_le_lt (m := m) (n := x) (by omega) (by omega)
      have hx2 : (((x : ℕ) : ZMod m)) ≠ 2 := by
        exact natCast_ne_two_of_three_le_lt (m := m) (n := x) hx3 (by omega)
      have hrho : rho2 (m := m) (((x : ℕ) : ZMod m)) = m := by
        simp [rho2, hx0, hx1, hx2]
      have hnm : n < m := by rwa [hrho] at hnlt
      by_cases h1 : n = 1
      · apply not_mem_range_linePoint_of_snd_ne_zero
        rw [h1]
        simpa [Function.iterate_one, R2xy_linePoint_odd_generic_start (m := m) hx3 hxle] using
          (neg_ne_zero.mpr (one_ne_zero (m := m)))
      · by_cases hfront : n ≤ 2 + (m - x - 3) / 2
        · let t : ℕ := n - 2
          have ht : t ≤ (m - x - 3) / 2 := by
            dsimp [t]
            omega
          have hnEq : n = t + 2 := by
            dsimp [t]
            omega
          have hiter :
              (R2xy (m := m)^[n]) (linePoint (m := m) (((x : ℕ) : ZMod m))) =
                ((((x + 1 : ℕ) : ZMod m)) + t, (-2 : ZMod m) - t) := by
            rw [hnEq]
            simpa using iterate_R2xy_from_linePoint_odd_generic_after_two (m := m) hxOdd hx3 hxle t ht
          apply not_mem_range_linePoint_of_snd_ne_zero
          rw [hiter]
          exact neg_two_sub_nat_ne_zero (m := m) (n := t) (by omega)
        · by_cases hmid : n ≤ 2 + (m - x - 3) / 2 + 1 + (m - x - 1) / 2
          · let d : ℕ := (x + m - 1) / 2
            let t : ℕ := n - (2 + (m - x - 3) / 2 + 1)
            have ht : t ≤ (m - x - 1) / 2 := by
              dsimp [t]
              omega
            have hnEq : n = 2 + (m - x - 3) / 2 + 1 + t := by
              dsimp [t]
              omega
            have hiter :
                (R2xy (m := m)^[n]) (linePoint (m := m) (((x : ℕ) : ZMod m))) =
                  ((((d : ℕ) : ZMod m)) + t, (((d : ℕ) : ZMod m)) - 2 - t) := by
              rw [hnEq]
              simpa [d] using
                iterate_R2xy_from_linePoint_odd_generic_after_diag_sub_two (m := m) hxOdd hx3 hxle t ht
            have hycast :
                ((((d : ℕ) : ZMod m)) - 2 - t) = (((d - 2 - t : ℕ) : ZMod m)) := by
              have h2t : 2 + t ≤ d := by
                dsimp [d, t]
                rcases hmEven with ⟨j, hj⟩
                rcases hxOdd with ⟨k, hk⟩
                omega
              have hsub : d - t - 2 = d - 2 - t := by
                dsimp [d, t]
                omega
              calc
                ((((d : ℕ) : ZMod m)) - 2 - t)
                    = ((((d : ℕ) : ZMod m)) - (((2 + t : ℕ) : ZMod m))) := by
                        simp [Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
                _ = (((d - (2 + t) : ℕ) : ZMod m)) := by rw [Nat.cast_sub h2t]
                _ = (((d - t - 2 : ℕ) : ZMod m)) := by rw [Nat.add_comm 2 t, ← Nat.sub_sub]
                _ = (((d - 2 - t : ℕ) : ZMod m)) := by
                      simpa using congrArg (fun s : ℕ => ((s : ℕ) : ZMod m)) hsub
            have hy : ((((d : ℕ) : ZMod m)) - 2 - t) ≠ 0 := by
              rw [hycast]
              exact natCast_ne_zero_of_pos_lt (m := m) (n := d - 2 - t) (by
                dsimp [d, t]
                rcases hmEven with ⟨j, hj⟩
                rcases hxOdd with ⟨k, hk⟩
                omega) (by
                dsimp [d, t]
                omega)
            apply not_mem_range_linePoint_of_snd_ne_zero
            rw [hiter]
            exact hy
          · let t : ℕ := n - (2 + (m - x - 3) / 2 + 1 + (m - x - 1) / 2 + 1)
            have hsplit : m = 2 + (m - x - 3) / 2 + 1 + (m - x - 1) / 2 + 1 + (x - 3) + 1 := by
              rcases hmEven with ⟨j, hj⟩
              rcases hxOdd with ⟨k, hk⟩
              omega
            have ht : t ≤ x - 3 := by
              dsimp [t]
              rw [hsplit] at hnm
              omega
            have hnEq : n = 2 + (m - x - 3) / 2 + 1 + (m - x - 1) / 2 + 1 + t := by
              dsimp [t]
              omega
            have hiter :
                (R2xy (m := m)^[n]) (linePoint (m := m) (((x : ℕ) : ZMod m))) =
                  ((((t : ℕ) : ZMod m)), (((x - 2 : ℕ) : ZMod m)) - t) := by
              rw [hnEq]
              simpa using
                iterate_R2xy_from_linePoint_odd_generic_after_zero_x_sub_two (m := m) hxOdd hx3 hxle t ht
            have hycast : (((x - 2 : ℕ) : ZMod m) - t) = (((x - 2 - t : ℕ) : ZMod m)) := by
              have htle : t ≤ x - 2 := by
                dsimp [t]
                omega
              rw [Nat.cast_sub htle]
            have hy : (((x - 2 : ℕ) : ZMod m) - t) ≠ 0 := by
              rw [hycast]
              exact natCast_ne_zero_of_pos_lt (m := m) (n := x - 2 - t) (by
                dsimp [t]
                omega) (by
                dsimp [t]
                omega)
            apply not_mem_range_linePoint_of_snd_ne_zero
            rw [hiter]
            exact hy

theorem hreturn [Fact (Even m)] [Fact (5 < m)] (x : ZMod m) :
    (R2xy (m := m)^[rho2 (m := m) x]) (linePoint (m := m) x) =
      linePoint (m := m) (T2 (m := m) x) := by
  have hmEven : Even m := Fact.out
  have hm5 : 5 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm2 : 2 < m := by omega
  letI : Fact (2 < m) := ⟨hm2⟩
  letI : NeZero m := ⟨Nat.ne_of_gt hm0⟩
  let a : ℕ := x.val
  have ha_lt : a < m := by
    simpa [a] using (ZMod.val_lt x)
  have hxcast : (((a : ℕ) : ZMod m)) = x := by
    simpa [a] using (ZMod.natCast_zmod_val x)
  rw [← hxcast]
  by_cases ha0 : a = 0
  · simpa [a, ha0] using firstReturn_zero (m := m)
  · by_cases ha1 : a = 1
    · simpa [a, ha1] using firstReturn_one (m := m)
    · by_cases ha2 : a = 2
      · simpa [a, ha2] using firstReturn_two (m := m)
      · by_cases ha4 : a = 4
        · simpa [a, ha4] using firstReturn_four (m := m)
        · by_cases ha6 : a = 6
          · have hm7 : 7 < m := by
              rcases hmEven with ⟨k, hk⟩
              omega
            letI : Fact (7 < m) := ⟨hm7⟩
            simpa [a, ha6] using firstReturn_six (m := m)
          · by_cases haMSubOne : a = m - 1
            · simpa [a, haMSubOne] using firstReturn_m_sub_one (m := m)
            · by_cases haMSubTwo : a = m - 2
              · have hm7 : 7 < m := by
                  rcases hmEven with ⟨k, hk⟩
                  omega
                letI : Fact (7 < m) := ⟨hm7⟩
                simpa [a, haMSubTwo] using firstReturn_m_sub_two (m := m)
              · rcases Nat.even_or_odd a with haEven | haOdd
                · have hm7 : 7 < m := by
                    rcases hmEven with ⟨k, hk⟩
                    rcases haEven with ⟨l, hl⟩
                    omega
                  letI : Fact (7 < m) := ⟨hm7⟩
                  have ha8 : 8 ≤ a := by
                    rcases haEven with ⟨l, hl⟩
                    omega
                  have hale : a ≤ m - 4 := by
                    rcases hmEven with ⟨k, hk⟩
                    rcases haEven with ⟨l, hl⟩
                    omega
                  simpa [a] using firstReturn_even_generic (m := m) haEven ha8 hale
                · have ha3 : 3 ≤ a := by
                    rcases haOdd with ⟨l, hl⟩
                    omega
                  have hale : a ≤ m - 3 := by
                    rcases hmEven with ⟨k, hk⟩
                    rcases haOdd with ⟨l, hl⟩
                    omega
                  simpa [a] using firstReturn_odd_generic (m := m) haOdd ha3 hale

theorem hfirst [Fact (Even m)] [Fact (5 < m)] (x : ZMod m) :
    ∀ n, 0 < n → n < rho2 (m := m) x →
      (R2xy (m := m)^[n]) (linePoint (m := m) x) ∉ Set.range (linePoint (m := m))
  | n, hn0, hnlt => by
      have hmEven : Even m := Fact.out
      have hm5 : 5 < m := Fact.out
      have hm0 : 0 < m := by omega
      have hm2 : 2 < m := by omega
      letI : Fact (2 < m) := ⟨hm2⟩
      letI : NeZero m := ⟨Nat.ne_of_gt hm0⟩
      let a : ℕ := x.val
      have ha_lt : a < m := by
        simpa [a] using (ZMod.val_lt x)
      have hxcast : (((a : ℕ) : ZMod m)) = x := by
        simpa [a] using (ZMod.natCast_zmod_val x)
      rw [← hxcast] at hnlt ⊢
      by_cases ha0 : a = 0
      · have hnlt0 : n < 1 := by
          simpa [a, ha0, rho2] using hnlt
        have hfalse : False := by omega
        exact hfalse.elim
      · by_cases ha1 : a = 1
        · have hnlt1 : n < rho2 (m := m) (1 : ZMod m) := by
            simpa [a, ha1] using hnlt
          simpa [a, ha1] using (hfirst_one (m := m) n hn0 hnlt1)
        · by_cases ha2 : a = 2
          · have hnlt2 : n < rho2 (m := m) (2 : ZMod m) := by
              simpa [a, ha2] using hnlt
            simpa [a, ha2] using (hfirst_two (m := m) n hn0 hnlt2)
          · by_cases ha4 : a = 4
            · have hnlt4 : n < rho2 (m := m) (4 : ZMod m) := by
                simpa [a, ha4] using hnlt
              simpa [a, ha4] using (hfirst_four (m := m) n hn0 hnlt4)
            · by_cases ha6 : a = 6
              · have hm7 : 7 < m := by
                  rcases hmEven with ⟨k, hk⟩
                  omega
                letI : Fact (7 < m) := ⟨hm7⟩
                have hnlt6 : n < rho2 (m := m) (6 : ZMod m) := by
                  simpa [a, ha6] using hnlt
                simpa [a, ha6] using (hfirst_six (m := m) n hn0 hnlt6)
              · by_cases haMSubOne : a = m - 1
                · have hnltMSubOne : n < rho2 (m := m) (((m - 1 : ℕ) : ZMod m)) := by
                    simpa [a, haMSubOne] using hnlt
                  simpa [a, haMSubOne] using (hfirst_m_sub_one (m := m) n hn0 hnltMSubOne)
                · by_cases haMSubTwo : a = m - 2
                  · have hm7 : 7 < m := by
                      rcases hmEven with ⟨k, hk⟩
                      omega
                    letI : Fact (7 < m) := ⟨hm7⟩
                    have hnltMSubTwo : n < rho2 (m := m) (((m - 2 : ℕ) : ZMod m)) := by
                      simpa [a, haMSubTwo] using hnlt
                    simpa [a, haMSubTwo] using (hfirst_m_sub_two (m := m) n hn0 hnltMSubTwo)
                  · rcases Nat.even_or_odd a with haEven | haOdd
                    · have hm7 : 7 < m := by
                        rcases hmEven with ⟨k, hk⟩
                        rcases haEven with ⟨l, hl⟩
                        omega
                      letI : Fact (7 < m) := ⟨hm7⟩
                      have ha8 : 8 ≤ a := by
                        rcases haEven with ⟨l, hl⟩
                        omega
                      have hale : a ≤ m - 4 := by
                        rcases hmEven with ⟨k, hk⟩
                        rcases haEven with ⟨l, hl⟩
                        omega
                      simpa [a] using hfirst_even_generic (m := m) haEven ha8 hale n hn0 hnlt
                    · have ha3 : 3 ≤ a := by
                        rcases haOdd with ⟨l, hl⟩
                        omega
                      have hale : a ≤ m - 3 := by
                        rcases hmEven with ⟨k, hk⟩
                        rcases haOdd with ⟨l, hl⟩
                        omega
                      simpa [a] using hfirst_odd_generic (m := m) haOdd ha3 hale n hn0 hnlt

theorem blockTime_eq_sum_range (T : α → α) (rho : α → ℕ) (x0 : α) :
    ∀ k, blockTime T rho x0 k = Finset.sum (Finset.range k) (fun i => rho ((T^[i]) x0)) := by
  intro k
  induction k with
  | zero =>
      simp [blockTime]
  | succ k ih =>
      rw [blockTime_succ, ih, Finset.sum_range_succ]

theorem sum_rho2 [NeZero m] [Fact (Even m)] [Fact (5 < m)] :
    ((∑ x : ZMod m, rho2 (m := m) x)) = m ^ 2 := by
  have hmEven : Even m := Fact.out
  have hm5 : 5 < m := Fact.out
  have hm0 : 0 < m := by omega
  have hm1 : 1 < m := by omega
  have hm2 : 2 < m := by omega
  have hm3 : 3 ≤ m := by omega
  letI : NeZero m := ⟨Nat.ne_of_gt hm0⟩
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (1 < m) := ⟨hm1⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  have hzero : rho2 (m := m) (0 : ZMod m) = 1 := by simp [rho2]
  have hone : rho2 (m := m) (1 : ZMod m) = m - 1 := by
    simp [rho2, one_ne_zero (m := m)]
  have htwo : rho2 (m := m) (2 : ZMod m) = 2 * m := by
    simp [rho2, two_ne_zero (m := m), two_ne_one (m := m)]
  have hfirstThree :
      Finset.sum (Finset.range 3) (fun k => rho2 (m := m) (((k : ℕ) : ZMod m))) = 3 * m := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    simp [hzero, hone, htwo]
    omega
  have hIco :
      Finset.sum (Finset.Ico 3 m) (fun k => rho2 (m := m) (((k : ℕ) : ZMod m))) = (m - 3) * m := by
    calc
      Finset.sum (Finset.Ico 3 m) (fun k => rho2 (m := m) (((k : ℕ) : ZMod m)))
          = Finset.sum (Finset.Ico 3 m) (fun _ => m) := by
              apply Finset.sum_congr rfl
              intro k hk
              have hk3 : 3 ≤ k := (Finset.mem_Ico.mp hk).1
              have hkm : k < m := (Finset.mem_Ico.mp hk).2
              have hk0 : (((k : ℕ) : ZMod m)) ≠ 0 := by
                exact natCast_ne_zero_of_pos_lt (m := m) (n := k) (by omega) hkm
              have hk1 : (((k : ℕ) : ZMod m)) ≠ 1 := by
                exact natCast_ne_one_of_two_le_lt (m := m) (n := k) (by omega) hkm
              have hk2 : (((k : ℕ) : ZMod m)) ≠ 2 := by
                exact natCast_ne_two_of_three_le_lt (m := m) (n := k) hk3 hkm
              simp [rho2, hk0, hk1, hk2]
      _ = (Finset.Ico 3 m).card * m := by simp
      _ = (m - 3) * m := by simp [Nat.card_Ico]
  let g : ℕ → ℕ := fun k => rho2 (m := m) (((k : ℕ) : ZMod m))
  have hsumZModToFin :
      (∑ x : ZMod m, rho2 (m := m) x) = ∑ i : Fin m, rho2 (m := m) ((i : ZMod m)) := by
    cases m with
    | zero =>
        cases (NeZero.ne (n := 0) rfl)
    | succ k =>
        have hsumSucc :
            (∑ x : ZMod (k + 1), rho2 (m := k + 1) x) =
              ∑ i : Fin (k + 1), rho2 (m := k + 1) i := by
          refine Fintype.sum_equiv (ZMod.finEquiv (k + 1)).toEquiv.symm
            (fun x : ZMod (k + 1) => rho2 (m := k + 1) x)
            (fun i : Fin (k + 1) => rho2 (m := k + 1) i) ?_
          intro x
          rfl
        convert hsumSucc using 1
        apply Finset.sum_congr rfl
        intro i hi
        change
          rho2 (m := k + 1) (((i : ZMod (k + 1)).val : ZMod (k + 1))) =
            rho2 (m := k + 1) i
        exact congrArg (rho2 (m := k + 1)) (ZMod.natCast_zmod_val (n := k + 1) i)
  have hsumRange :
      (∑ i : Fin m, rho2 (m := m) ((i : ZMod m))) = Finset.sum (Finset.range m) g := by
    simpa [g] using (Fin.sum_univ_eq_sum_range g m)
  calc
    (∑ x : ZMod m, rho2 (m := m) x) = ∑ i : Fin m, rho2 (m := m) ((i : ZMod m)) := hsumZModToFin
    _ = Finset.sum (Finset.range m) g := hsumRange
    _ = Finset.sum (Finset.range 3) g + Finset.sum (Finset.Ico 3 m) g := by
            symm
            exact Finset.sum_range_add_sum_Ico _ hm3
    _ = 3 * m + (m - 3) * m := by rw [hfirstThree, hIco]
    _ = (3 + (m - 3)) * m := by rw [← Nat.add_mul]
    _ = m * m := by congr 1; omega
    _ = m ^ 2 := by rw [pow_two]

theorem hsum [Fact (Even m)] [Fact (5 < m)] :
    blockTime (T2 (m := m)) (rho2 (m := m)) (0 : ZMod m) m = m ^ 2 := by
  have hm0 : 0 < m := by
    have hm5 : 5 < m := Fact.out
    omega
  have hm2 : 2 < m := by
    have hm5 : 5 < m := Fact.out
    omega
  letI : NeZero m := ⟨Nat.ne_of_gt hm0⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  let e : Fin m ≃ ZMod m :=
    Equiv.ofBijective (fun i : Fin m => ((T2 (m := m)^[i.1]) (0 : ZMod m))) (cycleOn_T2 (m := m)).1
  calc
    blockTime (T2 (m := m)) (rho2 (m := m)) (0 : ZMod m) m
        = Finset.sum (Finset.range m) (fun i => rho2 (m := m) (((T2 (m := m)^[i]) (0 : ZMod m)))) := by
            simpa using blockTime_eq_sum_range (T2 (m := m)) (rho2 (m := m)) (0 : ZMod m) m
    _ = ∑ i : Fin m, rho2 (m := m) (e i) := by
          rw [← Fin.sum_univ_eq_sum_range]
          rfl
    _ = ∑ x : ZMod m, rho2 (m := m) x := by
          exact Equiv.sum_comp e (fun x : ZMod m => rho2 (m := m) x)
    _ = m ^ 2 := sum_rho2 (m := m)

theorem cycleOn_color2 [Fact (Even m)] [Fact (5 < m)] :
    TorusD4.CycleOn (m ^ 2) (R2xy (m := m))
      (linePoint (m := m) (0 : ZMod m)) := by
  have hm0 : 0 < m := by
    have hm5 : 5 < m := Fact.out
    omega
  have hm1 : 1 < m := by
    have hm5 : 5 < m := Fact.out
    omega
  have hm2 : 2 < m := by
    have hm5 : 5 < m := Fact.out
    omega
  letI : NeZero m := ⟨Nat.ne_of_gt hm0⟩
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (1 < m) := ⟨hm1⟩
  letI : Fact (2 < m) := ⟨hm2⟩
  have hsumCard :
      blockTime (T2 (m := m)) (rho2 (m := m)) (0 : ZMod m) m = Fintype.card (P0Coord m) := by
    simpa [P0Coord, ZMod.card, pow_two] using hsum (m := m)
  simpa [P0Coord, ZMod.card, pow_two] using
    (firstReturn_counting
      (α := P0Coord m) (β := ZMod m)
      (F := R2xy (m := m)) (embed := linePoint (m := m))
      (T := T2 (m := m)) (rho := rho2 (m := m))
      (M := m) (x0 := (0 : ZMod m))
      linePoint_injective
      (cycleOn_T2 (m := m))
      (hreturn (m := m))
      (hfirst (m := m))
      hsumCard)

end TorusD3Even
