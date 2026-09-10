import TorusD3Odometer.Basic
import TorusD3Odometer.Lift
import TorusD3Odometer.Color1
import TorusD3Even.Counting
import Mathlib.Tactic

namespace TorusD3Odometer

open TorusD4

instance factZeroOfFactFive [Fact (5 < m)] : Fact (0 < m) :=
  ⟨lt_trans (by decide : 0 < 5) Fact.out⟩

instance factOneOfFactFive [Fact (5 < m)] : Fact (1 < m) :=
  ⟨lt_trans (by decide : 1 < 5) Fact.out⟩

instance factTwoOfFactFive [Fact (5 < m)] : Fact (2 < m) :=
  ⟨lt_trans (by decide : 2 < 5) Fact.out⟩

theorem natCast_ne_zero_of_pos_lt [Fact (0 < m)] {n : ℕ} (hn0 : 0 < n) (hnm : n < m) :
    ((n : ℕ) : ZMod m) ≠ 0 := by
  intro h
  have h' : n % m = 0 % m := (ZMod.natCast_eq_natCast_iff' n 0 m).1 (by simpa using h)
  rw [Nat.mod_eq_of_lt hnm, Nat.zero_mod] at h'
  exact Nat.ne_of_gt hn0 h'

theorem natCast_ne_one_of_two_le_lt [Fact (1 < m)] {n : ℕ} (hn1 : 2 ≤ n) (hnm : n < m) :
    ((n : ℕ) : ZMod m) ≠ 1 := by
  intro h
  have h1m : 1 < m := Fact.out
  have h' : n % m = 1 % m := (ZMod.natCast_eq_natCast_iff' n 1 m).1 (by simpa using h)
  rw [Nat.mod_eq_of_lt hnm, Nat.mod_eq_of_lt h1m] at h'
  omega

theorem one_ne_zero [Fact (1 < m)] : (1 : ZMod m) ≠ 0 := by
  simpa using natCast_ne_zero_of_pos_lt (m := m) (n := 1) (by decide) Fact.out

theorem two_ne_zero [Fact (2 < m)] : (2 : ZMod m) ≠ 0 := by
  letI : Fact (0 < m) := ⟨lt_trans (by decide : 0 < 2) Fact.out⟩
  simpa using natCast_ne_zero_of_pos_lt (m := m) (n := 2) (by decide) Fact.out

theorem two_ne_one [Fact (2 < m)] : (2 : ZMod m) ≠ 1 := by
  letI : Fact (1 < m) := ⟨lt_trans (by decide : 1 < 2) Fact.out⟩
  simpa using natCast_ne_one_of_two_le_lt (m := m) (n := 2) (by decide) Fact.out

theorem one_ne_neg_one [Fact (2 < m)] : (1 : ZMod m) ≠ (-1 : ZMod m) := by
  intro h
  have htwo' : (1 : ZMod m) + 1 = 0 := by
    simpa using congrArg (fun z : ZMod m => z + 1) h
  have htwo : (2 : ZMod m) = 0 := by
    calc
      (2 : ZMod m) = (1 : ZMod m) + 1 := by norm_num
      _ = 0 := htwo'
  exact two_ne_zero (m := m) htwo

theorem cast_sub_one_eq_neg_one (hm : 1 ≤ m) : (((m - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) := by
  rw [Nat.cast_sub hm]
  simp

theorem cast_sub_two_eq_neg_two (hm : 2 ≤ m) : (((m - 2 : ℕ) : ZMod m)) = (-2 : ZMod m) := by
  rw [Nat.cast_sub hm]
  simp

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
  have hzero : (((n + 2 : ℕ) : ZMod m)) = 0 := by
    have hstep := congrArg (fun z : ZMod m => z + 2) h
    simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using hstep
  exact natCast_ne_zero_of_pos_lt (m := m) (n := n + 2) (by omega) (by omega) hzero

theorem natCast_ne_neg_one_of_even [Fact (0 < m)] (hmEven : Even m) {n : ℕ} (hnEven : Even n) :
    ((n : ℕ) : ZMod m) ≠ (-1 : ZMod m) := by
  intro h
  have hzero : (((n + 1 : ℕ) : ZMod m)) = 0 := by
    have h' := congrArg (fun z : ZMod m => z + 1) h
    simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using h'
  have hdvd : m ∣ n + 1 := (ZMod.natCast_eq_zero_iff (n + 1) m).1 hzero
  rcases hmEven with ⟨q, hmq⟩
  rcases hnEven with ⟨r, hr⟩
  rw [hmq, hr] at hdvd
  have h2dvd : 2 ∣ r + r + 1 := by
    have h2q : 2 ∣ q + q := by
      simpa [two_mul] using (dvd_mul_of_dvd_left (dvd_refl 2) q)
    exact dvd_trans h2q hdvd
  omega

def dir1CaseILayerZero (u : P0Coord m) : Color :=
  let i : ZMod m := u.1
  let k : ZMod m := u.2
  if (i = 0 ∧ k = 0) ∨
      (i + k = (-1 : ZMod m) ∧ i ≠ 0 ∧ i ≠ (-2 : ZMod m) ∧ i ≠ (-1 : ZMod m)) ∨
      (i = (-1 : ZMod m) ∧ k = (-1 : ZMod m)) ∨
      (i = (-2 : ZMod m) ∧ k = 0) then
    0
  else if (i = 0 ∧ k ≠ 0 ∧ k ≠ (-1 : ZMod m)) ∨
      (i = (1 : ZMod m) ∧ k = (-1 : ZMod m)) ∨
      (i = (-2 : ZMod m) ∧ k = (1 : ZMod m)) then
    1
  else
    2

def dir1CaseI (z : FullCoord m) : Color :=
  let (u, s) := z
  if s = 0 then
    dir1CaseILayerZero (m := m) u
  else if s = 1 then
    0
  else
    1

def fullMap1CaseI (z : FullCoord m) : FullCoord m :=
  KMap (m := m) (dir1CaseI (m := m) z) z

@[simp] theorem fullMap1CaseI_snd (z : FullCoord m) :
    (fullMap1CaseI (m := m) z).2 = z.2 + 1 := by
  simp [fullMap1CaseI, KMap_snd]

def returnMap1CaseI (u : P0Coord m) : P0Coord m :=
  match dir1CaseILayerZero (m := m) u with
  | 0 => (u.1 + 2, u.2)
  | 1 => (u.1 + 1, u.2)
  | _ => (u.1 + 1, u.2 + 1)

def bulkMap1CaseI (u : P0Coord m) : P0Coord m :=
  (u.1 + 1, u.2 + 1)

def linePoint1 (x : Fin m) : P0Coord m :=
  (((x : Fin m) : ZMod m), 0)

theorem linePoint1_injective : Function.Injective (linePoint1 (m := m)) := by
  intro x y h
  apply Fin.ext
  have hcast : (((x : Fin m) : ZMod m)) = ((y : ZMod m)) := by
    simpa [linePoint1] using congrArg Prod.fst h
  have hmod : x.1 % m = y.1 % m := (ZMod.natCast_eq_natCast_iff' x.1 y.1 m).1 hcast
  simpa [Nat.mod_eq_of_lt x.2, Nat.mod_eq_of_lt y.2] using hmod

theorem mem_range_linePoint1_iff [Fact (0 < m)] {u : P0Coord m} :
    u ∈ Set.range (linePoint1 (m := m)) ↔ u.2 = 0 := by
  letI : NeZero m := ⟨Nat.ne_of_gt Fact.out⟩
  rcases u with ⟨x, y⟩
  constructor
  · rintro ⟨z, hz⟩
    simpa [linePoint1] using (congrArg Prod.snd hz).symm
  · intro hy
    refine ⟨⟨x.val, x.val_lt⟩, ?_⟩
    ext
    · simpa [linePoint1] using (ZMod.natCast_zmod_val x).symm
    · simpa [linePoint1] using hy.symm

theorem not_mem_range_linePoint1_of_snd_ne_zero [Fact (0 < m)] {u : P0Coord m} (hy : u.2 ≠ 0) :
    u ∉ Set.range (linePoint1 (m := m)) := by
  intro hu
  exact hy ((mem_range_linePoint1_iff (m := m)).1 hu)

theorem iterate_bulkMap1CaseI (n : ℕ) (u : P0Coord m) :
    (bulkMap1CaseI (m := m)^[n]) u = (u.1 + n, u.2 + n) := by
  induction n generalizing u with
  | zero =>
      rcases u with ⟨i, k⟩
      simp [bulkMap1CaseI]
  | succ n ih =>
      rcases u with ⟨i, k⟩
      rw [Function.iterate_succ_apply', ih]
      ext <;> simp [bulkMap1CaseI, Nat.cast_add]
      all_goals ring

theorem dir1CaseILayerZero_eq_two_of_not_special {i k : ZMod m}
    (h00 : ¬ (i = 0 ∧ k = 0))
    (hdiag : ¬ (i + k = (-1 : ZMod m) ∧ i ≠ 0 ∧ i ≠ (-2 : ZMod m) ∧ i ≠ (-1 : ZMod m)))
    (hneg1 : ¬ (i = (-1 : ZMod m) ∧ k = (-1 : ZMod m)))
    (hneg2 : ¬ (i = (-2 : ZMod m) ∧ k = 0))
    (hi0 : ¬ (i = 0 ∧ k ≠ 0 ∧ k ≠ (-1 : ZMod m)))
    (h1neg1 : ¬ (i = (1 : ZMod m) ∧ k = (-1 : ZMod m)))
    (hneg2one : ¬ (i = (-2 : ZMod m) ∧ k = (1 : ZMod m))) :
    dir1CaseILayerZero (m := m) (i, k) = 2 := by
  simp [dir1CaseILayerZero, h00, hdiag, hneg1, hneg2, hi0, h1neg1, hneg2one]

theorem returnMap1CaseI_eq_bulk_of_not_special {i k : ZMod m}
    (h00 : ¬ (i = 0 ∧ k = 0))
    (hdiag : ¬ (i + k = (-1 : ZMod m) ∧ i ≠ 0 ∧ i ≠ (-2 : ZMod m) ∧ i ≠ (-1 : ZMod m)))
    (hneg1 : ¬ (i = (-1 : ZMod m) ∧ k = (-1 : ZMod m)))
    (hneg2 : ¬ (i = (-2 : ZMod m) ∧ k = 0))
    (hi0 : ¬ (i = 0 ∧ k ≠ 0 ∧ k ≠ (-1 : ZMod m)))
    (h1neg1 : ¬ (i = (1 : ZMod m) ∧ k = (-1 : ZMod m)))
    (hneg2one : ¬ (i = (-2 : ZMod m) ∧ k = (1 : ZMod m))) :
    returnMap1CaseI (m := m) (i, k) = bulkMap1CaseI (m := m) (i, k) := by
  simp [returnMap1CaseI, bulkMap1CaseI,
    dir1CaseILayerZero_eq_two_of_not_special (m := m) h00 hdiag hneg1 hneg2 hi0 h1neg1 hneg2one]

theorem dir1CaseILayerZero_eq_zero_of_diag {i k : ZMod m}
    (hdiag : i + k = (-1 : ZMod m)) (hi0 : i ≠ 0) (him2 : i ≠ (-2 : ZMod m))
    (him1 : i ≠ (-1 : ZMod m)) :
    dir1CaseILayerZero (m := m) (i, k) = 0 := by
  simp [dir1CaseILayerZero, hdiag, hi0, him2, him1]

theorem dir1CaseILayerZero_eq_one_of_i_zero {k : ZMod m}
    (hk0 : k ≠ 0) (hkneg1 : k ≠ (-1 : ZMod m)) :
    dir1CaseILayerZero (m := m) ((0 : ZMod m), k) = 1 := by
  simp [dir1CaseILayerZero, hk0, hkneg1]

theorem returnMap1CaseI_eq_add_one_of_i_zero {k : ZMod m}
    (hk0 : k ≠ 0) (hkneg1 : k ≠ (-1 : ZMod m)) :
    returnMap1CaseI (m := m) ((0 : ZMod m), k) = ((1 : ZMod m), k) := by
  simp [returnMap1CaseI, dir1CaseILayerZero_eq_one_of_i_zero (m := m) hk0 hkneg1]

theorem iterate_eq_iterate_of_eq_on_prefix {α : Type*} (F G : α → α) (z : α) :
    ∀ n,
      (∀ t, t < n → F ((G^[t]) z) = G ((G^[t]) z)) →
        (F^[n]) z = (G^[n]) z
  | 0, _ => by rfl
  | n + 1, hprefix => by
      calc
        (F^[n + 1]) z = F ((F^[n]) z) := by rw [Function.iterate_succ_apply']
        _ = F ((G^[n]) z) := by rw [iterate_eq_iterate_of_eq_on_prefix F G z n (by
              intro t ht
              exact hprefix t (Nat.lt_trans ht (Nat.lt_succ_self _)))]
        _ = G ((G^[n]) z) := hprefix n (Nat.lt_succ_self _)
        _ = (G^[n + 1]) z := by rw [Function.iterate_succ_apply']

theorem iterate_add_apply_five {α : Type*} (f : α → α) (a b c d e : ℕ) (z : α) :
    (f^[a + (b + (c + (d + e)))]) z =
      (f^[a]) ((f^[b]) ((f^[c]) ((f^[d]) ((f^[e]) z)))) := by
  rw [Function.iterate_add_apply, Function.iterate_add_apply,
    Function.iterate_add_apply, Function.iterate_add_apply]

theorem iterate_returnMap1CaseI_odd_prefix [Fact (5 < m)] (hmEven : Even m)
    {x : ℕ} (hx1 : 1 ≤ x) (hxle : x ≤ m - 4) (hxodd : Odd x) :
    let xFin : Fin m := ⟨x, by omega⟩
    let a : ℕ := (m - 1 - x) / 2
    ((returnMap1CaseI (m := m)^[a]) (linePoint1 (m := m) xFin)) =
      ((((x + a : ℕ) : ZMod m)), (((a : ℕ) : ZMod m))) := by
  let xFin : Fin m := ⟨x, by omega⟩
  let a : ℕ := (m - 1 - x) / 2
  have ha_lt : a < m := by
    dsimp [a]
    omega
  calc
    ((returnMap1CaseI (m := m)^[a]) (linePoint1 (m := m) xFin))
        = ((bulkMap1CaseI (m := m)^[a]) (linePoint1 (m := m) xFin)) := by
            refine iterate_eq_iterate_of_eq_on_prefix
              (F := returnMap1CaseI (m := m)) (G := bulkMap1CaseI (m := m))
              (z := linePoint1 (m := m) xFin) a ?_
            intro t ht
            rw [iterate_bulkMap1CaseI (m := m) t (linePoint1 (m := m) xFin)]
            have hi_pos : 0 < x + t := by omega
            have hi_lt : x + t < m := by omega
            have hi_ne_zero : (((x + t : ℕ) : ZMod m)) ≠ 0 := by
              exact natCast_ne_zero_of_pos_lt (m := m) (n := x + t) hi_pos hi_lt
            have hi_ne_neg_two : (((x + t : ℕ) : ZMod m)) ≠ (-2 : ZMod m) := by
              exact natCast_ne_neg_two_of_lt (m := m) (n := x + t) (by omega)
            have hk_ne_neg_one : (((t : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
              exact natCast_ne_neg_one_of_lt (m := m) (n := t) (by omega)
            have h00 : ¬ ((((x + t : ℕ) : ZMod m)) = 0 ∧ (((t : ℕ) : ZMod m)) = 0) := by
              intro h
              exact hi_ne_zero h.1
            have hdiag :
                ¬ ((((x + t : ℕ) : ZMod m)) + (((t : ℕ) : ZMod m)) = (-1 : ZMod m) ∧
                    (((x + t : ℕ) : ZMod m)) ≠ 0 ∧
                    (((x + t : ℕ) : ZMod m)) ≠ (-2 : ZMod m) ∧
                    (((x + t : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              have hsum_ne : (((x + 2 * t : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
                exact natCast_ne_neg_one_of_lt (m := m) (n := x + 2 * t) (by omega)
              apply hsum_ne
              simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm, two_mul] using h.1
            have hneg1 :
                ¬ ((((x + t : ℕ) : ZMod m)) = (-1 : ZMod m) ∧ (((t : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              exact hk_ne_neg_one h.2
            have hneg2 :
                ¬ ((((x + t : ℕ) : ZMod m)) = (-2 : ZMod m) ∧ (((t : ℕ) : ZMod m)) = 0) := by
              intro h
              exact hi_ne_neg_two h.1
            have hi0 :
                ¬ ((((x + t : ℕ) : ZMod m)) = 0 ∧
                    (((t : ℕ) : ZMod m)) ≠ 0 ∧
                    (((t : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              exact hi_ne_zero h.1
            have h1neg1 :
                ¬ ((((x + t : ℕ) : ZMod m)) = (1 : ZMod m) ∧ (((t : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              exact hk_ne_neg_one h.2
            have hneg2one :
                ¬ ((((x + t : ℕ) : ZMod m)) = (-2 : ZMod m) ∧ (((t : ℕ) : ZMod m)) = (1 : ZMod m)) := by
              intro h
              exact hi_ne_neg_two h.1
            simpa [linePoint1, xFin] using
              returnMap1CaseI_eq_bulk_of_not_special (m := m)
                (i := (((x + t : ℕ) : ZMod m))) (k := (((t : ℕ) : ZMod m)))
                h00 hdiag hneg1 hneg2 hi0 h1neg1 hneg2one
    _ = ((((x : ℕ) : ZMod m) + (((a : ℕ) : ZMod m))), (((a : ℕ) : ZMod m))) := by
          rw [iterate_bulkMap1CaseI (m := m) a (linePoint1 (m := m) xFin)]
          simp [linePoint1, xFin]
    _ = ((((x + a : ℕ) : ZMod m)), (((a : ℕ) : ZMod m))) := by
          rw [Nat.cast_add]

theorem odd_caseI_half_eq [Fact (5 < m)] (hmEven : Even m)
    {x : ℕ} (hx1 : 1 ≤ x) (hxle : x ≤ m - 4) (hxodd : Odd x) :
    let a : ℕ := (m - 1 - x) / 2
    x + 2 * a = m - 1 := by
  dsimp
  rcases hmEven with ⟨q, rfl⟩
  rcases hxodd with ⟨r, rfl⟩
  omega

theorem returnMap1CaseI_odd_diag [Fact (5 < m)] (hmEven : Even m)
    {x : ℕ} (hx1 : 1 ≤ x) (hxle : x ≤ m - 4) (hxodd : Odd x) :
    let a : ℕ := (m - 1 - x) / 2
    returnMap1CaseI (m := m) ((((x + a : ℕ) : ZMod m)), (((a : ℕ) : ZMod m))) =
      ((((x + a + 2 : ℕ) : ZMod m)), (((a : ℕ) : ZMod m))) := by
  let a : ℕ := (m - 1 - x) / 2
  have hxa : x + 2 * a = m - 1 := by
    simpa [a] using odd_caseI_half_eq (m := m) hmEven hx1 hxle hxodd
  have hdiag : (((x + a + a : ℕ) : ZMod m)) = (-1 : ZMod m) := by
    rw [show x + a + a = x + 2 * a by omega, hxa]
    simpa using cast_sub_one_eq_neg_one (m := m) (by
      have hm5 : 5 < m := Fact.out
      omega)
  have hi0 : (((x + a : ℕ) : ZMod m)) ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := x + a) (by omega) (by omega)
  have him2 : (((x + a : ℕ) : ZMod m)) ≠ (-2 : ZMod m) := by
    exact natCast_ne_neg_two_of_lt (m := m) (n := x + a) (by omega)
  have him1 : (((x + a : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := x + a) (by omega)
  have hdiag' :
      (((x + a : ℕ) : ZMod m)) + (((a : ℕ) : ZMod m)) = (-1 : ZMod m) := by
    simpa [Nat.cast_add, add_assoc] using hdiag
  have hdir :
      dir1CaseILayerZero (m := m) ((((x + a : ℕ) : ZMod m)), (((a : ℕ) : ZMod m))) = 0 := by
    exact dir1CaseILayerZero_eq_zero_of_diag (m := m) hdiag' hi0 him2 him1
  have hdir' :
      dir1CaseILayerZero (m := m)
        ((((x : ℕ) : ZMod m) + (((a : ℕ) : ZMod m)), (((a : ℕ) : ZMod m)))) = 0 := by
    simpa [Nat.cast_add, add_assoc] using hdir
  simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
    (show returnMap1CaseI (m := m) ((((x + a : ℕ) : ZMod m)), (((a : ℕ) : ZMod m))) =
        ((((x + a : ℕ) : ZMod m)) + 2, (((a : ℕ) : ZMod m))) by
      simp [returnMap1CaseI, hdir, hdir'])

theorem iterate_returnMap1CaseI_odd_middle [Fact (5 < m)] (hmEven : Even m)
    {x : ℕ} (hx1 : 1 ≤ x) (hxle : x ≤ m - 4) (hxodd : Odd x) :
    let a : ℕ := (m - 1 - x) / 2
    ((returnMap1CaseI (m := m)^[a - 1]) ((((x + a + 2 : ℕ) : ZMod m)), (((a : ℕ) : ZMod m)))) =
      ((0 : ZMod m), (((m - x - 2 : ℕ) : ZMod m))) := by
  let a : ℕ := (m - 1 - x) / 2
  have hxa : x + 2 * a = m - 1 := by
    simpa [a] using odd_caseI_half_eq (m := m) hmEven hx1 hxle hxodd
  have ha2 : 2 ≤ a := by
    rcases hmEven with ⟨q, hmq⟩
    rcases hxodd with ⟨r, hrx⟩
    rw [hmq] at hxle
    rw [hrx] at hxle
    dsimp [a]
    omega
  calc
    ((returnMap1CaseI (m := m)^[a - 1]) ((((x + a + 2 : ℕ) : ZMod m)), (((a : ℕ) : ZMod m))))
        = ((bulkMap1CaseI (m := m)^[a - 1]) ((((x + a + 2 : ℕ) : ZMod m)), (((a : ℕ) : ZMod m)))) := by
            refine iterate_eq_iterate_of_eq_on_prefix
              (F := returnMap1CaseI (m := m)) (G := bulkMap1CaseI (m := m))
              (z := ((((x + a + 2 : ℕ) : ZMod m)), (((a : ℕ) : ZMod m)))) (a - 1) ?_
            intro t ht
            rw [iterate_bulkMap1CaseI (m := m) t ((((x + a + 2 : ℕ) : ZMod m)), (((a : ℕ) : ZMod m)))]
            have hi_pos : 0 < x + a + 2 + t := by omega
            have hi_lt : x + a + 2 + t < m := by omega
            have hk_pos : 0 < a + t := by omega
            have hk_lt : a + t < m := by omega
            have hk_ne_zero : (((a + t : ℕ) : ZMod m)) ≠ 0 := by
              exact natCast_ne_zero_of_pos_lt (m := m) (n := a + t) hk_pos hk_lt
            have hk_ne_one : (((a + t : ℕ) : ZMod m)) ≠ 1 := by
              exact natCast_ne_one_of_two_le_lt (m := m) (n := a + t) (by omega) hk_lt
            have hk_ne_neg_one : (((a + t : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
              exact natCast_ne_neg_one_of_lt (m := m) (n := a + t) (by omega)
            have hi_ne_zero : (((x + a + 2 + t : ℕ) : ZMod m)) ≠ 0 := by
              exact natCast_ne_zero_of_pos_lt (m := m) (n := x + a + 2 + t) hi_pos hi_lt
            have h00 :
                ¬ ((((x + a + 2 + t : ℕ) : ZMod m)) = 0 ∧ (((a + t : ℕ) : ZMod m)) = 0) := by
              intro h
              exact hi_ne_zero h.1
            have hdiag :
                ¬ ((((x + a + 2 + t : ℕ) : ZMod m)) + (((a + t : ℕ) : ZMod m)) = (-1 : ZMod m) ∧
                    (((x + a + 2 + t : ℕ) : ZMod m)) ≠ 0 ∧
                    (((x + a + 2 + t : ℕ) : ZMod m)) ≠ (-2 : ZMod m) ∧
                    (((x + a + 2 + t : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              have hsum_ne : (((1 + 2 * t : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
                exact natCast_ne_neg_one_of_lt (m := m) (n := 1 + 2 * t) (by omega)
              apply hsum_ne
              have hsumEq :
                  (((x + a + 2 + t + (a + t) : ℕ) : ZMod m)) =
                    (((1 + 2 * t : ℕ) : ZMod m)) := by
                rw [show x + a + 2 + t + (a + t) = x + 2 * a + (2 * t + 2) by omega, hxa]
                have hm1 : (((m - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) := by
                  exact cast_sub_one_eq_neg_one (m := m) (by
                    have hm5 : 5 < m := Fact.out
                    omega)
                rw [Nat.cast_add]
                rw [Nat.cast_add]
                rw [hm1]
                have hz :
                    (-1 : ZMod m) + (2 + 2 * ((t : ℕ) : ZMod m)) =
                      (1 : ZMod m) + 2 * ((t : ℕ) : ZMod m) := by
                  ring
                simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using hz
              have hsumLeft :
                  ((((x + a + 2 + t : ℕ) : ZMod m)) + (((a + t : ℕ) : ZMod m))) =
                    (((1 + 2 * t : ℕ) : ZMod m)) := by
                simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using hsumEq
              exact hsumLeft.symm.trans h.1
            have hneg1 :
                ¬ ((((x + a + 2 + t : ℕ) : ZMod m)) = (-1 : ZMod m) ∧
                    (((a + t : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              exact hk_ne_neg_one h.2
            have hneg2 :
                ¬ ((((x + a + 2 + t : ℕ) : ZMod m)) = (-2 : ZMod m) ∧
                    (((a + t : ℕ) : ZMod m)) = 0) := by
              intro h
              exact hk_ne_zero h.2
            have hi0 :
                ¬ ((((x + a + 2 + t : ℕ) : ZMod m)) = 0 ∧
                    (((a + t : ℕ) : ZMod m)) ≠ 0 ∧
                    (((a + t : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              exact hi_ne_zero h.1
            have h1neg1 :
                ¬ ((((x + a + 2 + t : ℕ) : ZMod m)) = (1 : ZMod m) ∧
                    (((a + t : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              exact hk_ne_neg_one h.2
            have hneg2one :
                ¬ ((((x + a + 2 + t : ℕ) : ZMod m)) = (-2 : ZMod m) ∧
                    (((a + t : ℕ) : ZMod m)) = (1 : ZMod m)) := by
              intro h
              exact hk_ne_one h.2
            simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
              returnMap1CaseI_eq_bulk_of_not_special (m := m)
              (i := (((x + a + 2 + t : ℕ) : ZMod m))) (k := (((a + t : ℕ) : ZMod m)))
              h00 hdiag hneg1 hneg2 hi0 h1neg1 hneg2one
    _ = ((((x + a + 2 + (a - 1) : ℕ) : ZMod m)), (((a + (a - 1) : ℕ) : ZMod m))) := by
          rw [iterate_bulkMap1CaseI (m := m) (a - 1) ((((x + a + 2 : ℕ) : ZMod m)), (((a : ℕ) : ZMod m)))]
          simp [Nat.cast_add, add_assoc, add_left_comm, add_comm]
    _ = ((0 : ZMod m), (((m - x - 2 : ℕ) : ZMod m))) := by
          have hfirst : x + a + 2 + (a - 1) = m := by
            omega
          have hsecond : a + (a - 1) = m - x - 2 := by
            omega
          simp [hfirst, hsecond]

theorem returnMap1CaseI_odd_vertical [Fact (5 < m)]
    {x : ℕ} (hx1 : 1 ≤ x) (hxle : x ≤ m - 4) :
    returnMap1CaseI (m := m) ((0 : ZMod m), (((m - x - 2 : ℕ) : ZMod m))) =
      ((1 : ZMod m), (((m - x - 2 : ℕ) : ZMod m))) := by
  have hk0 : (((m - x - 2 : ℕ) : ZMod m)) ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := m - x - 2) (by omega) (by omega)
  have hkneg1 : (((m - x - 2 : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := m - x - 2) (by omega)
  simpa using returnMap1CaseI_eq_add_one_of_i_zero (m := m) (k := (((m - x - 2 : ℕ) : ZMod m))) hk0 hkneg1

theorem iterate_returnMap1CaseI_odd_suffix [Fact (5 < m)] (hmEven : Even m)
    {x : ℕ} (hx1 : 1 ≤ x) (hxle : x ≤ m - 4) (hxodd : Odd x) :
    ((returnMap1CaseI (m := m)^[x + 2]) ((1 : ZMod m), (((m - x - 2 : ℕ) : ZMod m)))) =
      ((((x + 3 : ℕ) : ZMod m)), (0 : ZMod m)) := by
  calc
    ((returnMap1CaseI (m := m)^[x + 2]) ((1 : ZMod m), (((m - x - 2 : ℕ) : ZMod m))))
        = ((bulkMap1CaseI (m := m)^[x + 2]) ((1 : ZMod m), (((m - x - 2 : ℕ) : ZMod m)))) := by
            refine iterate_eq_iterate_of_eq_on_prefix
              (F := returnMap1CaseI (m := m)) (G := bulkMap1CaseI (m := m))
              (z := ((1 : ZMod m), (((m - x - 2 : ℕ) : ZMod m)))) (x + 2) ?_
            intro t ht
            rw [iterate_bulkMap1CaseI (m := m) t ((1 : ZMod m), (((m - x - 2 : ℕ) : ZMod m)))]
            have hi_pos : 0 < 1 + t := by omega
            have hi_lt : 1 + t < m := by
              rcases hmEven with ⟨q, hmq⟩
              rcases hxodd with ⟨r, hrx⟩
              rw [hmq] at hxle
              rw [hrx] at hxle
              omega
            have hi_ne_zero : (((1 + t : ℕ) : ZMod m)) ≠ 0 := by
              exact natCast_ne_zero_of_pos_lt (m := m) (n := 1 + t) hi_pos hi_lt
            have hi_ne_neg_one : (((1 + t : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
              exact natCast_ne_neg_one_of_lt (m := m) (n := 1 + t) (by omega)
            have hi_ne_neg_two : (((1 + t : ℕ) : ZMod m)) ≠ (-2 : ZMod m) := by
              exact natCast_ne_neg_two_of_lt (m := m) (n := 1 + t) (by
                rcases hmEven with ⟨q, hmq⟩
                rcases hxodd with ⟨r, hrx⟩
                rw [hmq] at hxle
                rw [hrx] at hxle
                omega)
            have h00 :
                ¬ ((((1 + t : ℕ) : ZMod m)) = 0 ∧ ((((m - x - 2) + t : ℕ) : ZMod m)) = 0) := by
              intro h
              exact hi_ne_zero h.1
            have hdiag :
                ¬ ((((1 + t : ℕ) : ZMod m)) + ((((m - x - 2) + t : ℕ) : ZMod m)) = (-1 : ZMod m) ∧
                    (((1 + t : ℕ) : ZMod m)) ≠ 0 ∧
                    (((1 + t : ℕ) : ZMod m)) ≠ (-2 : ZMod m) ∧
                    (((1 + t : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              have hsumEven : Even (m - x - 1 + 2 * t) := by
                rcases hmEven with ⟨q, hmq⟩
                rcases hxodd with ⟨r, hrx⟩
                rw [hmq, hrx]
                refine ⟨q - r - 1 + t, ?_⟩
                omega
              have hsum_ne : (((m - x - 1 + 2 * t : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
                exact natCast_ne_neg_one_of_even (m := m) hmEven hsumEven
              apply hsum_ne
              have hsumEq :
                  ((((1 + t : ℕ) : ZMod m)) + ((((m - x - 2) + t : ℕ) : ZMod m))) =
                    (((m - x - 1 + 2 * t : ℕ) : ZMod m)) := by
                have hnat : 1 + t + ((m - x - 2) + t) = m - x - 1 + 2 * t := by
                  omega
                simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
                  congrArg (fun n : ℕ => ((n : ℕ) : ZMod m)) hnat
              exact hsumEq.symm.trans h.1
            have hneg1 :
                ¬ ((((1 + t : ℕ) : ZMod m)) = (-1 : ZMod m) ∧
                    ((((m - x - 2) + t : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              exact hi_ne_neg_one h.1
            have hneg2 :
                ¬ ((((1 + t : ℕ) : ZMod m)) = (-2 : ZMod m) ∧
                    ((((m - x - 2) + t : ℕ) : ZMod m)) = 0) := by
              intro h
              exact hi_ne_neg_two h.1
            have hi0 :
                ¬ ((((1 + t : ℕ) : ZMod m)) = 0 ∧
                    ((((m - x - 2) + t : ℕ) : ZMod m)) ≠ 0 ∧
                    ((((m - x - 2) + t : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              exact hi_ne_zero h.1
            have h1neg1 :
                ¬ ((((1 + t : ℕ) : ZMod m)) = (1 : ZMod m) ∧
                    ((((m - x - 2) + t : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              have ht0 : t = 0 := by
                have hmod := (ZMod.natCast_eq_natCast_iff' (1 + t) 1 m).1 (by simpa using h.1)
                rw [Nat.mod_eq_of_lt hi_lt, Nat.mod_eq_of_lt (by
                  have hm5 : 5 < m := Fact.out
                  omega)] at hmod
                omega
              subst ht0
              have hkbase : (((m - x - 2 : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
                exact natCast_ne_neg_one_of_lt (m := m) (n := m - x - 2) (by omega)
              exact hkbase h.2
            have hneg2one :
                ¬ ((((1 + t : ℕ) : ZMod m)) = (-2 : ZMod m) ∧
                    ((((m - x - 2) + t : ℕ) : ZMod m)) = (1 : ZMod m)) := by
              intro h
              exact hi_ne_neg_two h.1
            simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
              returnMap1CaseI_eq_bulk_of_not_special (m := m)
                (i := (((1 + t : ℕ) : ZMod m))) (k := ((((m - x - 2) + t : ℕ) : ZMod m)))
                h00 hdiag hneg1 hneg2 hi0 h1neg1 hneg2one
    _ = ((((1 + (x + 2) : ℕ) : ZMod m)), ((((m - x - 2) + (x + 2) : ℕ) : ZMod m))) := by
          rw [iterate_bulkMap1CaseI (m := m) (x + 2) ((1 : ZMod m), (((m - x - 2 : ℕ) : ZMod m)))]
          ext <;> simp [Nat.cast_add, add_assoc, add_left_comm, add_comm]
          norm_num
    _ = ((((x + 3 : ℕ) : ZMod m)), (0 : ZMod m)) := by
          have hsum : (m - x - 2) + (x + 2) = m := by omega
          ext <;> simp [hsum, Nat.cast_add, add_assoc]
          ring

theorem iterate_returnMap1CaseI_odd_generic [Fact (5 < m)] (hmEven : Even m)
    {x : ℕ} (hx1 : 1 ≤ x) (hxle : x ≤ m - 4) (hxodd : Odd x) :
    let xFin : Fin m := ⟨x, by omega⟩
    ((returnMap1CaseI (m := m)^[m + 2]) (linePoint1 (m := m) xFin)) =
      ((((x + 3 : ℕ) : ZMod m)), (0 : ZMod m)) := by
  let xFin : Fin m := ⟨x, by omega⟩
  let a : ℕ := (m - 1 - x) / 2
  have hdecomp : m + 2 = (x + 2) + (1 + ((a - 1) + (1 + a))) := by
    dsimp [a]
    rcases hmEven with ⟨q, hmq⟩
    rcases hxodd with ⟨r, hrx⟩
    rw [hmq, hrx]
    omega
  have hsplit0 :
      ((returnMap1CaseI (m := m)^[m + 2]) (linePoint1 (m := m) xFin)) =
        ((returnMap1CaseI (m := m)^[x + 2])
          (((returnMap1CaseI (m := m)^[1 + ((a - 1) + (1 + a))]) (linePoint1 (m := m) xFin)))) := by
    simpa [hdecomp] using
      (Function.iterate_add_apply (f := returnMap1CaseI (m := m)) (m := x + 2)
        (n := 1 + ((a - 1) + (1 + a))) (linePoint1 (m := m) xFin))
  have hsplit1 :
      ((returnMap1CaseI (m := m)^[1 + ((a - 1) + (1 + a))]) (linePoint1 (m := m) xFin)) =
        returnMap1CaseI (m := m)
          (((returnMap1CaseI (m := m)^[(a - 1) + (1 + a)]) (linePoint1 (m := m) xFin))) := by
    simpa using
      (Function.iterate_add_apply (f := returnMap1CaseI (m := m)) (m := 1)
        (n := (a - 1) + (1 + a)) (linePoint1 (m := m) xFin))
  have hsplit2 :
      ((returnMap1CaseI (m := m)^[(a - 1) + (1 + a)]) (linePoint1 (m := m) xFin)) =
        ((returnMap1CaseI (m := m)^[a - 1])
          (((returnMap1CaseI (m := m)^[1 + a]) (linePoint1 (m := m) xFin)))) := by
    simpa [Nat.add_assoc] using
      (Function.iterate_add_apply (f := returnMap1CaseI (m := m)) (m := a - 1)
        (n := 1 + a) (linePoint1 (m := m) xFin))
  have hsplit3 :
      ((returnMap1CaseI (m := m)^[1 + a]) (linePoint1 (m := m) xFin)) =
        returnMap1CaseI (m := m)
          (((returnMap1CaseI (m := m)^[a]) (linePoint1 (m := m) xFin))) := by
    simpa using
      (Function.iterate_add_apply (f := returnMap1CaseI (m := m)) (m := 1)
        (n := a) (linePoint1 (m := m) xFin))
  calc
    ((returnMap1CaseI (m := m)^[m + 2]) (linePoint1 (m := m) xFin))
        = ((returnMap1CaseI (m := m)^[x + 2])
            (((returnMap1CaseI (m := m)^[1 + ((a - 1) + (1 + a))]) (linePoint1 (m := m) xFin)))) := by
              exact hsplit0
    _ = ((returnMap1CaseI (m := m)^[x + 2])
            (returnMap1CaseI (m := m)
              (((returnMap1CaseI (m := m)^[(a - 1) + (1 + a)]) (linePoint1 (m := m) xFin))))) := by
          rw [hsplit1]
    _ = ((returnMap1CaseI (m := m)^[x + 2])
            (returnMap1CaseI (m := m)
              (((returnMap1CaseI (m := m)^[a - 1])
                (((returnMap1CaseI (m := m)^[1 + a]) (linePoint1 (m := m) xFin))))))) := by
          rw [hsplit2]
    _ = ((returnMap1CaseI (m := m)^[x + 2])
            (returnMap1CaseI (m := m)
              (((returnMap1CaseI (m := m)^[a - 1])
                (returnMap1CaseI (m := m)
                  (((returnMap1CaseI (m := m)^[a]) (linePoint1 (m := m) xFin)))))))) := by
          rw [hsplit3]
    _ = ((returnMap1CaseI (m := m)^[x + 2])
            (returnMap1CaseI (m := m)
              (((returnMap1CaseI (m := m)^[a - 1])
                (returnMap1CaseI (m := m) ((((x + a : ℕ) : ZMod m)), (((a : ℕ) : ZMod m)))))))) := by
          simpa [xFin, a] using
            congrArg (fun u => ((returnMap1CaseI (m := m)^[x + 2])
              (returnMap1CaseI (m := m) (((returnMap1CaseI (m := m)^[a - 1]) (returnMap1CaseI (m := m) u))))))
              (iterate_returnMap1CaseI_odd_prefix (m := m) hmEven hx1 hxle hxodd)
    _ = ((returnMap1CaseI (m := m)^[x + 2])
            (returnMap1CaseI (m := m)
              (((returnMap1CaseI (m := m)^[a - 1])
                ((((x + a + 2 : ℕ) : ZMod m)), (((a : ℕ) : ZMod m))))))) := by
          simpa [xFin, a] using
            congrArg (fun u => ((returnMap1CaseI (m := m)^[x + 2])
              (returnMap1CaseI (m := m) (((returnMap1CaseI (m := m)^[a - 1]) u)))))
              (returnMap1CaseI_odd_diag (m := m) hmEven hx1 hxle hxodd)
    _ = ((returnMap1CaseI (m := m)^[x + 2])
            (returnMap1CaseI (m := m)
              ((0 : ZMod m), (((m - x - 2 : ℕ) : ZMod m))))) := by
          simpa [xFin, a] using
            congrArg (fun u => ((returnMap1CaseI (m := m)^[x + 2]) (returnMap1CaseI (m := m) u)))
              (iterate_returnMap1CaseI_odd_middle (m := m) hmEven hx1 hxle hxodd)
    _ = ((returnMap1CaseI (m := m)^[x + 2]) ((1 : ZMod m), (((m - x - 2 : ℕ) : ZMod m)))) := by
          simpa using
            congrArg (fun u => ((returnMap1CaseI (m := m)^[x + 2]) u))
              (returnMap1CaseI_odd_vertical (m := m) hx1 hxle)
    _ = ((((x + 3 : ℕ) : ZMod m)), (0 : ZMod m)) := by
          exact iterate_returnMap1CaseI_odd_suffix (m := m) hmEven hx1 hxle hxodd

theorem firstReturn_line_odd_generic [Fact (5 < m)] (hmEven : Even m)
    {x : ℕ} (hx1 : 1 ≤ x) (hxle : x ≤ m - 4) (hxodd : Odd x) :
    let xFin : Fin m := ⟨x, by omega⟩
    ((returnMap1CaseI (m := m)^[TorusD3Even.rho1CaseI (m := m) xFin]) (linePoint1 (m := m) xFin)) =
      linePoint1 (m := m) (TorusD3Even.T1CaseI (m := m) xFin) := by
  let xFin : Fin m := ⟨x, by omega⟩
  have hx0 : xFin.1 ≠ 0 := by
    simp [xFin]
    omega
  have hxm3 : xFin.1 ≠ m - 3 := by
    simp [xFin]
    omega
  have hxm2 : xFin.1 ≠ m - 2 := by
    simp [xFin]
    omega
  have hxm1 : xFin.1 ≠ m - 1 := by
    simp [xFin]
    omega
  have hrho : TorusD3Even.rho1CaseI (m := m) xFin = m + 2 := by
    simp [TorusD3Even.rho1CaseI, hx0, hxm2, hxm3, hxm1]
  have hT : (TorusD3Even.T1CaseI (m := m) xFin).1 = x + 3 := by
    simpa [xFin] using TorusD3Even.T1CaseI_eq_add_three_of_ne_special (m := m)
      (x := xFin) hx0 hxm3 hxm2 hxm1
  calc
    ((returnMap1CaseI (m := m)^[TorusD3Even.rho1CaseI (m := m) xFin]) (linePoint1 (m := m) xFin))
        = ((returnMap1CaseI (m := m)^[m + 2]) (linePoint1 (m := m) xFin)) := by rw [hrho]
    _ = ((((x + 3 : ℕ) : ZMod m)), (0 : ZMod m)) := by
          simpa [xFin] using iterate_returnMap1CaseI_odd_generic (m := m) hmEven hx1 hxle hxodd
    _ = linePoint1 (m := m) (TorusD3Even.T1CaseI (m := m) xFin) := by
          ext <;> simp [linePoint1, hT]

theorem iterate_returnMap1CaseI_even_prefix [Fact (5 < m)] (hmEven : Even m)
    {x : ℕ} (hx2 : 2 ≤ x) (hxle : x ≤ m - 4) (hxeven : Even x) :
    let xFin : Fin m := ⟨x, by omega⟩
    ((returnMap1CaseI (m := m)^[m - x]) (linePoint1 (m := m) xFin)) =
      ((0 : ZMod m), (((m - x : ℕ) : ZMod m))) := by
  let xFin : Fin m := ⟨x, by omega⟩
  calc
    ((returnMap1CaseI (m := m)^[m - x]) (linePoint1 (m := m) xFin))
        = ((bulkMap1CaseI (m := m)^[m - x]) (linePoint1 (m := m) xFin)) := by
            refine iterate_eq_iterate_of_eq_on_prefix
              (F := returnMap1CaseI (m := m)) (G := bulkMap1CaseI (m := m))
              (z := linePoint1 (m := m) xFin) (m - x) ?_
            intro t ht
            rw [iterate_bulkMap1CaseI (m := m) t (linePoint1 (m := m) xFin)]
            have hi_pos : 0 < x + t := by omega
            have hi_lt : x + t < m := by omega
            have hk_lt : t < m := by omega
            have hk_ne_neg_one : (((t : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
              exact natCast_ne_neg_one_of_lt (m := m) (n := t) (by omega)
            have hi_ne_zero : (((x + t : ℕ) : ZMod m)) ≠ 0 := by
              exact natCast_ne_zero_of_pos_lt (m := m) (n := x + t) hi_pos hi_lt
            have h00 : ¬ ((((x + t : ℕ) : ZMod m)) = 0 ∧ (((t : ℕ) : ZMod m)) = 0) := by
              intro h
              exact hi_ne_zero h.1
            have hdiag :
                ¬ ((((x + t : ℕ) : ZMod m)) + (((t : ℕ) : ZMod m)) = (-1 : ZMod m) ∧
                    (((x + t : ℕ) : ZMod m)) ≠ 0 ∧
                    (((x + t : ℕ) : ZMod m)) ≠ (-2 : ZMod m) ∧
                    (((x + t : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              have hsumEven : Even (x + 2 * t) := by
                rcases hxeven with ⟨r, hr⟩
                refine ⟨r + t, ?_⟩
                rw [hr]
                ring
              have hsum_ne : (((x + 2 * t : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
                exact natCast_ne_neg_one_of_even (m := m) hmEven hsumEven
              apply hsum_ne
              have hsumEq :
                  ((((x + t : ℕ) : ZMod m)) + (((t : ℕ) : ZMod m))) =
                    (((x + 2 * t : ℕ) : ZMod m)) := by
                simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
                  congrArg (fun n : ℕ => ((n : ℕ) : ZMod m)) (by omega : x + t + t = x + 2 * t)
              exact hsumEq.symm.trans h.1
            have hneg1 :
                ¬ ((((x + t : ℕ) : ZMod m)) = (-1 : ZMod m) ∧ (((t : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              exact hk_ne_neg_one h.2
            have hneg2 :
                ¬ ((((x + t : ℕ) : ZMod m)) = (-2 : ZMod m) ∧ (((t : ℕ) : ZMod m)) = 0) := by
              intro h
              have ht0 : t = 0 := by
                have hmod := (ZMod.natCast_eq_natCast_iff' t 0 m).1 (by simpa using h.2)
                rw [Nat.mod_eq_of_lt hk_lt, Nat.zero_mod] at hmod
                exact hmod
              subst ht0
              have hx_ne_neg_two : (((x : ℕ) : ZMod m)) ≠ (-2 : ZMod m) := by
                exact natCast_ne_neg_two_of_lt (m := m) (n := x) (by omega)
              exact hx_ne_neg_two h.1
            have hi0 :
                ¬ ((((x + t : ℕ) : ZMod m)) = 0 ∧
                    (((t : ℕ) : ZMod m)) ≠ 0 ∧
                    (((t : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              exact hi_ne_zero h.1
            have h1neg1 :
                ¬ ((((x + t : ℕ) : ZMod m)) = (1 : ZMod m) ∧ (((t : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              exact hk_ne_neg_one h.2
            have hneg2one :
                ¬ ((((x + t : ℕ) : ZMod m)) = (-2 : ZMod m) ∧ (((t : ℕ) : ZMod m)) = (1 : ZMod m)) := by
              intro h
              have ht1 : t = 1 := by
                have hmod := (ZMod.natCast_eq_natCast_iff' t 1 m).1 (by simpa using h.2)
                rw [Nat.mod_eq_of_lt hk_lt, Nat.mod_eq_of_lt (by
                  have hm5 : 5 < m := Fact.out
                  omega)] at hmod
                exact hmod
              subst ht1
              have hx1_ne_neg_two : (((x + 1 : ℕ) : ZMod m)) ≠ (-2 : ZMod m) := by
                exact natCast_ne_neg_two_of_lt (m := m) (n := x + 1) (by omega)
              exact hx1_ne_neg_two h.1
            simpa [linePoint1, xFin] using
              returnMap1CaseI_eq_bulk_of_not_special (m := m)
                (i := (((x + t : ℕ) : ZMod m))) (k := (((t : ℕ) : ZMod m)))
                h00 hdiag hneg1 hneg2 hi0 h1neg1 hneg2one
    _ = ((((x + (m - x) : ℕ) : ZMod m)), (((m - x : ℕ) : ZMod m))) := by
          rw [iterate_bulkMap1CaseI (m := m) (m - x) (linePoint1 (m := m) xFin)]
          simp [linePoint1, xFin, Nat.cast_add, add_assoc]
    _ = ((0 : ZMod m), (((m - x : ℕ) : ZMod m))) := by
          have hsum : x + (m - x) = m := by omega
          simp [hsum]

theorem returnMap1CaseI_even_vertical [Fact (5 < m)]
    {x : ℕ} (hx2 : 2 ≤ x) (hxle : x ≤ m - 4) :
    returnMap1CaseI (m := m) ((0 : ZMod m), (((m - x : ℕ) : ZMod m))) =
      ((1 : ZMod m), (((m - x : ℕ) : ZMod m))) := by
  have hk0 : (((m - x : ℕ) : ZMod m)) ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := m - x) (by omega) (by omega)
  have hkneg1 : (((m - x : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := m - x) (by omega)
  simpa using returnMap1CaseI_eq_add_one_of_i_zero (m := m) (k := (((m - x : ℕ) : ZMod m))) hk0 hkneg1

theorem iterate_returnMap1CaseI_even_middle [Fact (5 < m)] (hmEven : Even m)
    {x : ℕ} (hx2 : 2 ≤ x) (hxle : x ≤ m - 4) (hxeven : Even x) :
    let b : ℕ := x / 2 - 1
    ((returnMap1CaseI (m := m)^[b]) ((1 : ZMod m), (((m - x : ℕ) : ZMod m)))) =
      ((((x / 2 : ℕ) : ZMod m)), (((m - x / 2 - 1 : ℕ) : ZMod m))) := by
  let b : ℕ := x / 2 - 1
  calc
    ((returnMap1CaseI (m := m)^[b]) ((1 : ZMod m), (((m - x : ℕ) : ZMod m))))
        = ((bulkMap1CaseI (m := m)^[b]) ((1 : ZMod m), (((m - x : ℕ) : ZMod m)))) := by
            refine iterate_eq_iterate_of_eq_on_prefix
              (F := returnMap1CaseI (m := m)) (G := bulkMap1CaseI (m := m))
              (z := ((1 : ZMod m), (((m - x : ℕ) : ZMod m)))) b ?_
            intro t ht
            rw [iterate_bulkMap1CaseI (m := m) t ((1 : ZMod m), (((m - x : ℕ) : ZMod m)))]
            have hi_pos : 0 < 1 + t := by omega
            have hi_lt : 1 + t < m := by omega
            have hi_ne_zero : (((1 + t : ℕ) : ZMod m)) ≠ 0 := by
              exact natCast_ne_zero_of_pos_lt (m := m) (n := 1 + t) hi_pos hi_lt
            have hi_ne_neg_two : (((1 + t : ℕ) : ZMod m)) ≠ (-2 : ZMod m) := by
              exact natCast_ne_neg_two_of_lt (m := m) (n := 1 + t) (by omega)
            have hk_ne_neg_one : ((((m - x) + t : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
              exact natCast_ne_neg_one_of_lt (m := m) (n := (m - x) + t) (by omega)
            have h00 : ¬ ((((1 + t : ℕ) : ZMod m)) = 0 ∧ ((((m - x) + t : ℕ) : ZMod m)) = 0) := by
              intro h
              exact hi_ne_zero h.1
            have hdiag :
                ¬ ((((1 + t : ℕ) : ZMod m)) + ((((m - x) + t : ℕ) : ZMod m)) = (-1 : ZMod m) ∧
                    (((1 + t : ℕ) : ZMod m)) ≠ 0 ∧
                    (((1 + t : ℕ) : ZMod m)) ≠ (-2 : ZMod m) ∧
                    (((1 + t : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              have hsum_ne : (((m - x + 1 + 2 * t : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
                exact natCast_ne_neg_one_of_lt (m := m) (n := m - x + 1 + 2 * t) (by
                  dsimp [b] at ht
                  omega)
              apply hsum_ne
              have hsumEq :
                  ((((1 + t : ℕ) : ZMod m)) + ((((m - x) + t : ℕ) : ZMod m))) =
                    (((m - x + 1 + 2 * t : ℕ) : ZMod m)) := by
                have hnat : 1 + t + ((m - x) + t) = m - x + 1 + 2 * t := by omega
                simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
                  congrArg (fun n : ℕ => ((n : ℕ) : ZMod m)) hnat
              exact hsumEq.symm.trans h.1
            have hneg1 :
                ¬ ((((1 + t : ℕ) : ZMod m)) = (-1 : ZMod m) ∧ ((((m - x) + t : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              exact hk_ne_neg_one h.2
            have hneg2 :
                ¬ ((((1 + t : ℕ) : ZMod m)) = (-2 : ZMod m) ∧ ((((m - x) + t : ℕ) : ZMod m)) = 0) := by
              intro h
              exact hi_ne_neg_two h.1
            have hi0 :
                ¬ ((((1 + t : ℕ) : ZMod m)) = 0 ∧
                    ((((m - x) + t : ℕ) : ZMod m)) ≠ 0 ∧
                    ((((m - x) + t : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              exact hi_ne_zero h.1
            have h1neg1 :
                ¬ ((((1 + t : ℕ) : ZMod m)) = (1 : ZMod m) ∧ ((((m - x) + t : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              exact hk_ne_neg_one h.2
            have hneg2one :
                ¬ ((((1 + t : ℕ) : ZMod m)) = (-2 : ZMod m) ∧ ((((m - x) + t : ℕ) : ZMod m)) = (1 : ZMod m)) := by
              intro h
              exact hi_ne_neg_two h.1
            simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
              returnMap1CaseI_eq_bulk_of_not_special (m := m)
                (i := (((1 + t : ℕ) : ZMod m))) (k := ((((m - x) + t : ℕ) : ZMod m)))
                h00 hdiag hneg1 hneg2 hi0 h1neg1 hneg2one
    _ = ((((1 + b : ℕ) : ZMod m)), ((((m - x) + b : ℕ) : ZMod m))) := by
          rw [iterate_bulkMap1CaseI (m := m) b ((1 : ZMod m), (((m - x : ℕ) : ZMod m)))]
          simp [Nat.cast_add, add_assoc, add_left_comm, add_comm]
    _ = ((((x / 2 : ℕ) : ZMod m)), (((m - x / 2 - 1 : ℕ) : ZMod m))) := by
          dsimp [b]
          have hfirst : 1 + (x / 2 - 1) = x / 2 := by omega
          have hsecond : (m - x) + (x / 2 - 1) = m - x / 2 - 1 := by
            rcases hxeven with ⟨r, hr⟩
            rw [hr]
            omega
          simp [hfirst, hsecond]

theorem returnMap1CaseI_even_diag [Fact (5 < m)]
    {x : ℕ} (hx2 : 2 ≤ x) (hxle : x ≤ m - 4) (hxeven : Even x) :
    returnMap1CaseI (m := m) ((((x / 2 : ℕ) : ZMod m)), (((m - x / 2 - 1 : ℕ) : ZMod m))) =
      ((((x / 2 + 2 : ℕ) : ZMod m)), (((m - x / 2 - 1 : ℕ) : ZMod m))) := by
  have hdiag :
      (((x / 2 : ℕ) : ZMod m)) + (((m - x / 2 - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) := by
    have hm1 : (((m - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) := by
      exact cast_sub_one_eq_neg_one (m := m) (by
        have hm5 : 5 < m := Fact.out
        omega)
    have hnat : x / 2 + (m - x / 2 - 1) = m - 1 := by omega
    rw [← hm1]
    simpa [Nat.cast_add, add_assoc] using congrArg (fun n : ℕ => ((n : ℕ) : ZMod m)) hnat
  have hi0 : (((x / 2 : ℕ) : ZMod m)) ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := x / 2) (by
      rcases hxeven with ⟨r, hr⟩
      rw [hr]
      omega) (by omega)
  have him2 : (((x / 2 : ℕ) : ZMod m)) ≠ (-2 : ZMod m) := by
    exact natCast_ne_neg_two_of_lt (m := m) (n := x / 2) (by omega)
  have him1 : (((x / 2 : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := x / 2) (by omega)
  have hdir :
      dir1CaseILayerZero (m := m) ((((x / 2 : ℕ) : ZMod m)), (((m - x / 2 - 1 : ℕ) : ZMod m))) = 0 := by
    exact dir1CaseILayerZero_eq_zero_of_diag (m := m) hdiag hi0 him2 him1
  simp [returnMap1CaseI, hdir, Nat.cast_add, add_assoc, add_left_comm, add_comm]

theorem iterate_returnMap1CaseI_even_suffix [Fact (5 < m)]
    {x : ℕ} (hx2 : 2 ≤ x) (hxle : x ≤ m - 4) (hxeven : Even x) :
    ((returnMap1CaseI (m := m)^[x / 2 + 1])
      ((((x / 2 + 2 : ℕ) : ZMod m)), (((m - x / 2 - 1 : ℕ) : ZMod m)))) =
      ((((x + 3 : ℕ) : ZMod m)), (0 : ZMod m)) := by
  calc
    ((returnMap1CaseI (m := m)^[x / 2 + 1])
      ((((x / 2 + 2 : ℕ) : ZMod m)), (((m - x / 2 - 1 : ℕ) : ZMod m))))
        = ((bulkMap1CaseI (m := m)^[x / 2 + 1])
          ((((x / 2 + 2 : ℕ) : ZMod m)), (((m - x / 2 - 1 : ℕ) : ZMod m)))) := by
            refine iterate_eq_iterate_of_eq_on_prefix
              (F := returnMap1CaseI (m := m)) (G := bulkMap1CaseI (m := m))
              (z := ((((x / 2 + 2 : ℕ) : ZMod m)), (((m - x / 2 - 1 : ℕ) : ZMod m)))) (x / 2 + 1) ?_
            intro t ht
            rw [iterate_bulkMap1CaseI (m := m) t ((((x / 2 + 2 : ℕ) : ZMod m)), (((m - x / 2 - 1 : ℕ) : ZMod m)))]
            have hi_pos : 0 < x / 2 + 2 + t := by omega
            have hi_lt : x / 2 + 2 + t < m := by omega
            have hi_ne_zero : (((x / 2 + 2 + t : ℕ) : ZMod m)) ≠ 0 := by
              exact natCast_ne_zero_of_pos_lt (m := m) (n := x / 2 + 2 + t) hi_pos hi_lt
            have h00 : ¬ ((((x / 2 + 2 + t : ℕ) : ZMod m)) = 0 ∧ ((((m - x / 2 - 1) + t : ℕ) : ZMod m)) = 0) := by
              intro h
              exact hi_ne_zero h.1
            have hdiag :
                ¬ ((((x / 2 + 2 + t : ℕ) : ZMod m)) + ((((m - x / 2 - 1) + t : ℕ) : ZMod m)) = (-1 : ZMod m) ∧
                    (((x / 2 + 2 + t : ℕ) : ZMod m)) ≠ 0 ∧
                    (((x / 2 + 2 + t : ℕ) : ZMod m)) ≠ (-2 : ZMod m) ∧
                    (((x / 2 + 2 + t : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              have hsum_ne : (((1 + 2 * t : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
                exact natCast_ne_neg_one_of_lt (m := m) (n := 1 + 2 * t) (by omega)
              apply hsum_ne
              have hsumEq :
                  ((((x / 2 + 2 + t : ℕ) : ZMod m)) + ((((m - x / 2 - 1) + t : ℕ) : ZMod m))) =
                    (((m + (1 + 2 * t) : ℕ) : ZMod m)) := by
                have hnat : x / 2 + 2 + t + ((m - x / 2 - 1) + t) = m + (1 + 2 * t) := by omega
                simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
                  congrArg (fun n : ℕ => ((n : ℕ) : ZMod m)) hnat
              have hmcast : (((m + (1 + 2 * t) : ℕ) : ZMod m)) = (((1 + 2 * t : ℕ) : ZMod m)) := by
                rw [Nat.cast_add, ZMod.natCast_self, zero_add]
              exact (hsumEq.trans hmcast).symm.trans h.1
            have hneg1 :
                ¬ ((((x / 2 + 2 + t : ℕ) : ZMod m)) = (-1 : ZMod m) ∧
                    ((((m - x / 2 - 1) + t : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              have hk_neg_one : ((((m - x / 2 - 1) + t : ℕ) : ZMod m)) = (-1 : ZMod m) := h.2
              have hk_eq : (m - x / 2 - 1) + t = m - 1 := by
                have hmod := (ZMod.natCast_eq_natCast_iff' ((m - x / 2 - 1) + t) (m - 1) m).1 (by
                  have hm1 : (((m - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) := by
                    exact cast_sub_one_eq_neg_one (m := m) (by
                      have hm5 : 5 < m := Fact.out
                      omega)
                  exact hk_neg_one.trans hm1.symm)
                rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by
                  have hm5 : 5 < m := Fact.out
                  omega)] at hmod
                exact hmod
              have ht_eq : t = x / 2 := by omega
              have hi_last_lt : x / 2 + 2 + t < m - 1 := by
                rw [ht_eq]
                omega
              have hi_last_ne : (((x / 2 + 2 + t : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
                exact natCast_ne_neg_one_of_lt (m := m) (n := x / 2 + 2 + t) (by omega)
              exact hi_last_ne h.1
            have hneg2 :
                ¬ ((((x / 2 + 2 + t : ℕ) : ZMod m)) = (-2 : ZMod m) ∧
                    ((((m - x / 2 - 1) + t : ℕ) : ZMod m)) = 0) := by
              intro h
              have hk_pos : 0 < (m - x / 2 - 1) + t := by omega
              have hk_lt : (m - x / 2 - 1) + t < m := by omega
              exact natCast_ne_zero_of_pos_lt (m := m) (n := (m - x / 2 - 1) + t) hk_pos hk_lt h.2
            have hi0 :
                ¬ ((((x / 2 + 2 + t : ℕ) : ZMod m)) = 0 ∧
                    ((((m - x / 2 - 1) + t : ℕ) : ZMod m)) ≠ 0 ∧
                    ((((m - x / 2 - 1) + t : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              exact hi_ne_zero h.1
            have h1neg1 :
                ¬ ((((x / 2 + 2 + t : ℕ) : ZMod m)) = (1 : ZMod m) ∧
                    ((((m - x / 2 - 1) + t : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              have hi_ge : 3 ≤ x / 2 + 2 + t := by omega
              exact natCast_ne_one_of_two_le_lt (m := m) (n := x / 2 + 2 + t) (by omega) hi_lt h.1
            have hneg2one :
                ¬ ((((x / 2 + 2 + t : ℕ) : ZMod m)) = (-2 : ZMod m) ∧
                    ((((m - x / 2 - 1) + t : ℕ) : ZMod m)) = (1 : ZMod m)) := by
              intro h
              have hk_ne_one : ((((m - x / 2 - 1) + t : ℕ) : ZMod m)) ≠ 1 := by
                exact natCast_ne_one_of_two_le_lt (m := m) (n := (m - x / 2 - 1) + t) (by omega) (by omega)
              exact hk_ne_one h.2
            simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
              returnMap1CaseI_eq_bulk_of_not_special (m := m)
                (i := (((x / 2 + 2 + t : ℕ) : ZMod m))) (k := ((((m - x / 2 - 1) + t : ℕ) : ZMod m)))
                h00 hdiag hneg1 hneg2 hi0 h1neg1 hneg2one
    _ = ((((x / 2 + 2 + (x / 2 + 1) : ℕ) : ZMod m)), ((((m - x / 2 - 1) + (x / 2 + 1) : ℕ) : ZMod m))) := by
          rw [iterate_bulkMap1CaseI (m := m) (x / 2 + 1)
            ((((x / 2 + 2 : ℕ) : ZMod m)), (((m - x / 2 - 1 : ℕ) : ZMod m)))]
          simp [Nat.cast_add, add_assoc, add_left_comm, add_comm]
    _ = ((((x + 3 : ℕ) : ZMod m)), (0 : ZMod m)) := by
          have hfirst : x / 2 + 2 + (x / 2 + 1) = x + 3 := by
            rcases hxeven with ⟨r, hr⟩
            rw [hr]
            omega
          have hsecond : (m - x / 2 - 1) + (x / 2 + 1) = m := by
            omega
          simp [hfirst, hsecond]

theorem iterate_returnMap1CaseI_even_generic [Fact (5 < m)] (hmEven : Even m)
    {x : ℕ} (hx2 : 2 ≤ x) (hxle : x ≤ m - 4) (hxeven : Even x) :
    let xFin : Fin m := ⟨x, by omega⟩
    ((returnMap1CaseI (m := m)^[m + 2]) (linePoint1 (m := m) xFin)) =
      ((((x + 3 : ℕ) : ZMod m)), (0 : ZMod m)) := by
  let xFin : Fin m := ⟨x, by omega⟩
  have hsplit1 : m + 2 = (x / 2 + 1) + (1 + ((x / 2 - 1) + (1 + (m - x)))) := by
    rcases hxeven with ⟨r, hr⟩
    rw [hr]
    omega
  have hiter1 :
      ((returnMap1CaseI (m := m)^[m + 2]) (linePoint1 (m := m) xFin)) =
        ((returnMap1CaseI (m := m)^[x / 2 + 1])
          (((returnMap1CaseI (m := m)^[1 + ((x / 2 - 1) + (1 + (m - x)))])
            (linePoint1 (m := m) xFin)))) := by
    rw [hsplit1]
    simpa using Function.iterate_add_apply (f := returnMap1CaseI (m := m)) (m := x / 2 + 1)
      (n := 1 + ((x / 2 - 1) + (1 + (m - x)))) (linePoint1 (m := m) xFin)
  have hiter2 :
      ((returnMap1CaseI (m := m)^[1 + ((x / 2 - 1) + (1 + (m - x)))])
        (linePoint1 (m := m) xFin)) =
        returnMap1CaseI (m := m)
          (((returnMap1CaseI (m := m)^[(x / 2 - 1) + (1 + (m - x))])
            (linePoint1 (m := m) xFin))) := by
    simpa using Function.iterate_add_apply (f := returnMap1CaseI (m := m)) (m := 1)
      (n := (x / 2 - 1) + (1 + (m - x))) (linePoint1 (m := m) xFin)
  have hiter3 :
      ((returnMap1CaseI (m := m)^[(x / 2 - 1) + (1 + (m - x))]) (linePoint1 (m := m) xFin)) =
        ((returnMap1CaseI (m := m)^[x / 2 - 1])
          (((returnMap1CaseI (m := m)^[1 + (m - x)]) (linePoint1 (m := m) xFin)))) := by
    simpa using Function.iterate_add_apply (f := returnMap1CaseI (m := m)) (m := x / 2 - 1)
      (n := 1 + (m - x)) (linePoint1 (m := m) xFin)
  have hiter4 :
      ((returnMap1CaseI (m := m)^[1 + (m - x)]) (linePoint1 (m := m) xFin)) =
        returnMap1CaseI (m := m)
          (((returnMap1CaseI (m := m)^[m - x]) (linePoint1 (m := m) xFin))) := by
    simpa using Function.iterate_add_apply (f := returnMap1CaseI (m := m)) (m := 1)
      (n := m - x) (linePoint1 (m := m) xFin)
  calc
    ((returnMap1CaseI (m := m)^[m + 2]) (linePoint1 (m := m) xFin))
        = ((returnMap1CaseI (m := m)^[x / 2 + 1])
            (((returnMap1CaseI (m := m)^[1 + ((x / 2 - 1) + (1 + (m - x)))])
              (linePoint1 (m := m) xFin)))) := by
              exact hiter1
    _ = ((returnMap1CaseI (m := m)^[x / 2 + 1])
            (returnMap1CaseI (m := m)
              (((returnMap1CaseI (m := m)^[(x / 2 - 1) + (1 + (m - x))])
                (linePoint1 (m := m) xFin))))) := by
              rw [hiter2]
    _ = ((returnMap1CaseI (m := m)^[x / 2 + 1])
            (returnMap1CaseI (m := m)
              (((returnMap1CaseI (m := m)^[x / 2 - 1])
                (((returnMap1CaseI (m := m)^[1 + (m - x)]) (linePoint1 (m := m) xFin))))))) := by
              rw [hiter3]
    _ = ((returnMap1CaseI (m := m)^[x / 2 + 1])
            (returnMap1CaseI (m := m)
              (((returnMap1CaseI (m := m)^[x / 2 - 1])
                (returnMap1CaseI (m := m)
                  (((returnMap1CaseI (m := m)^[m - x]) (linePoint1 (m := m) xFin)))))))) := by
              rw [hiter4]
    _ = ((returnMap1CaseI (m := m)^[x / 2 + 1])
            (returnMap1CaseI (m := m)
              (((returnMap1CaseI (m := m)^[x / 2 - 1])
                (returnMap1CaseI (m := m) ((0 : ZMod m), (((m - x : ℕ) : ZMod m)))))))) := by
              rw [iterate_returnMap1CaseI_even_prefix (m := m) hmEven hx2 hxle hxeven]
    _ = ((returnMap1CaseI (m := m)^[x / 2 + 1])
            (returnMap1CaseI (m := m)
              (((returnMap1CaseI (m := m)^[x / 2 - 1])
                ((1 : ZMod m), (((m - x : ℕ) : ZMod m))))))) := by
              rw [returnMap1CaseI_even_vertical (m := m) hx2 hxle]
    _ = ((returnMap1CaseI (m := m)^[x / 2 + 1])
            (returnMap1CaseI (m := m)
              ((((x / 2 : ℕ) : ZMod m)), (((m - x / 2 - 1 : ℕ) : ZMod m))))) := by
              rw [iterate_returnMap1CaseI_even_middle (m := m) hmEven hx2 hxle hxeven]
    _ = ((returnMap1CaseI (m := m)^[x / 2 + 1])
            ((((x / 2 + 2 : ℕ) : ZMod m)), (((m - x / 2 - 1 : ℕ) : ZMod m)))) := by
              rw [returnMap1CaseI_even_diag (m := m) hx2 hxle hxeven]
    _ = ((((x + 3 : ℕ) : ZMod m)), (0 : ZMod m)) := by
          exact iterate_returnMap1CaseI_even_suffix (m := m) hx2 hxle hxeven

theorem firstReturn_line_even_generic [Fact (5 < m)] (hmEven : Even m)
    {x : ℕ} (hx2 : 2 ≤ x) (hxle : x ≤ m - 4) (hxeven : Even x) :
    let xFin : Fin m := ⟨x, by omega⟩
    ((returnMap1CaseI (m := m)^[TorusD3Even.rho1CaseI (m := m) xFin]) (linePoint1 (m := m) xFin)) =
      linePoint1 (m := m) (TorusD3Even.T1CaseI (m := m) xFin) := by
  let xFin : Fin m := ⟨x, by omega⟩
  have hx0 : xFin.1 ≠ 0 := by
    simp [xFin]
    omega
  have hxm3 : xFin.1 ≠ m - 3 := by
    simp [xFin]
    omega
  have hxm2 : xFin.1 ≠ m - 2 := by
    simp [xFin]
    omega
  have hxm1 : xFin.1 ≠ m - 1 := by
    simp [xFin]
    omega
  have hrho : TorusD3Even.rho1CaseI (m := m) xFin = m + 2 := by
    simp [TorusD3Even.rho1CaseI, hx0, hxm2, hxm3, hxm1]
  have hT : (TorusD3Even.T1CaseI (m := m) xFin).1 = x + 3 := by
    simpa [xFin] using TorusD3Even.T1CaseI_eq_add_three_of_ne_special (m := m)
      (x := xFin) hx0 hxm3 hxm2 hxm1
  calc
    ((returnMap1CaseI (m := m)^[TorusD3Even.rho1CaseI (m := m) xFin]) (linePoint1 (m := m) xFin))
        = ((returnMap1CaseI (m := m)^[m + 2]) (linePoint1 (m := m) xFin)) := by rw [hrho]
    _ = ((((x + 3 : ℕ) : ZMod m)), (0 : ZMod m)) := by
          simpa [xFin] using iterate_returnMap1CaseI_even_generic (m := m) hmEven hx2 hxle hxeven
    _ = linePoint1 (m := m) (TorusD3Even.T1CaseI (m := m) xFin) := by
          ext <;> simp [linePoint1, hT]

theorem dir1CaseILayerZero_eq_zero_origin :
    dir1CaseILayerZero (m := m) ((0 : ZMod m), (0 : ZMod m)) = 0 := by
  simp [dir1CaseILayerZero]

theorem dir1CaseILayerZero_eq_zero_neg_two_zero :
    dir1CaseILayerZero (m := m) ((-2 : ZMod m), (0 : ZMod m)) = 0 := by
  simp [dir1CaseILayerZero]

theorem dir1CaseILayerZero_eq_zero_neg_one_neg_one :
    dir1CaseILayerZero (m := m) ((-1 : ZMod m), (-1 : ZMod m)) = 0 := by
  simp [dir1CaseILayerZero]

theorem dir1CaseILayerZero_eq_one_one_neg_one [Fact (2 < m)] :
    dir1CaseILayerZero (m := m) ((1 : ZMod m), (-1 : ZMod m)) = 1 := by
  letI : Fact (1 < m) := ⟨lt_trans (by decide : 1 < 2) Fact.out⟩
  have hsum : ((1 : ZMod m) + (-1 : ZMod m)) ≠ (-1 : ZMod m) := by
    simpa using (one_ne_zero (m := m))
  have hneg1 : (-1 : ZMod m) ≠ 0 := by
    simpa using neg_ne_zero.mpr (one_ne_zero (m := m))
  simp [dir1CaseILayerZero, hsum, hneg1, one_ne_neg_one (m := m)]

theorem dir1CaseILayerZero_eq_one_neg_two_one [Fact (2 < m)] :
    dir1CaseILayerZero (m := m) ((-2 : ZMod m), (1 : ZMod m)) = 1 := by
  letI : Fact (1 < m) := ⟨lt_trans (by decide : 1 < 2) Fact.out⟩
  have h20 : (2 : ZMod m) ≠ 0 := two_ne_zero (m := m)
  have h21 : (2 : ZMod m) ≠ 1 := two_ne_one (m := m)
  have h10 : (1 : ZMod m) ≠ 0 := one_ne_zero (m := m)
  simp [dir1CaseILayerZero, h20, h21, h10]

theorem returnMap1CaseI_eq_add_two_of_diag {i k : ZMod m}
    (hdiag : i + k = (-1 : ZMod m)) (hi0 : i ≠ 0) (him2 : i ≠ (-2 : ZMod m))
    (him1 : i ≠ (-1 : ZMod m)) :
    returnMap1CaseI (m := m) (i, k) = (i + 2, k) := by
  simp [returnMap1CaseI, dir1CaseILayerZero_eq_zero_of_diag (m := m) hdiag hi0 him2 him1]

theorem returnMap1CaseI_origin :
    returnMap1CaseI (m := m) ((0 : ZMod m), (0 : ZMod m)) = ((2 : ZMod m), (0 : ZMod m)) := by
  simp [returnMap1CaseI, dir1CaseILayerZero_eq_zero_origin (m := m)]

theorem returnMap1CaseI_neg_two_zero :
    returnMap1CaseI (m := m) ((-2 : ZMod m), (0 : ZMod m)) = ((0 : ZMod m), (0 : ZMod m)) := by
  simp [returnMap1CaseI, dir1CaseILayerZero_eq_zero_neg_two_zero (m := m)]

theorem returnMap1CaseI_neg_one_neg_one :
    returnMap1CaseI (m := m) ((-1 : ZMod m), (-1 : ZMod m)) = ((1 : ZMod m), (-1 : ZMod m)) := by
  ext <;> simp [returnMap1CaseI, dir1CaseILayerZero_eq_zero_neg_one_neg_one (m := m)] <;> ring

theorem returnMap1CaseI_one_neg_one [Fact (2 < m)] :
    returnMap1CaseI (m := m) ((1 : ZMod m), (-1 : ZMod m)) = ((2 : ZMod m), (-1 : ZMod m)) := by
  ext <;> simp [returnMap1CaseI, dir1CaseILayerZero_eq_one_one_neg_one (m := m)] <;> ring

theorem returnMap1CaseI_neg_two_one [Fact (2 < m)] :
    returnMap1CaseI (m := m) ((-2 : ZMod m), (1 : ZMod m)) = ((-1 : ZMod m), (1 : ZMod m)) := by
  ext <;> simp [returnMap1CaseI, dir1CaseILayerZero_eq_one_neg_two_one (m := m)] <;> ring

theorem returnMap1CaseI_neg_one_one [Fact (5 < m)] :
    returnMap1CaseI (m := m) ((-1 : ZMod m), (1 : ZMod m)) = ((0 : ZMod m), (2 : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  have hneg10 : (-1 : ZMod m) ≠ 0 := by
    simpa using (neg_ne_zero.mpr (one_ne_zero (m := m)))
  have hneg1neg2 : (-1 : ZMod m) ≠ (-2 : ZMod m) := by
    intro hEq
    have hstep := congrArg (fun z : ZMod m => z + 2) hEq
    have hzero : ((-1 : ZMod m) + 2) = 0 := by
      simpa using hstep
    have hone : ((-1 : ZMod m) + 2) = (1 : ZMod m) := by
      ring
    have hzero' : (1 : ZMod m) = 0 := by
      exact hone.symm.trans hzero
    exact (one_ne_zero (m := m)) hzero'
  have h00 : ¬ (((-1 : ZMod m) = 0) ∧ ((1 : ZMod m) = 0)) := by
    intro h
    exact one_ne_zero (m := m) h.2
  have hdiag :
      ¬ (((-1 : ZMod m) + (1 : ZMod m) = (-1 : ZMod m)) ∧
          ((-1 : ZMod m)) ≠ 0 ∧
          ((-1 : ZMod m)) ≠ (-2 : ZMod m) ∧
          ((-1 : ZMod m)) ≠ (-1 : ZMod m)) := by
    intro h
    exact h.2.2.2 rfl
  have hneg1 : ¬ (((-1 : ZMod m) = (-1 : ZMod m)) ∧ ((1 : ZMod m) = (-1 : ZMod m))) := by
    intro h
    exact one_ne_neg_one (m := m) h.2
  have hneg2 : ¬ (((-1 : ZMod m) = (-2 : ZMod m)) ∧ ((1 : ZMod m) = 0)) := by
    intro h
    exact one_ne_zero (m := m) h.2
  have hi0 :
      ¬ (((-1 : ZMod m) = 0) ∧
          ((1 : ZMod m)) ≠ 0 ∧
          ((1 : ZMod m)) ≠ (-1 : ZMod m)) := by
    intro h
    exact hneg10 h.1
  have h1neg1 : ¬ (((-1 : ZMod m) = (1 : ZMod m)) ∧ ((1 : ZMod m) = (-1 : ZMod m))) := by
    intro h
    exact one_ne_neg_one (m := m) h.2
  have hneg2one : ¬ (((-1 : ZMod m) = (-2 : ZMod m)) ∧ ((1 : ZMod m) = (1 : ZMod m))) := by
    intro h
    exact hneg1neg2 h.1
  calc
    returnMap1CaseI (m := m) ((-1 : ZMod m), (1 : ZMod m))
        = bulkMap1CaseI (m := m) ((-1 : ZMod m), (1 : ZMod m)) := by
            exact returnMap1CaseI_eq_bulk_of_not_special (m := m)
              (i := (-1 : ZMod m)) (k := (1 : ZMod m))
              h00 hdiag hneg1 hneg2 hi0 h1neg1 hneg2one
    _ = ((0 : ZMod m), (2 : ZMod m)) := by
          ext <;> simp [bulkMap1CaseI] <;> ring

theorem returnMap1CaseI_zero_one [Fact (5 < m)] :
    returnMap1CaseI (m := m) ((0 : ZMod m), (1 : ZMod m)) = ((1 : ZMod m), (1 : ZMod m)) := by
  have hk0 : (1 : ZMod m) ≠ 0 := one_ne_zero (m := m)
  have hkneg1 : (1 : ZMod m) ≠ (-1 : ZMod m) := one_ne_neg_one (m := m)
  simpa using returnMap1CaseI_eq_add_one_of_i_zero (m := m) (k := (1 : ZMod m)) hk0 hkneg1

theorem returnMap1CaseI_zero_two [Fact (5 < m)] :
    returnMap1CaseI (m := m) ((0 : ZMod m), (2 : ZMod m)) = ((1 : ZMod m), (2 : ZMod m)) := by
  have hk0 : (2 : ZMod m) ≠ 0 := two_ne_zero (m := m)
  have hkneg1 : (2 : ZMod m) ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := 2) (by
      have hm5 : 5 < m := Fact.out
      omega)
  simpa using returnMap1CaseI_eq_add_one_of_i_zero (m := m) (k := (2 : ZMod m)) hk0 hkneg1

theorem returnMap1CaseI_two_neg_one [Fact (5 < m)] :
    returnMap1CaseI (m := m) ((2 : ZMod m), (-1 : ZMod m)) = ((3 : ZMod m), (0 : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  have hneg10 : (-1 : ZMod m) ≠ 0 := by
    simpa using (neg_ne_zero.mpr (one_ne_zero (m := m)))
  have h00 : ¬ (((2 : ZMod m) = 0) ∧ (((-1 : ZMod m)) = 0)) := by
    intro h
    exact two_ne_zero (m := m) h.1
  have hdiag :
      ¬ (((2 : ZMod m) + ((-1 : ZMod m)) = (-1 : ZMod m)) ∧
          ((2 : ZMod m)) ≠ 0 ∧
          ((2 : ZMod m)) ≠ (-2 : ZMod m) ∧
          ((2 : ZMod m)) ≠ (-1 : ZMod m)) := by
    intro h
    exact two_ne_zero (m := m) (by simpa using h.1)
  have hneg1 : ¬ (((2 : ZMod m) = (-1 : ZMod m)) ∧ (((-1 : ZMod m)) = (-1 : ZMod m))) := by
    intro h
    exact natCast_ne_neg_one_of_lt (m := m) (n := 2) (by
      have hm5 : 5 < m := Fact.out
      omega) h.1
  have hneg2 : ¬ (((2 : ZMod m) = (-2 : ZMod m)) ∧ (((-1 : ZMod m)) = 0)) := by
    intro h
    exact hneg10 h.2
  have hi0 :
      ¬ (((2 : ZMod m) = 0) ∧
          (((-1 : ZMod m))) ≠ 0 ∧
          (((-1 : ZMod m))) ≠ (-1 : ZMod m)) := by
    intro h
    exact two_ne_zero (m := m) h.1
  have h1neg1 : ¬ (((2 : ZMod m) = (1 : ZMod m)) ∧ (((-1 : ZMod m)) = (-1 : ZMod m))) := by
    intro h
    exact two_ne_one (m := m) h.1
  have hneg2one : ¬ (((2 : ZMod m) = (-2 : ZMod m)) ∧ (((-1 : ZMod m)) = (1 : ZMod m))) := by
    intro h
    exact one_ne_neg_one (m := m) h.2.symm
  calc
    returnMap1CaseI (m := m) ((2 : ZMod m), (-1 : ZMod m))
        = bulkMap1CaseI (m := m) ((2 : ZMod m), (-1 : ZMod m)) := by
            exact returnMap1CaseI_eq_bulk_of_not_special (m := m)
              (i := (2 : ZMod m)) (k := (-1 : ZMod m))
              h00 hdiag hneg1 hneg2 hi0 h1neg1 hneg2one
    _ = ((3 : ZMod m), (0 : ZMod m)) := by
          ext <;> simp [bulkMap1CaseI] <;> ring

theorem returnMap1CaseI_zero_neg_one [Fact (5 < m)] :
    returnMap1CaseI (m := m) ((0 : ZMod m), (-1 : ZMod m)) = ((1 : ZMod m), (0 : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  have hneg10 : (-1 : ZMod m) ≠ 0 := by
    simpa using (neg_ne_zero.mpr (one_ne_zero (m := m)))
  have h0neg1 : (0 : ZMod m) ≠ (-1 : ZMod m) := by
    simpa using natCast_ne_neg_one_of_lt (m := m) (n := 0) (by omega)
  have h0neg2 : (0 : ZMod m) ≠ (-2 : ZMod m) := by
    simpa using natCast_ne_neg_two_of_lt (m := m) (n := 0) (by omega)
  have h00 : ¬ (((0 : ZMod m) = 0) ∧ (((-1 : ZMod m)) = 0)) := by
    intro h
    exact hneg10 h.2
  have hdiag :
      ¬ (((0 : ZMod m) + ((-1 : ZMod m)) = (-1 : ZMod m)) ∧
          ((0 : ZMod m)) ≠ 0 ∧
          ((0 : ZMod m)) ≠ (-2 : ZMod m) ∧
          ((0 : ZMod m)) ≠ (-1 : ZMod m)) := by
    intro h
    exact h.2.1 rfl
  have hneg1 : ¬ (((0 : ZMod m) = (-1 : ZMod m)) ∧ (((-1 : ZMod m)) = (-1 : ZMod m))) := by
    intro h
    exact h0neg1 h.1
  have hneg2 : ¬ (((0 : ZMod m) = (-2 : ZMod m)) ∧ (((-1 : ZMod m)) = 0)) := by
    intro h
    exact h0neg2 h.1
  have hi0 :
      ¬ (((0 : ZMod m) = 0) ∧
          (((-1 : ZMod m))) ≠ 0 ∧
          (((-1 : ZMod m))) ≠ (-1 : ZMod m)) := by
    intro h
    exact h.2.2 rfl
  have h1neg1 : ¬ (((0 : ZMod m) = (1 : ZMod m)) ∧ (((-1 : ZMod m)) = (-1 : ZMod m))) := by
    intro h
    exact one_ne_zero (m := m) h.1.symm
  have hneg2one : ¬ (((0 : ZMod m) = (-2 : ZMod m)) ∧ (((-1 : ZMod m)) = (1 : ZMod m))) := by
    intro h
    exact one_ne_neg_one (m := m) h.2.symm
  calc
    returnMap1CaseI (m := m) ((0 : ZMod m), (-1 : ZMod m))
        = bulkMap1CaseI (m := m) ((0 : ZMod m), (-1 : ZMod m)) := by
            exact returnMap1CaseI_eq_bulk_of_not_special (m := m)
              (i := (0 : ZMod m)) (k := (-1 : ZMod m))
              h00 hdiag hneg1 hneg2 hi0 h1neg1 hneg2one
    _ = ((1 : ZMod m), (0 : ZMod m)) := by
          simp [bulkMap1CaseI]

theorem returnMap1CaseI_line_m_sub_three_start [Fact (5 < m)] :
    let x : Fin m := ⟨m - 3, by
      have hm5 : 5 < m := Fact.out
      omega⟩
    returnMap1CaseI (m := m) (linePoint1 (m := m) x) =
      ((((m - 2 : ℕ) : ZMod m)), (1 : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  let x : Fin m := ⟨m - 3, by
    omega⟩
  have hm3pos : 0 < m - 3 := by omega
  have hm3lt : m - 3 < m := by omega
  have hm2lt : m - 2 < m := by omega
  have hm1lt : m - 1 < m := by omega
  have him0 : (((m - 3 : ℕ) : ZMod m)) ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := m - 3) hm3pos hm3lt
  have himneg1 : (((m - 3 : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := m - 3) (by omega)
  have himneg2 : (((m - 3 : ℕ) : ZMod m)) ≠ (-2 : ZMod m) := by
    exact natCast_ne_neg_two_of_lt (m := m) (n := m - 3) (by omega)
  have h0neg1 : (0 : ZMod m) ≠ (-1 : ZMod m) := by
    simpa using natCast_ne_neg_one_of_lt (m := m) (n := 0) (by omega)
  have h00 : ¬ ((((m - 3 : ℕ) : ZMod m)) = 0 ∧ ((0 : ZMod m) = 0)) := by
    intro h
    exact him0 h.1
  have hdiag :
      ¬ ((((m - 3 : ℕ) : ZMod m)) + ((0 : ZMod m)) = (-1 : ZMod m) ∧
          (((m - 3 : ℕ) : ZMod m)) ≠ 0 ∧
          (((m - 3 : ℕ) : ZMod m)) ≠ (-2 : ZMod m) ∧
          (((m - 3 : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
    intro h
    exact himneg1 (by simpa using h.1)
  have hneg1 : ¬ ((((m - 3 : ℕ) : ZMod m)) = (-1 : ZMod m) ∧ ((0 : ZMod m) = (-1 : ZMod m))) := by
    intro h
    exact himneg1 h.1
  have hneg2 : ¬ ((((m - 3 : ℕ) : ZMod m)) = (-2 : ZMod m) ∧ ((0 : ZMod m) = 0)) := by
    intro h
    exact himneg2 h.1
  have hi0 :
      ¬ ((((m - 3 : ℕ) : ZMod m)) = 0 ∧
          ((0 : ZMod m)) ≠ 0 ∧
          ((0 : ZMod m)) ≠ (-1 : ZMod m)) := by
    intro h
    exact him0 h.1
  have h1neg1 : ¬ ((((m - 3 : ℕ) : ZMod m)) = (1 : ZMod m) ∧ ((0 : ZMod m) = (-1 : ZMod m))) := by
    intro h
    exact h0neg1 h.2
  have hneg2one : ¬ ((((m - 3 : ℕ) : ZMod m)) = (-2 : ZMod m) ∧ ((0 : ZMod m) = (1 : ZMod m))) := by
    intro h
    exact one_ne_zero (m := m) h.2.symm
  calc
    returnMap1CaseI (m := m) (linePoint1 (m := m) x)
        = bulkMap1CaseI (m := m) (linePoint1 (m := m) x) := by
            simpa [linePoint1, x] using
              returnMap1CaseI_eq_bulk_of_not_special (m := m)
                (i := (((m - 3 : ℕ) : ZMod m))) (k := (0 : ZMod m))
                h00 hdiag hneg1 hneg2 hi0 h1neg1 hneg2one
    _ = ((((m - 2 : ℕ) : ZMod m)), (1 : ZMod m)) := by
          have hfst :
              (((m - 3 : ℕ) : ZMod m) + 1) = (((m - 2 : ℕ) : ZMod m)) := by
            simpa [Nat.cast_add] using congrArg (fun n : ℕ => ((n : ℕ) : ZMod m))
              (show (m - 3) + 1 = m - 2 by omega)
          ext <;> simp [bulkMap1CaseI, linePoint1, x, hfst]

theorem returnMap1CaseI_line_m_sub_one_start [Fact (5 < m)] :
    let x : Fin m := ⟨m - 1, by
      have hm5 : 5 < m := Fact.out
      omega⟩
    returnMap1CaseI (m := m) (linePoint1 (m := m) x) =
      ((0 : ZMod m), (1 : ZMod m)) := by
  have hm5 : 5 < m := Fact.out
  let x : Fin m := ⟨m - 1, by
    omega⟩
  have hm1 : (((m - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) := cast_sub_one_eq_neg_one (m := m) (by
    omega)
  have hm1pos : 0 < m - 1 := by omega
  have hm1lt : m - 1 < m := by omega
  have him0 : (((m - 1 : ℕ) : ZMod m)) ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := m - 1) hm1pos hm1lt
  have hneg10 : (-1 : ZMod m) ≠ 0 := by
    simpa using (neg_ne_zero.mpr (one_ne_zero (m := m)))
  have hneg1neg2 : (-1 : ZMod m) ≠ (-2 : ZMod m) := by
    intro hEq
    have hstep := congrArg (fun z : ZMod m => z + 2) hEq
    have hzero : ((-1 : ZMod m) + 2) = 0 := by
      simpa using hstep
    have hone : ((-1 : ZMod m) + 2) = (1 : ZMod m) := by
      ring
    have hzero' : (1 : ZMod m) = 0 := by
      exact hone.symm.trans hzero
    exact (one_ne_zero (m := m)) hzero'
  have h0neg1 : (0 : ZMod m) ≠ (-1 : ZMod m) := by
    simpa using natCast_ne_neg_one_of_lt (m := m) (n := 0) (by omega)
  have h00 : ¬ ((((m - 1 : ℕ) : ZMod m)) = 0 ∧ ((0 : ZMod m) = 0)) := by
    intro h
    exact him0 h.1
  have hdiag :
      ¬ ((((m - 1 : ℕ) : ZMod m)) + ((0 : ZMod m)) = (-1 : ZMod m) ∧
          (((m - 1 : ℕ) : ZMod m)) ≠ 0 ∧
          (((m - 1 : ℕ) : ZMod m)) ≠ (-2 : ZMod m) ∧
          (((m - 1 : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
    intro h
    exact h.2.2.2 hm1
  have hneg1 : ¬ ((((m - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) ∧ ((0 : ZMod m) = (-1 : ZMod m))) := by
    intro h
    exact h0neg1 h.2
  have hneg2 : ¬ ((((m - 1 : ℕ) : ZMod m)) = (-2 : ZMod m) ∧ ((0 : ZMod m) = 0)) := by
    intro h
    exact hneg1neg2 (by simpa [hm1] using h.1)
  have hi0 :
      ¬ ((((m - 1 : ℕ) : ZMod m)) = 0 ∧
          ((0 : ZMod m)) ≠ 0 ∧
          ((0 : ZMod m)) ≠ (-1 : ZMod m)) := by
    intro h
    exact him0 h.1
  have h1neg1 : ¬ ((((m - 1 : ℕ) : ZMod m)) = (1 : ZMod m) ∧ ((0 : ZMod m) = (-1 : ZMod m))) := by
    intro h
    exact h0neg1 h.2
  have hneg2one : ¬ ((((m - 1 : ℕ) : ZMod m)) = (-2 : ZMod m) ∧ ((0 : ZMod m) = (1 : ZMod m))) := by
    intro h
    exact one_ne_zero (m := m) h.2.symm
  calc
    returnMap1CaseI (m := m) (linePoint1 (m := m) x)
        = bulkMap1CaseI (m := m) (linePoint1 (m := m) x) := by
            simpa [linePoint1, x] using
              returnMap1CaseI_eq_bulk_of_not_special (m := m)
                (i := (((m - 1 : ℕ) : ZMod m))) (k := (0 : ZMod m))
                h00 hdiag hneg1 hneg2 hi0 h1neg1 hneg2one
    _ = ((0 : ZMod m), (1 : ZMod m)) := by
          simp [bulkMap1CaseI, linePoint1, x, hm1]

theorem iterate_returnMap1CaseI_m_sub_three_middle [Fact (5 < m)] (hmEven : Even m) :
    ((returnMap1CaseI (m := m)^[m / 2 - 2]) ((1 : ZMod m), (2 : ZMod m))) =
      ((((m / 2 - 1 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m))) := by
  calc
    ((returnMap1CaseI (m := m)^[m / 2 - 2]) ((1 : ZMod m), (2 : ZMod m)))
        = ((bulkMap1CaseI (m := m)^[m / 2 - 2]) ((1 : ZMod m), (2 : ZMod m))) := by
            refine iterate_eq_iterate_of_eq_on_prefix
              (F := returnMap1CaseI (m := m)) (G := bulkMap1CaseI (m := m))
              (z := ((1 : ZMod m), (2 : ZMod m))) (m / 2 - 2) ?_
            intro t ht
            rw [iterate_bulkMap1CaseI (m := m) t ((1 : ZMod m), (2 : ZMod m))]
            have hi_pos : 0 < 1 + t := by omega
            have hi_lt : 1 + t < m := by
              rcases hmEven with ⟨q, hq⟩
              rw [hq] at ht ⊢
              omega
            have hk_pos : 0 < 2 + t := by omega
            have hk_lt : 2 + t < m := by
              rcases hmEven with ⟨q, hq⟩
              rw [hq] at ht ⊢
              omega
            have hi_ne_zero : (((1 + t : ℕ) : ZMod m)) ≠ 0 := by
              exact natCast_ne_zero_of_pos_lt (m := m) (n := 1 + t) hi_pos hi_lt
            have hk_ne_zero : (((2 + t : ℕ) : ZMod m)) ≠ 0 := by
              exact natCast_ne_zero_of_pos_lt (m := m) (n := 2 + t) hk_pos hk_lt
            have hk_ne_neg_one : (((2 + t : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
              exact natCast_ne_neg_one_of_lt (m := m) (n := 2 + t) (by
                rcases hmEven with ⟨q, hq⟩
                rw [hq] at ht ⊢
                omega)
            have hk_ne_one : (((2 + t : ℕ) : ZMod m)) ≠ 1 := by
              exact natCast_ne_one_of_two_le_lt (m := m) (n := 2 + t) (by omega) hk_lt
            have h00 : ¬ ((((1 + t : ℕ) : ZMod m)) = 0 ∧ (((2 + t : ℕ) : ZMod m)) = 0) := by
              intro h
              exact hi_ne_zero h.1
            have hdiag :
                ¬ ((((1 + t : ℕ) : ZMod m)) + (((2 + t : ℕ) : ZMod m)) = (-1 : ZMod m) ∧
                    (((1 + t : ℕ) : ZMod m)) ≠ 0 ∧
                    (((1 + t : ℕ) : ZMod m)) ≠ (-2 : ZMod m) ∧
                    (((1 + t : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              have hsum_ne : (((3 + 2 * t : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
                rcases hmEven with ⟨q, hq⟩
                have hmhalf : m / 2 = q := by
                  rw [hq]
                  omega
                exact natCast_ne_neg_one_of_lt (m := m) (n := 3 + 2 * t) (by
                  rw [hmhalf] at ht
                  rw [hq]
                  omega)
              apply hsum_ne
              have hsumEq :
                  ((((1 + t : ℕ) : ZMod m)) + (((2 + t : ℕ) : ZMod m))) =
                    (((3 + 2 * t : ℕ) : ZMod m)) := by
                have hsumEq' :
                    (((3 + 2 * t : ℕ) : ZMod m)) =
                      ((((1 + t : ℕ) : ZMod m)) + (((2 + t : ℕ) : ZMod m))) := by
                  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_add, Nat.cast_add]
                  ring
                exact hsumEq'.symm
              exact hsumEq.symm.trans h.1
            have hneg1 :
                ¬ ((((1 + t : ℕ) : ZMod m)) = (-1 : ZMod m) ∧ (((2 + t : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              exact hk_ne_neg_one h.2
            have hneg2 :
                ¬ ((((1 + t : ℕ) : ZMod m)) = (-2 : ZMod m) ∧ (((2 + t : ℕ) : ZMod m)) = 0) := by
              intro h
              exact hk_ne_zero h.2
            have hi0 :
                ¬ ((((1 + t : ℕ) : ZMod m)) = 0 ∧
                    (((2 + t : ℕ) : ZMod m)) ≠ 0 ∧
                    (((2 + t : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              exact hi_ne_zero h.1
            have h1neg1 :
                ¬ ((((1 + t : ℕ) : ZMod m)) = (1 : ZMod m) ∧ (((2 + t : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              exact hk_ne_neg_one h.2
            have hneg2one :
                ¬ ((((1 + t : ℕ) : ZMod m)) = (-2 : ZMod m) ∧ (((2 + t : ℕ) : ZMod m)) = (1 : ZMod m)) := by
              intro h
              exact hk_ne_one h.2
            simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
              returnMap1CaseI_eq_bulk_of_not_special (m := m)
                (i := (((1 + t : ℕ) : ZMod m))) (k := (((2 + t : ℕ) : ZMod m)))
                h00 hdiag hneg1 hneg2 hi0 h1neg1 hneg2one
    _ = ((((1 + (m / 2 - 2) : ℕ) : ZMod m)), (((2 + (m / 2 - 2) : ℕ) : ZMod m))) := by
          rw [iterate_bulkMap1CaseI (m := m) (m / 2 - 2) ((1 : ZMod m), (2 : ZMod m))]
          simp [Nat.cast_add, add_assoc, add_left_comm, add_comm]
    _ = ((((m / 2 - 1 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m))) := by
          have hm5 : 5 < m := Fact.out
          rcases hmEven with ⟨q, hq⟩
          have hmhalf : m / 2 = q := by
            rw [hq]
            omega
          have hq3 : 3 ≤ q := by
            rw [hq] at hm5
            omega
          have hfirst : 1 + (m / 2 - 2) = m / 2 - 1 := by
            rw [hmhalf]
            omega
          have hsecond : 2 + (m / 2 - 2) = m / 2 := by
            rw [hmhalf]
            omega
          simp [hfirst, hsecond]

theorem returnMap1CaseI_m_sub_three_diag [Fact (5 < m)] (hmEven : Even m) :
    returnMap1CaseI (m := m) ((((m / 2 - 1 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m))) =
      ((((m / 2 + 1 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m))) := by
  have hm5 : 5 < m := Fact.out
  rcases hmEven with ⟨q, hq⟩
  have hmhalf : m / 2 = q := by
    rw [hq]
    omega
  have hq3 : 3 ≤ q := by
    rw [hq] at hm5
    omega
  have hdiag :
      (((m / 2 - 1 : ℕ) : ZMod m)) + (((m / 2 : ℕ) : ZMod m)) = (-1 : ZMod m) := by
    have hm1 : (((m - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) := by
      exact cast_sub_one_eq_neg_one (m := m) (by
        have hm5 : 5 < m := Fact.out
        omega)
    have hnat : m / 2 - 1 + m / 2 = m - 1 := by
      rw [hmhalf, hq]
      omega
    rw [← hm1]
    simpa [Nat.cast_add, add_assoc] using congrArg (fun n : ℕ => ((n : ℕ) : ZMod m)) hnat
  have hi0 : (((m / 2 - 1 : ℕ) : ZMod m)) ≠ 0 := by
    rw [hmhalf]
    exact natCast_ne_zero_of_pos_lt (m := m) (n := q - 1) (by omega) (by omega)
  have him2 : (((m / 2 - 1 : ℕ) : ZMod m)) ≠ (-2 : ZMod m) := by
    rw [hmhalf]
    exact natCast_ne_neg_two_of_lt (m := m) (n := q - 1) (by omega)
  have him1 : (((m / 2 - 1 : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
    rw [hmhalf]
    exact natCast_ne_neg_one_of_lt (m := m) (n := q - 1) (by omega)
  calc
    returnMap1CaseI (m := m) ((((m / 2 - 1 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m)))
        = ((((m / 2 - 1 : ℕ) : ZMod m)) + 2, (((m / 2 : ℕ) : ZMod m))) := by
            exact returnMap1CaseI_eq_add_two_of_diag (m := m) hdiag hi0 him2 him1
    _ = ((((m / 2 + 1 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m))) := by
          have hfirst : m / 2 - 1 + 2 = m / 2 + 1 := by
            rw [hmhalf]
            omega
          have hcoord :
              (((m / 2 - 1 : ℕ) : ZMod m)) + 2 = (((m / 2 + 1 : ℕ) : ZMod m)) := by
            simpa [Nat.cast_add] using congrArg (fun n : ℕ => ((n : ℕ) : ZMod m)) hfirst
          ext
          · exact hcoord
          · rfl

theorem iterate_returnMap1CaseI_m_sub_three_tail [Fact (5 < m)] (hmEven : Even m) :
    ((returnMap1CaseI (m := m)^[m / 2 - 1])
      ((((m / 2 + 1 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m)))) =
      ((0 : ZMod m), (-1 : ZMod m)) := by
  calc
    ((returnMap1CaseI (m := m)^[m / 2 - 1])
      ((((m / 2 + 1 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m))))
        = ((bulkMap1CaseI (m := m)^[m / 2 - 1])
            ((((m / 2 + 1 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m)))) := by
            refine iterate_eq_iterate_of_eq_on_prefix
              (F := returnMap1CaseI (m := m)) (G := bulkMap1CaseI (m := m))
              (z := ((((m / 2 + 1 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m)))) (m / 2 - 1) ?_
            intro t ht
            rw [iterate_bulkMap1CaseI (m := m) t
              ((((m / 2 + 1 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m)))]
            have hi_pos : 0 < m / 2 + 1 + t := by
              rcases hmEven with ⟨q, hq⟩
              rw [hq]
              omega
            have hi_lt : m / 2 + 1 + t < m := by
              rcases hmEven with ⟨q, hq⟩
              rw [hq] at ht ⊢
              omega
            have hk_pos : 0 < m / 2 + t := by
              rcases hmEven with ⟨q, hq⟩
              rw [hq]
              omega
            have hk_lt : m / 2 + t < m := by
              rcases hmEven with ⟨q, hq⟩
              rw [hq] at ht ⊢
              omega
            have hi_ne_zero : (((m / 2 + 1 + t : ℕ) : ZMod m)) ≠ 0 := by
              exact natCast_ne_zero_of_pos_lt (m := m) (n := m / 2 + 1 + t) hi_pos hi_lt
            have hk_ne_zero : (((m / 2 + t : ℕ) : ZMod m)) ≠ 0 := by
              exact natCast_ne_zero_of_pos_lt (m := m) (n := m / 2 + t) hk_pos hk_lt
            have hk_ne_neg_one : (((m / 2 + t : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
              exact natCast_ne_neg_one_of_lt (m := m) (n := m / 2 + t) (by
                rcases hmEven with ⟨q, hq⟩
                rw [hq] at ht ⊢
                omega)
            have hk_ne_one : (((m / 2 + t : ℕ) : ZMod m)) ≠ 1 := by
              exact natCast_ne_one_of_two_le_lt (m := m) (n := m / 2 + t) (by
                rcases hmEven with ⟨q, hq⟩
                rw [hq]
                omega) hk_lt
            have h00 :
                ¬ ((((m / 2 + 1 + t : ℕ) : ZMod m)) = 0 ∧
                    (((m / 2 + t : ℕ) : ZMod m)) = 0) := by
              intro h
              exact hi_ne_zero h.1
            have hdiag :
                ¬ ((((m / 2 + 1 + t : ℕ) : ZMod m)) + (((m / 2 + t : ℕ) : ZMod m)) = (-1 : ZMod m) ∧
                    (((m / 2 + 1 + t : ℕ) : ZMod m)) ≠ 0 ∧
                    (((m / 2 + 1 + t : ℕ) : ZMod m)) ≠ (-2 : ZMod m) ∧
                    (((m / 2 + 1 + t : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              have hsum_ne : (((1 + 2 * t : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
                exact natCast_ne_neg_one_of_lt (m := m) (n := 1 + 2 * t) (by
                  rcases hmEven with ⟨q, hq⟩
                  rw [hq] at ht ⊢
                  omega)
              apply hsum_ne
              have hsumEq :
                  ((((m / 2 + 1 + t : ℕ) : ZMod m)) + (((m / 2 + t : ℕ) : ZMod m))) =
                    (((m + (1 + 2 * t) : ℕ) : ZMod m)) := by
                have hnat : m / 2 + 1 + t + (m / 2 + t) = m + (1 + 2 * t) := by
                  rcases hmEven with ⟨q, hq⟩
                  rw [hq]
                  omega
                simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
                  congrArg (fun n : ℕ => ((n : ℕ) : ZMod m)) hnat
              have hmcast : (((m + (1 + 2 * t) : ℕ) : ZMod m)) = (((1 + 2 * t : ℕ) : ZMod m)) := by
                rw [Nat.cast_add, ZMod.natCast_self, zero_add]
              exact (hsumEq.trans hmcast).symm.trans h.1
            have hneg1 :
                ¬ ((((m / 2 + 1 + t : ℕ) : ZMod m)) = (-1 : ZMod m) ∧
                    (((m / 2 + t : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              exact hk_ne_neg_one h.2
            have hneg2 :
                ¬ ((((m / 2 + 1 + t : ℕ) : ZMod m)) = (-2 : ZMod m) ∧
                    (((m / 2 + t : ℕ) : ZMod m)) = 0) := by
              intro h
              exact hk_ne_zero h.2
            have hi0 :
                ¬ ((((m / 2 + 1 + t : ℕ) : ZMod m)) = 0 ∧
                    (((m / 2 + t : ℕ) : ZMod m)) ≠ 0 ∧
                    (((m / 2 + t : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              exact hi_ne_zero h.1
            have h1neg1 :
                ¬ ((((m / 2 + 1 + t : ℕ) : ZMod m)) = (1 : ZMod m) ∧
                    (((m / 2 + t : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              exact hk_ne_neg_one h.2
            have hneg2one :
                ¬ ((((m / 2 + 1 + t : ℕ) : ZMod m)) = (-2 : ZMod m) ∧
                    (((m / 2 + t : ℕ) : ZMod m)) = (1 : ZMod m)) := by
              intro h
              exact hk_ne_one h.2
            simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
              returnMap1CaseI_eq_bulk_of_not_special (m := m)
                (i := (((m / 2 + 1 + t : ℕ) : ZMod m))) (k := (((m / 2 + t : ℕ) : ZMod m)))
                h00 hdiag hneg1 hneg2 hi0 h1neg1 hneg2one
    _ = ((((m / 2 + 1 + (m / 2 - 1) : ℕ) : ZMod m)), (((m / 2 + (m / 2 - 1) : ℕ) : ZMod m))) := by
          rw [iterate_bulkMap1CaseI (m := m) (m / 2 - 1)
            ((((m / 2 + 1 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m)))]
          simp [Nat.cast_add, add_assoc, add_left_comm, add_comm]
    _ = ((0 : ZMod m), (-1 : ZMod m)) := by
          have hm5 : 5 < m := Fact.out
          rcases hmEven with ⟨q, hq⟩
          have hmhalf : m / 2 = q := by
            rw [hq]
            omega
          have hq3 : 3 ≤ q := by
            rw [hq] at hm5
            omega
          have hfirst : m / 2 + 1 + (m / 2 - 1) = m := by
            rw [hmhalf, hq]
            omega
          have hsecond : m / 2 + (m / 2 - 1) = m - 1 := by
            rw [hmhalf, hq]
            omega
          have hm1 : (((m - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) := by
            exact cast_sub_one_eq_neg_one (m := m) (by
              have hm5 : 5 < m := Fact.out
              omega)
          ext
          · simp [hfirst]
          · simp [hsecond, hm1]

theorem iterate_returnMap1CaseI_from_zero_two [Fact (5 < m)] (hmEven : Even m) :
    ((returnMap1CaseI (m := m)^[m]) ((0 : ZMod m), (2 : ZMod m))) = ((1 : ZMod m), (0 : ZMod m)) := by
  let R : P0Coord m → P0Coord m := returnMap1CaseI (m := m)
  have hm5 : 5 < m := Fact.out
  rcases hmEven with ⟨q, hq⟩
  have hmhalf : m / 2 = q := by
    rw [hq]
    omega
  have hq3 : 3 ≤ q := by
    rw [hq] at hm5
    omega
  have hsplit : m = 1 + ((m / 2 - 1) + (1 + ((m / 2 - 2) + 1))) := by
    rw [hq]
    have hqq : (q + q) / 2 = q := by omega
    rw [hqq]
    omega
  have hiter :
      ((R^[m]) ((0 : ZMod m), (2 : ZMod m))) =
        R ((R^[m / 2 - 1]) (R ((R^[m / 2 - 2]) (R ((0 : ZMod m), (2 : ZMod m)))))) := by
    have hiter0 := iterate_add_apply_five
      (f := R) 1 (m / 2 - 1) 1 (m / 2 - 2) 1 ((0 : ZMod m), (2 : ZMod m))
    rw [← hsplit] at hiter0
    exact hiter0
  calc
    ((returnMap1CaseI (m := m)^[m]) ((0 : ZMod m), (2 : ZMod m)))
        = (R^[m]) ((0 : ZMod m), (2 : ZMod m)) := by rfl
    _ = R ((R^[m / 2 - 1]) (R ((R^[m / 2 - 2]) (R ((0 : ZMod m), (2 : ZMod m)))))) := hiter
    _ = R ((R^[m / 2 - 1]) (R ((R^[m / 2 - 2]) ((1 : ZMod m), (2 : ZMod m))))) := by
          simp [R, returnMap1CaseI_zero_two (m := m)]
    _ = R ((R^[m / 2 - 1]) (R ((((m / 2 - 1 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m))))) := by
          rw [iterate_returnMap1CaseI_m_sub_three_middle (m := m) (by exact ⟨q, hq⟩)]
    _ = R ((R^[m / 2 - 1]) ((((m / 2 + 1 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m)))) := by
          simp [R, returnMap1CaseI_m_sub_three_diag (m := m) (by exact ⟨q, hq⟩)]
    _ = R ((0 : ZMod m), (-1 : ZMod m)) := by
          rw [iterate_returnMap1CaseI_m_sub_three_tail (m := m) (by exact ⟨q, hq⟩)]
    _ = ((1 : ZMod m), (0 : ZMod m)) := by
          simpa [R] using returnMap1CaseI_zero_neg_one (m := m)

theorem iterate_returnMap1CaseI_from_one_one [Fact (5 < m)] (hmEven : Even m) :
    ((returnMap1CaseI (m := m)^[m - 2]) ((1 : ZMod m), (1 : ZMod m))) =
      ((-1 : ZMod m), (-1 : ZMod m)) := by
  calc
    ((returnMap1CaseI (m := m)^[m - 2]) ((1 : ZMod m), (1 : ZMod m)))
        = ((bulkMap1CaseI (m := m)^[m - 2]) ((1 : ZMod m), (1 : ZMod m))) := by
            refine iterate_eq_iterate_of_eq_on_prefix
              (F := returnMap1CaseI (m := m)) (G := bulkMap1CaseI (m := m))
              (z := ((1 : ZMod m), (1 : ZMod m))) (m - 2) ?_
            intro t ht
            rw [iterate_bulkMap1CaseI (m := m) t ((1 : ZMod m), (1 : ZMod m))]
            have hi_pos : 0 < 1 + t := by omega
            have hi_lt : 1 + t < m := by omega
            have hi_ne_zero : (((1 + t : ℕ) : ZMod m)) ≠ 0 := by
              exact natCast_ne_zero_of_pos_lt (m := m) (n := 1 + t) hi_pos hi_lt
            have hk_ne_neg_one : (((1 + t : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
              exact natCast_ne_neg_one_of_lt (m := m) (n := 1 + t) (by omega)
            have h00 : ¬ ((((1 + t : ℕ) : ZMod m)) = 0 ∧ (((1 + t : ℕ) : ZMod m)) = 0) := by
              intro h
              exact hi_ne_zero h.1
            have hdiag :
                ¬ ((((1 + t : ℕ) : ZMod m)) + (((1 + t : ℕ) : ZMod m)) = (-1 : ZMod m) ∧
                    (((1 + t : ℕ) : ZMod m)) ≠ 0 ∧
                    (((1 + t : ℕ) : ZMod m)) ≠ (-2 : ZMod m) ∧
                    (((1 + t : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              have hsumEven : Even (2 + 2 * t) := by
                refine ⟨1 + t, by ring⟩
              have hsum_ne : (((2 + 2 * t : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
                exact natCast_ne_neg_one_of_even (m := m) hmEven hsumEven
              apply hsum_ne
              have hsumEq :
                  ((((1 + t : ℕ) : ZMod m)) + (((1 + t : ℕ) : ZMod m))) =
                    (((2 + 2 * t : ℕ) : ZMod m)) := by
                have hsumEq' :
                    (((2 + 2 * t : ℕ) : ZMod m)) =
                      ((((1 + t : ℕ) : ZMod m)) + (((1 + t : ℕ) : ZMod m))) := by
                  calc
                    (((2 + 2 * t : ℕ) : ZMod m)) = (2 : ZMod m) + ((2 : ZMod m) * t) := by
                      rw [Nat.cast_add, Nat.cast_mul]
                      norm_num
                    _ = (1 : ZMod m) + t + ((1 : ZMod m) + t) := by
                      ring
                    _ = ((((1 + t : ℕ) : ZMod m)) + (((1 + t : ℕ) : ZMod m))) := by
                      simp [Nat.cast_add, add_assoc, add_left_comm, add_comm]
                exact hsumEq'.symm
              exact hsumEq.symm.trans h.1
            have hneg1 :
                ¬ ((((1 + t : ℕ) : ZMod m)) = (-1 : ZMod m) ∧ (((1 + t : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              exact hk_ne_neg_one h.2
            have hneg2 :
                ¬ ((((1 + t : ℕ) : ZMod m)) = (-2 : ZMod m) ∧ (((1 + t : ℕ) : ZMod m)) = 0) := by
              intro h
              exact hi_ne_zero h.2
            have hi0 :
                ¬ ((((1 + t : ℕ) : ZMod m)) = 0 ∧
                    (((1 + t : ℕ) : ZMod m)) ≠ 0 ∧
                    (((1 + t : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              exact hi_ne_zero h.1
            have h1neg1 :
                ¬ ((((1 + t : ℕ) : ZMod m)) = (1 : ZMod m) ∧ (((1 + t : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              exact hk_ne_neg_one h.2
            have hneg2one :
                ¬ ((((1 + t : ℕ) : ZMod m)) = (-2 : ZMod m) ∧ (((1 + t : ℕ) : ZMod m)) = (1 : ZMod m)) := by
              intro h
              have ht0 : t = 0 := by
                have hmod := (ZMod.natCast_eq_natCast_iff' (1 + t) 1 m).1 (by simpa using h.2)
                rw [Nat.mod_eq_of_lt hi_lt, Nat.mod_eq_of_lt (by
                  have hm5 : 5 < m := Fact.out
                  omega)] at hmod
                omega
              subst ht0
              exact natCast_ne_neg_two_of_lt (m := m) (n := 1) (by
                have hm5 : 5 < m := Fact.out
                omega) h.1
            simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
              returnMap1CaseI_eq_bulk_of_not_special (m := m)
                (i := (((1 + t : ℕ) : ZMod m))) (k := (((1 + t : ℕ) : ZMod m)))
                h00 hdiag hneg1 hneg2 hi0 h1neg1 hneg2one
    _ = ((((1 + (m - 2) : ℕ) : ZMod m)), (((1 + (m - 2) : ℕ) : ZMod m))) := by
          rw [iterate_bulkMap1CaseI (m := m) (m - 2) ((1 : ZMod m), (1 : ZMod m))]
          simp [Nat.cast_add, add_assoc, add_left_comm, add_comm]
    _ = ((-1 : ZMod m), (-1 : ZMod m)) := by
          have hm5 : 5 < m := Fact.out
          have hm1 : (((m - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) := by
            exact cast_sub_one_eq_neg_one (m := m) (by
              omega)
          have hsum : 1 + (m - 2) = m - 1 := by omega
          simp [hsum, hm1]

theorem iterate_returnMap1CaseI_from_zero_one [Fact (5 < m)] (hmEven : Even m) :
    ((returnMap1CaseI (m := m)^[m + 2]) ((0 : ZMod m), (1 : ZMod m))) = ((3 : ZMod m), (0 : ZMod m)) := by
  let R : P0Coord m → P0Coord m := returnMap1CaseI (m := m)
  have hm5 : 5 < m := Fact.out
  have hsplit : m + 2 = 1 + (1 + (1 + ((m - 2) + 1))) := by omega
  have hiter :
      ((R^[m + 2]) ((0 : ZMod m), (1 : ZMod m))) =
        R (R (R ((R^[m - 2]) (R ((0 : ZMod m), (1 : ZMod m)))))) := by
    have hiter0 := iterate_add_apply_five
      (f := R) 1 1 1 (m - 2) 1 ((0 : ZMod m), (1 : ZMod m))
    rw [← hsplit] at hiter0
    exact hiter0
  calc
    ((returnMap1CaseI (m := m)^[m + 2]) ((0 : ZMod m), (1 : ZMod m)))
        = (R^[m + 2]) ((0 : ZMod m), (1 : ZMod m)) := by rfl
    _ = R (R (R ((R^[m - 2]) (R ((0 : ZMod m), (1 : ZMod m)))))) := hiter
    _ = R (R (R ((R^[m - 2]) ((1 : ZMod m), (1 : ZMod m))))) := by
          simp [R, returnMap1CaseI_zero_one (m := m)]
    _ = R (R (R ((-1 : ZMod m), (-1 : ZMod m)))) := by
          rw [iterate_returnMap1CaseI_from_one_one (m := m) hmEven]
    _ = R (R ((1 : ZMod m), (-1 : ZMod m))) := by
          simp [R, returnMap1CaseI_neg_one_neg_one (m := m)]
    _ = R ((2 : ZMod m), (-1 : ZMod m)) := by
          simp [R, returnMap1CaseI_one_neg_one (m := m)]
    _ = ((3 : ZMod m), (0 : ZMod m)) := by
          simpa [R] using returnMap1CaseI_two_neg_one (m := m)

theorem iterate_KMap1 (n : ℕ) (u : P0Coord m) (s : ZMod m) :
    ((KMap (m := m) 1)^[n]) (u, s) = (u, s + n) := by
  induction n generalizing u s with
  | zero =>
      simp [KMap]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      ext <;> simp [KMap, Nat.cast_add]
      ring

theorem fullMap1CaseI_of_s_ne_zero_one {u : P0Coord m} {s : ZMod m}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    fullMap1CaseI (m := m) (u, s) = KMap (m := m) 1 (u, s) := by
  simp [fullMap1CaseI, dir1CaseI, hs0, hs1]

theorem iterate_fullMap1CaseI_from_two [Fact (5 < m)] :
    ∀ n u, n ≤ m - 2 →
      ((fullMap1CaseI (m := m)^[n]) (u, (2 : ZMod m))) =
        ((KMap (m := m) 1)^[n]) (u, (2 : ZMod m))
  | 0, u, _ => by simp
  | n + 1, u, hn => by
      have hm5 : 5 < m := Fact.out
      letI : Fact (0 < m) := inferInstance
      letI : Fact (1 < m) := inferInstance
      have hn' : n ≤ m - 2 := Nat.le_of_succ_le hn
      have hcur_lt : n + 2 < m := by omega
      have hs0 : (2 : ZMod m) + n ≠ 0 := by
        simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
          natCast_ne_zero_of_pos_lt (m := m) (n := n + 2) (by omega) hcur_lt
      have hs1 : (2 : ZMod m) + n ≠ 1 := by
        simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
          natCast_ne_one_of_two_le_lt (m := m) (n := n + 2) (by omega) hcur_lt
      calc
        ((fullMap1CaseI (m := m)^[n + 1]) (u, (2 : ZMod m)))
            = fullMap1CaseI (m := m) (((fullMap1CaseI (m := m)^[n]) (u, (2 : ZMod m)))) := by
                rw [Function.iterate_succ_apply']
        _ = fullMap1CaseI (m := m) (((KMap (m := m) 1)^[n]) (u, (2 : ZMod m))) := by
              rw [iterate_fullMap1CaseI_from_two (m := m) n u hn']
        _ = fullMap1CaseI (m := m) (u, (2 : ZMod m) + n) := by rw [iterate_KMap1]
        _ = KMap (m := m) 1 (u, (2 : ZMod m) + n) := by
              simpa using fullMap1CaseI_of_s_ne_zero_one (m := m) (u := u) hs0 hs1
        _ = ((KMap (m := m) 1)^[n + 1]) (u, (2 : ZMod m)) := by
              symm
              rw [Function.iterate_succ_apply', iterate_KMap1]

theorem iterate_m_sub_two_fullMap1CaseI [Fact (5 < m)] (u : P0Coord m) :
    ((fullMap1CaseI (m := m)^[m - 2]) (u, (2 : ZMod m))) = slicePoint (0 : ZMod m) u := by
  have hm2 : 2 ≤ m := by
    have hm5 : 5 < m := Fact.out
    omega
  calc
    ((fullMap1CaseI (m := m)^[m - 2]) (u, (2 : ZMod m)))
        = ((KMap (m := m) 1)^[m - 2]) (u, (2 : ZMod m)) := by
            simpa using iterate_fullMap1CaseI_from_two (m := m) (m - 2) u le_rfl
    _ = (u, (2 : ZMod m) + (((m - 2 : ℕ) : ZMod m))) := by rw [iterate_KMap1]
    _ = slicePoint (0 : ZMod m) u := by
          ext <;> simp [slicePoint, Nat.cast_sub hm2]
          all_goals ring

theorem fullMap1CaseI_step_zero_of_dir0 {u : P0Coord m}
    (hdir : dir1CaseILayerZero (m := m) u = 0) :
    fullMap1CaseI (m := m) (slicePoint (0 : ZMod m) u) = ((u.1 + 1, u.2), (1 : ZMod m)) := by
  simp [fullMap1CaseI, dir1CaseI, hdir, KMap, slicePoint]

theorem fullMap1CaseI_step_zero_of_dir1 {u : P0Coord m}
    (hdir : dir1CaseILayerZero (m := m) u = 1) :
    fullMap1CaseI (m := m) (slicePoint (0 : ZMod m) u) = (u, (1 : ZMod m)) := by
  simp [fullMap1CaseI, dir1CaseI, hdir, KMap, slicePoint]

theorem fullMap1CaseI_step_zero_of_dir2 {u : P0Coord m}
    (hdir : dir1CaseILayerZero (m := m) u = 2) :
    fullMap1CaseI (m := m) (slicePoint (0 : ZMod m) u) = ((u.1, u.2 + 1), (1 : ZMod m)) := by
  simp [fullMap1CaseI, dir1CaseI, hdir, KMap, slicePoint]

theorem fullMap1CaseI_step_one (u : P0Coord m) [Fact (5 < m)] :
    fullMap1CaseI (m := m) (u, (1 : ZMod m)) = ((u.1 + 1, u.2), (2 : ZMod m)) := by
  letI : Fact (1 < m) := inferInstance
  ext <;> simp [fullMap1CaseI, dir1CaseI, KMap, one_ne_zero (m := m)]
  ring

theorem iterate_two_fullMap1CaseI_of_dir0 [Fact (5 < m)] {u : P0Coord m}
    (hdir : dir1CaseILayerZero (m := m) u = 0) :
    ((fullMap1CaseI (m := m)^[2]) (slicePoint (0 : ZMod m) u)) =
      ((u.1 + 2, u.2), (2 : ZMod m)) := by
  calc
    ((fullMap1CaseI (m := m)^[2]) (slicePoint (0 : ZMod m) u))
        = fullMap1CaseI (m := m) (fullMap1CaseI (m := m) (slicePoint (0 : ZMod m) u)) := by
            simp [Function.iterate_succ_apply']
    _ = fullMap1CaseI (m := m) (((u.1 + 1, u.2), (1 : ZMod m))) := by
          rw [fullMap1CaseI_step_zero_of_dir0 (m := m) hdir]
    _ = ((u.1 + 2, u.2), (2 : ZMod m)) := by
          rw [fullMap1CaseI_step_one (m := m) (u := (u.1 + 1, u.2))]
          ring

theorem iterate_two_fullMap1CaseI_of_dir1 [Fact (5 < m)] {u : P0Coord m}
    (hdir : dir1CaseILayerZero (m := m) u = 1) :
    ((fullMap1CaseI (m := m)^[2]) (slicePoint (0 : ZMod m) u)) =
      ((u.1 + 1, u.2), (2 : ZMod m)) := by
  calc
    ((fullMap1CaseI (m := m)^[2]) (slicePoint (0 : ZMod m) u))
        = fullMap1CaseI (m := m) (fullMap1CaseI (m := m) (slicePoint (0 : ZMod m) u)) := by
            simp [Function.iterate_succ_apply']
    _ = fullMap1CaseI (m := m) ((u, (1 : ZMod m))) := by
          rw [fullMap1CaseI_step_zero_of_dir1 (m := m) hdir]
    _ = ((u.1 + 1, u.2), (2 : ZMod m)) := by
          simpa using fullMap1CaseI_step_one (m := m) (u := u)

theorem iterate_two_fullMap1CaseI_of_dir2 [Fact (5 < m)] {u : P0Coord m}
    (hdir : dir1CaseILayerZero (m := m) u = 2) :
    ((fullMap1CaseI (m := m)^[2]) (slicePoint (0 : ZMod m) u)) =
      ((u.1 + 1, u.2 + 1), (2 : ZMod m)) := by
  calc
    ((fullMap1CaseI (m := m)^[2]) (slicePoint (0 : ZMod m) u))
        = fullMap1CaseI (m := m) (fullMap1CaseI (m := m) (slicePoint (0 : ZMod m) u)) := by
            simp [Function.iterate_succ_apply']
    _ = fullMap1CaseI (m := m) (((u.1, u.2 + 1), (1 : ZMod m))) := by
          rw [fullMap1CaseI_step_zero_of_dir2 (m := m) hdir]
    _ = ((u.1 + 1, u.2 + 1), (2 : ZMod m)) := by
          simpa using fullMap1CaseI_step_one (m := m) (u := (u.1, u.2 + 1))

theorem iterate_m_fullMap1CaseI_of_dir0 [Fact (5 < m)] {u : P0Coord m}
    (hdir : dir1CaseILayerZero (m := m) u = 0) :
    ((fullMap1CaseI (m := m)^[m]) (slicePoint (0 : ZMod m) u)) =
      slicePoint (0 : ZMod m) (u.1 + 2, u.2) := by
  have hm2 : 2 ≤ m := by
    have hm5 : 5 < m := Fact.out
    omega
  calc
    ((fullMap1CaseI (m := m)^[m]) (slicePoint (0 : ZMod m) u))
        = ((fullMap1CaseI (m := m)^[m - 2]) (((fullMap1CaseI (m := m)^[2]) (slicePoint (0 : ZMod m) u)))) := by
            simpa [Nat.sub_add_cancel hm2] using
              (Function.iterate_add_apply (f := fullMap1CaseI (m := m)) (m := m - 2) (n := 2)
                (slicePoint (0 : ZMod m) u))
    _ = ((fullMap1CaseI (m := m)^[m - 2]) (((u.1 + 2, u.2), (2 : ZMod m)))) := by
          rw [iterate_two_fullMap1CaseI_of_dir0 (m := m) hdir]
    _ = slicePoint (0 : ZMod m) (u.1 + 2, u.2) := iterate_m_sub_two_fullMap1CaseI (m := m) _

theorem iterate_m_fullMap1CaseI_of_dir1 [Fact (5 < m)] {u : P0Coord m}
    (hdir : dir1CaseILayerZero (m := m) u = 1) :
    ((fullMap1CaseI (m := m)^[m]) (slicePoint (0 : ZMod m) u)) =
      slicePoint (0 : ZMod m) (u.1 + 1, u.2) := by
  have hm2 : 2 ≤ m := by
    have hm5 : 5 < m := Fact.out
    omega
  calc
    ((fullMap1CaseI (m := m)^[m]) (slicePoint (0 : ZMod m) u))
        = ((fullMap1CaseI (m := m)^[m - 2]) (((fullMap1CaseI (m := m)^[2]) (slicePoint (0 : ZMod m) u)))) := by
            simpa [Nat.sub_add_cancel hm2] using
              (Function.iterate_add_apply (f := fullMap1CaseI (m := m)) (m := m - 2) (n := 2)
                (slicePoint (0 : ZMod m) u))
    _ = ((fullMap1CaseI (m := m)^[m - 2]) (((u.1 + 1, u.2), (2 : ZMod m)))) := by
          rw [iterate_two_fullMap1CaseI_of_dir1 (m := m) hdir]
    _ = slicePoint (0 : ZMod m) (u.1 + 1, u.2) := iterate_m_sub_two_fullMap1CaseI (m := m) _

theorem iterate_m_fullMap1CaseI_of_dir2 [Fact (5 < m)] {u : P0Coord m}
    (hdir : dir1CaseILayerZero (m := m) u = 2) :
    ((fullMap1CaseI (m := m)^[m]) (slicePoint (0 : ZMod m) u)) =
      slicePoint (0 : ZMod m) (u.1 + 1, u.2 + 1) := by
  have hm2 : 2 ≤ m := by
    have hm5 : 5 < m := Fact.out
    omega
  calc
    ((fullMap1CaseI (m := m)^[m]) (slicePoint (0 : ZMod m) u))
        = ((fullMap1CaseI (m := m)^[m - 2]) (((fullMap1CaseI (m := m)^[2]) (slicePoint (0 : ZMod m) u)))) := by
            simpa [Nat.sub_add_cancel hm2] using
              (Function.iterate_add_apply (f := fullMap1CaseI (m := m)) (m := m - 2) (n := 2)
                (slicePoint (0 : ZMod m) u))
    _ = ((fullMap1CaseI (m := m)^[m - 2]) (((u.1 + 1, u.2 + 1), (2 : ZMod m)))) := by
          rw [iterate_two_fullMap1CaseI_of_dir2 (m := m) hdir]
    _ = slicePoint (0 : ZMod m) (u.1 + 1, u.2 + 1) := iterate_m_sub_two_fullMap1CaseI (m := m) _

theorem iterate_m_fullMap1CaseI_slicePoint_zero [Fact (5 < m)] (u : P0Coord m) :
    ((fullMap1CaseI (m := m)^[m]) (slicePoint (0 : ZMod m) u)) =
      slicePoint (0 : ZMod m) (returnMap1CaseI (m := m) u) := by
  by_cases hdir0 : dir1CaseILayerZero (m := m) u = 0
  · simpa [returnMap1CaseI, hdir0] using
      iterate_m_fullMap1CaseI_of_dir0 (m := m) (u := u) hdir0
  by_cases hdir1 : dir1CaseILayerZero (m := m) u = 1
  · simpa [returnMap1CaseI, hdir0, hdir1] using
      iterate_m_fullMap1CaseI_of_dir1 (m := m) (u := u) hdir1
  have hdir2 : dir1CaseILayerZero (m := m) u = 2 := by
    apply Fin.ext
    have hlt : (dir1CaseILayerZero (m := m) u).1 < 3 := (dir1CaseILayerZero (m := m) u).2
    interval_cases hval : (dir1CaseILayerZero (m := m) u).1
    · exact False.elim (hdir0 (Fin.ext hval))
    · exact False.elim (hdir1 (Fin.ext hval))
    · rfl
  simpa [returnMap1CaseI, hdir0, hdir1, hdir2] using
    iterate_m_fullMap1CaseI_of_dir2 (m := m) (u := u) hdir2

theorem returnMap1CaseI_line_zero [Fact (5 < m)] :
    returnMap1CaseI (m := m) (linePoint1 (m := m) 0) =
      linePoint1 (m := m) (TorusD3Even.T1CaseI (m := m) 0) := by
  ext <;> simp [linePoint1, returnMap1CaseI_origin, TorusD3Even.T1CaseI]

theorem firstReturn_line_zero [Fact (5 < m)] :
    ((returnMap1CaseI (m := m)^[TorusD3Even.rho1CaseI (m := m) 0])
        (linePoint1 (m := m) 0)) =
      linePoint1 (m := m) (TorusD3Even.T1CaseI (m := m) 0) := by
  simpa [TorusD3Even.rho1CaseI] using returnMap1CaseI_line_zero (m := m)

theorem returnMap1CaseI_line_m_sub_two [Fact (5 < m)] :
    let x : Fin m := ⟨m - 2, by
      have hm5 : 5 < m := Fact.out
      omega⟩
    returnMap1CaseI (m := m) (linePoint1 (m := m) x) =
      linePoint1 (m := m) (TorusD3Even.T1CaseI (m := m) x) := by
  let x : Fin m := ⟨m - 2, by
    have hm5 : 5 < m := Fact.out
    omega⟩
  have hxm2 : (((x : Fin m) : ZMod m)) = (-2 : ZMod m) := by
    change (((m - 2 : ℕ) : ZMod m)) = (-2 : ZMod m)
    have hm2 : 2 ≤ m := by
      have hm5 : 5 < m := Fact.out
      omega
    rw [Nat.cast_sub hm2]
    simp
  have htx : (TorusD3Even.T1CaseI (m := m) x).1 = 0 := by
    apply TorusD3Even.T1CaseI_eq_zero_of_val_eq_m_sub_two (m := m)
    simp [x]
  have hret : returnMap1CaseI (m := m) (linePoint1 (m := m) x) = ((0 : ZMod m), (0 : ZMod m)) := by
    simpa [linePoint1, hxm2] using returnMap1CaseI_neg_two_zero (m := m)
  calc
    returnMap1CaseI (m := m) (linePoint1 (m := m) x) = ((0 : ZMod m), (0 : ZMod m)) := hret
    _ = linePoint1 (m := m) (TorusD3Even.T1CaseI (m := m) x) := by
          ext <;> simp [linePoint1, htx]

theorem firstReturn_line_m_sub_two [Fact (5 < m)] :
    let x : Fin m := ⟨m - 2, by
      have hm5 : 5 < m := Fact.out
      omega⟩
    ((returnMap1CaseI (m := m)^[TorusD3Even.rho1CaseI (m := m) x]) (linePoint1 (m := m) x)) =
      linePoint1 (m := m) (TorusD3Even.T1CaseI (m := m) x) := by
  let x : Fin m := ⟨m - 2, by
    have hm5 : 5 < m := Fact.out
    omega⟩
  simpa [x, TorusD3Even.rho1CaseI] using returnMap1CaseI_line_m_sub_two (m := m)

theorem iterate_three_returnMap1CaseI_line_m_sub_three [Fact (5 < m)] {x : Fin m}
    (hx : x.1 = m - 3) :
    ((returnMap1CaseI (m := m)^[3]) (linePoint1 (m := m) x)) =
      ((0 : ZMod m), (2 : ZMod m)) := by
  let x0 : Fin m := ⟨m - 3, by
    have hm5 : 5 < m := Fact.out
    omega⟩
  have hx' : x = x0 := Fin.ext hx
  calc
    ((returnMap1CaseI (m := m)^[3]) (linePoint1 (m := m) x))
        = ((returnMap1CaseI (m := m)^[3]) (linePoint1 (m := m) x0)) := by
            simpa [hx']
    _ = ((0 : ZMod m), (2 : ZMod m)) := by
          calc
            ((returnMap1CaseI (m := m)^[3]) (linePoint1 (m := m) x0))
                = returnMap1CaseI (m := m)
                    (returnMap1CaseI (m := m)
                      (returnMap1CaseI (m := m) (linePoint1 (m := m) x0))) := by
                        simp [Function.iterate_succ_apply']
            _ = returnMap1CaseI (m := m)
                  (returnMap1CaseI (m := m) ((((m - 2 : ℕ) : ZMod m)), (1 : ZMod m))) := by
                    rw [show returnMap1CaseI (m := m) (linePoint1 (m := m) x0) =
                        ((((m - 2 : ℕ) : ZMod m)), (1 : ZMod m)) by
                        simpa [x0] using returnMap1CaseI_line_m_sub_three_start (m := m)]
            _ = returnMap1CaseI (m := m) ((-1 : ZMod m), (1 : ZMod m)) := by
                  rw [show returnMap1CaseI (m := m) ((((m - 2 : ℕ) : ZMod m)), (1 : ZMod m)) =
                      ((-1 : ZMod m), (1 : ZMod m)) by
                        have hm2 : 2 ≤ m := by
                          have hm5 : 5 < m := Fact.out
                          omega
                        simpa [cast_sub_two_eq_neg_two (m := m) hm2] using
                          returnMap1CaseI_neg_two_one (m := m)]
            _ = ((0 : ZMod m), (2 : ZMod m)) := by
                  rw [returnMap1CaseI_neg_one_one (m := m)]

theorem firstReturn_line_m_sub_three [Fact (5 < m)] (hmEven : Even m) {x : Fin m}
    (hx : x.1 = m - 3) :
    ((returnMap1CaseI (m := m)^[TorusD3Even.rho1CaseI (m := m) x]) (linePoint1 (m := m) x)) =
      linePoint1 (m := m) (TorusD3Even.T1CaseI (m := m) x) := by
  have hm5 : 5 < m := Fact.out
  have hm3ne0 : m - 3 ≠ 0 := by omega
  have hm3nem2 : m - 3 ≠ m - 2 := by omega
  have hrho : TorusD3Even.rho1CaseI (m := m) x = m + 3 := by
    simp [TorusD3Even.rho1CaseI, hx, hm3ne0, hm3nem2]
  have hT : (TorusD3Even.T1CaseI (m := m) x).1 = 1 := by
    simpa using TorusD3Even.T1CaseI_eq_one_of_val_eq_m_sub_three (m := m) hx
  calc
    ((returnMap1CaseI (m := m)^[TorusD3Even.rho1CaseI (m := m) x]) (linePoint1 (m := m) x))
        = ((returnMap1CaseI (m := m)^[m + 3]) (linePoint1 (m := m) x)) := by
            rw [hrho]
    _ = ((returnMap1CaseI (m := m)^[m]) (((returnMap1CaseI (m := m)^[3]) (linePoint1 (m := m) x)))) := by
          simpa using
            (Function.iterate_add_apply (f := returnMap1CaseI (m := m)) (m := m) (n := 3)
              (linePoint1 (m := m) x))
    _ = ((returnMap1CaseI (m := m)^[m]) ((0 : ZMod m), (2 : ZMod m))) := by
          rw [iterate_three_returnMap1CaseI_line_m_sub_three (m := m) hx]
    _ = ((1 : ZMod m), (0 : ZMod m)) := by
          exact iterate_returnMap1CaseI_from_zero_two (m := m) hmEven
    _ = linePoint1 (m := m) (TorusD3Even.T1CaseI (m := m) x) := by
          ext <;> simp [linePoint1, hT]

theorem firstReturn_line_m_sub_one [Fact (5 < m)] (hmEven : Even m) {x : Fin m}
    (hx : x.1 = m - 1) :
    ((returnMap1CaseI (m := m)^[TorusD3Even.rho1CaseI (m := m) x]) (linePoint1 (m := m) x)) =
      linePoint1 (m := m) (TorusD3Even.T1CaseI (m := m) x) := by
  have hm5 : 5 < m := Fact.out
  have hm1ne0 : m - 1 ≠ 0 := by omega
  have hm1nem2 : m - 1 ≠ m - 2 := by omega
  have hrho : TorusD3Even.rho1CaseI (m := m) x = m + 3 := by
    simp [TorusD3Even.rho1CaseI, hx, hm1ne0, hm1nem2]
  have hT : (TorusD3Even.T1CaseI (m := m) x).1 = 3 := by
    simpa using TorusD3Even.T1CaseI_eq_three_of_val_eq_m_sub_one (m := m) hx
  calc
    ((returnMap1CaseI (m := m)^[TorusD3Even.rho1CaseI (m := m) x]) (linePoint1 (m := m) x))
        = ((returnMap1CaseI (m := m)^[m + 3]) (linePoint1 (m := m) x)) := by
            rw [hrho]
    _ = ((returnMap1CaseI (m := m)^[m + 2]) (returnMap1CaseI (m := m) (linePoint1 (m := m) x))) := by
          simpa using
            (Function.iterate_add_apply (f := returnMap1CaseI (m := m)) (m := m + 2) (n := 1)
              (linePoint1 (m := m) x))
    _ = ((returnMap1CaseI (m := m)^[m + 2]) ((0 : ZMod m), (1 : ZMod m))) := by
          rw [show returnMap1CaseI (m := m) (linePoint1 (m := m) x) = ((0 : ZMod m), (1 : ZMod m)) by
            let x0 : Fin m := ⟨m - 1, by omega⟩
            have hx' : x = x0 := Fin.ext hx
            calc
              returnMap1CaseI (m := m) (linePoint1 (m := m) x)
                  = returnMap1CaseI (m := m) (linePoint1 (m := m) x0) := by
                      simpa [hx']
              _ = ((0 : ZMod m), (1 : ZMod m)) := by
                    simpa [x0] using returnMap1CaseI_line_m_sub_one_start (m := m)]
    _ = ((3 : ZMod m), (0 : ZMod m)) := by
          exact iterate_returnMap1CaseI_from_zero_one (m := m) hmEven
    _ = linePoint1 (m := m) (TorusD3Even.T1CaseI (m := m) x) := by
          ext <;> simp [linePoint1, hT]

theorem firstReturn_line_caseI [Fact (5 < m)] (hmEven : Even m) (x : Fin m) :
    ((returnMap1CaseI (m := m)^[TorusD3Even.rho1CaseI (m := m) x]) (linePoint1 (m := m) x)) =
      linePoint1 (m := m) (TorusD3Even.T1CaseI (m := m) x) := by
  by_cases hx0 : x.1 = 0
  · have hx' : x = 0 := Fin.ext hx0
    simpa [hx'] using firstReturn_line_zero (m := m)
  by_cases hxm2 : x.1 = m - 2
  · have hm5 : 5 < m := Fact.out
    have hx' : x = ⟨m - 2, by omega⟩ := Fin.ext hxm2
    simpa [hx'] using firstReturn_line_m_sub_two (m := m)
  by_cases hxm3 : x.1 = m - 3
  · exact firstReturn_line_m_sub_three (m := m) hmEven hxm3
  by_cases hxm1 : x.1 = m - 1
  · exact firstReturn_line_m_sub_one (m := m) hmEven hxm1
  have hx1 : 1 ≤ x.1 := by
    exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hx0)
  rcases Nat.even_or_odd x.1 with hxeven | hxodd
  · have hx2 : 2 ≤ x.1 := by
      rcases hxeven with ⟨k, hk⟩
      have hkpos : 0 < k := by
        by_contra hk0
        have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk0
        exact hx0 (by rw [hk, hkzero])
      omega
    have hxle : x.1 ≤ m - 4 := by
      omega
    simpa using firstReturn_line_even_generic (m := m) hmEven (x := x.1) hx2 hxle hxeven
  · have hx1 : 1 ≤ x.1 := by
      exact hx1
    have hxle : x.1 ≤ m - 4 := by
      omega
    simpa using firstReturn_line_odd_generic (m := m) hmEven (x := x.1) hx1 hxle hxodd

theorem cycleOn_T1CaseI_caseI [Fact (5 < m)] (hmEven : Even m) (hcase : m % 6 ≠ 4) :
    TorusD4.CycleOn m (TorusD3Even.T1CaseI (m := m)) ⟨0, by
      have hm5 : 5 < m := Fact.out
      omega⟩ := by
  have hm5 : 5 < m := Fact.out
  rcases mod_six_eq_zero_or_two_or_four_of_even (m := m) hmEven with hm0 | hm2 | hm4
  · simpa [laneMap1CaseI] using cycleOn_laneMap1_caseI_mod_zero (m := m) hm0
  · have hm7 : 7 < m := by
      rcases TorusD3Even.eq_six_mul_add_two_of_mod_six_eq_two (m := m) hm2 with ⟨q, hq⟩
      have hq1 : 1 ≤ q := by
        rw [hq] at hm5
        omega
      rw [hq]
      omega
    letI : Fact (7 < m) := ⟨hm7⟩
    simpa [laneMap1CaseI] using cycleOn_laneMap1_caseI_mod_two (m := m) hm2
  · exact False.elim (hcase hm4)

theorem hreturn_line_caseI [Fact (5 < m)] (hmEven : Even m) (x : Fin m) :
    ((returnMap1CaseI (m := m)^[TorusD3Even.rho1CaseI (m := m) x]) (linePoint1 (m := m) x)) =
      linePoint1 (m := m) (TorusD3Even.T1CaseI (m := m) x) := by
  exact firstReturn_line_caseI (m := m) hmEven x

theorem blockTime_eq_sum_range {α : Type*} (T : α → α) (rho : α → ℕ) (x0 : α) :
    ∀ k,
      TorusD3Even.blockTime T rho x0 k =
        Finset.sum (Finset.range k) (fun i => rho ((T^[i]) x0)) := by
  intro k
  induction k with
  | zero =>
      simp [TorusD3Even.blockTime]
  | succ k ih =>
      rw [TorusD3Even.blockTime_succ, ih, Finset.sum_range_succ]

theorem rho1CaseI_zero [Fact (5 < m)] :
    TorusD3Even.rho1CaseI (m := m) (0 : Fin m) = 1 := by
  simp [TorusD3Even.rho1CaseI]

theorem rho1CaseI_of_one_le_lt_m_sub_three [Fact (5 < m)] {x : ℕ}
    (hx1 : 1 ≤ x) (hxlt : x < m - 3) :
    TorusD3Even.rho1CaseI (m := m) (⟨x, by omega⟩ : Fin m) = m + 2 := by
  have hx0 : x ≠ 0 := by
    omega
  have hxm2 : x ≠ m - 2 := by
    omega
  have hxm3 : x ≠ m - 3 := by
    omega
  have hxm1 : x ≠ m - 1 := by
    omega
  simp [TorusD3Even.rho1CaseI, hx0, hxm2, hxm3, hxm1]

theorem rho1CaseI_m_sub_three [Fact (5 < m)] :
    TorusD3Even.rho1CaseI (m := m)
      (⟨m - 3, by
        have hm5 : 5 < m := Fact.out
        omega⟩ : Fin m) = m + 3 := by
  have hm5 : 5 < m := Fact.out
  have hm3ne0 : m - 3 ≠ 0 := by
    omega
  have hm3nem2 : m - 3 ≠ m - 2 := by
    omega
  simp [TorusD3Even.rho1CaseI, hm3ne0, hm3nem2]

theorem rho1CaseI_m_sub_two [Fact (5 < m)] :
    TorusD3Even.rho1CaseI (m := m)
      (⟨m - 2, by
        have hm5 : 5 < m := Fact.out
        omega⟩ : Fin m) = 1 := by
  have hm5 : 5 < m := Fact.out
  have hm2ne0 : m - 2 ≠ 0 := by
    omega
  simp [TorusD3Even.rho1CaseI, hm2ne0]

theorem rho1CaseI_m_sub_one [Fact (5 < m)] :
    TorusD3Even.rho1CaseI (m := m)
      (⟨m - 1, by
        have hm5 : 5 < m := Fact.out
        omega⟩ : Fin m) = m + 3 := by
  have hm5 : 5 < m := Fact.out
  have hm1ne0 : m - 1 ≠ 0 := by
    omega
  have hm1nem2 : m - 1 ≠ m - 2 := by
    omega
  have hm1nem3 : m - 1 ≠ m - 3 := by
    omega
  simp [TorusD3Even.rho1CaseI, hm1ne0, hm1nem2, hm1nem3]

theorem sum_rho1CaseI [Fact (5 < m)] :
    (∑ x : Fin m, TorusD3Even.rho1CaseI (m := m) x) = m ^ 2 := by
  have hm0 : 0 < m := by
    have hm5 : 5 < m := Fact.out
    omega
  have hm1 : 1 ≤ m - 3 := by
    have hm5 : 5 < m := Fact.out
    omega
  let g : ℕ → ℕ := fun k =>
    if hk : k < m then TorusD3Even.rho1CaseI (m := m) (⟨k, hk⟩ : Fin m) else 0
  have hsumRange :
      (∑ x : Fin m, TorusD3Even.rho1CaseI (m := m) x) = Finset.sum (Finset.range m) g := by
    simpa [g] using (Fin.sum_univ_eq_sum_range g m)
  have hhead : Finset.sum (Finset.range 1) g = 1 := by
    have hg0 : g 0 = 1 := by
      simpa [g, hm0] using rho1CaseI_zero (m := m)
    simpa [hg0]
  have hmid :
      Finset.sum (Finset.Ico 1 (m - 3)) g = (m - 4) * (m + 2) := by
    calc
      Finset.sum (Finset.Ico 1 (m - 3)) g
          = Finset.sum (Finset.Ico 1 (m - 3)) (fun _ => m + 2) := by
              apply Finset.sum_congr rfl
              intro k hk
              have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
              have hklt : k < m - 3 := (Finset.mem_Ico.mp hk).2
              have hkm : k < m := by
                omega
              have hkval :
                  TorusD3Even.rho1CaseI (m := m) (⟨k, hkm⟩ : Fin m) = m + 2 :=
                rho1CaseI_of_one_le_lt_m_sub_three (m := m) hk1 hklt
              simpa [g, hkm] using hkval
      _ = (Finset.Ico 1 (m - 3)).card * (m + 2) := by
            simp
      _ = (m - 4) * (m + 2) := by
            simp [Nat.card_Ico]
            omega
  have hsuffix :
      Finset.sum (Finset.Ico (m - 3) m) g = 2 * m + 7 := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hlen : m - (m - 3) = 3 := by
      omega
    rw [hlen, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    rw [Finset.sum_range_zero]
    have hm3lt : m - 3 < m := by
      omega
    have hm2lt : m - 2 < m := by
      omega
    have hm1lt : m - 1 < m := by
      omega
    rw [show m - 3 + 0 = m - 3 by omega,
      show m - 3 + 1 = m - 2 by omega,
      show m - 3 + 2 = m - 1 by omega]
    simp [g, hm3lt, hm2lt, hm1lt, rho1CaseI_m_sub_three, rho1CaseI_m_sub_two,
      rho1CaseI_m_sub_one, add_assoc, add_left_comm, add_comm]
    omega
  have hm3le : m - 3 ≤ m := by
    omega
  calc
    (∑ x : Fin m, TorusD3Even.rho1CaseI (m := m) x) = Finset.sum (Finset.range m) g := hsumRange
    _ = Finset.sum (Finset.range (m - 3)) g + Finset.sum (Finset.Ico (m - 3) m) g := by
          symm
          exact Finset.sum_range_add_sum_Ico g hm3le
    _ = (Finset.sum (Finset.range 1) g + Finset.sum (Finset.Ico 1 (m - 3)) g)
          + Finset.sum (Finset.Ico (m - 3) m) g := by
            rw [show Finset.sum (Finset.range (m - 3)) g =
              Finset.sum (Finset.range 1) g + Finset.sum (Finset.Ico 1 (m - 3)) g by
                symm
                exact Finset.sum_range_add_sum_Ico g hm1]
    _ = (1 + (m - 4) * (m + 2)) + (2 * m + 7) := by
          rw [hhead, hmid, hsuffix]
    _ = m ^ 2 := by
          let k : ℕ := m - 4
          have hmEq : m = k + 4 := by
            dsimp [k]
            omega
          rw [hmEq, pow_two]
          simp
          ring_nf

theorem hsum_caseI [Fact (5 < m)] (hmEven : Even m) (hcase : m % 6 ≠ 4) :
    TorusD3Even.blockTime
        (TorusD3Even.T1CaseI (m := m))
        (TorusD3Even.rho1CaseI (m := m))
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
      (fun i : Fin m => ((TorusD3Even.T1CaseI (m := m)^[i.1]) x0))
      (cycleOn_T1CaseI_caseI (m := m) hmEven hcase).1
  calc
    TorusD3Even.blockTime
        (TorusD3Even.T1CaseI (m := m))
        (TorusD3Even.rho1CaseI (m := m))
        x0
        m
        = Finset.sum (Finset.range m) (fun i =>
            TorusD3Even.rho1CaseI (m := m) (((TorusD3Even.T1CaseI (m := m)^[i]) x0))) := by
            simpa using
              blockTime_eq_sum_range
                (TorusD3Even.T1CaseI (m := m))
                (TorusD3Even.rho1CaseI (m := m))
                x0
                m
    _ = ∑ i : Fin m, TorusD3Even.rho1CaseI (m := m) (e i) := by
          rw [← Fin.sum_univ_eq_sum_range]
          rfl
    _ = ∑ x : Fin m, TorusD3Even.rho1CaseI (m := m) x := by
          exact Equiv.sum_comp e (fun x : Fin m => TorusD3Even.rho1CaseI (m := m) x)
    _ = m ^ 2 := sum_rho1CaseI (m := m)

theorem iterate_returnMap1CaseI_odd_prefix_partial [Fact (5 < m)]
    {x t : ℕ} (hx1 : 1 ≤ x) (hxle : x ≤ m - 4) (hxodd : Odd x)
    (ht : t ≤ (m - 1 - x) / 2) :
    let xFin : Fin m := ⟨x, by omega⟩
    ((returnMap1CaseI (m := m)^[t]) (linePoint1 (m := m) xFin)) =
      ((((x + t : ℕ) : ZMod m)), (((t : ℕ) : ZMod m))) := by
  let xFin : Fin m := ⟨x, by omega⟩
  calc
    ((returnMap1CaseI (m := m)^[t]) (linePoint1 (m := m) xFin))
        = ((bulkMap1CaseI (m := m)^[t]) (linePoint1 (m := m) xFin)) := by
            refine iterate_eq_iterate_of_eq_on_prefix
              (F := returnMap1CaseI (m := m)) (G := bulkMap1CaseI (m := m))
              (z := linePoint1 (m := m) xFin) t ?_
            intro s hs
            rw [iterate_bulkMap1CaseI (m := m) s (linePoint1 (m := m) xFin)]
            have hi_pos : 0 < x + s := by omega
            have hi_lt : x + s < m := by omega
            have hi_ne_zero : (((x + s : ℕ) : ZMod m)) ≠ 0 := by
              exact natCast_ne_zero_of_pos_lt (m := m) (n := x + s) hi_pos hi_lt
            have hi_ne_neg_two : (((x + s : ℕ) : ZMod m)) ≠ (-2 : ZMod m) := by
              exact natCast_ne_neg_two_of_lt (m := m) (n := x + s) (by omega)
            have hk_ne_neg_one : (((s : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
              exact natCast_ne_neg_one_of_lt (m := m) (n := s) (by omega)
            have h00 : ¬ ((((x + s : ℕ) : ZMod m)) = 0 ∧ (((s : ℕ) : ZMod m)) = 0) := by
              intro h
              exact hi_ne_zero h.1
            have hdiag :
                ¬ ((((x + s : ℕ) : ZMod m)) + (((s : ℕ) : ZMod m)) = (-1 : ZMod m) ∧
                    (((x + s : ℕ) : ZMod m)) ≠ 0 ∧
                    (((x + s : ℕ) : ZMod m)) ≠ (-2 : ZMod m) ∧
                    (((x + s : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              have hsum_ne : (((x + 2 * s : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
                exact natCast_ne_neg_one_of_lt (m := m) (n := x + 2 * s) (by omega)
              apply hsum_ne
              simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm, two_mul] using h.1
            have hneg1 :
                ¬ ((((x + s : ℕ) : ZMod m)) = (-1 : ZMod m) ∧ (((s : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              exact hk_ne_neg_one h.2
            have hneg2 :
                ¬ ((((x + s : ℕ) : ZMod m)) = (-2 : ZMod m) ∧ (((s : ℕ) : ZMod m)) = 0) := by
              intro h
              exact hi_ne_neg_two h.1
            have hi0 :
                ¬ ((((x + s : ℕ) : ZMod m)) = 0 ∧
                    (((s : ℕ) : ZMod m)) ≠ 0 ∧
                    (((s : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              exact hi_ne_zero h.1
            have h1neg1 :
                ¬ ((((x + s : ℕ) : ZMod m)) = (1 : ZMod m) ∧ (((s : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              exact hk_ne_neg_one h.2
            have hneg2one :
                ¬ ((((x + s : ℕ) : ZMod m)) = (-2 : ZMod m) ∧ (((s : ℕ) : ZMod m)) = (1 : ZMod m)) := by
              intro h
              exact hi_ne_neg_two h.1
            simpa [linePoint1, xFin] using
              returnMap1CaseI_eq_bulk_of_not_special (m := m)
                (i := (((x + s : ℕ) : ZMod m))) (k := (((s : ℕ) : ZMod m)))
                h00 hdiag hneg1 hneg2 hi0 h1neg1 hneg2one
    _ = ((((x : ℕ) : ZMod m) + (((t : ℕ) : ZMod m))), (((t : ℕ) : ZMod m))) := by
          rw [iterate_bulkMap1CaseI (m := m) t (linePoint1 (m := m) xFin)]
          simp [linePoint1, xFin]
    _ = ((((x + t : ℕ) : ZMod m)), (((t : ℕ) : ZMod m))) := by
          rw [Nat.cast_add]

theorem iterate_returnMap1CaseI_odd_middle_partial [Fact (5 < m)] (hmEven : Even m)
    {x t : ℕ} (hx1 : 1 ≤ x) (hxle : x ≤ m - 4) (hxodd : Odd x)
    (ht : t ≤ (m - 1 - x) / 2 - 1) :
    let a : ℕ := (m - 1 - x) / 2
    ((returnMap1CaseI (m := m)^[t]) ((((x + a + 2 : ℕ) : ZMod m)), (((a : ℕ) : ZMod m)))) =
      ((((x + a + 2 + t : ℕ) : ZMod m)), (((a + t : ℕ) : ZMod m))) := by
  let a : ℕ := (m - 1 - x) / 2
  have hxa : x + 2 * a = m - 1 := by
    simpa [a] using odd_caseI_half_eq (m := m) hmEven hx1 hxle hxodd
  calc
    ((returnMap1CaseI (m := m)^[t]) ((((x + a + 2 : ℕ) : ZMod m)), (((a : ℕ) : ZMod m))))
        = ((bulkMap1CaseI (m := m)^[t]) ((((x + a + 2 : ℕ) : ZMod m)), (((a : ℕ) : ZMod m)))) := by
            refine iterate_eq_iterate_of_eq_on_prefix
              (F := returnMap1CaseI (m := m)) (G := bulkMap1CaseI (m := m))
              (z := ((((x + a + 2 : ℕ) : ZMod m)), (((a : ℕ) : ZMod m)))) t ?_
            intro s hs
            rw [iterate_bulkMap1CaseI (m := m) s ((((x + a + 2 : ℕ) : ZMod m)), (((a : ℕ) : ZMod m)))]
            have hi_pos : 0 < x + a + 2 + s := by omega
            have hi_lt : x + a + 2 + s < m := by omega
            have hk_pos : 0 < a + s := by omega
            have hk_lt : a + s < m := by omega
            have hk_ne_zero : (((a + s : ℕ) : ZMod m)) ≠ 0 := by
              exact natCast_ne_zero_of_pos_lt (m := m) (n := a + s) hk_pos hk_lt
            have hk_ne_one : (((a + s : ℕ) : ZMod m)) ≠ 1 := by
              exact natCast_ne_one_of_two_le_lt (m := m) (n := a + s) (by omega) hk_lt
            have hk_ne_neg_one : (((a + s : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
              exact natCast_ne_neg_one_of_lt (m := m) (n := a + s) (by omega)
            have hi_ne_zero : (((x + a + 2 + s : ℕ) : ZMod m)) ≠ 0 := by
              exact natCast_ne_zero_of_pos_lt (m := m) (n := x + a + 2 + s) hi_pos hi_lt
            have h00 :
                ¬ ((((x + a + 2 + s : ℕ) : ZMod m)) = 0 ∧ (((a + s : ℕ) : ZMod m)) = 0) := by
              intro h
              exact hi_ne_zero h.1
            have hdiag :
                ¬ ((((x + a + 2 + s : ℕ) : ZMod m)) + (((a + s : ℕ) : ZMod m)) = (-1 : ZMod m) ∧
                    (((x + a + 2 + s : ℕ) : ZMod m)) ≠ 0 ∧
                    (((x + a + 2 + s : ℕ) : ZMod m)) ≠ (-2 : ZMod m) ∧
                    (((x + a + 2 + s : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              have hsum_ne : (((1 + 2 * s : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
                exact natCast_ne_neg_one_of_lt (m := m) (n := 1 + 2 * s) (by omega)
              apply hsum_ne
              have hsumEq :
                  (((x + a + 2 + s + (a + s) : ℕ) : ZMod m)) =
                    (((1 + 2 * s : ℕ) : ZMod m)) := by
                rw [show x + a + 2 + s + (a + s) = x + 2 * a + (2 * s + 2) by omega, hxa]
                have hm1 : (((m - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) := by
                  exact cast_sub_one_eq_neg_one (m := m) (by
                    have hm5 : 5 < m := Fact.out
                    omega)
                rw [Nat.cast_add, Nat.cast_add, hm1]
                have hz :
                    (-1 : ZMod m) + (2 + 2 * ((s : ℕ) : ZMod m)) =
                      (1 : ZMod m) + 2 * ((s : ℕ) : ZMod m) := by
                  ring
                simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using hz
              have hsumLeft :
                  ((((x + a + 2 + s : ℕ) : ZMod m)) + (((a + s : ℕ) : ZMod m))) =
                    (((1 + 2 * s : ℕ) : ZMod m)) := by
                simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using hsumEq
              exact hsumLeft.symm.trans h.1
            have hneg1 :
                ¬ ((((x + a + 2 + s : ℕ) : ZMod m)) = (-1 : ZMod m) ∧
                    (((a + s : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              exact hk_ne_neg_one h.2
            have hneg2 :
                ¬ ((((x + a + 2 + s : ℕ) : ZMod m)) = (-2 : ZMod m) ∧
                    (((a + s : ℕ) : ZMod m)) = 0) := by
              intro h
              exact hk_ne_zero h.2
            have hi0 :
                ¬ ((((x + a + 2 + s : ℕ) : ZMod m)) = 0 ∧
                    (((a + s : ℕ) : ZMod m)) ≠ 0 ∧
                    (((a + s : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              exact hi_ne_zero h.1
            have h1neg1 :
                ¬ ((((x + a + 2 + s : ℕ) : ZMod m)) = (1 : ZMod m) ∧
                    (((a + s : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              exact hk_ne_neg_one h.2
            have hneg2one :
                ¬ ((((x + a + 2 + s : ℕ) : ZMod m)) = (-2 : ZMod m) ∧
                    (((a + s : ℕ) : ZMod m)) = (1 : ZMod m)) := by
              intro h
              exact hk_ne_one h.2
            simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
              returnMap1CaseI_eq_bulk_of_not_special (m := m)
                (i := (((x + a + 2 + s : ℕ) : ZMod m))) (k := (((a + s : ℕ) : ZMod m)))
                h00 hdiag hneg1 hneg2 hi0 h1neg1 hneg2one
    _ = ((((x + a + 2 + t : ℕ) : ZMod m)), (((a + t : ℕ) : ZMod m))) := by
          rw [iterate_bulkMap1CaseI (m := m) t ((((x + a + 2 : ℕ) : ZMod m)), (((a : ℕ) : ZMod m)))]
          simp [Nat.cast_add, add_assoc, add_left_comm, add_comm]

theorem iterate_returnMap1CaseI_odd_suffix_partial [Fact (5 < m)] (hmEven : Even m)
    {x t : ℕ} (hx1 : 1 ≤ x) (hxle : x ≤ m - 4) (hxodd : Odd x)
    (ht : t ≤ x + 1) :
    ((returnMap1CaseI (m := m)^[t]) ((1 : ZMod m), (((m - x - 2 : ℕ) : ZMod m)))) =
      ((((1 + t : ℕ) : ZMod m)), ((((m - x - 2) + t : ℕ) : ZMod m))) := by
  calc
    ((returnMap1CaseI (m := m)^[t]) ((1 : ZMod m), (((m - x - 2 : ℕ) : ZMod m))))
        = ((bulkMap1CaseI (m := m)^[t]) ((1 : ZMod m), (((m - x - 2 : ℕ) : ZMod m)))) := by
            refine iterate_eq_iterate_of_eq_on_prefix
              (F := returnMap1CaseI (m := m)) (G := bulkMap1CaseI (m := m))
              (z := ((1 : ZMod m), (((m - x - 2 : ℕ) : ZMod m)))) t ?_
            intro s hs
            rw [iterate_bulkMap1CaseI (m := m) s ((1 : ZMod m), (((m - x - 2 : ℕ) : ZMod m)))]
            have hi_pos : 0 < 1 + s := by omega
            have hi_lt : 1 + s < m := by
              rcases hmEven with ⟨q, hmq⟩
              rcases hxodd with ⟨r, hrx⟩
              rw [hmq] at hxle
              rw [hrx] at hxle
              omega
            have hi_ne_zero : (((1 + s : ℕ) : ZMod m)) ≠ 0 := by
              exact natCast_ne_zero_of_pos_lt (m := m) (n := 1 + s) hi_pos hi_lt
            have hi_ne_neg_one : (((1 + s : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
              exact natCast_ne_neg_one_of_lt (m := m) (n := 1 + s) (by omega)
            have hi_ne_neg_two : (((1 + s : ℕ) : ZMod m)) ≠ (-2 : ZMod m) := by
              exact natCast_ne_neg_two_of_lt (m := m) (n := 1 + s) (by
                rcases hmEven with ⟨q, hmq⟩
                rcases hxodd with ⟨r, hrx⟩
                rw [hmq] at hxle
                rw [hrx] at hxle
                omega)
            have h00 :
                ¬ ((((1 + s : ℕ) : ZMod m)) = 0 ∧ ((((m - x - 2) + s : ℕ) : ZMod m)) = 0) := by
              intro h
              exact hi_ne_zero h.1
            have hdiag :
                ¬ ((((1 + s : ℕ) : ZMod m)) + ((((m - x - 2) + s : ℕ) : ZMod m)) = (-1 : ZMod m) ∧
                    (((1 + s : ℕ) : ZMod m)) ≠ 0 ∧
                    (((1 + s : ℕ) : ZMod m)) ≠ (-2 : ZMod m) ∧
                    (((1 + s : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              have hsumEven : Even (m - x - 1 + 2 * s) := by
                rcases hmEven with ⟨q, hmq⟩
                rcases hxodd with ⟨r, hrx⟩
                rw [hmq, hrx]
                refine ⟨q - r - 1 + s, ?_⟩
                omega
              have hsum_ne : (((m - x - 1 + 2 * s : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
                exact natCast_ne_neg_one_of_even (m := m) hmEven hsumEven
              apply hsum_ne
              have hsumEq :
                  ((((1 + s : ℕ) : ZMod m)) + ((((m - x - 2) + s : ℕ) : ZMod m))) =
                    (((m - x - 1 + 2 * s : ℕ) : ZMod m)) := by
                have hnat : 1 + s + ((m - x - 2) + s) = m - x - 1 + 2 * s := by
                  omega
                simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
                  congrArg (fun n : ℕ => ((n : ℕ) : ZMod m)) hnat
              exact hsumEq.symm.trans h.1
            have hneg1 :
                ¬ ((((1 + s : ℕ) : ZMod m)) = (-1 : ZMod m) ∧
                    ((((m - x - 2) + s : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              exact hi_ne_neg_one h.1
            have hneg2 :
                ¬ ((((1 + s : ℕ) : ZMod m)) = (-2 : ZMod m) ∧
                    ((((m - x - 2) + s : ℕ) : ZMod m)) = 0) := by
              intro h
              exact hi_ne_neg_two h.1
            have hi0 :
                ¬ ((((1 + s : ℕ) : ZMod m)) = 0 ∧
                    ((((m - x - 2) + s : ℕ) : ZMod m)) ≠ 0 ∧
                    ((((m - x - 2) + s : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              exact hi_ne_zero h.1
            have h1neg1 :
                ¬ ((((1 + s : ℕ) : ZMod m)) = (1 : ZMod m) ∧
                    ((((m - x - 2) + s : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              have hs0 : s = 0 := by
                have hmod := (ZMod.natCast_eq_natCast_iff' (1 + s) 1 m).1 (by simpa using h.1)
                rw [Nat.mod_eq_of_lt hi_lt, Nat.mod_eq_of_lt (by
                  have hm5 : 5 < m := Fact.out
                  omega)] at hmod
                omega
              subst hs0
              have hkbase : (((m - x - 2 : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
                exact natCast_ne_neg_one_of_lt (m := m) (n := m - x - 2) (by omega)
              exact hkbase h.2
            have hneg2one :
                ¬ ((((1 + s : ℕ) : ZMod m)) = (-2 : ZMod m) ∧
                    ((((m - x - 2) + s : ℕ) : ZMod m)) = (1 : ZMod m)) := by
              intro h
              exact hi_ne_neg_two h.1
            simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
              returnMap1CaseI_eq_bulk_of_not_special (m := m)
                (i := (((1 + s : ℕ) : ZMod m))) (k := ((((m - x - 2) + s : ℕ) : ZMod m)))
                h00 hdiag hneg1 hneg2 hi0 h1neg1 hneg2one
    _ = ((((1 + t : ℕ) : ZMod m)), ((((m - x - 2) + t : ℕ) : ZMod m))) := by
          rw [iterate_bulkMap1CaseI (m := m) t ((1 : ZMod m), (((m - x - 2 : ℕ) : ZMod m)))]
          ext <;> simp [Nat.cast_add, add_assoc, add_left_comm, add_comm]

theorem hfirst_line_odd_generic [Fact (5 < m)] (hmEven : Even m)
    {x : ℕ} (hx1 : 1 ≤ x) (hxle : x ≤ m - 4) (hxodd : Odd x) :
    ∀ n, 0 < n →
      n < TorusD3Even.rho1CaseI (m := m) (⟨x, by omega⟩ : Fin m) →
        (returnMap1CaseI (m := m)^[n]) (linePoint1 (m := m) (⟨x, by omega⟩ : Fin m)) ∉
          Set.range (linePoint1 (m := m)) := by
  let xFin : Fin m := ⟨x, by omega⟩
  intro n hn0 hnlt
  have hm0 : 0 < m := by
    have hm5 : 5 < m := Fact.out
    omega
  letI : Fact (0 < m) := ⟨hm0⟩
  let a : ℕ := (m - 1 - x) / 2
  have hx0 : xFin.1 ≠ 0 := by
    simp [xFin]
    omega
  have hxm3 : xFin.1 ≠ m - 3 := by
    simp [xFin]
    omega
  have hxm2 : xFin.1 ≠ m - 2 := by
    simp [xFin]
    omega
  have hxm1 : xFin.1 ≠ m - 1 := by
    simp [xFin]
    omega
  have hrho : TorusD3Even.rho1CaseI (m := m) xFin = m + 2 := by
    simp [TorusD3Even.rho1CaseI, hx0, hxm2, hxm3, hxm1]
  have hnm : n < m + 2 := by simpa [xFin, hrho] using hnlt
  have ha1 : 1 ≤ a := by
    dsimp [a]
    omega
  by_cases hprefix : n ≤ a
  · have hiter :
        (returnMap1CaseI (m := m)^[n]) (linePoint1 (m := m) xFin) =
          ((((x + n : ℕ) : ZMod m)), (((n : ℕ) : ZMod m))) := by
      simpa [xFin, a] using
        iterate_returnMap1CaseI_odd_prefix_partial (m := m) (x := x) (t := n) hx1 hxle hxodd hprefix
    apply not_mem_range_linePoint1_of_snd_ne_zero
    rw [hiter]
    exact natCast_ne_zero_of_pos_lt (m := m) (n := n) hn0 (by omega)
  · by_cases hdiag : n = a + 1
    · have hiter :
          (returnMap1CaseI (m := m)^[n]) (linePoint1 (m := m) xFin) =
            ((((x + a + 2 : ℕ) : ZMod m)), (((a : ℕ) : ZMod m))) := by
        rw [hdiag]
        rw [show a + 1 = 1 + a by omega, Function.iterate_add_apply]
        rw [iterate_returnMap1CaseI_odd_prefix_partial (m := m) (x := x) (t := a) hx1 hxle hxodd le_rfl]
        exact returnMap1CaseI_odd_diag (m := m) hmEven hx1 hxle hxodd
      apply not_mem_range_linePoint1_of_snd_ne_zero
      rw [hiter]
      exact natCast_ne_zero_of_pos_lt (m := m) (n := a) ha1 (by omega)
    · by_cases hmiddle : n ≤ 2 * a
      · let t : ℕ := n - (a + 1)
        have ht_pos : 0 < t := by
          dsimp [t]
          omega
        have ht : t ≤ a - 1 := by
          dsimp [t]
          omega
        have hnEq : n = a + 1 + t := by
          dsimp [t]
          omega
        have hiter :
            (returnMap1CaseI (m := m)^[n]) (linePoint1 (m := m) xFin) =
              ((((x + a + 2 + t : ℕ) : ZMod m)), (((a + t : ℕ) : ZMod m))) := by
          have hdiagStep :
              (returnMap1CaseI (m := m)^[1]) ((((x + a : ℕ) : ZMod m)), (((a : ℕ) : ZMod m))) =
                ((((x + a + 2 : ℕ) : ZMod m)), (((a : ℕ) : ZMod m))) := by
            simpa [Function.iterate_one] using
              returnMap1CaseI_odd_diag (m := m) hmEven hx1 hxle hxodd
          rw [hnEq]
          rw [show a + 1 + t = t + (a + 1) by omega, Function.iterate_add_apply]
          rw [show a + 1 = 1 + a by omega, Function.iterate_add_apply]
          rw [iterate_returnMap1CaseI_odd_prefix_partial (m := m) (x := x) (t := a) hx1 hxle hxodd le_rfl]
          rw [hdiagStep]
          simpa [a] using
            iterate_returnMap1CaseI_odd_middle_partial (m := m) hmEven
              (x := x) (t := t) hx1 hxle hxodd ht
        apply not_mem_range_linePoint1_of_snd_ne_zero
        rw [hiter]
        exact natCast_ne_zero_of_pos_lt (m := m) (n := a + t) (by omega) (by omega)
      · by_cases hvert : n = 2 * a + 1
        · have hiter :
            (returnMap1CaseI (m := m)^[n]) (linePoint1 (m := m) xFin) =
              ((1 : ZMod m), (((m - x - 2 : ℕ) : ZMod m))) := by
            have hdiagStep :
                (returnMap1CaseI (m := m)^[1]) ((((x + a : ℕ) : ZMod m)), (((a : ℕ) : ZMod m))) =
                  ((((x + a + 2 : ℕ) : ZMod m)), (((a : ℕ) : ZMod m))) := by
              simpa [Function.iterate_one] using
                returnMap1CaseI_odd_diag (m := m) hmEven hx1 hxle hxodd
            rw [hvert]
            rw [show 2 * a + 1 = 1 + (a + 1 + (a - 1)) by omega, Function.iterate_add_apply]
            rw [show a + 1 + (a - 1) = (a - 1) + (a + 1) by omega, Function.iterate_add_apply]
            rw [show a + 1 = 1 + a by omega, Function.iterate_add_apply]
            rw [iterate_returnMap1CaseI_odd_prefix_partial (m := m) (x := x) (t := a) hx1 hxle hxodd le_rfl]
            rw [hdiagStep]
            have hmidEnd :
                (returnMap1CaseI (m := m)^[a - 1])
                  ((((x + a + 2 : ℕ) : ZMod m)), (((a : ℕ) : ZMod m))) =
                    ((0 : ZMod m), (((m - x - 2 : ℕ) : ZMod m))) := by
              simpa [a] using iterate_returnMap1CaseI_odd_middle (m := m) hmEven hx1 hxle hxodd
            rw [hmidEnd]
            simpa [Function.iterate_one] using returnMap1CaseI_odd_vertical (m := m) hx1 hxle
          apply not_mem_range_linePoint1_of_snd_ne_zero
          rw [hiter]
          exact natCast_ne_zero_of_pos_lt (m := m) (n := m - x - 2) (by omega) (by omega)
        · let t : ℕ := n - (2 * a + 1)
          have ht_pos : 0 < t := by
            dsimp [t]
            omega
          have hsplit : m + 2 = 2 * a + 1 + (x + 2) := by
            dsimp [a]
            rcases hmEven with ⟨q, hmq⟩
            rcases hxodd with ⟨r, hrx⟩
            rw [hmq, hrx]
            omega
          have ht : t ≤ x + 1 := by
            dsimp [t]
            rw [hsplit] at hnm
            omega
          have hnEq : n = 2 * a + 1 + t := by
            dsimp [t]
            omega
          have hiter :
              (returnMap1CaseI (m := m)^[n]) (linePoint1 (m := m) xFin) =
                ((((1 + t : ℕ) : ZMod m)), ((((m - x - 2) + t : ℕ) : ZMod m))) := by
            rw [hnEq]
            rw [show 2 * a + 1 + t = t + (2 * a + 1) by omega, Function.iterate_add_apply]
            have hstart :
                (returnMap1CaseI (m := m)^[2 * a + 1]) (linePoint1 (m := m) xFin) =
                  ((1 : ZMod m), (((m - x - 2 : ℕ) : ZMod m))) := by
              have hdiagStep :
                  (returnMap1CaseI (m := m)^[1]) ((((x + a : ℕ) : ZMod m)), (((a : ℕ) : ZMod m))) =
                    ((((x + a + 2 : ℕ) : ZMod m)), (((a : ℕ) : ZMod m))) := by
                simpa [Function.iterate_one] using
                  returnMap1CaseI_odd_diag (m := m) hmEven hx1 hxle hxodd
              rw [show 2 * a + 1 = 1 + (a + 1 + (a - 1)) by omega, Function.iterate_add_apply]
              rw [show a + 1 + (a - 1) = (a - 1) + (a + 1) by omega, Function.iterate_add_apply]
              rw [show a + 1 = 1 + a by omega, Function.iterate_add_apply]
              rw [iterate_returnMap1CaseI_odd_prefix_partial (m := m) (x := x) (t := a) hx1 hxle hxodd le_rfl]
              rw [hdiagStep]
              have hmidEnd :
                  (returnMap1CaseI (m := m)^[a - 1])
                    ((((x + a + 2 : ℕ) : ZMod m)), (((a : ℕ) : ZMod m))) =
                      ((0 : ZMod m), (((m - x - 2 : ℕ) : ZMod m))) := by
                simpa [a] using iterate_returnMap1CaseI_odd_middle (m := m) hmEven hx1 hxle hxodd
              rw [hmidEnd]
              simpa [Function.iterate_one] using returnMap1CaseI_odd_vertical (m := m) hx1 hxle
            rw [hstart]
            exact iterate_returnMap1CaseI_odd_suffix_partial (m := m) hmEven
              (x := x) (t := t) hx1 hxle hxodd ht
          have hy :
              ((((m - x - 2) + t : ℕ) : ZMod m)) ≠ 0 := by
            exact natCast_ne_zero_of_pos_lt (m := m) (n := (m - x - 2) + t) (by omega) (by omega)
          apply not_mem_range_linePoint1_of_snd_ne_zero
          rw [hiter]
          exact hy

theorem iterate_returnMap1CaseI_even_prefix_partial [Fact (5 < m)] (hmEven : Even m)
    {x t : ℕ} (hx2 : 2 ≤ x) (hxle : x ≤ m - 4) (hxeven : Even x)
    (ht : t ≤ m - x) :
    let xFin : Fin m := ⟨x, by omega⟩
    ((returnMap1CaseI (m := m)^[t]) (linePoint1 (m := m) xFin)) =
      ((((x + t : ℕ) : ZMod m)), (((t : ℕ) : ZMod m))) := by
  let xFin : Fin m := ⟨x, by omega⟩
  calc
    ((returnMap1CaseI (m := m)^[t]) (linePoint1 (m := m) xFin))
        = ((bulkMap1CaseI (m := m)^[t]) (linePoint1 (m := m) xFin)) := by
            refine iterate_eq_iterate_of_eq_on_prefix
              (F := returnMap1CaseI (m := m)) (G := bulkMap1CaseI (m := m))
              (z := linePoint1 (m := m) xFin) t ?_
            intro s hs
            rw [iterate_bulkMap1CaseI (m := m) s (linePoint1 (m := m) xFin)]
            have hi_pos : 0 < x + s := by omega
            have hi_lt : x + s < m := by omega
            have hk_lt : s < m := by omega
            have hi_ne_zero : (((x + s : ℕ) : ZMod m)) ≠ 0 := by
              exact natCast_ne_zero_of_pos_lt (m := m) (n := x + s) hi_pos hi_lt
            have hk_ne_neg_one : (((s : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
              exact natCast_ne_neg_one_of_lt (m := m) (n := s) (by omega)
            have h00 : ¬ ((((x + s : ℕ) : ZMod m)) = 0 ∧ (((s : ℕ) : ZMod m)) = 0) := by
              intro h
              exact hi_ne_zero h.1
            have hdiag :
                ¬ ((((x + s : ℕ) : ZMod m)) + (((s : ℕ) : ZMod m)) = (-1 : ZMod m) ∧
                    (((x + s : ℕ) : ZMod m)) ≠ 0 ∧
                    (((x + s : ℕ) : ZMod m)) ≠ (-2 : ZMod m) ∧
                    (((x + s : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              have hsumEven : Even (x + 2 * s) := by
                rcases hxeven with ⟨r, hr⟩
                refine ⟨r + s, ?_⟩
                rw [hr]
                ring
              have hsum_ne : (((x + 2 * s : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
                exact natCast_ne_neg_one_of_even (m := m) hmEven hsumEven
              apply hsum_ne
              have hsumEq :
                  ((((x + s : ℕ) : ZMod m)) + (((s : ℕ) : ZMod m))) =
                    (((x + 2 * s : ℕ) : ZMod m)) := by
                simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
                  congrArg (fun n : ℕ => ((n : ℕ) : ZMod m)) (by omega : x + s + s = x + 2 * s)
              exact hsumEq.symm.trans h.1
            have hneg1 :
                ¬ ((((x + s : ℕ) : ZMod m)) = (-1 : ZMod m) ∧ (((s : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              exact hk_ne_neg_one h.2
            have hneg2 :
                ¬ ((((x + s : ℕ) : ZMod m)) = (-2 : ZMod m) ∧ (((s : ℕ) : ZMod m)) = 0) := by
              intro h
              have hs0 : s = 0 := by
                have hmod := (ZMod.natCast_eq_natCast_iff' s 0 m).1 (by simpa using h.2)
                rw [Nat.mod_eq_of_lt hk_lt, Nat.zero_mod] at hmod
                exact hmod
              subst hs0
              exact natCast_ne_neg_two_of_lt (m := m) (n := x) (by omega) h.1
            have hi0 :
                ¬ ((((x + s : ℕ) : ZMod m)) = 0 ∧
                    (((s : ℕ) : ZMod m)) ≠ 0 ∧
                    (((s : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              exact hi_ne_zero h.1
            have h1neg1 :
                ¬ ((((x + s : ℕ) : ZMod m)) = (1 : ZMod m) ∧ (((s : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              exact hk_ne_neg_one h.2
            have hneg2one :
                ¬ ((((x + s : ℕ) : ZMod m)) = (-2 : ZMod m) ∧ (((s : ℕ) : ZMod m)) = (1 : ZMod m)) := by
              intro h
              have hs1 : s = 1 := by
                have hmod := (ZMod.natCast_eq_natCast_iff' s 1 m).1 (by simpa using h.2)
                rw [Nat.mod_eq_of_lt hk_lt, Nat.mod_eq_of_lt (by
                  have hm5 : 5 < m := Fact.out
                  omega)] at hmod
                exact hmod
              subst hs1
              exact natCast_ne_neg_two_of_lt (m := m) (n := x + 1) (by omega) h.1
            simpa [linePoint1, xFin] using
              returnMap1CaseI_eq_bulk_of_not_special (m := m)
                (i := (((x + s : ℕ) : ZMod m))) (k := (((s : ℕ) : ZMod m)))
                h00 hdiag hneg1 hneg2 hi0 h1neg1 hneg2one
    _ = ((((x : ℕ) : ZMod m) + (((t : ℕ) : ZMod m))), (((t : ℕ) : ZMod m))) := by
          rw [iterate_bulkMap1CaseI (m := m) t (linePoint1 (m := m) xFin)]
          simp [linePoint1, xFin]
    _ = ((((x + t : ℕ) : ZMod m)), (((t : ℕ) : ZMod m))) := by
          rw [Nat.cast_add]

theorem iterate_returnMap1CaseI_even_middle_partial [Fact (5 < m)]
    {x t : ℕ} (hx2 : 2 ≤ x) (hxle : x ≤ m - 4) (hxeven : Even x)
    (ht : t ≤ x / 2 - 1) :
    ((returnMap1CaseI (m := m)^[t]) ((1 : ZMod m), (((m - x : ℕ) : ZMod m)))) =
      ((((1 + t : ℕ) : ZMod m)), ((((m - x) + t : ℕ) : ZMod m))) := by
  calc
    ((returnMap1CaseI (m := m)^[t]) ((1 : ZMod m), (((m - x : ℕ) : ZMod m))))
        = ((bulkMap1CaseI (m := m)^[t]) ((1 : ZMod m), (((m - x : ℕ) : ZMod m)))) := by
            refine iterate_eq_iterate_of_eq_on_prefix
              (F := returnMap1CaseI (m := m)) (G := bulkMap1CaseI (m := m))
              (z := ((1 : ZMod m), (((m - x : ℕ) : ZMod m)))) t ?_
            intro s hs
            rw [iterate_bulkMap1CaseI (m := m) s ((1 : ZMod m), (((m - x : ℕ) : ZMod m)))]
            have hi_pos : 0 < 1 + s := by omega
            have hi_lt : 1 + s < m := by omega
            have hi_ne_zero : (((1 + s : ℕ) : ZMod m)) ≠ 0 := by
              exact natCast_ne_zero_of_pos_lt (m := m) (n := 1 + s) hi_pos hi_lt
            have hi_ne_neg_two : (((1 + s : ℕ) : ZMod m)) ≠ (-2 : ZMod m) := by
              exact natCast_ne_neg_two_of_lt (m := m) (n := 1 + s) (by omega)
            have hk_ne_neg_one : ((((m - x) + s : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
              exact natCast_ne_neg_one_of_lt (m := m) (n := (m - x) + s) (by omega)
            have h00 : ¬ ((((1 + s : ℕ) : ZMod m)) = 0 ∧ ((((m - x) + s : ℕ) : ZMod m)) = 0) := by
              intro h
              exact hi_ne_zero h.1
            have hdiag :
                ¬ ((((1 + s : ℕ) : ZMod m)) + ((((m - x) + s : ℕ) : ZMod m)) = (-1 : ZMod m) ∧
                    (((1 + s : ℕ) : ZMod m)) ≠ 0 ∧
                    (((1 + s : ℕ) : ZMod m)) ≠ (-2 : ZMod m) ∧
                    (((1 + s : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              have hsum_ne : (((m - x + 1 + 2 * s : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
                exact natCast_ne_neg_one_of_lt (m := m) (n := m - x + 1 + 2 * s) (by
                  omega)
              apply hsum_ne
              have hsumEq :
                  ((((1 + s : ℕ) : ZMod m)) + ((((m - x) + s : ℕ) : ZMod m))) =
                    (((m - x + 1 + 2 * s : ℕ) : ZMod m)) := by
                have hnat : 1 + s + ((m - x) + s) = m - x + 1 + 2 * s := by omega
                simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
                  congrArg (fun n : ℕ => ((n : ℕ) : ZMod m)) hnat
              exact hsumEq.symm.trans h.1
            have hneg1 :
                ¬ ((((1 + s : ℕ) : ZMod m)) = (-1 : ZMod m) ∧ ((((m - x) + s : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              exact hk_ne_neg_one h.2
            have hneg2 :
                ¬ ((((1 + s : ℕ) : ZMod m)) = (-2 : ZMod m) ∧ ((((m - x) + s : ℕ) : ZMod m)) = 0) := by
              intro h
              exact hi_ne_neg_two h.1
            have hi0 :
                ¬ ((((1 + s : ℕ) : ZMod m)) = 0 ∧
                    ((((m - x) + s : ℕ) : ZMod m)) ≠ 0 ∧
                    ((((m - x) + s : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              exact hi_ne_zero h.1
            have h1neg1 :
                ¬ ((((1 + s : ℕ) : ZMod m)) = (1 : ZMod m) ∧ ((((m - x) + s : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              exact hk_ne_neg_one h.2
            have hneg2one :
                ¬ ((((1 + s : ℕ) : ZMod m)) = (-2 : ZMod m) ∧ ((((m - x) + s : ℕ) : ZMod m)) = (1 : ZMod m)) := by
              intro h
              exact hi_ne_neg_two h.1
            simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
              returnMap1CaseI_eq_bulk_of_not_special (m := m)
                (i := (((1 + s : ℕ) : ZMod m))) (k := ((((m - x) + s : ℕ) : ZMod m)))
                h00 hdiag hneg1 hneg2 hi0 h1neg1 hneg2one
    _ = ((((1 + t : ℕ) : ZMod m)), ((((m - x) + t : ℕ) : ZMod m))) := by
          rw [iterate_bulkMap1CaseI (m := m) t ((1 : ZMod m), (((m - x : ℕ) : ZMod m)))]
          simp [Nat.cast_add, add_assoc, add_left_comm, add_comm]

theorem iterate_returnMap1CaseI_even_suffix_partial [Fact (5 < m)]
    {x t : ℕ} (hx2 : 2 ≤ x) (hxle : x ≤ m - 4) (hxeven : Even x)
    (ht : t ≤ x / 2) :
    ((returnMap1CaseI (m := m)^[t])
      ((((x / 2 + 2 : ℕ) : ZMod m)), (((m - x / 2 - 1 : ℕ) : ZMod m)))) =
      ((((x / 2 + 2 + t : ℕ) : ZMod m)), ((((m - x / 2 - 1) + t : ℕ) : ZMod m))) := by
  calc
    ((returnMap1CaseI (m := m)^[t])
      ((((x / 2 + 2 : ℕ) : ZMod m)), (((m - x / 2 - 1 : ℕ) : ZMod m))))
        = ((bulkMap1CaseI (m := m)^[t])
          ((((x / 2 + 2 : ℕ) : ZMod m)), (((m - x / 2 - 1 : ℕ) : ZMod m)))) := by
            refine iterate_eq_iterate_of_eq_on_prefix
              (F := returnMap1CaseI (m := m)) (G := bulkMap1CaseI (m := m))
              (z := ((((x / 2 + 2 : ℕ) : ZMod m)), (((m - x / 2 - 1 : ℕ) : ZMod m)))) t ?_
            intro s hs
            rw [iterate_bulkMap1CaseI (m := m) s ((((x / 2 + 2 : ℕ) : ZMod m)), (((m - x / 2 - 1 : ℕ) : ZMod m)))]
            have hi_pos : 0 < x / 2 + 2 + s := by omega
            have hi_lt : x / 2 + 2 + s < m := by omega
            have hi_ne_zero : (((x / 2 + 2 + s : ℕ) : ZMod m)) ≠ 0 := by
              exact natCast_ne_zero_of_pos_lt (m := m) (n := x / 2 + 2 + s) hi_pos hi_lt
            have h00 :
                ¬ ((((x / 2 + 2 + s : ℕ) : ZMod m)) = 0 ∧ ((((m - x / 2 - 1) + s : ℕ) : ZMod m)) = 0) := by
              intro h
              exact hi_ne_zero h.1
            have hdiag :
                ¬ ((((x / 2 + 2 + s : ℕ) : ZMod m)) + ((((m - x / 2 - 1) + s : ℕ) : ZMod m)) = (-1 : ZMod m) ∧
                    (((x / 2 + 2 + s : ℕ) : ZMod m)) ≠ 0 ∧
                    (((x / 2 + 2 + s : ℕ) : ZMod m)) ≠ (-2 : ZMod m) ∧
                    (((x / 2 + 2 + s : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              have hsum_ne : (((1 + 2 * s : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
                exact natCast_ne_neg_one_of_lt (m := m) (n := 1 + 2 * s) (by omega)
              apply hsum_ne
              have hsumEq :
                  ((((x / 2 + 2 + s : ℕ) : ZMod m)) + ((((m - x / 2 - 1) + s : ℕ) : ZMod m))) =
                    (((m + (1 + 2 * s) : ℕ) : ZMod m)) := by
                have hnat : x / 2 + 2 + s + ((m - x / 2 - 1) + s) = m + (1 + 2 * s) := by omega
                simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
                  congrArg (fun n : ℕ => ((n : ℕ) : ZMod m)) hnat
              have hmcast : (((m + (1 + 2 * s) : ℕ) : ZMod m)) = (((1 + 2 * s : ℕ) : ZMod m)) := by
                rw [Nat.cast_add, ZMod.natCast_self, zero_add]
              exact (hsumEq.trans hmcast).symm.trans h.1
            have hneg1 :
                ¬ ((((x / 2 + 2 + s : ℕ) : ZMod m)) = (-1 : ZMod m) ∧
                    ((((m - x / 2 - 1) + s : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              have hk_neg_one : ((((m - x / 2 - 1) + s : ℕ) : ZMod m)) = (-1 : ZMod m) := h.2
              have hk_eq : (m - x / 2 - 1) + s = m - 1 := by
                have hmod := (ZMod.natCast_eq_natCast_iff' ((m - x / 2 - 1) + s) (m - 1) m).1 (by
                  have hm1 : (((m - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) := by
                    exact cast_sub_one_eq_neg_one (m := m) (by
                      have hm5 : 5 < m := Fact.out
                      omega)
                  exact hk_neg_one.trans hm1.symm)
                rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by
                  have hm5 : 5 < m := Fact.out
                  omega)] at hmod
                exact hmod
              have hs_eq : s = x / 2 := by omega
              have hi_last_lt : x / 2 + 2 + s < m - 1 := by
                rw [hs_eq]
                omega
              have hi_last_ne : (((x / 2 + 2 + s : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
                exact natCast_ne_neg_one_of_lt (m := m) (n := x / 2 + 2 + s) (by omega)
              exact hi_last_ne h.1
            have hneg2 :
                ¬ ((((x / 2 + 2 + s : ℕ) : ZMod m)) = (-2 : ZMod m) ∧
                    ((((m - x / 2 - 1) + s : ℕ) : ZMod m)) = 0) := by
              intro h
              have hk_pos : 0 < (m - x / 2 - 1) + s := by omega
              have hk_lt : (m - x / 2 - 1) + s < m := by omega
              exact natCast_ne_zero_of_pos_lt (m := m) (n := (m - x / 2 - 1) + s) hk_pos hk_lt h.2
            have hi0 :
                ¬ ((((x / 2 + 2 + s : ℕ) : ZMod m)) = 0 ∧
                    ((((m - x / 2 - 1) + s : ℕ) : ZMod m)) ≠ 0 ∧
                    ((((m - x / 2 - 1) + s : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              exact hi_ne_zero h.1
            have h1neg1 :
                ¬ ((((x / 2 + 2 + s : ℕ) : ZMod m)) = (1 : ZMod m) ∧
                    ((((m - x / 2 - 1) + s : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              exact natCast_ne_one_of_two_le_lt (m := m) (n := x / 2 + 2 + s) (by omega) hi_lt h.1
            have hneg2one :
                ¬ ((((x / 2 + 2 + s : ℕ) : ZMod m)) = (-2 : ZMod m) ∧
                    ((((m - x / 2 - 1) + s : ℕ) : ZMod m)) = (1 : ZMod m)) := by
              intro h
              have hk_ne_one : ((((m - x / 2 - 1) + s : ℕ) : ZMod m)) ≠ 1 := by
                exact natCast_ne_one_of_two_le_lt (m := m) (n := (m - x / 2 - 1) + s) (by omega) (by omega)
              exact hk_ne_one h.2
            simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
              returnMap1CaseI_eq_bulk_of_not_special (m := m)
                (i := (((x / 2 + 2 + s : ℕ) : ZMod m))) (k := ((((m - x / 2 - 1) + s : ℕ) : ZMod m)))
                h00 hdiag hneg1 hneg2 hi0 h1neg1 hneg2one
    _ = ((((x / 2 + 2 + t : ℕ) : ZMod m)), ((((m - x / 2 - 1) + t : ℕ) : ZMod m))) := by
          rw [iterate_bulkMap1CaseI (m := m) t
            ((((x / 2 + 2 : ℕ) : ZMod m)), (((m - x / 2 - 1 : ℕ) : ZMod m)))]
          simp [Nat.cast_add, add_assoc, add_left_comm, add_comm]

theorem hfirst_line_even_generic [Fact (5 < m)] (hmEven : Even m)
    {x : ℕ} (hx2 : 2 ≤ x) (hxle : x ≤ m - 4) (hxeven : Even x) :
    ∀ n, 0 < n →
      n < TorusD3Even.rho1CaseI (m := m) (⟨x, by omega⟩ : Fin m) →
        (returnMap1CaseI (m := m)^[n]) (linePoint1 (m := m) (⟨x, by omega⟩ : Fin m)) ∉
          Set.range (linePoint1 (m := m)) := by
  let xFin : Fin m := ⟨x, by omega⟩
  intro n hn0 hnlt
  have hm0 : 0 < m := by
    have hm5 : 5 < m := Fact.out
    omega
  letI : Fact (0 < m) := ⟨hm0⟩
  have hx0 : xFin.1 ≠ 0 := by
    simp [xFin]
    omega
  have hxm3 : xFin.1 ≠ m - 3 := by
    simp [xFin]
    omega
  have hxm2 : xFin.1 ≠ m - 2 := by
    simp [xFin]
    omega
  have hxm1 : xFin.1 ≠ m - 1 := by
    simp [xFin]
    omega
  have hrho : TorusD3Even.rho1CaseI (m := m) xFin = m + 2 := by
    simp [TorusD3Even.rho1CaseI, hx0, hxm2, hxm3, hxm1]
  have hnm : n < m + 2 := by simpa [xFin, hrho] using hnlt
  by_cases hprefix : n ≤ m - x
  · have hiter :
        (returnMap1CaseI (m := m)^[n]) (linePoint1 (m := m) xFin) =
          ((((x + n : ℕ) : ZMod m)), (((n : ℕ) : ZMod m))) := by
      simpa [xFin] using
        iterate_returnMap1CaseI_even_prefix_partial (m := m) hmEven (x := x) (t := n)
          hx2 hxle hxeven hprefix
    apply not_mem_range_linePoint1_of_snd_ne_zero
    rw [hiter]
    exact natCast_ne_zero_of_pos_lt (m := m) (n := n) hn0 (by omega)
  · by_cases hvert : n = m - x + 1
    · have hiter :
          (returnMap1CaseI (m := m)^[n]) (linePoint1 (m := m) xFin) =
            ((1 : ZMod m), (((m - x : ℕ) : ZMod m))) := by
        rw [hvert]
        rw [show m - x + 1 = 1 + (m - x) by omega, Function.iterate_add_apply]
        rw [show (returnMap1CaseI (m := m)^[m - x]) (linePoint1 (m := m) xFin) =
          ((0 : ZMod m), (((m - x : ℕ) : ZMod m))) by
            simpa [xFin] using iterate_returnMap1CaseI_even_prefix (m := m) hmEven hx2 hxle hxeven]
        simpa [Function.iterate_one] using returnMap1CaseI_even_vertical (m := m) hx2 hxle
      apply not_mem_range_linePoint1_of_snd_ne_zero
      rw [hiter]
      exact natCast_ne_zero_of_pos_lt (m := m) (n := m - x) (by omega) (by omega)
    · by_cases hmiddle : n ≤ m - x + x / 2
      · let t : ℕ := n - (m - x + 1)
        have ht : t ≤ x / 2 - 1 := by
          dsimp [t]
          omega
        have hnEq : n = m - x + 1 + t := by
          dsimp [t]
          omega
        have hiter :
            (returnMap1CaseI (m := m)^[n]) (linePoint1 (m := m) xFin) =
              ((((1 + t : ℕ) : ZMod m)), ((((m - x) + t : ℕ) : ZMod m))) := by
          rw [hnEq]
          rw [show m - x + 1 + t = t + (m - x + 1) by omega, Function.iterate_add_apply]
          have hstart :
              (returnMap1CaseI (m := m)^[m - x + 1]) (linePoint1 (m := m) xFin) =
                ((1 : ZMod m), (((m - x : ℕ) : ZMod m))) := by
            rw [show m - x + 1 = 1 + (m - x) by omega, Function.iterate_add_apply]
            rw [show (returnMap1CaseI (m := m)^[m - x]) (linePoint1 (m := m) xFin) =
              ((0 : ZMod m), (((m - x : ℕ) : ZMod m))) by
                simpa [xFin] using iterate_returnMap1CaseI_even_prefix (m := m) hmEven hx2 hxle hxeven]
            simpa [Function.iterate_one] using returnMap1CaseI_even_vertical (m := m) hx2 hxle
          rw [hstart]
          exact iterate_returnMap1CaseI_even_middle_partial (m := m)
            (x := x) (t := t) hx2 hxle hxeven ht
        apply not_mem_range_linePoint1_of_snd_ne_zero
        rw [hiter]
        exact natCast_ne_zero_of_pos_lt (m := m) (n := (m - x) + t) (by omega) (by omega)
      · by_cases hdiag : n = m - x + x / 2 + 1
        · have hiter :
            (returnMap1CaseI (m := m)^[n]) (linePoint1 (m := m) xFin) =
              ((((x / 2 + 2 : ℕ) : ZMod m)), (((m - x / 2 - 1 : ℕ) : ZMod m))) := by
            have hmidEnd :
                (returnMap1CaseI (m := m)^[x / 2 - 1]) ((1 : ZMod m), (((m - x : ℕ) : ZMod m))) =
                  ((((x / 2 : ℕ) : ZMod m)), (((m - x / 2 - 1 : ℕ) : ZMod m))) := by
              simpa using iterate_returnMap1CaseI_even_middle (m := m) hmEven hx2 hxle hxeven
            rw [hdiag]
            rw [show m - x + x / 2 + 1 = 1 + (m - x + x / 2) by omega, Function.iterate_add_apply]
            have hstart :
                (returnMap1CaseI (m := m)^[m - x + x / 2]) (linePoint1 (m := m) xFin) =
                  ((((x / 2 : ℕ) : ZMod m)), (((m - x / 2 - 1 : ℕ) : ZMod m))) := by
              rw [show m - x + x / 2 = (x / 2 - 1) + (m - x + 1) by omega, Function.iterate_add_apply]
              have hstart0 :
                  (returnMap1CaseI (m := m)^[m - x + 1]) (linePoint1 (m := m) xFin) =
                    ((1 : ZMod m), (((m - x : ℕ) : ZMod m))) := by
                rw [show m - x + 1 = 1 + (m - x) by omega, Function.iterate_add_apply]
                rw [show (returnMap1CaseI (m := m)^[m - x]) (linePoint1 (m := m) xFin) =
                  ((0 : ZMod m), (((m - x : ℕ) : ZMod m))) by
                    simpa [xFin] using iterate_returnMap1CaseI_even_prefix (m := m) hmEven hx2 hxle hxeven]
                simpa [Function.iterate_one] using returnMap1CaseI_even_vertical (m := m) hx2 hxle
              rw [hstart0]
              exact hmidEnd
            rw [hstart]
            simpa [Function.iterate_one] using returnMap1CaseI_even_diag (m := m) hx2 hxle hxeven
          apply not_mem_range_linePoint1_of_snd_ne_zero
          rw [hiter]
          exact natCast_ne_zero_of_pos_lt (m := m) (n := m - x / 2 - 1) (by omega) (by omega)
        · let t : ℕ := n - (m - x + x / 2 + 1)
          have hsplit : m + 2 = (m - x + x / 2 + 1) + (x / 2 + 1) := by
            rcases hxeven with ⟨r, hr⟩
            rw [hr]
            omega
          have ht : t ≤ x / 2 := by
            dsimp [t]
            rw [hsplit] at hnm
            omega
          have hnEq : n = m - x + x / 2 + 1 + t := by
            dsimp [t]
            omega
          have hiter :
              (returnMap1CaseI (m := m)^[n]) (linePoint1 (m := m) xFin) =
                ((((x / 2 + 2 + t : ℕ) : ZMod m)), ((((m - x / 2 - 1) + t : ℕ) : ZMod m))) := by
            rw [hnEq]
            rw [show m - x + x / 2 + 1 + t = t + (m - x + x / 2 + 1) by omega, Function.iterate_add_apply]
            have hstart :
                (returnMap1CaseI (m := m)^[m - x + x / 2 + 1]) (linePoint1 (m := m) xFin) =
                  ((((x / 2 + 2 : ℕ) : ZMod m)), (((m - x / 2 - 1 : ℕ) : ZMod m))) := by
              have hmidEnd :
                  (returnMap1CaseI (m := m)^[x / 2 - 1]) ((1 : ZMod m), (((m - x : ℕ) : ZMod m))) =
                    ((((x / 2 : ℕ) : ZMod m)), (((m - x / 2 - 1 : ℕ) : ZMod m))) := by
                simpa using iterate_returnMap1CaseI_even_middle (m := m) hmEven hx2 hxle hxeven
              rw [show m - x + x / 2 + 1 = 1 + (m - x + x / 2) by omega, Function.iterate_add_apply]
              rw [show m - x + x / 2 = (x / 2 - 1) + (m - x + 1) by omega, Function.iterate_add_apply]
              have hstart0 :
                  (returnMap1CaseI (m := m)^[m - x + 1]) (linePoint1 (m := m) xFin) =
                    ((1 : ZMod m), (((m - x : ℕ) : ZMod m))) := by
                rw [show m - x + 1 = 1 + (m - x) by omega, Function.iterate_add_apply]
                rw [show (returnMap1CaseI (m := m)^[m - x]) (linePoint1 (m := m) xFin) =
                  ((0 : ZMod m), (((m - x : ℕ) : ZMod m))) by
                    simpa [xFin] using iterate_returnMap1CaseI_even_prefix (m := m) hmEven hx2 hxle hxeven]
                simpa [Function.iterate_one] using returnMap1CaseI_even_vertical (m := m) hx2 hxle
              rw [hstart0]
              rw [hmidEnd]
              simpa [Function.iterate_one] using returnMap1CaseI_even_diag (m := m) hx2 hxle hxeven
            rw [hstart]
            exact iterate_returnMap1CaseI_even_suffix_partial (m := m)
              (x := x) (t := t) hx2 hxle hxeven ht
          have hy :
              ((((m - x / 2 - 1) + t : ℕ) : ZMod m)) ≠ 0 := by
            exact natCast_ne_zero_of_pos_lt (m := m) (n := (m - x / 2 - 1) + t) (by omega) (by omega)
          apply not_mem_range_linePoint1_of_snd_ne_zero
          rw [hiter]
          exact hy

theorem hfirst_line_zero [Fact (5 < m)] :
    ∀ n, 0 < n →
      n < TorusD3Even.rho1CaseI (m := m) (0 : Fin m) →
        (returnMap1CaseI (m := m)^[n]) (linePoint1 (m := m) (0 : Fin m)) ∉
          Set.range (linePoint1 (m := m)) := by
  intro n hn0 hnlt
  have hrho : TorusD3Even.rho1CaseI (m := m) (0 : Fin m) = 1 := by
    exact rho1CaseI_zero (m := m)
  omega

theorem hfirst_line_m_sub_two [Fact (5 < m)] :
    ∀ n, 0 < n →
      n < TorusD3Even.rho1CaseI (m := m)
        (⟨m - 2, by
          have hm5 : 5 < m := Fact.out
          omega⟩ : Fin m) →
        (returnMap1CaseI (m := m)^[n])
            (linePoint1 (m := m)
              (⟨m - 2, by
                have hm5 : 5 < m := Fact.out
                omega⟩ : Fin m)) ∉
          Set.range (linePoint1 (m := m)) := by
  let x : Fin m := ⟨m - 2, by
    have hm5 : 5 < m := Fact.out
    omega⟩
  intro n hn0 hnlt
  have hrho : TorusD3Even.rho1CaseI (m := m) x = 1 := by
    simpa [x] using rho1CaseI_m_sub_two (m := m)
  have hnlt' : n < 1 := by
    simpa [x, hrho] using hnlt
  omega

theorem iterate_returnMap1CaseI_from_one_one_partial [Fact (5 < m)] (hmEven : Even m)
    {t : ℕ} (ht : t ≤ m - 2) :
    ((returnMap1CaseI (m := m)^[t]) ((1 : ZMod m), (1 : ZMod m))) =
      ((((1 + t : ℕ) : ZMod m)), (((1 + t : ℕ) : ZMod m))) := by
  calc
    ((returnMap1CaseI (m := m)^[t]) ((1 : ZMod m), (1 : ZMod m)))
        = ((bulkMap1CaseI (m := m)^[t]) ((1 : ZMod m), (1 : ZMod m))) := by
            refine iterate_eq_iterate_of_eq_on_prefix
              (F := returnMap1CaseI (m := m)) (G := bulkMap1CaseI (m := m))
              (z := ((1 : ZMod m), (1 : ZMod m))) t ?_
            intro s hs
            rw [iterate_bulkMap1CaseI (m := m) s ((1 : ZMod m), (1 : ZMod m))]
            have hi_pos : 0 < 1 + s := by omega
            have hi_lt : 1 + s < m := by omega
            have hi_ne_zero : (((1 + s : ℕ) : ZMod m)) ≠ 0 := by
              exact natCast_ne_zero_of_pos_lt (m := m) (n := 1 + s) hi_pos hi_lt
            have hk_ne_neg_one : (((1 + s : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
              exact natCast_ne_neg_one_of_lt (m := m) (n := 1 + s) (by omega)
            have h00 : ¬ ((((1 + s : ℕ) : ZMod m)) = 0 ∧ (((1 + s : ℕ) : ZMod m)) = 0) := by
              intro h
              exact hi_ne_zero h.1
            have hdiag :
                ¬ ((((1 + s : ℕ) : ZMod m)) + (((1 + s : ℕ) : ZMod m)) = (-1 : ZMod m) ∧
                    (((1 + s : ℕ) : ZMod m)) ≠ 0 ∧
                    (((1 + s : ℕ) : ZMod m)) ≠ (-2 : ZMod m) ∧
                    (((1 + s : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              have hsumEven : Even (2 + 2 * s) := by
                refine ⟨1 + s, by ring⟩
              have hsum_ne : (((2 + 2 * s : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
                exact natCast_ne_neg_one_of_even (m := m) hmEven hsumEven
              apply hsum_ne
              have hsumEq :
                  ((((1 + s : ℕ) : ZMod m)) + (((1 + s : ℕ) : ZMod m))) =
                    (((2 + 2 * s : ℕ) : ZMod m)) := by
                have hsumEq' :
                    (((2 + 2 * s : ℕ) : ZMod m)) =
                      ((((1 + s : ℕ) : ZMod m)) + (((1 + s : ℕ) : ZMod m))) := by
                  calc
                    (((2 + 2 * s : ℕ) : ZMod m)) = (2 : ZMod m) + ((2 : ZMod m) * s) := by
                      rw [Nat.cast_add, Nat.cast_mul]
                      norm_num
                    _ = (1 : ZMod m) + s + ((1 : ZMod m) + s) := by
                      ring
                    _ = ((((1 + s : ℕ) : ZMod m)) + (((1 + s : ℕ) : ZMod m))) := by
                      simp [Nat.cast_add, add_assoc, add_left_comm, add_comm]
                exact hsumEq'.symm
              exact hsumEq.symm.trans h.1
            have hneg1 :
                ¬ ((((1 + s : ℕ) : ZMod m)) = (-1 : ZMod m) ∧ (((1 + s : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              exact hk_ne_neg_one h.2
            have hneg2 :
                ¬ ((((1 + s : ℕ) : ZMod m)) = (-2 : ZMod m) ∧ (((1 + s : ℕ) : ZMod m)) = 0) := by
              intro h
              exact hi_ne_zero h.2
            have hi0 :
                ¬ ((((1 + s : ℕ) : ZMod m)) = 0 ∧
                    (((1 + s : ℕ) : ZMod m)) ≠ 0 ∧
                    (((1 + s : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              exact hi_ne_zero h.1
            have h1neg1 :
                ¬ ((((1 + s : ℕ) : ZMod m)) = (1 : ZMod m) ∧ (((1 + s : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              exact hk_ne_neg_one h.2
            have hneg2one :
                ¬ ((((1 + s : ℕ) : ZMod m)) = (-2 : ZMod m) ∧ (((1 + s : ℕ) : ZMod m)) = (1 : ZMod m)) := by
              intro h
              have hs0 : s = 0 := by
                have hmod := (ZMod.natCast_eq_natCast_iff' (1 + s) 1 m).1 (by simpa using h.2)
                rw [Nat.mod_eq_of_lt hi_lt, Nat.mod_eq_of_lt (by
                  have hm5 : 5 < m := Fact.out
                  omega)] at hmod
                omega
              subst hs0
              exact natCast_ne_neg_two_of_lt (m := m) (n := 1) (by
                have hm5 : 5 < m := Fact.out
                omega) h.1
            simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
              returnMap1CaseI_eq_bulk_of_not_special (m := m)
                (i := (((1 + s : ℕ) : ZMod m))) (k := (((1 + s : ℕ) : ZMod m)))
                h00 hdiag hneg1 hneg2 hi0 h1neg1 hneg2one
    _ = ((((1 + t : ℕ) : ZMod m)), (((1 + t : ℕ) : ZMod m))) := by
          rw [iterate_bulkMap1CaseI (m := m) t ((1 : ZMod m), (1 : ZMod m))]
          simp [Nat.cast_add, add_assoc, add_left_comm, add_comm]

theorem hfirst_line_m_sub_one [Fact (5 < m)] (hmEven : Even m) {x : Fin m}
    (hx : x.1 = m - 1) :
    ∀ n, 0 < n →
      n < TorusD3Even.rho1CaseI (m := m) x →
        (returnMap1CaseI (m := m)^[n]) (linePoint1 (m := m) x) ∉ Set.range (linePoint1 (m := m)) := by
  intro n hn0 hnlt
  have hm0 : 0 < m := by
    have hm5 : 5 < m := Fact.out
    omega
  letI : Fact (0 < m) := ⟨hm0⟩
  have hm5 : 5 < m := Fact.out
  have hm1ne0 : m - 1 ≠ 0 := by omega
  have hm1nem2 : m - 1 ≠ m - 2 := by omega
  have hrho : TorusD3Even.rho1CaseI (m := m) x = m + 3 := by
    simp [TorusD3Even.rho1CaseI, hx, hm1ne0, hm1nem2]
  have hnm : n < m + 3 := by rwa [hrho] at hnlt
  let x0 : Fin m := ⟨m - 1, by omega⟩
  have hx' : x = x0 := Fin.ext hx
  by_cases h1 : n = 1
  · have hiter :
        (returnMap1CaseI (m := m)^[n]) (linePoint1 (m := m) x) = ((0 : ZMod m), (1 : ZMod m)) := by
      rw [h1]
      simpa [hx', Function.iterate_one] using returnMap1CaseI_line_m_sub_one_start (m := m)
    apply not_mem_range_linePoint1_of_snd_ne_zero
    rw [hiter]
    exact one_ne_zero (m := m)
  · by_cases hmid : n ≤ m
    · let t : ℕ := n - 2
      have ht : t ≤ m - 2 := by
        dsimp [t]
        omega
      have hnEq : n = t + 2 := by
        dsimp [t]
        omega
      have hstepTwo :
          (returnMap1CaseI (m := m)^[2]) (linePoint1 (m := m) x) = ((1 : ZMod m), (1 : ZMod m)) := by
        rw [show (2 : ℕ) = 1 + 1 by norm_num, Function.iterate_add_apply]
        rw [show (returnMap1CaseI (m := m)^[1]) (linePoint1 (m := m) x) = ((0 : ZMod m), (1 : ZMod m)) by
          simpa [hx', Function.iterate_one] using returnMap1CaseI_line_m_sub_one_start (m := m)]
        simpa [Function.iterate_one] using returnMap1CaseI_zero_one (m := m)
      have hiter :
          (returnMap1CaseI (m := m)^[n]) (linePoint1 (m := m) x) =
            ((((1 + t : ℕ) : ZMod m)), (((1 + t : ℕ) : ZMod m))) := by
        rw [hnEq, Function.iterate_add_apply]
        rw [hstepTwo]
        exact iterate_returnMap1CaseI_from_one_one_partial (m := m) hmEven ht
      apply not_mem_range_linePoint1_of_snd_ne_zero
      rw [hiter]
      exact natCast_ne_zero_of_pos_lt (m := m) (n := 1 + t) (by omega) (by omega)
    · have hstepTwo :
          (returnMap1CaseI (m := m)^[2]) (linePoint1 (m := m) x) = ((1 : ZMod m), (1 : ZMod m)) := by
        rw [show (2 : ℕ) = 1 + 1 by norm_num, Function.iterate_add_apply]
        rw [show (returnMap1CaseI (m := m)^[1]) (linePoint1 (m := m) x) = ((0 : ZMod m), (1 : ZMod m)) by
          simpa [hx', Function.iterate_one] using returnMap1CaseI_line_m_sub_one_start (m := m)]
        simpa [Function.iterate_one] using returnMap1CaseI_zero_one (m := m)
      have hstepM :
          (returnMap1CaseI (m := m)^[m]) (linePoint1 (m := m) x) = ((-1 : ZMod m), (-1 : ZMod m)) := by
        calc
          (returnMap1CaseI (m := m)^[m]) (linePoint1 (m := m) x)
              = (returnMap1CaseI (m := m)^[m - 2 + 2]) (linePoint1 (m := m) x) := by
                  congr 1
                  omega
          _ = (returnMap1CaseI (m := m)^[m - 2])
                ((returnMap1CaseI (m := m)^[2]) (linePoint1 (m := m) x)) := by
                  simpa [Nat.add_comm] using
                    Function.iterate_add_apply (returnMap1CaseI (m := m)) (m - 2) 2
                      (linePoint1 (m := m) x)
          _ = (returnMap1CaseI (m := m)^[m - 2]) ((1 : ZMod m), (1 : ZMod m)) := by
                rw [hstepTwo]
          _ = ((((1 + (m - 2) : ℕ) : ZMod m)), (((1 + (m - 2) : ℕ) : ZMod m))) := by
                simpa using iterate_returnMap1CaseI_from_one_one_partial (m := m) hmEven
                  (t := m - 2) le_rfl
          _ = ((-1 : ZMod m), (-1 : ZMod m)) := by
                have hm1 : (((m - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) := by
                  exact cast_sub_one_eq_neg_one (m := m) (by omega)
                have hsum : 1 + (m - 2) = m - 1 := by omega
                simp [hsum, hm1]
      by_cases hm1 : n = m + 1
      · have hiter :
            (returnMap1CaseI (m := m)^[n]) (linePoint1 (m := m) x) = ((1 : ZMod m), (-1 : ZMod m)) := by
          rw [hm1]
          rw [show m + 1 = 1 + m by omega, Function.iterate_add_apply]
          rw [hstepM]
          simpa [Function.iterate_one] using returnMap1CaseI_neg_one_neg_one (m := m)
        apply not_mem_range_linePoint1_of_snd_ne_zero
        rw [hiter]
        exact neg_ne_zero.mpr (one_ne_zero (m := m))
      · have hm2 : n = m + 2 := by
          omega
        have hstepM1 :
            (returnMap1CaseI (m := m)^[m + 1]) (linePoint1 (m := m) x) = ((1 : ZMod m), (-1 : ZMod m)) := by
          rw [show m + 1 = 1 + m by omega, Function.iterate_add_apply]
          rw [hstepM]
          simpa [Function.iterate_one] using returnMap1CaseI_neg_one_neg_one (m := m)
        have hiter :
            (returnMap1CaseI (m := m)^[n]) (linePoint1 (m := m) x) = ((2 : ZMod m), (-1 : ZMod m)) := by
          rw [hm2]
          rw [show m + 2 = 1 + (m + 1) by omega, Function.iterate_add_apply]
          rw [hstepM1]
          simpa [Function.iterate_one] using returnMap1CaseI_one_neg_one (m := m)
        apply not_mem_range_linePoint1_of_snd_ne_zero
        rw [hiter]
        exact neg_ne_zero.mpr (one_ne_zero (m := m))

theorem iterate_returnMap1CaseI_m_sub_three_middle_partial [Fact (5 < m)] (hmEven : Even m)
    {t : ℕ} (ht : t ≤ m / 2 - 2) :
    ((returnMap1CaseI (m := m)^[t]) ((1 : ZMod m), (2 : ZMod m))) =
      ((((1 + t : ℕ) : ZMod m)), (((2 + t : ℕ) : ZMod m))) := by
  calc
    ((returnMap1CaseI (m := m)^[t]) ((1 : ZMod m), (2 : ZMod m)))
        = ((bulkMap1CaseI (m := m)^[t]) ((1 : ZMod m), (2 : ZMod m))) := by
            refine iterate_eq_iterate_of_eq_on_prefix
              (F := returnMap1CaseI (m := m)) (G := bulkMap1CaseI (m := m))
              (z := ((1 : ZMod m), (2 : ZMod m))) t ?_
            intro s hs
            rw [iterate_bulkMap1CaseI (m := m) s ((1 : ZMod m), (2 : ZMod m))]
            have hi_pos : 0 < 1 + s := by omega
            have hi_lt : 1 + s < m := by
              rcases hmEven with ⟨q, hq⟩
              omega
            have hk_pos : 0 < 2 + s := by omega
            have hk_lt : 2 + s < m := by
              rcases hmEven with ⟨q, hq⟩
              omega
            have hi_ne_zero : (((1 + s : ℕ) : ZMod m)) ≠ 0 := by
              exact natCast_ne_zero_of_pos_lt (m := m) (n := 1 + s) hi_pos hi_lt
            have hk_ne_zero : (((2 + s : ℕ) : ZMod m)) ≠ 0 := by
              exact natCast_ne_zero_of_pos_lt (m := m) (n := 2 + s) hk_pos hk_lt
            have hk_ne_neg_one : (((2 + s : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
              exact natCast_ne_neg_one_of_lt (m := m) (n := 2 + s) (by
                rcases hmEven with ⟨q, hq⟩
                omega)
            have hk_ne_one : (((2 + s : ℕ) : ZMod m)) ≠ 1 := by
              exact natCast_ne_one_of_two_le_lt (m := m) (n := 2 + s) (by omega) hk_lt
            have h00 : ¬ ((((1 + s : ℕ) : ZMod m)) = 0 ∧ (((2 + s : ℕ) : ZMod m)) = 0) := by
              intro h
              exact hi_ne_zero h.1
            have hdiag :
                ¬ ((((1 + s : ℕ) : ZMod m)) + (((2 + s : ℕ) : ZMod m)) = (-1 : ZMod m) ∧
                    (((1 + s : ℕ) : ZMod m)) ≠ 0 ∧
                    (((1 + s : ℕ) : ZMod m)) ≠ (-2 : ZMod m) ∧
                    (((1 + s : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              have hsum_ne : (((3 + 2 * s : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
                rcases hmEven with ⟨q, hq⟩
                exact natCast_ne_neg_one_of_lt (m := m) (n := 3 + 2 * s) (by
                  omega)
              apply hsum_ne
              have hsumEq :
                  ((((1 + s : ℕ) : ZMod m)) + (((2 + s : ℕ) : ZMod m))) =
                    (((3 + 2 * s : ℕ) : ZMod m)) := by
                have hsumEq' :
                    (((3 + 2 * s : ℕ) : ZMod m)) =
                      ((((1 + s : ℕ) : ZMod m)) + (((2 + s : ℕ) : ZMod m))) := by
                  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_add, Nat.cast_add]
                  ring
                exact hsumEq'.symm
              exact hsumEq.symm.trans h.1
            have hneg1 :
                ¬ ((((1 + s : ℕ) : ZMod m)) = (-1 : ZMod m) ∧ (((2 + s : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              exact hk_ne_neg_one h.2
            have hneg2 :
                ¬ ((((1 + s : ℕ) : ZMod m)) = (-2 : ZMod m) ∧ (((2 + s : ℕ) : ZMod m)) = 0) := by
              intro h
              exact hk_ne_zero h.2
            have hi0 :
                ¬ ((((1 + s : ℕ) : ZMod m)) = 0 ∧
                    (((2 + s : ℕ) : ZMod m)) ≠ 0 ∧
                    (((2 + s : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              exact hi_ne_zero h.1
            have h1neg1 :
                ¬ ((((1 + s : ℕ) : ZMod m)) = (1 : ZMod m) ∧ (((2 + s : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              exact hk_ne_neg_one h.2
            have hneg2one :
                ¬ ((((1 + s : ℕ) : ZMod m)) = (-2 : ZMod m) ∧ (((2 + s : ℕ) : ZMod m)) = (1 : ZMod m)) := by
              intro h
              exact hk_ne_one h.2
            simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
              returnMap1CaseI_eq_bulk_of_not_special (m := m)
                (i := (((1 + s : ℕ) : ZMod m))) (k := (((2 + s : ℕ) : ZMod m)))
                h00 hdiag hneg1 hneg2 hi0 h1neg1 hneg2one
    _ = ((((1 + t : ℕ) : ZMod m)), (((2 + t : ℕ) : ZMod m))) := by
          rw [iterate_bulkMap1CaseI (m := m) t ((1 : ZMod m), (2 : ZMod m))]
          simp [Nat.cast_add, add_assoc, add_left_comm, add_comm]

theorem iterate_returnMap1CaseI_m_sub_three_tail_partial [Fact (5 < m)] (hmEven : Even m)
    {t : ℕ} (ht : t ≤ m / 2 - 1) :
    ((returnMap1CaseI (m := m)^[t])
      ((((m / 2 + 1 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m)))) =
      ((((m / 2 + 1 + t : ℕ) : ZMod m)), (((m / 2 + t : ℕ) : ZMod m))) := by
  calc
    ((returnMap1CaseI (m := m)^[t])
      ((((m / 2 + 1 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m))))
        = ((bulkMap1CaseI (m := m)^[t])
          ((((m / 2 + 1 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m)))) := by
            refine iterate_eq_iterate_of_eq_on_prefix
              (F := returnMap1CaseI (m := m)) (G := bulkMap1CaseI (m := m))
              (z := ((((m / 2 + 1 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m)))) t ?_
            intro s hs
            rw [iterate_bulkMap1CaseI (m := m) s
              ((((m / 2 + 1 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m)))]
            have hi_pos : 0 < m / 2 + 1 + s := by
              rcases hmEven with ⟨q, hq⟩
              rw [hq]
              omega
            have hi_lt : m / 2 + 1 + s < m := by
              rcases hmEven with ⟨q, hq⟩
              omega
            have hk_pos : 0 < m / 2 + s := by
              rcases hmEven with ⟨q, hq⟩
              rw [hq]
              omega
            have hk_lt : m / 2 + s < m := by
              rcases hmEven with ⟨q, hq⟩
              omega
            have hi_ne_zero : (((m / 2 + 1 + s : ℕ) : ZMod m)) ≠ 0 := by
              exact natCast_ne_zero_of_pos_lt (m := m) (n := m / 2 + 1 + s) hi_pos hi_lt
            have hk_ne_zero : (((m / 2 + s : ℕ) : ZMod m)) ≠ 0 := by
              exact natCast_ne_zero_of_pos_lt (m := m) (n := m / 2 + s) hk_pos hk_lt
            have hk_ne_neg_one : (((m / 2 + s : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
              exact natCast_ne_neg_one_of_lt (m := m) (n := m / 2 + s) (by
                rcases hmEven with ⟨q, hq⟩
                omega)
            have hk_ne_one : (((m / 2 + s : ℕ) : ZMod m)) ≠ 1 := by
              exact natCast_ne_one_of_two_le_lt (m := m) (n := m / 2 + s) (by
                rcases hmEven with ⟨q, hq⟩
                rw [hq]
                omega) hk_lt
            have h00 :
                ¬ ((((m / 2 + 1 + s : ℕ) : ZMod m)) = 0 ∧
                    (((m / 2 + s : ℕ) : ZMod m)) = 0) := by
              intro h
              exact hi_ne_zero h.1
            have hdiag :
                ¬ ((((m / 2 + 1 + s : ℕ) : ZMod m)) + (((m / 2 + s : ℕ) : ZMod m)) = (-1 : ZMod m) ∧
                    (((m / 2 + 1 + s : ℕ) : ZMod m)) ≠ 0 ∧
                    (((m / 2 + 1 + s : ℕ) : ZMod m)) ≠ (-2 : ZMod m) ∧
                    (((m / 2 + 1 + s : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              have hsum_ne : (((1 + 2 * s : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
                exact natCast_ne_neg_one_of_lt (m := m) (n := 1 + 2 * s) (by
                  rcases hmEven with ⟨q, hq⟩
                  omega)
              apply hsum_ne
              have hsumEq :
                  ((((m / 2 + 1 + s : ℕ) : ZMod m)) + (((m / 2 + s : ℕ) : ZMod m))) =
                    (((m + (1 + 2 * s) : ℕ) : ZMod m)) := by
                have hnat : m / 2 + 1 + s + (m / 2 + s) = m + (1 + 2 * s) := by
                  rcases hmEven with ⟨q, hq⟩
                  rw [hq]
                  omega
                simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
                  congrArg (fun n : ℕ => ((n : ℕ) : ZMod m)) hnat
              have hmcast : (((m + (1 + 2 * s) : ℕ) : ZMod m)) = (((1 + 2 * s : ℕ) : ZMod m)) := by
                rw [Nat.cast_add, ZMod.natCast_self, zero_add]
              exact (hsumEq.trans hmcast).symm.trans h.1
            have hneg1 :
                ¬ ((((m / 2 + 1 + s : ℕ) : ZMod m)) = (-1 : ZMod m) ∧
                    (((m / 2 + s : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              exact hk_ne_neg_one h.2
            have hneg2 :
                ¬ ((((m / 2 + 1 + s : ℕ) : ZMod m)) = (-2 : ZMod m) ∧
                    (((m / 2 + s : ℕ) : ZMod m)) = 0) := by
              intro h
              exact hk_ne_zero h.2
            have hi0 :
                ¬ ((((m / 2 + 1 + s : ℕ) : ZMod m)) = 0 ∧
                    (((m / 2 + s : ℕ) : ZMod m)) ≠ 0 ∧
                    (((m / 2 + s : ℕ) : ZMod m)) ≠ (-1 : ZMod m)) := by
              intro h
              exact hi_ne_zero h.1
            have h1neg1 :
                ¬ ((((m / 2 + 1 + s : ℕ) : ZMod m)) = (1 : ZMod m) ∧
                    (((m / 2 + s : ℕ) : ZMod m)) = (-1 : ZMod m)) := by
              intro h
              exact hk_ne_neg_one h.2
            have hneg2one :
                ¬ ((((m / 2 + 1 + s : ℕ) : ZMod m)) = (-2 : ZMod m) ∧
                    (((m / 2 + s : ℕ) : ZMod m)) = (1 : ZMod m)) := by
              intro h
              exact hk_ne_one h.2
            simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
              returnMap1CaseI_eq_bulk_of_not_special (m := m)
                (i := (((m / 2 + 1 + s : ℕ) : ZMod m))) (k := (((m / 2 + s : ℕ) : ZMod m)))
                h00 hdiag hneg1 hneg2 hi0 h1neg1 hneg2one
    _ = ((((m / 2 + 1 + t : ℕ) : ZMod m)), (((m / 2 + t : ℕ) : ZMod m))) := by
          rw [iterate_bulkMap1CaseI (m := m) t
            ((((m / 2 + 1 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m)))]
          simp [Nat.cast_add, add_assoc, add_left_comm, add_comm]

theorem hfirst_line_m_sub_three [Fact (5 < m)] (hmEven : Even m) {x : Fin m}
    (hx : x.1 = m - 3) :
    ∀ n, 0 < n →
      n < TorusD3Even.rho1CaseI (m := m) x →
        (returnMap1CaseI (m := m)^[n]) (linePoint1 (m := m) x) ∉ Set.range (linePoint1 (m := m)) := by
  intro n hn0 hnlt
  have hm0 : 0 < m := by
    have hm5 : 5 < m := Fact.out
    omega
  letI : Fact (0 < m) := ⟨hm0⟩
  have hm5 : 5 < m := Fact.out
  have hm3ne0 : m - 3 ≠ 0 := by omega
  have hm3nem2 : m - 3 ≠ m - 2 := by omega
  have hrho : TorusD3Even.rho1CaseI (m := m) x = m + 3 := by
    simp [TorusD3Even.rho1CaseI, hx, hm3ne0, hm3nem2]
  have hnm : n < m + 3 := by rwa [hrho] at hnlt
  let x0 : Fin m := ⟨m - 3, by omega⟩
  have hx' : x = x0 := Fin.ext hx
  by_cases h1 : n = 1
  · have hiter :
        (returnMap1CaseI (m := m)^[n]) (linePoint1 (m := m) x) =
          ((((m - 2 : ℕ) : ZMod m)), (1 : ZMod m)) := by
      rw [h1]
      simpa [hx', Function.iterate_one] using returnMap1CaseI_line_m_sub_three_start (m := m)
    apply not_mem_range_linePoint1_of_snd_ne_zero
    rw [hiter]
    exact one_ne_zero (m := m)
  · by_cases h2 : n = 2
    · have hiter :
          (returnMap1CaseI (m := m)^[n]) (linePoint1 (m := m) x) = ((-1 : ZMod m), (1 : ZMod m)) := by
        rw [h2]
        rw [show (2 : ℕ) = 1 + 1 by norm_num, Function.iterate_add_apply]
        rw [show (returnMap1CaseI (m := m)^[1]) (linePoint1 (m := m) x) =
          ((((m - 2 : ℕ) : ZMod m)), (1 : ZMod m)) by
            simpa [hx', Function.iterate_one] using returnMap1CaseI_line_m_sub_three_start (m := m)]
        have hm2 : 2 ≤ m := by omega
        simpa [Function.iterate_one, cast_sub_two_eq_neg_two (m := m) hm2] using
          returnMap1CaseI_neg_two_one (m := m)
      apply not_mem_range_linePoint1_of_snd_ne_zero
      rw [hiter]
      exact one_ne_zero (m := m)
    · by_cases h3 : n = 3
      · have hiter :
          (returnMap1CaseI (m := m)^[n]) (linePoint1 (m := m) x) = ((0 : ZMod m), (2 : ZMod m)) := by
          simpa [h3] using iterate_three_returnMap1CaseI_line_m_sub_three (m := m) hx
        apply not_mem_range_linePoint1_of_snd_ne_zero
        rw [hiter]
        exact two_ne_zero (m := m)
      · have hstepFour :
            (returnMap1CaseI (m := m)^[4]) (linePoint1 (m := m) x) = ((1 : ZMod m), (2 : ZMod m)) := by
          rw [show (4 : ℕ) = 1 + 3 by norm_num, Function.iterate_add_apply]
          rw [show (returnMap1CaseI (m := m)^[3]) (linePoint1 (m := m) x) = ((0 : ZMod m), (2 : ZMod m)) by
            simpa using iterate_three_returnMap1CaseI_line_m_sub_three (m := m) hx]
          simpa [Function.iterate_one] using returnMap1CaseI_zero_two (m := m)
        by_cases hmid : n ≤ m / 2 + 2
        · let t : ℕ := n - 4
          have ht : t ≤ m / 2 - 2 := by
            dsimp [t]
            omega
          have hnEq : n = 4 + t := by
            dsimp [t]
            omega
          have hiter :
              (returnMap1CaseI (m := m)^[n]) (linePoint1 (m := m) x) =
                ((((1 + t : ℕ) : ZMod m)), (((2 + t : ℕ) : ZMod m))) := by
            rw [hnEq]
            rw [show 4 + t = t + 4 by omega, Function.iterate_add_apply]
            rw [hstepFour]
            exact iterate_returnMap1CaseI_m_sub_three_middle_partial (m := m) hmEven ht
          apply not_mem_range_linePoint1_of_snd_ne_zero
          rw [hiter]
          exact natCast_ne_zero_of_pos_lt (m := m) (n := 2 + t) (by omega) (by omega)
        · by_cases hdiag : n = m / 2 + 3
          · have hiter :
              (returnMap1CaseI (m := m)^[n]) (linePoint1 (m := m) x) =
                ((((m / 2 + 1 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m))) := by
              rw [hdiag]
              rw [show m / 2 + 3 = 1 + (m / 2 + 2) by omega, Function.iterate_add_apply]
              have hmidEnd :
                  (returnMap1CaseI (m := m)^[m / 2 + 2]) (linePoint1 (m := m) x) =
                    ((((m / 2 - 1 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m))) := by
                rw [show m / 2 + 2 = (m / 2 - 2) + 4 by omega, Function.iterate_add_apply]
                rw [hstepFour]
                have hmid' :=
                  iterate_returnMap1CaseI_m_sub_three_middle_partial (m := m) hmEven
                    (t := m / 2 - 2) le_rfl
                have hnat1 : 1 + (m / 2 - 2) = m / 2 - 1 := by omega
                have hnat2 : 2 + (m / 2 - 2) = m / 2 := by omega
                simpa [hnat1, hnat2] using hmid'
              rw [hmidEnd]
              simpa [Function.iterate_one] using returnMap1CaseI_m_sub_three_diag (m := m) hmEven
            apply not_mem_range_linePoint1_of_snd_ne_zero
            rw [hiter]
            exact natCast_ne_zero_of_pos_lt (m := m) (n := m / 2) (by omega) (by omega)
          · let t : ℕ := n - (m / 2 + 3)
            have hsplit : m + 3 = m / 2 + 3 + (m / 2) := by
              rcases hmEven with ⟨q, hq⟩
              rw [hq]
              omega
            have ht : t ≤ m / 2 - 1 := by
              dsimp [t]
              rw [hsplit] at hnm
              omega
            have hnEq : n = m / 2 + 3 + t := by
              dsimp [t]
              omega
            have hiter :
                (returnMap1CaseI (m := m)^[n]) (linePoint1 (m := m) x) =
                  ((((m / 2 + 1 + t : ℕ) : ZMod m)), (((m / 2 + t : ℕ) : ZMod m))) := by
              rw [hnEq]
              rw [show m / 2 + 3 + t = t + (m / 2 + 3) by omega, Function.iterate_add_apply]
              have hstart :
                  (returnMap1CaseI (m := m)^[m / 2 + 3]) (linePoint1 (m := m) x) =
                    ((((m / 2 + 1 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m))) := by
                rw [show m / 2 + 3 = 1 + (m / 2 + 2) by omega, Function.iterate_add_apply]
                have hmidEnd :
                    (returnMap1CaseI (m := m)^[m / 2 + 2]) (linePoint1 (m := m) x) =
                      ((((m / 2 - 1 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m))) := by
                  rw [show m / 2 + 2 = (m / 2 - 2) + 4 by omega, Function.iterate_add_apply]
                  rw [hstepFour]
                  have hmid' :=
                    iterate_returnMap1CaseI_m_sub_three_middle_partial (m := m) hmEven
                      (t := m / 2 - 2) le_rfl
                  have hnat1 : 1 + (m / 2 - 2) = m / 2 - 1 := by omega
                  have hnat2 : 2 + (m / 2 - 2) = m / 2 := by omega
                  simpa [hnat1, hnat2] using hmid'
                rw [hmidEnd]
                simpa [Function.iterate_one] using returnMap1CaseI_m_sub_three_diag (m := m) hmEven
              rw [hstart]
              exact iterate_returnMap1CaseI_m_sub_three_tail_partial (m := m) hmEven ht
            apply not_mem_range_linePoint1_of_snd_ne_zero
            rw [hiter]
            have hy : (((m / 2 + t : ℕ) : ZMod m)) ≠ 0 := by
              exact natCast_ne_zero_of_pos_lt (m := m) (n := m / 2 + t) (by omega) (by omega)
            exact hy

theorem hfirst_line_caseI [Fact (5 < m)] (hmEven : Even m) (x : Fin m) :
    ∀ n, 0 < n →
      n < TorusD3Even.rho1CaseI (m := m) x →
        (returnMap1CaseI (m := m)^[n]) (linePoint1 (m := m) x) ∉ Set.range (linePoint1 (m := m)) := by
  by_cases hx0 : x.1 = 0
  · have hx' : x = 0 := Fin.ext hx0
    simpa [hx'] using hfirst_line_zero (m := m)
  by_cases hxm2 : x.1 = m - 2
  · have hm5 : 5 < m := Fact.out
    have hx' : x = ⟨m - 2, by omega⟩ := Fin.ext hxm2
    simpa [hx'] using hfirst_line_m_sub_two (m := m)
  by_cases hxm3 : x.1 = m - 3
  · exact hfirst_line_m_sub_three (m := m) hmEven hxm3
  by_cases hxm1 : x.1 = m - 1
  · exact hfirst_line_m_sub_one (m := m) hmEven hxm1
  have hx1 : 1 ≤ x.1 := by
    exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hx0)
  rcases Nat.even_or_odd x.1 with hxeven | hxodd
  · have hx2 : 2 ≤ x.1 := by
      rcases hxeven with ⟨k, hk⟩
      have hkpos : 0 < k := by
        by_contra hk0
        have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk0
        exact hx0 (by rw [hk, hkzero])
      omega
    have hxle : x.1 ≤ m - 4 := by
      omega
    simpa using hfirst_line_even_generic (m := m) hmEven (x := x.1) hx2 hxle hxeven
  · have hxle : x.1 ≤ m - 4 := by
      omega
    simpa using hfirst_line_odd_generic (m := m) hmEven (x := x.1) hx1 hxle hxodd

theorem cycleOn_returnMap1CaseI_caseI [Fact (5 < m)] (hmEven : Even m) (hcase : m % 6 ≠ 4) :
    TorusD4.CycleOn (m ^ 2) (returnMap1CaseI (m := m))
      (linePoint1 (m := m) (0 : Fin m)) := by
  have hm0 : 0 < m := by
    have hm5 : 5 < m := Fact.out
    omega
  letI : NeZero m := ⟨Nat.ne_of_gt hm0⟩
  letI : Fact (0 < m) := ⟨hm0⟩
  have hsumCard :
      TorusD3Even.blockTime
          (TorusD3Even.T1CaseI (m := m))
          (TorusD3Even.rho1CaseI (m := m))
          ⟨0, hm0⟩
          m = Fintype.card (P0Coord m) := by
    simpa [P0Coord, ZMod.card, pow_two] using hsum_caseI (m := m) hmEven hcase
  simpa [P0Coord, ZMod.card, pow_two] using
    (TorusD3Even.firstReturn_counting
      (α := P0Coord m) (β := Fin m)
      (F := returnMap1CaseI (m := m)) (embed := linePoint1 (m := m))
      (T := TorusD3Even.T1CaseI (m := m)) (rho := TorusD3Even.rho1CaseI (m := m))
      (M := m) (x0 := (0 : Fin m))
      linePoint1_injective
      (cycleOn_T1CaseI_caseI (m := m) hmEven hcase)
      (hreturn_line_caseI (m := m) hmEven)
      (hfirst_line_caseI (m := m) hmEven)
      hsumCard)

theorem cycleOn_fullMap1CaseI_caseI [Fact (5 < m)] (hmEven : Even m) (hcase : m % 6 ≠ 4) :
    TorusD4.CycleOn (m ^ 3) (fullMap1CaseI (m := m))
      (slicePoint (0 : ZMod m) (linePoint1 (m := m) (0 : Fin m))) := by
  have hm0 : 0 < m := by
    have hm5 : 5 < m := Fact.out
    omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : NeZero m := ⟨Nat.ne_of_gt hm0⟩
  exact cycleOn_full_of_cycleOn_p0 (m := m)
    (F := fullMap1CaseI (m := m)) (T := returnMap1CaseI (m := m))
    (hstep := fullMap1CaseI_snd (m := m))
    (hreturn := iterate_m_fullMap1CaseI_slicePoint_zero (m := m))
    (u := linePoint1 (m := m) (0 : Fin m))
    (cycleOn_returnMap1CaseI_caseI (m := m) hmEven hcase)

end TorusD3Odometer
