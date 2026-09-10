import TorusD3Odometer.Color0FullCaseI

namespace TorusD3Odometer

open TorusD4
open TorusD3Even

def dir0FromLayerZero (dir0 : P0Coord m → Color) (z : FullCoord m) : Color :=
  let (u, s) := z
  if s = 0 then
    dir0 u
  else if s = 1 then
    if u.1 = 0 then 1 else 2
  else if s = 2 then
    if u.1 + u.2 = (2 : ZMod m) then 2 else 0
  else
    0

def fullMapColor0 (dir0 : P0Coord m → Color) (z : FullCoord m) : FullCoord m :=
  KMap (m := m) (dir0FromLayerZero (m := m) dir0 z) z

@[simp] theorem fullMapColor0_snd (dir0 : P0Coord m → Color) (z : FullCoord m) :
    (fullMapColor0 (m := m) dir0 z).2 = z.2 + 1 := by
  simp [fullMapColor0, KMap_snd]

theorem fullMapColor0_of_s_ne_zero_one_two (dir0 : P0Coord m → Color) {u : P0Coord m} {s : ZMod m}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hs2 : s ≠ 2) :
    fullMapColor0 (m := m) dir0 (u, s) = KMap (m := m) 0 (u, s) := by
  simp [fullMapColor0, dir0FromLayerZero, hs0, hs1, hs2]

theorem iterate_fullMapColor0_from_three [Fact (4 < m)] (dir0 : P0Coord m → Color) :
    ∀ n u, n ≤ m - 3 →
      ((fullMapColor0 (m := m) dir0)^[n]) (u, (3 : ZMod m)) =
        ((KMap (m := m) 0)^[n]) (u, (3 : ZMod m))
  | 0, u, _ => by simp
  | n + 1, u, hn => by
      have hcur_lt : n + 3 < m := by
        have hm4 : 4 < m := Fact.out
        omega
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
        ((fullMapColor0 (m := m) dir0)^[n + 1]) (u, (3 : ZMod m))
            = fullMapColor0 (m := m) dir0 (((fullMapColor0 (m := m) dir0)^[n]) (u, (3 : ZMod m))) := by
                rw [Function.iterate_succ_apply']
        _ = fullMapColor0 (m := m) dir0 (((KMap (m := m) 0)^[n]) (u, (3 : ZMod m))) := by
              rw [iterate_fullMapColor0_from_three (m := m) dir0 n u hn']
        _ = fullMapColor0 (m := m) dir0 ((u.1 + n, u.2), (3 : ZMod m) + n) := by
              rw [iterate_KMap0]
        _ = KMap (m := m) 0 ((u.1 + n, u.2), (3 : ZMod m) + n) := by
              simpa using fullMapColor0_of_s_ne_zero_one_two (m := m) dir0 (u := (u.1 + n, u.2)) hs0 hs1 hs2
        _ = ((KMap (m := m) 0)^[n + 1]) (u, (3 : ZMod m)) := by
              symm
              rw [Function.iterate_succ_apply', iterate_KMap0]

theorem iterate_m_sub_three_fullMapColor0 [Fact (4 < m)] (dir0 : P0Coord m → Color) (u : P0Coord m) :
    (((fullMapColor0 (m := m) dir0)^[m - 3]) (u, (3 : ZMod m))) =
      slicePoint (0 : ZMod m) (u.1 + (((m - 3 : ℕ) : ZMod m)), u.2) := by
  have hm3 : 3 ≤ m := by
    have hm4 : 4 < m := Fact.out
    omega
  calc
    (((fullMapColor0 (m := m) dir0)^[m - 3]) (u, (3 : ZMod m)))
        = ((KMap (m := m) 0)^[m - 3]) (u, (3 : ZMod m)) := by
            rw [iterate_fullMapColor0_from_three (m := m) dir0 (m - 3) u le_rfl]
    _ = ((u.1 + (((m - 3 : ℕ) : ZMod m)), u.2), (3 : ZMod m) + (((m - 3 : ℕ) : ZMod m))) := by
          rw [iterate_KMap0]
    _ = slicePoint (0 : ZMod m) (u.1 + (((m - 3 : ℕ) : ZMod m)), u.2) := by
          ext <;> simp [slicePoint]
          rw [Nat.cast_sub hm3]
          simp

def dir0CaseIILayerZero (u : P0Coord m) : Color :=
  let i : ZMod m := u.1
  let k : ZMod m := u.2
  if (k = 0 ∧ i ≠ 0 ∧ i ≠ (1 : ZMod m) ∧ i ≠ (-2 : ZMod m) ∧ i ≠ (-1 : ZMod m)) ∨
      (i = 0 ∧ k = (-1 : ZMod m)) ∨
      (i = (-1 : ZMod m) ∧ k = (1 : ZMod m)) ∨
      (i = (1 : ZMod m) ∧ k = (-2 : ZMod m)) ∨
      (i = (-2 : ZMod m) ∧ k = (1 : ZMod m)) then
    0
  else if (i = 0 ∧ k ≠ 0 ∧ k ≠ (-1 : ZMod m)) ∨
      (i = (1 : ZMod m) ∧ k ≠ (-2 : ZMod m)) ∨
      (i = (2 : ZMod m) ∧ k = (-2 : ZMod m)) ∨
      (i = (2 : ZMod m) ∧ k = (-1 : ZMod m)) ∨
      (i = (-2 : ZMod m) ∧ k = 0) then
    2
  else
    1

def dir0CaseII (z : FullCoord m) : Color :=
  dir0FromLayerZero (m := m) (dir0CaseIILayerZero (m := m)) z

def fullMap0CaseII (z : FullCoord m) : FullCoord m :=
  fullMapColor0 (m := m) (dir0CaseIILayerZero (m := m)) z

@[simp] theorem fullMap0CaseII_snd (z : FullCoord m) :
    (fullMap0CaseII (m := m) z).2 = z.2 + 1 := by
  change (fullMapColor0 (m := m) (dir0CaseIILayerZero (m := m)) z).2 = z.2 + 1
  simp

def returnMap0CaseII (u : P0Coord m) : P0Coord m :=
  (((fullMap0CaseII (m := m)^[m]) (slicePoint (0 : ZMod m) u))).1

def returnMap0CaseIIXY (u : P0Coord m) : P0Coord m :=
  toXY (m := m) (returnMap0CaseII (m := m) (fromXY (m := m) u))

theorem iterate_m_fullMap0CaseII_slicePoint_zero [Fact (9 < m)] (u : P0Coord m) :
    ((fullMap0CaseII (m := m)^[m]) (slicePoint (0 : ZMod m) u)) =
      slicePoint (0 : ZMod m) (returnMap0CaseII (m := m) u) := by
  rcases hiter : ((fullMap0CaseII (m := m)^[m]) (slicePoint (0 : ZMod m) u)) with ⟨v, s⟩
  have hm0 : 0 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (0 < m) := ⟨hm0⟩
  have hs : s = 0 := by
    have hs0 :
        ((fullMap0CaseII (m := m)^[m]) (slicePoint (0 : ZMod m) u)).2 = 0 := by
      simpa [slicePoint] using
        (snd_iterate_add_one (m := m) (F := fullMap0CaseII (m := m))
          (hstep := fullMap0CaseII_snd (m := m)) m (slicePoint (0 : ZMod m) u))
    simpa [hiter] using hs0
  have hv : v = ((fullMap0CaseII (m := m)^[m]) (slicePoint (0 : ZMod m) u)).1 := by
    simpa using (congrArg Prod.fst hiter).symm
  simp [returnMap0CaseII, slicePoint, hs, hv]

theorem returnMap0CaseII_semiconj_xy :
    Function.Semiconj (xyEquiv (m := m)) (returnMap0CaseII (m := m)) (returnMap0CaseIIXY (m := m)) := by
  intro u
  change toXY (m := m) (returnMap0CaseII (m := m) u) =
    toXY (m := m) (returnMap0CaseII (m := m) (fromXY (m := m) (toXY (m := m) u)))
  rw [fromXY_toXY]

theorem returnMap0CaseII_semiconj_xy_symm :
    Function.Semiconj (xyEquiv (m := m)).symm (returnMap0CaseIIXY (m := m)) (returnMap0CaseII (m := m)) := by
  intro u
  change fromXY (m := m) (toXY (m := m) (returnMap0CaseII (m := m) (fromXY (m := m) u))) =
    returnMap0CaseII (m := m) (fromXY (m := m) u)
  simpa using fromXY_toXY (m := m) (returnMap0CaseII (m := m) (fromXY (m := m) u))

def rho0CaseII [Fact (9 < m)] (x : Fin m) : ℕ :=
  if _hx0 : x.1 = 0 then
    1
  else if _hxm6 : x.1 = m - 6 then
    2 * m - 4
  else if _hxm5 : x.1 = m - 5 then
    m - 1
  else if _hxm3 : x.1 = m - 3 then
    2 * m - 3
  else if _hxm2 : x.1 = m - 2 then
    2 * m - 4
  else if _hxm1 : x.1 = m - 1 then
    m - 1
  else
    m - 2

theorem rho0CaseII_zero [Fact (9 < m)] :
    rho0CaseII (m := m) (0 : Fin m) = 1 := by
  simp [rho0CaseII]

theorem rho0CaseII_eq_two_mul_sub_four_of_val_eq_m_sub_six [Fact (9 < m)] {x : Fin m}
    (hx : x.1 = m - 6) :
    rho0CaseII (m := m) x = 2 * m - 4 := by
  have hm9 : 9 < m := Fact.out
  have hm60 : m - 6 ≠ 0 := by omega
  simpa [hx] using (show rho0CaseII (m := m) x = 2 * m - 4 by
    simp [rho0CaseII, hx, hm60])

theorem rho0CaseII_eq_sub_one_of_val_eq_m_sub_five [Fact (9 < m)] {x : Fin m}
    (hx : x.1 = m - 5) :
    rho0CaseII (m := m) x = m - 1 := by
  have hm9 : 9 < m := Fact.out
  have hm50 : m - 5 ≠ 0 := by omega
  have hm56 : m - 5 ≠ m - 6 := by omega
  simpa [hx] using (show rho0CaseII (m := m) x = m - 1 by
    simp [rho0CaseII, hx, hm50, hm56])

theorem rho0CaseII_eq_two_mul_sub_three_of_val_eq_m_sub_three [Fact (9 < m)] {x : Fin m}
    (hx : x.1 = m - 3) :
    rho0CaseII (m := m) x = 2 * m - 3 := by
  have hm9 : 9 < m := Fact.out
  have hm30 : m - 3 ≠ 0 := by omega
  have hm36 : m - 3 ≠ m - 6 := by omega
  have hm35 : m - 3 ≠ m - 5 := by omega
  simpa [hx] using (show rho0CaseII (m := m) x = 2 * m - 3 by
    simp [rho0CaseII, hx, hm30, hm36, hm35])

theorem rho0CaseII_eq_two_mul_sub_four_of_val_eq_m_sub_two [Fact (9 < m)] {x : Fin m}
    (hx : x.1 = m - 2) :
    rho0CaseII (m := m) x = 2 * m - 4 := by
  have hm9 : 9 < m := Fact.out
  have hm20 : m - 2 ≠ 0 := by omega
  have hm26 : m - 2 ≠ m - 6 := by omega
  have hm25 : m - 2 ≠ m - 5 := by omega
  have hm23 : m - 2 ≠ m - 3 := by omega
  simpa [hx] using (show rho0CaseII (m := m) x = 2 * m - 4 by
    simp [rho0CaseII, hx, hm20, hm26, hm25, hm23])

theorem rho0CaseII_eq_sub_one_of_val_eq_m_sub_one [Fact (9 < m)] {x : Fin m}
    (hx : x.1 = m - 1) :
    rho0CaseII (m := m) x = m - 1 := by
  have hm9 : 9 < m := Fact.out
  have hm10 : m - 1 ≠ 0 := by omega
  have hm16 : m - 1 ≠ m - 6 := by omega
  have hm15 : m - 1 ≠ m - 5 := by omega
  have hm13 : m - 1 ≠ m - 3 := by omega
  have hm12 : m - 1 ≠ m - 2 := by omega
  simpa [hx] using (show rho0CaseII (m := m) x = m - 1 by
    simp [rho0CaseII, hx, hm10, hm16, hm15, hm13, hm12])

theorem rho0CaseII_other [Fact (9 < m)] {x : ℕ}
    (hxlt : x < m) (hx0 : x ≠ 0) (hxm6 : x ≠ m - 6) (hxm5 : x ≠ m - 5)
    (hxm3 : x ≠ m - 3) (hxm2 : x ≠ m - 2) (hxm1 : x ≠ m - 1) :
    rho0CaseII (m := m) (⟨x, hxlt⟩ : Fin m) = m - 2 := by
  simp [rho0CaseII, hx0, hxm6, hxm5, hxm3, hxm2, hxm1]

theorem sum_rho0CaseII [Fact (9 < m)] :
    (∑ x : Fin m, rho0CaseII (m := m) x) = m ^ 2 := by
  have hm0 : 0 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  have hm1 : 1 ≤ m - 6 := by
    have hm9 : 9 < m := Fact.out
    omega
  let g : ℕ → ℕ := fun k =>
    if hk : k < m then rho0CaseII (m := m) (⟨k, hk⟩ : Fin m) else 0
  have hsumRange :
      (∑ x : Fin m, rho0CaseII (m := m) x) = Finset.sum (Finset.range m) g := by
    simpa [g] using (Fin.sum_univ_eq_sum_range g m)
  have hm9 : 9 < m := Fact.out
  have hm6lt : m - 6 < m := by omega
  have hm5lt : m - 5 < m := by omega
  have hm4lt : m - 4 < m := by omega
  have hm3lt : m - 3 < m := by omega
  have hm2lt : m - 2 < m := by omega
  have hm1lt : m - 1 < m := by omega
  have hhead : Finset.sum (Finset.range 1) g = 1 := by
    have hg0 : g 0 = 1 := by
      simpa [g, hm0] using rho0CaseII_zero (m := m)
    simp [hg0]
  have hmid :
      Finset.sum (Finset.Ico 1 (m - 6)) g = (m - 7) * (m - 2) := by
    calc
      Finset.sum (Finset.Ico 1 (m - 6)) g
          = Finset.sum (Finset.Ico 1 (m - 6)) (fun _ => m - 2) := by
              apply Finset.sum_congr rfl
              intro k hk
              have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
              have hklt : k < m - 6 := (Finset.mem_Ico.mp hk).2
              have hkm : k < m := by omega
              have hk0 : k ≠ 0 := by omega
              have hkm6 : k ≠ m - 6 := by omega
              have hkm5 : k ≠ m - 5 := by omega
              have hkm3 : k ≠ m - 3 := by omega
              have hkm2 : k ≠ m - 2 := by omega
              have hkm1 : k ≠ m - 1 := by omega
              simpa [g, hkm] using
                rho0CaseII_other (m := m) hkm hk0 hkm6 hkm5 hkm3 hkm2 hkm1
      _ = (Finset.Ico 1 (m - 6)).card * (m - 2) := by
            simp
      _ = (m - 7) * (m - 2) := by
            simp [Nat.card_Ico]
            omega
  have hρm4 :
      rho0CaseII (m := m) (⟨m - 4, hm4lt⟩ : Fin m) = m - 2 := by
    have hm40 : m - 4 ≠ 0 := by omega
    have hm46 : m - 4 ≠ m - 6 := by omega
    have hm45 : m - 4 ≠ m - 5 := by omega
    have hm43 : m - 4 ≠ m - 3 := by omega
    have hm42 : m - 4 ≠ m - 2 := by omega
    have hm41 : m - 4 ≠ m - 1 := by omega
    simp [rho0CaseII, hm40, hm46, hm45, hm43, hm42, hm41]
  have hg_m6 : g (m - 6) = 2 * m - 4 := by
    simpa [g, hm6lt] using
      rho0CaseII_eq_two_mul_sub_four_of_val_eq_m_sub_six (m := m)
        (x := (⟨m - 6, hm6lt⟩ : Fin m)) rfl
  have hg_m5 : g (m - 5) = m - 1 := by
    simpa [g, hm5lt] using
      rho0CaseII_eq_sub_one_of_val_eq_m_sub_five (m := m)
        (x := (⟨m - 5, hm5lt⟩ : Fin m)) rfl
  have hg_m4 : g (m - 4) = m - 2 := by
    simpa [g, hm4lt] using hρm4
  have hg_m3 : g (m - 3) = 2 * m - 3 := by
    simpa [g, hm3lt] using
      rho0CaseII_eq_two_mul_sub_three_of_val_eq_m_sub_three (m := m)
        (x := (⟨m - 3, hm3lt⟩ : Fin m)) rfl
  have hg_m2 : g (m - 2) = 2 * m - 4 := by
    simpa [g, hm2lt] using
      rho0CaseII_eq_two_mul_sub_four_of_val_eq_m_sub_two (m := m)
        (x := (⟨m - 2, hm2lt⟩ : Fin m)) rfl
  have hg_m1 : g (m - 1) = m - 1 := by
    simpa [g, hm1lt] using
      rho0CaseII_eq_sub_one_of_val_eq_m_sub_one (m := m)
        (x := (⟨m - 1, hm1lt⟩ : Fin m)) rfl
  have hsuffix :
      Finset.sum (Finset.Ico (m - 6) m) g = 9 * m - 15 := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hlen : m - (m - 6) = 6 := by omega
    rw [hlen, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    rw [Finset.sum_range_zero]
    rw [show m - 6 + 0 = m - 6 by omega,
      show m - 6 + 1 = m - 5 by omega,
      show m - 6 + 2 = m - 4 by omega,
      show m - 6 + 3 = m - 3 by omega,
      show m - 6 + 4 = m - 2 by omega,
      show m - 6 + 5 = m - 1 by omega]
    simp [hm6lt, hm5lt, hm4lt, hm3lt, hm2lt, hm1lt]
    rw [rho0CaseII_eq_two_mul_sub_four_of_val_eq_m_sub_six (m := m)
          (x := (⟨m - 6, hm6lt⟩ : Fin m)) rfl,
      rho0CaseII_eq_sub_one_of_val_eq_m_sub_five (m := m)
          (x := (⟨m - 5, hm5lt⟩ : Fin m)) rfl,
      hρm4,
      rho0CaseII_eq_two_mul_sub_three_of_val_eq_m_sub_three (m := m)
          (x := (⟨m - 3, hm3lt⟩ : Fin m)) rfl,
      rho0CaseII_eq_two_mul_sub_four_of_val_eq_m_sub_two (m := m)
          (x := (⟨m - 2, hm2lt⟩ : Fin m)) rfl,
      rho0CaseII_eq_sub_one_of_val_eq_m_sub_one (m := m)
          (x := (⟨m - 1, hm1lt⟩ : Fin m)) rfl]
    omega
  have hm6le : m - 6 ≤ m := by omega
  calc
    (∑ x : Fin m, rho0CaseII (m := m) x) = Finset.sum (Finset.range m) g := hsumRange
    _ = Finset.sum (Finset.range (m - 6)) g + Finset.sum (Finset.Ico (m - 6) m) g := by
          symm
          exact Finset.sum_range_add_sum_Ico g hm6le
    _ = (Finset.sum (Finset.range 1) g + Finset.sum (Finset.Ico 1 (m - 6)) g)
          + Finset.sum (Finset.Ico (m - 6) m) g := by
            rw [show Finset.sum (Finset.range (m - 6)) g =
              Finset.sum (Finset.range 1) g + Finset.sum (Finset.Ico 1 (m - 6)) g by
                symm
                exact Finset.sum_range_add_sum_Ico g hm1]
    _ = (1 + (m - 7) * (m - 2)) + (9 * m - 15) := by
          rw [hhead, hmid, hsuffix]
    _ = m ^ 2 := by
          let k : ℕ := m - 7
          have hmEq : m = k + 7 := by
            dsimp [k]
            omega
          rw [hmEq, pow_two]
          have hk1 : k + 7 - 7 = k := by omega
          have hk2 : k + 7 - 2 = k + 5 := by omega
          have hk3 : 9 * (k + 7) - 15 = 9 * k + 48 := by omega
          rw [hk1, hk2, hk3]
          ring_nf

theorem dir0CaseIILayerZero_eq_zero_of_k_zero_generic [Fact (4 < m)] {i : ZMod m}
    (hi0 : i ≠ 0) (hi1 : i ≠ (1 : ZMod m)) (hineg2 : i ≠ (-2 : ZMod m))
    (hineg1 : i ≠ (-1 : ZMod m)) :
    dir0CaseIILayerZero (m := m) (i, (0 : ZMod m)) = 0 := by
  simp [dir0CaseIILayerZero, hi0, hi1, hineg2, hineg1]

theorem dir0CaseIILayerZero_eq_zero_zero_neg_one [Fact (4 < m)] :
    dir0CaseIILayerZero (m := m) ((0 : ZMod m), (-1 : ZMod m)) = 0 := by
  simp [dir0CaseIILayerZero, one_ne_zero (m := m)]

theorem dir0CaseIILayerZero_eq_zero_neg_one_one [Fact (4 < m)] :
    dir0CaseIILayerZero (m := m) ((-1 : ZMod m), (1 : ZMod m)) = 0 := by
  simp [dir0CaseIILayerZero, one_ne_zero (m := m), one_ne_neg_one (m := m)]

theorem dir0CaseIILayerZero_eq_zero_one_neg_two [Fact (4 < m)] :
    dir0CaseIILayerZero (m := m) ((1 : ZMod m), (-2 : ZMod m)) = 0 := by
  have h1ne0 : (1 : ZMod m) ≠ 0 := one_ne_zero (m := m)
  have h1ne_neg2 : (1 : ZMod m) ≠ (-2 : ZMod m) := one_ne_neg_two_case0 (m := m)
  simp [dir0CaseIILayerZero, h1ne0, h1ne_neg2, one_ne_neg_one (m := m)]

theorem dir0CaseIILayerZero_eq_zero_neg_two_one [Fact (4 < m)] :
    dir0CaseIILayerZero (m := m) ((-2 : ZMod m), (1 : ZMod m)) = 0 := by
  simp [dir0CaseIILayerZero, one_ne_zero (m := m), one_ne_neg_one (m := m),
    two_ne_zero (m := m)]

theorem dir0CaseIILayerZero_eq_two_of_i_zero [Fact (4 < m)] {k : ZMod m}
    (hk0 : k ≠ 0) (hkneg1 : k ≠ (-1 : ZMod m)) :
    dir0CaseIILayerZero (m := m) ((0 : ZMod m), k) = 2 := by
  simp [dir0CaseIILayerZero, hk0, hkneg1, one_ne_zero (m := m), two_ne_zero (m := m)]

theorem dir0CaseIILayerZero_eq_two_of_i_one [Fact (4 < m)] {k : ZMod m}
    (hkneg2 : k ≠ (-2 : ZMod m)) :
    dir0CaseIILayerZero (m := m) ((1 : ZMod m), k) = 2 := by
  have h1ne0 : (1 : ZMod m) ≠ 0 := one_ne_zero (m := m)
  have h1ne_neg2 : (1 : ZMod m) ≠ (-2 : ZMod m) := one_ne_neg_two_case0 (m := m)
  have h1ne_neg1 : (1 : ZMod m) ≠ (-1 : ZMod m) := one_ne_neg_one (m := m)
  simp [dir0CaseIILayerZero, hkneg2, h1ne0, h1ne_neg2, h1ne_neg1]

theorem dir0CaseIILayerZero_eq_two_two_neg_two [Fact (4 < m)] :
    dir0CaseIILayerZero (m := m) ((2 : ZMod m), (-2 : ZMod m)) = 2 := by
  have h20 : (2 : ZMod m) ≠ 0 := two_ne_zero (m := m)
  have h21 : (2 : ZMod m) ≠ (1 : ZMod m) := two_ne_one (m := m)
  have h2neg2 : (2 : ZMod m) ≠ (-2 : ZMod m) := by
    have hm4 : 4 < m := Fact.out
    exact natCast_ne_neg_two_of_lt (m := m) (n := 2) hm4
  have h2neg1 : (2 : ZMod m) ≠ (-1 : ZMod m) := by
    have hm4 : 4 < m := Fact.out
    exact natCast_ne_neg_one_of_lt (m := m) (n := 2) (by omega)
  simp [dir0CaseIILayerZero, h20, h21, h2neg2, h2neg1]

theorem dir0CaseIILayerZero_eq_two_two_neg_one [Fact (4 < m)] :
    dir0CaseIILayerZero (m := m) ((2 : ZMod m), (-1 : ZMod m)) = 2 := by
  have h20 : (2 : ZMod m) ≠ 0 := two_ne_zero (m := m)
  have h21 : (2 : ZMod m) ≠ (1 : ZMod m) := two_ne_one (m := m)
  have h2neg2 : (2 : ZMod m) ≠ (-2 : ZMod m) := by
    have hm4 : 4 < m := Fact.out
    exact natCast_ne_neg_two_of_lt (m := m) (n := 2) hm4
  have h2neg1 : (2 : ZMod m) ≠ (-1 : ZMod m) := by
    have hm4 : 4 < m := Fact.out
    exact natCast_ne_neg_one_of_lt (m := m) (n := 2) (by omega)
  simp [dir0CaseIILayerZero, h20, h21, h2neg2, h2neg1]

theorem dir0CaseIILayerZero_eq_two_neg_two_zero [Fact (4 < m)] :
    dir0CaseIILayerZero (m := m) ((-2 : ZMod m), (0 : ZMod m)) = 2 := by
  have hneg20 : (-2 : ZMod m) ≠ 0 := neg_ne_zero.mpr (two_ne_zero (m := m))
  have hneg21 : (-2 : ZMod m) ≠ (1 : ZMod m) := by
    intro h
    exact one_ne_neg_two_case0 (m := m) h.symm
  have hneg2neg1 : (-2 : ZMod m) ≠ (-1 : ZMod m) := by
    intro h
    exact two_ne_one (m := m) (by simpa using congrArg Neg.neg h)
  simp [dir0CaseIILayerZero, hneg20, hneg21, hneg2neg1]

theorem dir0CaseIILayerZero_eq_one_origin [Fact (4 < m)] :
    dir0CaseIILayerZero (m := m) ((0 : ZMod m), (0 : ZMod m)) = 1 := by
  simp [dir0CaseIILayerZero, one_ne_zero (m := m), two_ne_zero (m := m)]

theorem dir0CaseIILayerZero_eq_one_m_sub_one_m_sub_one [Fact (4 < m)] :
    dir0CaseIILayerZero (m := m) ((-1 : ZMod m), (-1 : ZMod m)) = 1 := by
  have hneg1_ne_one : (-1 : ZMod m) ≠ (1 : ZMod m) := by
    intro h
    exact one_ne_neg_one (m := m) h.symm
  have hneg1_ne_two : (-1 : ZMod m) ≠ (2 : ZMod m) := by
    intro h
    have hm4 : 4 < m := Fact.out
    exact natCast_ne_neg_one_of_lt (m := m) (n := 2) (by omega) h.symm
  have h1_ne_two : (1 : ZMod m) ≠ (2 : ZMod m) := by
    exact two_ne_one (m := m) |> fun h => h.symm
  simp [dir0CaseIILayerZero, one_ne_zero (m := m), hneg1_ne_one, hneg1_ne_two, h1_ne_two]

theorem dir0CaseIILayerZero_eq_one_of_generic [Fact (4 < m)] {i k : ZMod m}
    (hi0 : i ≠ 0) (hi1 : i ≠ 1)
    (hk0 : k ≠ 0) (hk1 : k ≠ 1) (hkneg1 : k ≠ (-1 : ZMod m)) (hkneg2 : k ≠ (-2 : ZMod m)) :
    dir0CaseIILayerZero (m := m) (i, k) = 1 := by
  simp [dir0CaseIILayerZero, hi0, hi1, hk0, hk1, hkneg1, hkneg2]

theorem dir0CaseIILayerZero_eq_one_of_k_neg_one_generic [Fact (4 < m)] {i : ZMod m}
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hi2 : i ≠ (2 : ZMod m)) :
    dir0CaseIILayerZero (m := m) (i, (-1 : ZMod m)) = 1 := by
  have hneg1_ne_one : (-1 : ZMod m) ≠ (1 : ZMod m) := by
    intro h
    exact one_ne_neg_one (m := m) h.symm
  simp [dir0CaseIILayerZero, hi0, hi1, hi2, hneg1_ne_one]

theorem dir0CaseIILayerZero_eq_one_of_k_neg_two_generic [Fact (4 < m)] {i : ZMod m}
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hi2 : i ≠ (2 : ZMod m)) :
    dir0CaseIILayerZero (m := m) (i, (-2 : ZMod m)) = 1 := by
  have hneg2_ne_one : (-2 : ZMod m) ≠ (1 : ZMod m) := by
    intro h
    have h' : (((1 : ℕ) : ZMod m)) = (-2 : ZMod m) := by
      simpa using h.symm
    exact natCast_ne_neg_two_of_lt (m := m) (n := 1) (by
      have hm4 : 4 < m := Fact.out
      omega) h'
  simp [dir0CaseIILayerZero, hi0, hi1, hi2, hneg2_ne_one, two_ne_zero (m := m)]

theorem dir0CaseIILayerZero_eq_one_of_k_one_generic [Fact (4 < m)] {i : ZMod m}
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hineg1 : i ≠ (-1 : ZMod m)) (hineg2 : i ≠ (-2 : ZMod m)) :
    dir0CaseIILayerZero (m := m) (i, (1 : ZMod m)) = 1 := by
  have h1_ne_zero : (1 : ZMod m) ≠ 0 := one_ne_zero (m := m)
  have h1_ne_neg_one : (1 : ZMod m) ≠ (-1 : ZMod m) := by
    intro h
    exact one_ne_neg_one (m := m) h
  have h1_ne_neg_two : (1 : ZMod m) ≠ (-2 : ZMod m) := by
    intro h
    have h' : (((1 : ℕ) : ZMod m)) = (-2 : ZMod m) := by
      simpa using h
    exact natCast_ne_neg_two_of_lt (m := m) (n := 1) (by
      have hm4 : 4 < m := Fact.out
      omega) h'
  simp [dir0CaseIILayerZero, hi0, hi1, hineg1, hineg2, h1_ne_zero, h1_ne_neg_one, h1_ne_neg_two]

theorem fullMapColor0_step_zero_of_dir0 (dir0 : P0Coord m → Color) {u : P0Coord m}
    (hdir : dir0 u = 0) :
    fullMapColor0 (m := m) dir0 (slicePoint (0 : ZMod m) u) = ((u.1 + 1, u.2), (1 : ZMod m)) := by
  simp [fullMapColor0, dir0FromLayerZero, hdir, KMap, slicePoint]

theorem fullMapColor0_step_zero_of_dir1 (dir0 : P0Coord m → Color) {u : P0Coord m}
    (hdir : dir0 u = 1) :
    fullMapColor0 (m := m) dir0 (slicePoint (0 : ZMod m) u) = (u, (1 : ZMod m)) := by
  simp [fullMapColor0, dir0FromLayerZero, hdir, KMap, slicePoint]

theorem fullMapColor0_step_zero_of_dir2 (dir0 : P0Coord m → Color) {u : P0Coord m}
    (hdir : dir0 u = 2) :
    fullMapColor0 (m := m) dir0 (slicePoint (0 : ZMod m) u) = ((u.1, u.2 + 1), (1 : ZMod m)) := by
  simp [fullMapColor0, dir0FromLayerZero, hdir, KMap, slicePoint]

theorem fullMapColor0_step_one_of_i_zero (dir0 : P0Coord m → Color) [Fact (4 < m)] {k : ZMod m} :
    fullMapColor0 (m := m) dir0 (((0 : ZMod m), k), (1 : ZMod m)) =
      (((0 : ZMod m), k), (2 : ZMod m)) := by
  ext <;> simp [fullMapColor0, dir0FromLayerZero, KMap, one_ne_zero (m := m)]
  ring

theorem fullMapColor0_step_one_of_i_ne_zero (dir0 : P0Coord m → Color) [Fact (4 < m)]
    {i k : ZMod m} (hi0 : i ≠ 0) :
    fullMapColor0 (m := m) dir0 ((i, k), (1 : ZMod m)) =
      ((i, k + 1), (2 : ZMod m)) := by
  ext <;> simp [fullMapColor0, dir0FromLayerZero, KMap, one_ne_zero (m := m), hi0]
  ring

theorem fullMapColor0_step_two_of_sum_two (dir0 : P0Coord m → Color) [Fact (4 < m)] {i k : ZMod m}
    (hsum : i + k = (2 : ZMod m)) :
    fullMapColor0 (m := m) dir0 ((i, k), (2 : ZMod m)) =
      ((i, k + 1), (3 : ZMod m)) := by
  ext <;> simp [fullMapColor0, dir0FromLayerZero, KMap, two_ne_zero (m := m),
    two_ne_one (m := m), hsum]
  ring

theorem fullMapColor0_step_two_of_sum_ne_two (dir0 : P0Coord m → Color) [Fact (4 < m)]
    {i k : ZMod m} (hsum : i + k ≠ (2 : ZMod m)) :
    fullMapColor0 (m := m) dir0 ((i, k), (2 : ZMod m)) =
      ((i + 1, k), (3 : ZMod m)) := by
  ext <;> simp [fullMapColor0, dir0FromLayerZero, KMap, two_ne_zero (m := m),
    two_ne_one (m := m), hsum]
  ring

theorem iterate_three_fullMapColor0_of_dir0_generic (dir0 : P0Coord m → Color) [Fact (4 < m)]
    {u : P0Coord m} (hdir : dir0 u = 0) (hi : u.1 ≠ (-1 : ZMod m)) (hsum0 : u.1 + u.2 ≠ 0) :
    (((fullMapColor0 (m := m) dir0)^[3]) (slicePoint (0 : ZMod m) u)) =
      ((u.1 + 2, u.2 + 1), (3 : ZMod m)) := by
  have hi1 : u.1 + 1 ≠ 0 := by
    intro h
    apply hi
    calc
      u.1 = (u.1 + 1) - 1 := by ring
      _ = (-1 : ZMod m) := by rw [h]; ring
  calc
    (((fullMapColor0 (m := m) dir0)^[3]) (slicePoint (0 : ZMod m) u))
        = (((fullMapColor0 (m := m) dir0)^[2]) ((u.1 + 1, u.2), (1 : ZMod m))) := by
            rw [Function.iterate_succ_apply']
            simpa using congrArg (fun z => ((fullMapColor0 (m := m) dir0)^[2]) z)
              (fullMapColor0_step_zero_of_dir0 (m := m) dir0 hdir)
    _ = fullMapColor0 (m := m) dir0 ((u.1 + 1, u.2 + 1), (2 : ZMod m)) := by
          rw [Function.iterate_succ_apply']
          simpa using congrArg (fullMapColor0 (m := m) dir0)
            (fullMapColor0_step_one_of_i_ne_zero (m := m) dir0 (i := u.1 + 1) (k := u.2) hi1)
    _ = ((u.1 + 2, u.2 + 1), (3 : ZMod m)) := by
          have hsum : u.1 + 1 + (u.2 + 1) ≠ (2 : ZMod m) := by
            intro h
            apply hsum0
            have hsum0' : u.1 + u.2 = 0 := by
              calc
                u.1 + u.2 = (u.1 + 1 + (u.2 + 1)) - 2 := by ring
                _ = 0 := by rw [h]; ring
            exact hsum0'
          have hstep := fullMapColor0_step_two_of_sum_ne_two (m := m) dir0
            (i := u.1 + 1) (k := u.2 + 1) hsum
          calc
            fullMapColor0 (m := m) dir0 ((u.1 + 1, u.2 + 1), (2 : ZMod m))
                = ((u.1 + (1 + 1), u.2 + 1), (3 : ZMod m)) := by
                    simpa [add_assoc] using hstep
            _ = ((u.1 + 2, u.2 + 1), (3 : ZMod m)) := by
                  ext <;> ring

theorem iterate_three_fullMapColor0_origin (dir0 : P0Coord m → Color) [Fact (4 < m)]
    (hdir : dir0 ((0 : ZMod m), (0 : ZMod m)) = 1) :
    (((fullMapColor0 (m := m) dir0)^[3]) (slicePoint (0 : ZMod m) ((0 : ZMod m), (0 : ZMod m)))) =
      (((1 : ZMod m), (0 : ZMod m)), (3 : ZMod m)) := by
  calc
    (((fullMapColor0 (m := m) dir0)^[3]) (slicePoint (0 : ZMod m) ((0 : ZMod m), (0 : ZMod m))))
        = (((fullMapColor0 (m := m) dir0)^[2]) (((0 : ZMod m), (0 : ZMod m)), (1 : ZMod m))) := by
            rw [Function.iterate_succ_apply']
            simpa using congrArg (fun z => ((fullMapColor0 (m := m) dir0)^[2]) z)
              (fullMapColor0_step_zero_of_dir1 (m := m) dir0 (u := ((0 : ZMod m), (0 : ZMod m))) hdir)
    _ = fullMapColor0 (m := m) dir0 (((0 : ZMod m), (0 : ZMod m)), (2 : ZMod m)) := by
          rw [Function.iterate_succ_apply']
          simpa using congrArg (fullMapColor0 (m := m) dir0)
            (fullMapColor0_step_one_of_i_zero (m := m) dir0 (k := (0 : ZMod m)))
    _ = (((1 : ZMod m), (0 : ZMod m)), (3 : ZMod m)) := by
          have hsum : ((0 : ZMod m) + (0 : ZMod m)) ≠ (2 : ZMod m) := by
            intro h
            exact two_ne_zero (m := m) (by simpa using h.symm)
          calc
            fullMapColor0 (m := m) dir0 ((0, 0), (2 : ZMod m))
                = (((0 : ZMod m) + 1, (0 : ZMod m)), (3 : ZMod m)) := by
                    exact fullMapColor0_step_two_of_sum_ne_two (m := m) dir0
                      (i := (0 : ZMod m)) (k := (0 : ZMod m)) hsum
            _ = (((1 : ZMod m), (0 : ZMod m)), (3 : ZMod m)) := by
                  ext <;> ring

theorem iterate_three_fullMapColor0_of_dir2_i_ne_zero_generic (dir0 : P0Coord m → Color) [Fact (4 < m)]
    {u : P0Coord m} (hdir : dir0 u = 2) (hi0 : u.1 ≠ 0) (hsum0 : u.1 + u.2 ≠ 0) :
    (((fullMapColor0 (m := m) dir0)^[3]) (slicePoint (0 : ZMod m) u)) =
      ((u.1 + 1, u.2 + 2), (3 : ZMod m)) := by
  calc
    (((fullMapColor0 (m := m) dir0)^[3]) (slicePoint (0 : ZMod m) u))
        = (((fullMapColor0 (m := m) dir0)^[2]) ((u.1, u.2 + 1), (1 : ZMod m))) := by
            rw [Function.iterate_succ_apply']
            simpa using congrArg (fun z => ((fullMapColor0 (m := m) dir0)^[2]) z)
              (fullMapColor0_step_zero_of_dir2 (m := m) dir0 hdir)
    _ = fullMapColor0 (m := m) dir0 ((u.1, u.2 + 2), (2 : ZMod m)) := by
          rw [Function.iterate_succ_apply']
          calc
            fullMapColor0 (m := m) dir0 (fullMapColor0 (m := m) dir0 ((u.1, u.2 + 1), (1 : ZMod m)))
                = fullMapColor0 (m := m) dir0 ((u.1, (u.2 + 1) + 1), (2 : ZMod m)) := by
                    simpa using congrArg (fullMapColor0 (m := m) dir0)
                      (fullMapColor0_step_one_of_i_ne_zero (m := m) dir0
                        (i := u.1) (k := u.2 + 1) hi0)
            _ = fullMapColor0 (m := m) dir0 ((u.1, u.2 + 2), (2 : ZMod m)) := by
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
            fullMapColor0 (m := m) dir0 ((u.1, u.2 + 2), (2 : ZMod m))
                = (((u.1 + 1), u.2 + 2), (3 : ZMod m)) := by
                    exact fullMapColor0_step_two_of_sum_ne_two (m := m) dir0
                      (i := u.1) (k := u.2 + 2) hsum'
            _ = ((u.1 + 1, u.2 + 2), (3 : ZMod m)) := by rfl

theorem iterate_three_fullMapColor0_of_dir2_i_ne_zero_sum_zero (dir0 : P0Coord m → Color)
    [Fact (4 < m)] {u : P0Coord m}
    (hdir : dir0 u = 2) (hi0 : u.1 ≠ 0) (hsum0 : u.1 + u.2 = 0) :
    (((fullMapColor0 (m := m) dir0)^[3]) (slicePoint (0 : ZMod m) u)) =
      ((u.1, u.2 + 3), (3 : ZMod m)) := by
  calc
    (((fullMapColor0 (m := m) dir0)^[3]) (slicePoint (0 : ZMod m) u))
        = (((fullMapColor0 (m := m) dir0)^[2]) ((u.1, u.2 + 1), (1 : ZMod m))) := by
            rw [Function.iterate_succ_apply']
            simpa using congrArg (fun z => ((fullMapColor0 (m := m) dir0)^[2]) z)
              (fullMapColor0_step_zero_of_dir2 (m := m) dir0 (u := u) hdir)
    _ = fullMapColor0 (m := m) dir0 ((u.1, u.2 + 2), (2 : ZMod m)) := by
          rw [Function.iterate_succ_apply']
          calc
            fullMapColor0 (m := m) dir0
                (fullMapColor0 (m := m) dir0 ((u.1, u.2 + 1), (1 : ZMod m)))
                = fullMapColor0 (m := m) dir0 ((u.1, (u.2 + 1) + 1), (2 : ZMod m)) := by
                    simpa using congrArg (fullMapColor0 (m := m) dir0)
                      (fullMapColor0_step_one_of_i_ne_zero (m := m) dir0
                        (i := u.1) (k := u.2 + 1) hi0)
            _ = fullMapColor0 (m := m) dir0 ((u.1, u.2 + 2), (2 : ZMod m)) := by
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
            fullMapColor0 (m := m) dir0 ((u.1, u.2 + 2), (2 : ZMod m))
                = ((u.1, (u.2 + 2) + 1), (3 : ZMod m)) := by
                    exact fullMapColor0_step_two_of_sum_two (m := m) dir0
                      (i := u.1) (k := u.2 + 2) hsum'
            _ = ((u.1, u.2 + 3), (3 : ZMod m)) := by
                  ext <;> ring

theorem iterate_three_fullMapColor0_of_dir1_generic (dir0 : P0Coord m → Color) [Fact (4 < m)]
    {u : P0Coord m} (hdir : dir0 u = 1) (hi0 : u.1 ≠ 0) (hsum1 : u.1 + u.2 ≠ 1) :
    (((fullMapColor0 (m := m) dir0)^[3]) (slicePoint (0 : ZMod m) u)) =
      ((u.1 + 1, u.2 + 1), (3 : ZMod m)) := by
  calc
    (((fullMapColor0 (m := m) dir0)^[3]) (slicePoint (0 : ZMod m) u))
        = (((fullMapColor0 (m := m) dir0)^[2]) (u, (1 : ZMod m))) := by
            rw [Function.iterate_succ_apply']
            simpa using congrArg (fun z => ((fullMapColor0 (m := m) dir0)^[2]) z)
              (fullMapColor0_step_zero_of_dir1 (m := m) dir0 hdir)
    _ = fullMapColor0 (m := m) dir0 ((u.1, u.2 + 1), (2 : ZMod m)) := by
          rw [Function.iterate_succ_apply']
          simpa using congrArg (fullMapColor0 (m := m) dir0)
            (fullMapColor0_step_one_of_i_ne_zero (m := m) dir0 (i := u.1) (k := u.2) hi0)
    _ = ((u.1 + 1, u.2 + 1), (3 : ZMod m)) := by
          have hsum2 : u.1 + (u.2 + 1) ≠ (2 : ZMod m) := by
            intro h
            apply hsum1
            calc
              u.1 + u.2 = (u.1 + (u.2 + 1)) - 1 := by ring
              _ = 1 := by rw [h]; ring
          calc
            fullMapColor0 (m := m) dir0 ((u.1, u.2 + 1), (2 : ZMod m))
                = (((u.1 + 1), u.2 + 1), (3 : ZMod m)) := by
                    exact fullMapColor0_step_two_of_sum_ne_two (m := m) dir0
                      (i := u.1) (k := u.2 + 1) hsum2
            _ = ((u.1 + 1, u.2 + 1), (3 : ZMod m)) := by rfl

theorem iterate_three_fullMapColor0_of_dir1_sum_one (dir0 : P0Coord m → Color) [Fact (4 < m)]
    {u : P0Coord m} (hdir : dir0 u = 1) (hi0 : u.1 ≠ 0) (hsum1 : u.1 + u.2 = 1) :
    (((fullMapColor0 (m := m) dir0)^[3]) (slicePoint (0 : ZMod m) u)) =
      ((u.1, u.2 + 2), (3 : ZMod m)) := by
  calc
    (((fullMapColor0 (m := m) dir0)^[3]) (slicePoint (0 : ZMod m) u))
        = (((fullMapColor0 (m := m) dir0)^[2]) (u, (1 : ZMod m))) := by
            rw [Function.iterate_succ_apply']
            simpa using congrArg (fun z => ((fullMapColor0 (m := m) dir0)^[2]) z)
              (fullMapColor0_step_zero_of_dir1 (m := m) dir0 hdir)
    _ = fullMapColor0 (m := m) dir0 ((u.1, u.2 + 1), (2 : ZMod m)) := by
          rw [Function.iterate_succ_apply']
          simpa using congrArg (fullMapColor0 (m := m) dir0)
            (fullMapColor0_step_one_of_i_ne_zero (m := m) dir0 (i := u.1) (k := u.2) hi0)
    _ = ((u.1, u.2 + 2), (3 : ZMod m)) := by
          have hsum2 : u.1 + (u.2 + 1) = (2 : ZMod m) := by
            calc
              u.1 + (u.2 + 1) = (u.1 + u.2) + 1 := by ring
              _ = 2 := by rw [hsum1]; ring
          calc
            fullMapColor0 (m := m) dir0 ((u.1, u.2 + 1), (2 : ZMod m))
                = ((u.1, (u.2 + 1) + 1), (3 : ZMod m)) := by
                    exact fullMapColor0_step_two_of_sum_two (m := m) dir0
                      (i := u.1) (k := u.2 + 1) hsum2
            _ = ((u.1, u.2 + 2), (3 : ZMod m)) := by
                  ext <;> ring

theorem iterate_three_fullMapColor0_of_dir2_i_zero_generic (dir0 : P0Coord m → Color) [Fact (4 < m)]
    {k : ZMod m} (hdir : dir0 ((0 : ZMod m), k) = 2) (hk1 : k ≠ (1 : ZMod m)) :
    (((fullMapColor0 (m := m) dir0)^[3]) (slicePoint (0 : ZMod m) ((0 : ZMod m), k))) =
      (((1 : ZMod m), k + 1), (3 : ZMod m)) := by
  calc
    (((fullMapColor0 (m := m) dir0)^[3]) (slicePoint (0 : ZMod m) ((0 : ZMod m), k)))
        = (((fullMapColor0 (m := m) dir0)^[2]) (((0 : ZMod m), k + 1), (1 : ZMod m))) := by
            rw [Function.iterate_succ_apply']
            simpa using congrArg (fun z => ((fullMapColor0 (m := m) dir0)^[2]) z)
              (fullMapColor0_step_zero_of_dir2 (m := m) dir0 (u := ((0 : ZMod m), k)) hdir)
    _ = fullMapColor0 (m := m) dir0 (((0 : ZMod m), k + 1), (2 : ZMod m)) := by
          rw [Function.iterate_succ_apply']
          simpa using congrArg (fullMapColor0 (m := m) dir0)
            (fullMapColor0_step_one_of_i_zero (m := m) dir0 (k := k + 1))
    _ = (((1 : ZMod m), k + 1), (3 : ZMod m)) := by
          have hsum2 : (0 : ZMod m) + (k + 1) ≠ (2 : ZMod m) := by
            intro h
            apply hk1
            calc
              k = ((0 : ZMod m) + (k + 1)) - 1 := by ring
              _ = 1 := by rw [h]; ring
          calc
            fullMapColor0 (m := m) dir0 (((0 : ZMod m), k + 1), (2 : ZMod m))
                = ((((0 : ZMod m) + 1), k + 1), (3 : ZMod m)) := by
                    exact fullMapColor0_step_two_of_sum_ne_two (m := m) dir0
                      (i := (0 : ZMod m)) (k := k + 1) hsum2
            _ = (((1 : ZMod m), k + 1), (3 : ZMod m)) := by
                  ext <;> ring

theorem iterate_three_fullMapColor0_of_dir2_i_zero_eq_one (dir0 : P0Coord m → Color) [Fact (4 < m)]
    (hdir : dir0 ((0 : ZMod m), (1 : ZMod m)) = 2) :
    (((fullMapColor0 (m := m) dir0)^[3]) (slicePoint (0 : ZMod m) ((0 : ZMod m), (1 : ZMod m)))) =
      (((0 : ZMod m), (3 : ZMod m)), (3 : ZMod m)) := by
  have hstep0 :
      fullMapColor0 (m := m) dir0 (slicePoint (0 : ZMod m) ((0 : ZMod m), (1 : ZMod m))) =
        (((0 : ZMod m), (2 : ZMod m)), (1 : ZMod m)) := by
    calc
      fullMapColor0 (m := m) dir0 (slicePoint (0 : ZMod m) ((0 : ZMod m), (1 : ZMod m)))
          = (((0 : ZMod m), (1 : ZMod m) + 1), (1 : ZMod m)) := by
              simpa using fullMapColor0_step_zero_of_dir2 (m := m) dir0
                (u := ((0 : ZMod m), (1 : ZMod m))) hdir
      _ = (((0 : ZMod m), (2 : ZMod m)), (1 : ZMod m)) := by
            ext <;> ring
  calc
    (((fullMapColor0 (m := m) dir0)^[3]) (slicePoint (0 : ZMod m) ((0 : ZMod m), (1 : ZMod m))))
        = (((fullMapColor0 (m := m) dir0)^[2]) (((0 : ZMod m), (2 : ZMod m)), (1 : ZMod m))) := by
            rw [Function.iterate_succ_apply']
            simpa using congrArg (fun z => ((fullMapColor0 (m := m) dir0)^[2]) z) hstep0
    _ = fullMapColor0 (m := m) dir0 (((0 : ZMod m), (2 : ZMod m)), (2 : ZMod m)) := by
          rw [Function.iterate_succ_apply']
          simpa using congrArg (fullMapColor0 (m := m) dir0)
            (fullMapColor0_step_one_of_i_zero (m := m) dir0 (k := (2 : ZMod m)))
    _ = (((0 : ZMod m), (3 : ZMod m)), (3 : ZMod m)) := by
          have hsum2 : (0 : ZMod m) + (2 : ZMod m) = (2 : ZMod m) := by ring
          calc
            fullMapColor0 (m := m) dir0 (((0 : ZMod m), (2 : ZMod m)), (2 : ZMod m))
                = (((0 : ZMod m), (2 : ZMod m) + 1), (3 : ZMod m)) := by
                    exact fullMapColor0_step_two_of_sum_two (m := m) dir0
                      (i := (0 : ZMod m)) (k := (2 : ZMod m)) hsum2
            _ = (((0 : ZMod m), (3 : ZMod m)), (3 : ZMod m)) := by
                  ext <;> ring

theorem iterate_m_fullMapColor0_of_three (dir0 : P0Coord m → Color) [Fact (4 < m)] {u v : P0Coord m}
    (h3 : (((fullMapColor0 (m := m) dir0)^[3]) (slicePoint (0 : ZMod m) u)) = (v, (3 : ZMod m))) :
    (((fullMapColor0 (m := m) dir0)^[m]) (slicePoint (0 : ZMod m) u)) =
      slicePoint (0 : ZMod m) (v.1 - 3, v.2) := by
  have hm3 : 3 ≤ m := by
    have hm4 : 4 < m := Fact.out
    omega
  calc
    (((fullMapColor0 (m := m) dir0)^[m]) (slicePoint (0 : ZMod m) u))
        = (((fullMapColor0 (m := m) dir0)^[m - 3])
            ((((fullMapColor0 (m := m) dir0)^[3]) (slicePoint (0 : ZMod m) u)))) := by
              simpa [Nat.sub_add_cancel hm3] using
                (Function.iterate_add_apply (f := fullMapColor0 (m := m) dir0) (m := m - 3) (n := 3)
                  (slicePoint (0 : ZMod m) u))
    _ = (((fullMapColor0 (m := m) dir0)^[m - 3]) (v, (3 : ZMod m))) := by rw [h3]
    _ = slicePoint (0 : ZMod m) (v.1 - 3, v.2) := by
          calc
            (((fullMapColor0 (m := m) dir0)^[m - 3]) (v, (3 : ZMod m)))
                = slicePoint (0 : ZMod m) (v.1 + (((m - 3 : ℕ) : ZMod m)), v.2) := by
                    exact iterate_m_sub_three_fullMapColor0 (m := m) dir0 v
            _ = slicePoint (0 : ZMod m) (v.1 - 3, v.2) := by
                  ext <;> simp [slicePoint, Nat.cast_sub hm3]
                  all_goals ring

theorem returnMap0CaseII_of_dir1_generic [Fact (9 < m)] {u : P0Coord m}
    (hdir : dir0CaseIILayerZero (m := m) u = 1) (hi0 : u.1 ≠ 0) (hsum1 : u.1 + u.2 ≠ 1) :
    returnMap0CaseII (m := m) u = (u.1 - 2, u.2 + 1) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  have h3 := iterate_three_fullMapColor0_of_dir1_generic (m := m)
    (dir0 := dir0CaseIILayerZero (m := m)) (u := u) hdir hi0 hsum1
  have h3' :
      (((fullMapColor0 (m := m) (dir0CaseIILayerZero (m := m)))^[3]) (slicePoint (0 : ZMod m) u)) =
        ((u.1 + 1, u.2 + 1), (3 : ZMod m)) := by
    simpa using h3
  have hmain := iterate_m_fullMapColor0_of_three (m := m)
    (dir0 := dir0CaseIILayerZero (m := m)) (u := u) (v := (u.1 + 1, u.2 + 1)) h3'
  have hfst :
      returnMap0CaseII (m := m) u = ((u.1 + 1) - 3, u.2 + 1) := by
    simpa [fullMap0CaseII, returnMap0CaseII, slicePoint] using congrArg Prod.fst hmain
  calc
    returnMap0CaseII (m := m) u = ((u.1 + 1) - 3, u.2 + 1) := hfst
    _ = (u.1 - 2, u.2 + 1) := by
          ext <;> ring

theorem returnMap0CaseII_of_dir1_sum_one [Fact (9 < m)] {u : P0Coord m}
    (hdir : dir0CaseIILayerZero (m := m) u = 1) (hi0 : u.1 ≠ 0) (hsum1 : u.1 + u.2 = 1) :
    returnMap0CaseII (m := m) u = (u.1 - 3, u.2 + 2) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  have h3 := iterate_three_fullMapColor0_of_dir1_sum_one (m := m)
    (dir0 := dir0CaseIILayerZero (m := m)) (u := u) hdir hi0 hsum1
  have hmain := iterate_m_fullMapColor0_of_three (m := m)
    (dir0 := dir0CaseIILayerZero (m := m)) (u := u) (v := (u.1, u.2 + 2)) h3
  have hfst :
      returnMap0CaseII (m := m) u = (u.1 - 3, u.2 + 2) := by
    simpa [fullMap0CaseII, returnMap0CaseII, slicePoint] using congrArg Prod.fst hmain
  exact hfst

theorem returnMap0CaseII_of_dir2_i_ne_zero_sum_zero [Fact (9 < m)] {u : P0Coord m}
    (hdir : dir0CaseIILayerZero (m := m) u = 2) (hi0 : u.1 ≠ 0) (hsum0 : u.1 + u.2 = 0) :
    returnMap0CaseII (m := m) u = (u.1 - 3, u.2 + 3) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  have h3 := iterate_three_fullMapColor0_of_dir2_i_ne_zero_sum_zero (m := m)
    (dir0 := dir0CaseIILayerZero (m := m)) (u := u) hdir hi0 hsum0
  have hmain := iterate_m_fullMapColor0_of_three (m := m)
    (dir0 := dir0CaseIILayerZero (m := m)) (u := u) (v := (u.1, u.2 + 3)) h3
  have hfst :
      returnMap0CaseII (m := m) u = (u.1 - 3, u.2 + 3) := by
    simpa [fullMap0CaseII, returnMap0CaseII, slicePoint] using congrArg Prod.fst hmain
  exact hfst

theorem returnMap0CaseII_of_dir2_i_ne_zero_generic [Fact (9 < m)] {u : P0Coord m}
    (hdir : dir0CaseIILayerZero (m := m) u = 2) (hi0 : u.1 ≠ 0) (hsum0 : u.1 + u.2 ≠ 0) :
    returnMap0CaseII (m := m) u = (u.1 - 2, u.2 + 2) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  have h3 := iterate_three_fullMapColor0_of_dir2_i_ne_zero_generic (m := m)
    (dir0 := dir0CaseIILayerZero (m := m)) (u := u) hdir hi0 hsum0
  have hmain := iterate_m_fullMapColor0_of_three (m := m)
    (dir0 := dir0CaseIILayerZero (m := m)) (u := u) (v := (u.1 + 1, u.2 + 2)) h3
  have hfst :
      returnMap0CaseII (m := m) u = ((u.1 + 1) - 3, u.2 + 2) := by
    simpa [fullMap0CaseII, returnMap0CaseII, slicePoint] using congrArg Prod.fst hmain
  calc
    returnMap0CaseII (m := m) u = ((u.1 + 1) - 3, u.2 + 2) := hfst
    _ = (u.1 - 2, u.2 + 2) := by
          ext <;> ring

theorem returnMap0CaseII_of_dir2_i_zero_generic [Fact (9 < m)] {k : ZMod m}
    (hdir : dir0CaseIILayerZero (m := m) ((0 : ZMod m), k) = 2) (hk1 : k ≠ (1 : ZMod m)) :
    returnMap0CaseII (m := m) ((0 : ZMod m), k) = ((-2 : ZMod m), k + 1) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  have h3 := iterate_three_fullMapColor0_of_dir2_i_zero_generic (m := m)
    (dir0 := dir0CaseIILayerZero (m := m)) (k := k) hdir hk1
  have hmain := iterate_m_fullMapColor0_of_three (m := m)
    (dir0 := dir0CaseIILayerZero (m := m))
    (u := ((0 : ZMod m), k)) (v := ((1 : ZMod m), k + 1)) h3
  have hfst :
      returnMap0CaseII (m := m) ((0 : ZMod m), k) = (((1 : ZMod m) - 3), k + 1) := by
    simpa [fullMap0CaseII, returnMap0CaseII, slicePoint] using congrArg Prod.fst hmain
  calc
    returnMap0CaseII (m := m) ((0 : ZMod m), k) = (((1 : ZMod m) - 3), k + 1) := hfst
    _ = ((-2 : ZMod m), k + 1) := by
          ext <;> ring

theorem returnMap0CaseII_of_dir0_generic [Fact (9 < m)] {u : P0Coord m}
    (hdir : dir0CaseIILayerZero (m := m) u = 0) (hi : u.1 ≠ (-1 : ZMod m))
    (hsum0 : u.1 + u.2 ≠ 0) :
    returnMap0CaseII (m := m) u = (u.1 - 1, u.2 + 1) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  have h3 := iterate_three_fullMapColor0_of_dir0_generic (m := m)
    (dir0 := dir0CaseIILayerZero (m := m)) (u := u) hdir hi hsum0
  have hmain := iterate_m_fullMapColor0_of_three (m := m)
    (dir0 := dir0CaseIILayerZero (m := m)) (u := u) (v := (u.1 + 2, u.2 + 1)) h3
  have hfst :
      returnMap0CaseII (m := m) u = ((u.1 + 2) - 3, u.2 + 1) := by
    simpa [fullMap0CaseII, returnMap0CaseII, slicePoint] using congrArg Prod.fst hmain
  calc
    returnMap0CaseII (m := m) u = ((u.1 + 2) - 3, u.2 + 1) := hfst
    _ = (u.1 - 1, u.2 + 1) := by
          ext <;> ring

theorem returnMap0CaseII_zero_zero [Fact (9 < m)] :
    returnMap0CaseII (m := m) ((0 : ZMod m), (0 : ZMod m)) = ((-2 : ZMod m), (0 : ZMod m)) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  have h3 := iterate_three_fullMapColor0_origin (m := m) (dir0 := dir0CaseIILayerZero (m := m))
    (dir0CaseIILayerZero_eq_one_origin (m := m))
  have hmain := iterate_m_fullMapColor0_of_three (m := m) (dir0 := dir0CaseIILayerZero (m := m))
    (u := ((0 : ZMod m), (0 : ZMod m))) (v := ((1 : ZMod m), (0 : ZMod m))) h3
  have hfst :
      returnMap0CaseII (m := m) ((0 : ZMod m), (0 : ZMod m)) =
        (((1 : ZMod m) - 3), (0 : ZMod m)) := by
    simpa [fullMap0CaseII, returnMap0CaseII, slicePoint] using congrArg Prod.fst hmain
  calc
    returnMap0CaseII (m := m) ((0 : ZMod m), (0 : ZMod m))
        = (((1 : ZMod m) - 3), (0 : ZMod m)) := hfst
    _ = ((-2 : ZMod m), (0 : ZMod m)) := by
          ext <;> ring

theorem returnMap0CaseIIXY_zero_zero [Fact (9 < m)] :
    returnMap0CaseIIXY (m := m) ((0 : ZMod m), (0 : ZMod m)) = ((-2 : ZMod m), (0 : ZMod m)) := by
  simp [returnMap0CaseIIXY, fromXY, toXY, returnMap0CaseII_zero_zero]

theorem returnMap0CaseII_one_zero [Fact (9 < m)] :
    returnMap0CaseII (m := m) ((1 : ZMod m), (0 : ZMod m)) = ((-1 : ZMod m), (2 : ZMod m)) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  have h0neg2 : (0 : ZMod m) ≠ (-2 : ZMod m) := by
    intro h
    exact neg_ne_zero.mpr (two_ne_zero (m := m)) h.symm
  have hdir : dir0CaseIILayerZero (m := m) ((1 : ZMod m), (0 : ZMod m)) = 2 :=
    dir0CaseIILayerZero_eq_two_of_i_one (m := m) (k := (0 : ZMod m)) h0neg2
  have hsum0 : (1 : ZMod m) + (0 : ZMod m) ≠ 0 := by
    rw [add_zero]
    exact one_ne_zero (m := m)
  have h3 := iterate_three_fullMapColor0_of_dir2_i_ne_zero_generic (m := m)
    (dir0 := dir0CaseIILayerZero (m := m)) (u := ((1 : ZMod m), (0 : ZMod m)))
    hdir (one_ne_zero (m := m)) hsum0
  have hmain := iterate_m_fullMapColor0_of_three (m := m) (dir0 := dir0CaseIILayerZero (m := m))
    (u := ((1 : ZMod m), (0 : ZMod m))) (v := (((1 : ZMod m) + 1), ((0 : ZMod m) + 2))) h3
  have hfst :
      returnMap0CaseII (m := m) ((1 : ZMod m), (0 : ZMod m)) =
        ((((1 : ZMod m) + 1) - 3), ((0 : ZMod m) + 2)) := by
    simpa [fullMap0CaseII, returnMap0CaseII, slicePoint] using congrArg Prod.fst hmain
  calc
    returnMap0CaseII (m := m) ((1 : ZMod m), (0 : ZMod m))
        = ((((1 : ZMod m) + 1) - 3), ((0 : ZMod m) + 2)) := hfst
    _ = ((-1 : ZMod m), (2 : ZMod m)) := by
          ext <;> ring

theorem returnMap0CaseIIXY_one_zero [Fact (9 < m)] :
    returnMap0CaseIIXY (m := m) ((1 : ZMod m), (0 : ZMod m)) = ((3 : ZMod m), (2 : ZMod m)) := by
  calc
    returnMap0CaseIIXY (m := m) ((1 : ZMod m), (0 : ZMod m))
        = toXY (m := m) (returnMap0CaseII (m := m) ((1 : ZMod m), (0 : ZMod m))) := by
            simp [returnMap0CaseIIXY, fromXY]
    _ = toXY (m := m) ((-1 : ZMod m), (2 : ZMod m)) := by rw [returnMap0CaseII_one_zero (m := m)]
    _ = ((3 : ZMod m), (2 : ZMod m)) := by
          ext <;> simp [toXY]
          ring_nf

theorem returnMap0CaseIIXY_zero_one [Fact (9 < m)] :
    returnMap0CaseIIXY (m := m) ((0 : ZMod m), (1 : ZMod m)) = ((1 : ZMod m), (2 : ZMod m)) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let pre : QCoord m := ((-2 : ZMod m), (1 : ZMod m))
  have hxy : fromXY (m := m) ((0 : ZMod m), (1 : ZMod m)) = pre := by
    ext <;> simp [pre, fromXY]
  have hdir : dir0CaseIILayerZero (m := m) pre = 0 := by
    simpa [pre] using dir0CaseIILayerZero_eq_zero_neg_two_one (m := m)
  have hi : pre.1 ≠ (-1 : ZMod m) := by
    intro h
    exact two_ne_one (m := m) (by simpa [pre] using congrArg Neg.neg h)
  have hsum0 : pre.1 + pre.2 ≠ 0 := by
    change (-2 : ZMod m) + (1 : ZMod m) ≠ 0
    intro h
    have : (1 : ZMod m) = 2 := by
      calc
        (1 : ZMod m) = ((-2 : ZMod m) + (1 : ZMod m)) + 2 := by ring
        _ = 0 + 2 := by rw [h]
        _ = 2 := by ring
    exact two_ne_one (m := m) this.symm
  have hret := returnMap0CaseII_of_dir0_generic (m := m) (u := pre) hdir hi hsum0
  calc
    returnMap0CaseIIXY (m := m) ((0 : ZMod m), (1 : ZMod m))
        = toXY (m := m) (returnMap0CaseII (m := m) (fromXY (m := m) ((0 : ZMod m), (1 : ZMod m)))) := by
            simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) pre) := by rw [hxy]
    _ = toXY (m := m) (pre.1 - 1, pre.2 + 1) := by
          simpa using congrArg (toXY (m := m)) hret
    _ = ((1 : ZMod m), (2 : ZMod m)) := by
          ext
          · change (-2 : ZMod m) - 1 + 2 * (1 + 1) = 1
            ring
          · change (1 : ZMod m) + 1 = 2
            ring

theorem returnMap0CaseIIXY_one_one [Fact (9 < m)] :
    returnMap0CaseIIXY (m := m) ((1 : ZMod m), (1 : ZMod m)) = ((0 : ZMod m), (1 : ZMod m)) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let pre : QCoord m := ((-1 : ZMod m), (1 : ZMod m))
  have hxy : fromXY (m := m) ((1 : ZMod m), (1 : ZMod m)) = pre := by
    ext <;> simp [pre, fromXY]
    ring_nf
  have hdir : dir0CaseIILayerZero (m := m) pre = 0 := by
    simpa [pre] using dir0CaseIILayerZero_eq_zero_neg_one_one (m := m)
  have h3 :
      (((fullMapColor0 (m := m) (dir0CaseIILayerZero (m := m)))^[3]) (slicePoint (0 : ZMod m) pre)) =
        (((1 : ZMod m), (1 : ZMod m)), (3 : ZMod m)) := by
    calc
      (((fullMapColor0 (m := m) (dir0CaseIILayerZero (m := m)))^[3]) (slicePoint (0 : ZMod m) pre))
          = (((fullMapColor0 (m := m) (dir0CaseIILayerZero (m := m)))^[2]) (((0 : ZMod m), (1 : ZMod m)), (1 : ZMod m))) := by
              rw [Function.iterate_succ_apply']
              simpa [pre] using congrArg
                (fun z => ((fullMapColor0 (m := m) (dir0CaseIILayerZero (m := m)))^[2]) z)
                (fullMapColor0_step_zero_of_dir0 (m := m)
                  (dir0 := dir0CaseIILayerZero (m := m)) hdir)
      _ = fullMapColor0 (m := m) (dir0CaseIILayerZero (m := m)) (((0 : ZMod m), (1 : ZMod m)), (2 : ZMod m)) := by
            rw [Function.iterate_succ_apply']
            simpa using congrArg
              (fullMapColor0 (m := m) (dir0CaseIILayerZero (m := m)))
              (fullMapColor0_step_one_of_i_zero (m := m)
                (dir0 := dir0CaseIILayerZero (m := m)) (k := (1 : ZMod m)))
      _ = (((1 : ZMod m), (1 : ZMod m)), (3 : ZMod m)) := by
            have hsum : (0 : ZMod m) + (1 : ZMod m) ≠ (2 : ZMod m) := by
              intro h
              exact two_ne_one (m := m) (by simpa using h.symm)
            calc
              fullMapColor0 (m := m) (dir0CaseIILayerZero (m := m)) (((0 : ZMod m), (1 : ZMod m)), (2 : ZMod m))
                  = ((((0 : ZMod m) + 1), (1 : ZMod m)), (3 : ZMod m)) := by
                      exact fullMapColor0_step_two_of_sum_ne_two (m := m)
                        (dir0 := dir0CaseIILayerZero (m := m))
                        (i := (0 : ZMod m)) (k := (1 : ZMod m)) hsum
              _ = (((1 : ZMod m), (1 : ZMod m)), (3 : ZMod m)) := by
                    ext <;> ring
  have hmain := iterate_m_fullMapColor0_of_three (m := m)
    (dir0 := dir0CaseIILayerZero (m := m)) (u := pre) (v := ((1 : ZMod m), (1 : ZMod m))) h3
  have hret :
      returnMap0CaseII (m := m) pre = ((-2 : ZMod m), (1 : ZMod m)) := by
    have hfst :
        returnMap0CaseII (m := m) pre = (((1 : ZMod m) - 3), (1 : ZMod m)) := by
      simpa [fullMap0CaseII, returnMap0CaseII, slicePoint, pre] using congrArg Prod.fst hmain
    calc
      returnMap0CaseII (m := m) pre = (((1 : ZMod m) - 3), (1 : ZMod m)) := hfst
      _ = ((-2 : ZMod m), (1 : ZMod m)) := by
            ext <;> ring
  calc
    returnMap0CaseIIXY (m := m) ((1 : ZMod m), (1 : ZMod m))
        = toXY (m := m) (returnMap0CaseII (m := m) (fromXY (m := m) ((1 : ZMod m), (1 : ZMod m)))) := by
            simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) pre) := by rw [hxy]
    _ = toXY (m := m) ((-2 : ZMod m), (1 : ZMod m)) := by rw [hret]
    _ = ((0 : ZMod m), (1 : ZMod m)) := by
          ext <;> simp [toXY]

theorem returnMap0CaseIIXY_one_column_lower_step [Fact (9 < m)] (hm : m % 12 = 10) {y : ℕ}
    (hy2 : 2 ≤ y) (hyle : y ≤ m / 2 - 1) :
    returnMap0CaseIIXY (m := m) ((1 : ZMod m), (((y : ℕ) : ZMod m))) =
      ((1 : ZMod m), (((y + 1 : ℕ) : ZMod m))) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let k : ZMod m := (((y : ℕ) : ZMod m))
  let i : ZMod m := (((m + 1 - 2 * y : ℕ) : ZMod m))
  have hylt : y < m := by omega
  have hilt : m + 1 - 2 * y < m := by
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rw [hq] at hyle ⊢
    omega
  have hipos : 0 < m + 1 - 2 * y := by
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rw [hq] at hyle ⊢
    omega
  have hitwo : 2 ≤ m + 1 - 2 * y := by
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rw [hq] at hyle ⊢
    omega
  have hxy : fromXY (m := m) ((1 : ZMod m), k) = (i, k) := by
    ext <;> simp [i, k, fromXY]
    · have hle : 2 * y ≤ m + 1 := by
        rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
        rw [hq] at hyle ⊢
        omega
      rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul]
      simp
  have hi0 : i ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := m + 1 - 2 * y) hipos hilt
  have hi1 : i ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := m + 1 - 2 * y) hitwo hilt
  have hk0 : k ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := y) (by omega) hylt
  have hk1 : k ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := y) hy2 hylt
  have hkneg1 : k ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := y) (by omega)
  have hkneg2 : k ≠ (-2 : ZMod m) := by
    exact natCast_ne_neg_two_of_lt (m := m) (n := y) (by omega)
  have hdir :
      dir0CaseIILayerZero (m := m) (i, k) = 1 :=
    dir0CaseIILayerZero_eq_one_of_generic (m := m) hi0 hi1 hk0 hk1 hkneg1 hkneg2
  have hi2k : i + 2 * k = (1 : ZMod m) := by
    have h := congrArg (fun u : P0Coord m => u.1 + 2 * u.2) hxy
    simpa [fromXY] using h.symm
  have hsum1 : i + k ≠ 1 := by
    intro h
    have hkzero : k = 0 := by
      calc
        k = (i + 2 * k) - (i + k) := by ring
        _ = (1 : ZMod m) - 1 := by rw [hi2k, h]
        _ = 0 := by ring
    exact hk0 hkzero
  have hret := returnMap0CaseII_of_dir1_generic (m := m) (u := (i, k)) hdir hi0 hsum1
  calc
    returnMap0CaseIIXY (m := m) ((1 : ZMod m), k)
        = toXY (m := m) (returnMap0CaseII (m := m) (fromXY (m := m) ((1 : ZMod m), k))) := by
            simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) (i, k)) := by rw [hxy]
    _ = toXY (m := m) (i - 2, k + 1) := by
          simpa using congrArg (toXY (m := m)) hret
    _ = ((1 : ZMod m), k + 1) := by
          ext
          · calc
              (i - 2) + 2 * (k + 1) = i + 2 * k := by ring
              _ = (1 : ZMod m) := hi2k
          · rfl
    _ = ((1 : ZMod m), (((y + 1 : ℕ) : ZMod m))) := by
          simp [k, Nat.cast_add]

theorem iterate_returnMap0CaseIIXY_one_column_lower_partial [Fact (9 < m)] (hm : m % 12 = 10)
    {t : ℕ} (ht : t ≤ m / 2 - 2) :
    ((returnMap0CaseIIXY (m := m)^[t]) ((1 : ZMod m), (2 : ZMod m))) =
      ((1 : ZMod m), (((2 + t : ℕ) : ZMod m))) := by
  induction t with
  | zero =>
      simp
  | succ t iht =>
      have ht' : t ≤ m / 2 - 2 := Nat.le_of_succ_le ht
      have hstep :
          returnMap0CaseIIXY (m := m) ((1 : ZMod m), (((2 + t : ℕ) : ZMod m))) =
            ((1 : ZMod m), (((2 + t + 1 : ℕ) : ZMod m))) := by
        have hy2 : 2 ≤ 2 + t := by omega
        have hyle : 2 + t ≤ m / 2 - 1 := by omega
        simpa [Nat.add_assoc] using
          returnMap0CaseIIXY_one_column_lower_step (m := m) hm (y := 2 + t) hy2 hyle
      calc
        ((returnMap0CaseIIXY (m := m)^[t.succ]) ((1 : ZMod m), (2 : ZMod m)))
            = returnMap0CaseIIXY (m := m)
                (((returnMap0CaseIIXY (m := m)^[t]) ((1 : ZMod m), (2 : ZMod m)))) := by
                    rw [Function.iterate_succ_apply']
        _ = returnMap0CaseIIXY (m := m) ((1 : ZMod m), (((2 + t : ℕ) : ZMod m))) := by
              rw [iht ht']
        _ = ((1 : ZMod m), (((2 + t + 1 : ℕ) : ZMod m))) := hstep
        _ = ((1 : ZMod m), (((2 + t.succ : ℕ) : ZMod m))) := by
              simp [Nat.succ_eq_add_one, Nat.add_assoc]

theorem returnMap0CaseIIXY_one_column_mid_step [Fact (9 < m)] (hm : m % 12 = 10) :
    returnMap0CaseIIXY (m := m) ((1 : ZMod m), (((m / 2 : ℕ) : ZMod m))) =
      ((3 : ZMod m), (((m / 2 + 2 : ℕ) : ZMod m))) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let pre : QCoord m := ((1 : ZMod m), (((m / 2 : ℕ) : ZMod m)))
  have hxy : fromXY (m := m) ((1 : ZMod m), (((m / 2 : ℕ) : ZMod m))) = pre := by
    ext <;> simp [pre, fromXY]
    · have htwo : 2 * (m / 2) = m := by
        rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
        rw [hq]
        omega
      have hhalf : (2 : ZMod m) * (((m / 2 : ℕ) : ZMod m)) = 0 := by
        calc
          (2 : ZMod m) * (((m / 2 : ℕ) : ZMod m))
              = (((2 * (m / 2) : ℕ) : ZMod m)) := by
                  simp [Nat.cast_mul]
          _ = (((m : ℕ) : ZMod m)) := by rw [htwo]
          _ = 0 := by simp
      simpa using hhalf
  have hkneg2 : (((m / 2 : ℕ) : ZMod m)) ≠ (-2 : ZMod m) := by
    exact natCast_ne_neg_two_of_lt (m := m) (n := m / 2) (by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega)
  have hdir :
      dir0CaseIILayerZero (m := m) pre = 2 := by
    simpa [pre] using dir0CaseIILayerZero_eq_two_of_i_one (m := m) (k := (((m / 2 : ℕ) : ZMod m))) hkneg2
  have hi0 : pre.1 ≠ 0 := by
    change (1 : ZMod m) ≠ 0
    exact one_ne_zero (m := m)
  have hsum0 : pre.1 + pre.2 ≠ 0 := by
    have hmhalf : m / 2 + 1 < m := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega
    simpa [pre, Nat.cast_add, add_comm] using
      natCast_ne_zero_of_pos_lt (m := m) (n := m / 2 + 1) (by omega) hmhalf
  have hret := returnMap0CaseII_of_dir2_i_ne_zero_generic (m := m) (u := pre) hdir hi0 hsum0
  calc
    returnMap0CaseIIXY (m := m) ((1 : ZMod m), (((m / 2 : ℕ) : ZMod m)))
        = toXY (m := m) (returnMap0CaseII (m := m) (fromXY (m := m) ((1 : ZMod m), (((m / 2 : ℕ) : ZMod m))))) := by
            simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) pre) := by rw [hxy]
    _ = toXY (m := m) (pre.1 - 2, pre.2 + 2) := by
          simpa using congrArg (toXY (m := m)) hret
    _ = ((3 : ZMod m), (((m / 2 + 2 : ℕ) : ZMod m))) := by
          have hhalf : (2 : ZMod m) * (((m / 2 : ℕ) : ZMod m)) = 0 := by
            calc
              (2 : ZMod m) * (((m / 2 : ℕ) : ZMod m))
                  = (((2 * (m / 2) : ℕ) : ZMod m)) := by
                      simp [Nat.cast_mul]
              _ = (((m : ℕ) : ZMod m)) := by
                    have htwo : 2 * (m / 2) = m := by
                      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
                      rw [hq]
                      omega
                    rw [htwo]
              _ = 0 := by simp
          ext
          · calc
              ((1 : ZMod m) - 2) + 2 * ((((m / 2 : ℕ) : ZMod m)) + 2) = (2 : ZMod m) * (((m / 2 : ℕ) : ZMod m)) + 3 := by ring
              _ = 3 := by rw [hhalf]; ring
          · simp [toXY, pre, Nat.cast_add]

theorem returnMap0CaseII_line_start_generic [Fact (9 < m)] {x : ℕ}
    (hx2 : 2 ≤ x) (hxle : x ≤ m - 3) :
    returnMap0CaseII (m := m) ((((x : ℕ) : ZMod m)), (0 : ZMod m)) =
      ((((x : ℕ) : ZMod m)) - 1, (1 : ZMod m)) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  have hxm : x < m := by omega
  have hxm1 : x + 1 < m := by omega
  have hxm2 : x + 2 < m := by omega
  have hxpos : 0 < x := by omega
  have hx0 : (((x : ℕ) : ZMod m)) ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := x) hxpos hxm
  have hx1 : (((x : ℕ) : ZMod m)) ≠ (1 : ZMod m) := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := x) hx2 hxm
  have hxneg2 : (((x : ℕ) : ZMod m)) ≠ (-2 : ZMod m) := by
    exact natCast_ne_neg_two_of_lt (m := m) (n := x) hxm2
  have hxneg1 : (((x : ℕ) : ZMod m)) ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := x) hxm1
  have hsum0 : (((x : ℕ) : ZMod m)) + (0 : ZMod m) ≠ 0 := by
    simpa using hx0
  have hdir := dir0CaseIILayerZero_eq_zero_of_k_zero_generic (m := m)
    (i := (((x : ℕ) : ZMod m))) hx0 hx1 hxneg2 hxneg1
  have h3 := iterate_three_fullMapColor0_of_dir0_generic (m := m)
    (dir0 := dir0CaseIILayerZero (m := m))
    (u := ((((x : ℕ) : ZMod m)), (0 : ZMod m))) hdir hxneg1 hsum0
  have h3' :
      (((fullMapColor0 (m := m) (dir0CaseIILayerZero (m := m)))^[3])
        (slicePoint (0 : ZMod m) ((((x : ℕ) : ZMod m)), (0 : ZMod m)))) =
        (((((x + 2 : ℕ) : ZMod m)), (1 : ZMod m)), (3 : ZMod m)) := by
    simpa [Nat.cast_add] using h3
  have hmain := iterate_m_fullMapColor0_of_three (m := m)
    (dir0 := dir0CaseIILayerZero (m := m))
    (u := ((((x : ℕ) : ZMod m)), (0 : ZMod m)))
    (v := ((((x + 2 : ℕ) : ZMod m)), (1 : ZMod m))) h3'
  have hfst :
      returnMap0CaseII (m := m) ((((x : ℕ) : ZMod m)), (0 : ZMod m)) =
        (((((x + 2 : ℕ) : ZMod m)) - 3), (1 : ZMod m)) := by
    simpa [fullMap0CaseII, returnMap0CaseII, slicePoint, Nat.cast_add] using congrArg Prod.fst hmain
  calc
    returnMap0CaseII (m := m) ((((x : ℕ) : ZMod m)), (0 : ZMod m))
        = (((((x + 2 : ℕ) : ZMod m)) - 3), (1 : ZMod m)) := hfst
    _ = ((((x : ℕ) : ZMod m)) - 1, (1 : ZMod m)) := by
          ext
          · simp [Nat.cast_add]
            ring
          · rfl

theorem returnMap0CaseIIXY_line_start_generic [Fact (9 < m)] {x : ℕ}
    (hx2 : 2 ≤ x) (hxle : x ≤ m - 3) :
    returnMap0CaseIIXY (m := m) ((((x : ℕ) : ZMod m)), (0 : ZMod m)) =
      ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m)) := by
  calc
    returnMap0CaseIIXY (m := m) ((((x : ℕ) : ZMod m)), (0 : ZMod m))
        = toXY (m := m) (returnMap0CaseII (m := m) ((((x : ℕ) : ZMod m)), (0 : ZMod m))) := by
            simp [returnMap0CaseIIXY, fromXY]
    _ = toXY (m := m) ((((x : ℕ) : ZMod m)) - 1, (1 : ZMod m)) := by
          rw [returnMap0CaseII_line_start_generic (m := m) hx2 hxle]
    _ = ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m)) := by
          ext <;> simp [toXY, Nat.cast_add]
          ring_nf

theorem returnMap0CaseIIXY_R_line [Fact (9 < m)] {y : ℕ}
    (hy : y ≤ m - 3) :
    returnMap0CaseIIXY (m := m) ((((1 + 2 * y : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))) =
      ((((3 + 2 * y : ℕ) : ZMod m)), (((y + 2 : ℕ) : ZMod m))) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  have hym : y < m := by omega
  have hyNotNeg2 : (((y : ℕ) : ZMod m)) ≠ (-2 : ZMod m) := by
    have hy2 : y + 2 < m := by omega
    exact natCast_ne_neg_two_of_lt (m := m) (n := y) hy2
  have hdir :
      dir0CaseIILayerZero (m := m) ((1 : ZMod m), (((y : ℕ) : ZMod m))) = 2 :=
    dir0CaseIILayerZero_eq_two_of_i_one (m := m) (k := (((y : ℕ) : ZMod m))) hyNotNeg2
  have hsum0 : (1 : ZMod m) + (((y : ℕ) : ZMod m)) ≠ 0 := by
    have hy1lt : y + 1 < m := by omega
    simpa [Nat.cast_add, add_comm] using
      natCast_ne_zero_of_pos_lt (m := m) (n := y + 1) (by omega) hy1lt
  have h3 := iterate_three_fullMapColor0_of_dir2_i_ne_zero_generic (m := m)
    (dir0 := dir0CaseIILayerZero (m := m)) (u := ((1 : ZMod m), (((y : ℕ) : ZMod m))))
    hdir (one_ne_zero (m := m)) hsum0
  have h3' :
      (((fullMapColor0 (m := m) (dir0CaseIILayerZero (m := m)))^[3])
        (slicePoint (0 : ZMod m) ((1 : ZMod m), (((y : ℕ) : ZMod m))))) =
        (((2 : ZMod m), (((y + 2 : ℕ) : ZMod m))), (3 : ZMod m)) := by
    calc
      (((fullMapColor0 (m := m) (dir0CaseIILayerZero (m := m)))^[3])
        (slicePoint (0 : ZMod m) ((1 : ZMod m), (((y : ℕ) : ZMod m)))))
          = (((1 : ZMod m) + 1, (((y + 2 : ℕ) : ZMod m))), (3 : ZMod m)) := by
              simpa [Nat.cast_add, two_mul] using h3
      _ = (((2 : ZMod m), (((y + 2 : ℕ) : ZMod m))), (3 : ZMod m)) := by
            ext <;> ring
  have hmain := iterate_m_fullMapColor0_of_three (m := m)
    (dir0 := dir0CaseIILayerZero (m := m))
    (u := ((1 : ZMod m), (((y : ℕ) : ZMod m))))
    (v := ((2 : ZMod m), (((y + 2 : ℕ) : ZMod m)))) h3'
  have hfst :
      returnMap0CaseII (m := m) ((1 : ZMod m), (((y : ℕ) : ZMod m))) =
        (((2 : ZMod m) - 3), (((y + 2 : ℕ) : ZMod m))) := by
    simpa [fullMap0CaseII, returnMap0CaseII, slicePoint, Nat.cast_add, two_mul] using congrArg Prod.fst hmain
  calc
    returnMap0CaseIIXY (m := m) ((((1 + 2 * y : ℕ) : ZMod m)), (((y : ℕ) : ZMod m)))
        = toXY (m := m) (returnMap0CaseII (m := m) ((1 : ZMod m), (((y : ℕ) : ZMod m)))) := by
            simp [returnMap0CaseIIXY, fromXY, Nat.cast_add, two_mul]
    _ = toXY (m := m) (((2 : ZMod m) - 3), (((y + 2 : ℕ) : ZMod m))) := by rw [hfst]
    _ = ((((3 + 2 * y : ℕ) : ZMod m)), (((y + 2 : ℕ) : ZMod m))) := by
          ext <;> simp [toXY, Nat.cast_add, two_mul]
          all_goals ring_nf

theorem returnMap0CaseIIXY_two_one [Fact (9 < m)] :
    returnMap0CaseIIXY (m := m) ((2 : ZMod m), (1 : ZMod m)) = ((3 : ZMod m), (3 : ZMod m)) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  have hdir : dir0CaseIILayerZero (m := m) ((0 : ZMod m), (1 : ZMod m)) = 2 := by
    have h1ne0 : (1 : ZMod m) ≠ 0 := one_ne_zero (m := m)
    have h1neneg1 : (1 : ZMod m) ≠ (-1 : ZMod m) := by
      intro h
      exact one_ne_neg_one (m := m) h
    exact dir0CaseIILayerZero_eq_two_of_i_zero (m := m) (k := (1 : ZMod m)) h1ne0 h1neneg1
  have h3 := iterate_three_fullMapColor0_of_dir2_i_zero_eq_one (m := m)
    (dir0 := dir0CaseIILayerZero (m := m)) hdir
  have hmain := iterate_m_fullMapColor0_of_three (m := m)
    (dir0 := dir0CaseIILayerZero (m := m))
    (u := ((0 : ZMod m), (1 : ZMod m)))
    (v := ((0 : ZMod m), (3 : ZMod m))) h3
  have hfst :
      returnMap0CaseII (m := m) ((0 : ZMod m), (1 : ZMod m)) =
        ((-3 : ZMod m), (3 : ZMod m)) := by
    simpa [fullMap0CaseII, returnMap0CaseII, slicePoint] using congrArg Prod.fst hmain
  calc
    returnMap0CaseIIXY (m := m) ((2 : ZMod m), (1 : ZMod m))
        = toXY (m := m) (returnMap0CaseII (m := m) ((0 : ZMod m), (1 : ZMod m))) := by
            simp [returnMap0CaseIIXY, fromXY, toXY]
    _ = toXY (m := m) ((-3 : ZMod m), (3 : ZMod m)) := by rw [hfst]
    _ = ((3 : ZMod m), (3 : ZMod m)) := by
          ext <;> simp [toXY]
          all_goals ring_nf

theorem returnMap0CaseIIXY_three_two [Fact (9 < m)] :
    returnMap0CaseIIXY (m := m) ((3 : ZMod m), (2 : ZMod m)) = ((4 : ZMod m), (4 : ZMod m)) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  have hneg1_ne_zero : (-1 : ZMod m) ≠ 0 := neg_ne_zero.mpr (one_ne_zero (m := m))
  have hdir : dir0CaseIILayerZero (m := m) ((-1 : ZMod m), (2 : ZMod m)) = 1 := by
    have h2ne0 : (2 : ZMod m) ≠ 0 := two_ne_zero (m := m)
    have h2neneg1 : (2 : ZMod m) ≠ (-1 : ZMod m) :=
      natCast_ne_neg_one_of_lt (m := m) (n := 2) (by omega)
    have h2neneg2 : (2 : ZMod m) ≠ (-2 : ZMod m) :=
      natCast_ne_neg_two_of_lt (m := m) (n := 2) (by omega)
    have hneg1_ne_one : (-1 : ZMod m) ≠ (1 : ZMod m) := by
      intro h
      exact one_ne_neg_one (m := m) h.symm
    have hneg1_ne_neg2 : (-1 : ZMod m) ≠ (-2 : ZMod m) := by
      intro h
      have h' : (1 : ZMod m) = 0 := by
        calc
          (1 : ZMod m) = (-1 : ZMod m) + (2 : ZMod m) := by ring
          _ = (-2 : ZMod m) + (2 : ZMod m) := by rw [h]
          _ = 0 := by ring
      exact one_ne_zero (m := m) h'
    have h2ne1 : (2 : ZMod m) ≠ (1 : ZMod m) := two_ne_one (m := m)
    simp [dir0CaseIILayerZero, h2ne0, h2neneg1, h2neneg2, hneg1_ne_zero,
      hneg1_ne_one, hneg1_ne_neg2, h2ne1]
  have hsum1 : (-1 : ZMod m) + (2 : ZMod m) = 1 := by ring
  have h3 := iterate_three_fullMapColor0_of_dir1_sum_one (m := m)
    (dir0 := dir0CaseIILayerZero (m := m)) (u := ((-1 : ZMod m), (2 : ZMod m)))
    hdir hneg1_ne_zero hsum1
  have h3' :
      (((fullMapColor0 (m := m) (dir0CaseIILayerZero (m := m)))^[3])
        (slicePoint (0 : ZMod m) ((-1 : ZMod m), (2 : ZMod m)))) =
        (((-1 : ZMod m), (4 : ZMod m)), (3 : ZMod m)) := by
    calc
      (((fullMapColor0 (m := m) (dir0CaseIILayerZero (m := m)))^[3])
        (slicePoint (0 : ZMod m) ((-1 : ZMod m), (2 : ZMod m))))
          = (((-1 : ZMod m), (2 : ZMod m) + 2), (3 : ZMod m)) := by
              simpa using h3
      _ = (((-1 : ZMod m), (4 : ZMod m)), (3 : ZMod m)) := by
            ext <;> ring
  have hmain := iterate_m_fullMapColor0_of_three (m := m)
    (dir0 := dir0CaseIILayerZero (m := m))
    (u := ((-1 : ZMod m), (2 : ZMod m)))
    (v := ((-1 : ZMod m), (4 : ZMod m))) h3'
  have hfst :
      returnMap0CaseII (m := m) ((-1 : ZMod m), (2 : ZMod m)) =
        (((-1 : ZMod m) - 3), (4 : ZMod m)) := by
    simpa [fullMap0CaseII, returnMap0CaseII, slicePoint] using congrArg Prod.fst hmain
  calc
    returnMap0CaseIIXY (m := m) ((3 : ZMod m), (2 : ZMod m))
        = toXY (m := m) (returnMap0CaseII (m := m) ((-1 : ZMod m), (2 : ZMod m))) := by
            have hxy : fromXY (m := m) ((3 : ZMod m), (2 : ZMod m)) =
                ((-1 : ZMod m), (2 : ZMod m)) := by
              ext <;> simp [fromXY]
              all_goals ring
            simp [returnMap0CaseIIXY, hxy]
    _ = toXY (m := m) (((-1 : ZMod m) - 3), (4 : ZMod m)) := by rw [hfst]
    _ = ((4 : ZMod m), (4 : ZMod m)) := by
          ext <;> simp [toXY]
          all_goals ring_nf

theorem returnMap0CaseIIXY_five_three [Fact (9 < m)] :
    returnMap0CaseIIXY (m := m) ((5 : ZMod m), (3 : ZMod m)) = ((5 : ZMod m), (4 : ZMod m)) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let preG : QCoord m := ((-1 : ZMod m), (3 : ZMod m))
  have hxy : fromXY (m := m) ((5 : ZMod m), (3 : ZMod m)) = preG := by
    ext <;> simp [preG, fromXY]
    all_goals ring_nf
  have hi0 : preG.1 ≠ 0 := by
    exact neg_ne_zero.mpr (one_ne_zero (m := m))
  have hi1 : preG.1 ≠ 1 := by
    intro h
    exact one_ne_neg_one (m := m) h.symm
  have hk0 : preG.2 ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := 3) (by omega) (by omega)
  have hk1 : preG.2 ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := 3) (by omega) (by omega)
  have hkneg1 : preG.2 ≠ (-1 : ZMod m) := by
    have hm9 : 9 < m := Fact.out
    exact natCast_ne_neg_one_of_lt (m := m) (n := 3) (by omega)
  have hkneg2 : preG.2 ≠ (-2 : ZMod m) := by
    have hm9 : 9 < m := Fact.out
    exact natCast_ne_neg_two_of_lt (m := m) (n := 3) (by omega)
  have hdir :
      dir0CaseIILayerZero (m := m) preG = 1 :=
    dir0CaseIILayerZero_eq_one_of_generic (m := m) hi0 hi1 hk0 hk1 hkneg1 hkneg2
  have htwo : preG.1 + preG.2 = (2 : ZMod m) := by
    change (-1 : ZMod m) + (3 : ZMod m) = (2 : ZMod m)
    ring
  have hsum1 : preG.1 + preG.2 ≠ 1 := by
    intro h
    have : (2 : ZMod m) = 1 := by rw [← htwo, h]
    exact two_ne_one (m := m) this
  have hret := returnMap0CaseII_of_dir1_generic (m := m) (u := preG) hdir hi0 hsum1
  calc
    returnMap0CaseIIXY (m := m) ((5 : ZMod m), (3 : ZMod m))
        = toXY (m := m) (returnMap0CaseII (m := m) (fromXY (m := m) ((5 : ZMod m), (3 : ZMod m)))) := by
            simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) preG) := by rw [hxy]
    _ = toXY (m := m) (returnMap0CaseII (m := m) preG) := by rfl
    _ = toXY (m := m) (preG.1 - 2, preG.2 + 1) := by
          simpa using congrArg (toXY (m := m)) hret
    _ = ((5 : ZMod m), (4 : ZMod m)) := by
          ext <;> simp [toXY, preG]
          all_goals ring_nf

theorem returnMap0CaseIIXY_five_four [Fact (9 < m)] :
    returnMap0CaseIIXY (m := m) ((5 : ZMod m), (4 : ZMod m)) = ((6 : ZMod m), (6 : ZMod m)) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let preA : QCoord m := ((-3 : ZMod m), (4 : ZMod m))
  have hneg3 : (((m - 3 : ℕ) : ZMod m)) = (-3 : ZMod m) := by
    have hm3 : 3 ≤ m := by omega
    calc
      (((m - 3 : ℕ) : ZMod m)) = (((m : ℕ) : ZMod m) - (3 : ZMod m)) := by
        rw [Nat.cast_sub hm3]
        simp
      _ = (-3 : ZMod m) := by simp
  have hxy : fromXY (m := m) ((5 : ZMod m), (4 : ZMod m)) = preA := by
    ext <;> simp [preA, fromXY]
    all_goals ring_nf
  have h3ne0 : (3 : ZMod m) ≠ 0 :=
    natCast_ne_zero_of_pos_lt (m := m) (n := 3) (by omega) (by omega)
  have hi0 : preA.1 ≠ 0 := by
    exact neg_ne_zero.mpr h3ne0
  have hi1 : preA.1 ≠ 1 := by
    intro h
    have h4ne0 : (4 : ZMod m) ≠ 0 :=
      natCast_ne_zero_of_pos_lt (m := m) (n := 4) (by omega) (by omega)
    have : (4 : ZMod m) = 0 := by
      calc
        (4 : ZMod m) = (1 : ZMod m) - (-3 : ZMod m) := by ring
        _ = 0 := by rw [← h]; ring
    exact h4ne0 this
  have hk0 : preA.2 ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := 4) (by omega) (by omega)
  have hk1 : preA.2 ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := 4) (by omega) (by omega)
  have hkneg1 : preA.2 ≠ (-1 : ZMod m) := by
    have hm9 : 9 < m := Fact.out
    exact natCast_ne_neg_one_of_lt (m := m) (n := 4) (by omega)
  have hkneg2 : preA.2 ≠ (-2 : ZMod m) := by
    have hm9 : 9 < m := Fact.out
    exact natCast_ne_neg_two_of_lt (m := m) (n := 4) (by omega)
  have hdir :
      dir0CaseIILayerZero (m := m) preA = 1 :=
    dir0CaseIILayerZero_eq_one_of_generic (m := m) hi0 hi1 hk0 hk1 hkneg1 hkneg2
  have hsum1 : preA.1 + preA.2 = 1 := by
    change (-3 : ZMod m) + (4 : ZMod m) = (1 : ZMod m)
    ring
  have hret := returnMap0CaseII_of_dir1_sum_one (m := m) (u := preA) hdir hi0 hsum1
  calc
    returnMap0CaseIIXY (m := m) ((5 : ZMod m), (4 : ZMod m))
        = toXY (m := m) (returnMap0CaseII (m := m) (fromXY (m := m) ((5 : ZMod m), (4 : ZMod m)))) := by
            simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) preA) := by rw [hxy]
    _ = toXY (m := m) (preA.1 - 3, preA.2 + 2) := by
          simpa using congrArg (toXY (m := m)) hret
    _ = ((6 : ZMod m), (6 : ZMod m)) := by
          ext <;> simp [toXY, preA]
          all_goals ring_nf

theorem fromXY_four_column_lower [Fact (9 < m)] (hm : m % 12 = 10) {y : ℕ}
    (_hy4 : 4 ≤ y) (hyle : y ≤ m / 2 + 1) :
    fromXY (m := m) ((4 : ZMod m), (((y : ℕ) : ZMod m))) =
      ((((m + 4 - 2 * y : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))) := by
  ext <;> simp [fromXY]
  · have hle : 2 * y ≤ m + 4 := by omega
    rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul]
    simp

theorem fromXY_four_column_mid [Fact (9 < m)] (hm : m % 12 = 10) :
    fromXY (m := m) ((4 : ZMod m), (((m / 2 + 2 : ℕ) : ZMod m))) =
      ((0 : ZMod m), (((m / 2 + 2 : ℕ) : ZMod m))) := by
  ext <;> simp [fromXY]
  · have h2k : (2 : ZMod m) * (((m / 2 + 2 : ℕ) : ZMod m)) = (4 : ZMod m) := by
      calc
        (2 : ZMod m) * (((m / 2 + 2 : ℕ) : ZMod m))
            = (((2 * (m / 2 + 2) : ℕ) : ZMod m)) := by
                simp [Nat.cast_mul]
        _ = (((m + 4 : ℕ) : ZMod m)) := by
              have hmid : 2 * (m / 2 + 2) = m + 4 := by omega
              rw [hmid]
        _ = (4 : ZMod m) := by
              simp [Nat.cast_add]
    simpa [Nat.cast_add, Nat.cast_mul] using h2k.symm

theorem fromXY_four_column_upper [Fact (9 < m)] (hm : m % 12 = 10) {y : ℕ}
    (_hymid : m / 2 + 3 ≤ y) (hyle : y ≤ m - 1) :
    fromXY (m := m) ((4 : ZMod m), (((y : ℕ) : ZMod m))) =
      ((((2 * m + 4 - 2 * y : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))) := by
  ext <;> simp [fromXY]
  · have hle : 2 * y ≤ 2 * m + 4 := by omega
    rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul]
    simp

theorem returnMap0CaseIIXY_four_column_mid_step [Fact (9 < m)] (hm : m % 12 = 10) :
    returnMap0CaseIIXY (m := m) ((4 : ZMod m), (((m / 2 + 2 : ℕ) : ZMod m))) =
      ((4 : ZMod m), (((m / 2 + 3 : ℕ) : ZMod m))) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let midK : ZMod m := (((m / 2 + 2 : ℕ) : ZMod m))
  have hxy : fromXY (m := m) ((4 : ZMod m), midK) = ((0 : ZMod m), midK) := by
    simpa [midK] using fromXY_four_column_mid (m := m) hm
  have hmid_lt : m / 2 + 2 < m := by omega
  have hmid_ne_zero : midK ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := m / 2 + 2) (by omega) hmid_lt
  have hmid_ne_neg_one : midK ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := m / 2 + 2) (by omega)
  have hdir :
      dir0CaseIILayerZero (m := m) ((0 : ZMod m), midK) = 2 :=
    dir0CaseIILayerZero_eq_two_of_i_zero (m := m) hmid_ne_zero hmid_ne_neg_one
  have hmid_ne_one : midK ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := m / 2 + 2) (by omega) hmid_lt
  have hret := returnMap0CaseII_of_dir2_i_zero_generic (m := m) (k := midK) hdir hmid_ne_one
  have h2k : 2 * midK = (4 : ZMod m) := by
    change (2 : ZMod m) * (((m / 2 + 2 : ℕ) : ZMod m)) = (4 : ZMod m)
    calc
      (2 : ZMod m) * (((m / 2 + 2 : ℕ) : ZMod m))
          = (((2 * (m / 2 + 2) : ℕ) : ZMod m)) := by
              simp [Nat.cast_mul]
      _ = (((m + 4 : ℕ) : ZMod m)) := by
        have hmid : 2 * (m / 2 + 2) = m + 4 := by omega
        rw [hmid]
      _ = (4 : ZMod m) := by
        simp [Nat.cast_add]
  calc
    returnMap0CaseIIXY (m := m) ((4 : ZMod m), midK)
        = toXY (m := m) (returnMap0CaseII (m := m) ((0 : ZMod m), midK)) := by
            simp [returnMap0CaseIIXY, hxy]
    _ = toXY (m := m) ((-2 : ZMod m), midK + 1) := by rw [hret]
    _ = ((4 : ZMod m), midK + 1) := by
          have h2k' : midK * 2 = (4 : ZMod m) := by simpa [mul_comm] using h2k
          ext
          · calc
              (-2 : ZMod m) + 2 * (midK + 1) = midK * 2 := by ring
              _ = (4 : ZMod m) := h2k'
          · rfl
    _ = ((4 : ZMod m), (((m / 2 + 3 : ℕ) : ZMod m))) := by
          change ((4 : ZMod m), ((((m / 2 + 2 : ℕ) : ZMod m)) + 1)) =
            ((4 : ZMod m), (((m / 2 + 3 : ℕ) : ZMod m)))
          ext
          · rfl
          · simp [Nat.cast_add]
            ring_nf

theorem returnMap0CaseIIXY_four_column_lower_step [Fact (9 < m)] (hm : m % 12 = 10) {y : ℕ}
    (hy4 : 4 ≤ y) (hyle : y ≤ m / 2 + 1) :
    returnMap0CaseIIXY (m := m) ((4 : ZMod m), (((y : ℕ) : ZMod m))) =
      ((4 : ZMod m), (((y + 1 : ℕ) : ZMod m))) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let k : ZMod m := (((y : ℕ) : ZMod m))
  let i : ZMod m := (((m + 4 - 2 * y : ℕ) : ZMod m))
  have hylt : y < m := by omega
  have hilt : m + 4 - 2 * y < m := by omega
  have hipos : 0 < m + 4 - 2 * y := by omega
  have hitwo : 2 ≤ m + 4 - 2 * y := by omega
  have hxy : fromXY (m := m) ((4 : ZMod m), k) = (i, k) := by
    simpa [i, k] using fromXY_four_column_lower (m := m) hm (y := y) hy4 hyle
  have hi0 : i ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := m + 4 - 2 * y) hipos hilt
  have hi1 : i ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := m + 4 - 2 * y) hitwo hilt
  have hk0 : k ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := y) (by omega) hylt
  have hk1 : k ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := y) (by omega) hylt
  have hkneg1 : k ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := y) (by omega)
  have hkneg2 : k ≠ (-2 : ZMod m) := by
    exact natCast_ne_neg_two_of_lt (m := m) (n := y) (by omega)
  have hdir :
      dir0CaseIILayerZero (m := m) (i, k) = 1 :=
    dir0CaseIILayerZero_eq_one_of_generic (m := m) hi0 hi1 hk0 hk1 hkneg1 hkneg2
  have hi2k : i + 2 * k = (4 : ZMod m) := by
    have h := congrArg (fun u : P0Coord m => u.1 + 2 * u.2) hxy
    simpa [fromXY] using h.symm
  have hsum1 : i + k ≠ 1 := by
    intro h
    have hk3 : k = (3 : ZMod m) := by
      calc
        k = (i + 2 * k) - (i + k) := by ring
        _ = (4 : ZMod m) - 1 := by rw [hi2k, h]
        _ = (3 : ZMod m) := by ring
    have hcast : (((y : ℕ) : ZMod m)) = (3 : ZMod m) := by simpa [k] using hk3
    have hmod := (ZMod.natCast_eq_natCast_iff' y 3 m).1 hcast
    have h3lt : 3 < m := by omega
    rw [Nat.mod_eq_of_lt hylt, Nat.mod_eq_of_lt h3lt] at hmod
    omega
  have hret := returnMap0CaseII_of_dir1_generic (m := m) (u := (i, k)) hdir hi0 hsum1
  calc
    returnMap0CaseIIXY (m := m) ((4 : ZMod m), k)
        = toXY (m := m) (returnMap0CaseII (m := m) (i, k)) := by
            simp [returnMap0CaseIIXY, hxy]
    _ = toXY (m := m) (i - 2, k + 1) := by rw [hret]
    _ = ((4 : ZMod m), k + 1) := by
          ext
          · calc
              (i - 2) + 2 * (k + 1) = i + 2 * k := by ring
              _ = (4 : ZMod m) := hi2k
          · rfl
    _ = ((4 : ZMod m), (((y + 1 : ℕ) : ZMod m))) := by
          simp [k, Nat.cast_add]

theorem returnMap0CaseIIXY_four_column_upper_step [Fact (9 < m)] (hm : m % 12 = 10) {y : ℕ}
    (hymid : m / 2 + 3 ≤ y) (hyle : y ≤ m - 3) :
    returnMap0CaseIIXY (m := m) ((4 : ZMod m), (((y : ℕ) : ZMod m))) =
      ((4 : ZMod m), (((y + 1 : ℕ) : ZMod m))) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let k : ZMod m := (((y : ℕ) : ZMod m))
  let i : ZMod m := (((2 * m + 4 - 2 * y : ℕ) : ZMod m))
  have hylt : y < m := by omega
  have hilt : 2 * m + 4 - 2 * y < m := by omega
  have hipos : 0 < 2 * m + 4 - 2 * y := by omega
  have hitwo : 2 ≤ 2 * m + 4 - 2 * y := by omega
  have hxy : fromXY (m := m) ((4 : ZMod m), k) = (i, k) := by
    simpa [i, k] using fromXY_four_column_upper (m := m) hm (y := y) hymid (by omega)
  have hi0 : i ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := 2 * m + 4 - 2 * y) hipos hilt
  have hi1 : i ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := 2 * m + 4 - 2 * y) hitwo hilt
  have hk0 : k ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := y) (by omega) hylt
  have hk1 : k ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := y) (by omega) hylt
  have hkneg1 : k ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := y) (by omega)
  have hkneg2 : k ≠ (-2 : ZMod m) := by
    exact natCast_ne_neg_two_of_lt (m := m) (n := y) (by omega)
  have hdir :
      dir0CaseIILayerZero (m := m) (i, k) = 1 :=
    dir0CaseIILayerZero_eq_one_of_generic (m := m) hi0 hi1 hk0 hk1 hkneg1 hkneg2
  have hi2k : i + 2 * k = (4 : ZMod m) := by
    have h := congrArg (fun u : P0Coord m => u.1 + 2 * u.2) hxy
    simpa [fromXY] using h.symm
  have hsum1 : i + k ≠ 1 := by
    intro h
    have hk3 : k = (3 : ZMod m) := by
      calc
        k = (i + 2 * k) - (i + k) := by ring
        _ = (4 : ZMod m) - 1 := by rw [hi2k, h]
        _ = (3 : ZMod m) := by ring
    have hcast : (((y : ℕ) : ZMod m)) = (3 : ZMod m) := by simpa [k] using hk3
    have hmod := (ZMod.natCast_eq_natCast_iff' y 3 m).1 hcast
    have h3lt : 3 < m := by omega
    rw [Nat.mod_eq_of_lt hylt, Nat.mod_eq_of_lt h3lt] at hmod
    omega
  have hret := returnMap0CaseII_of_dir1_generic (m := m) (u := (i, k)) hdir hi0 hsum1
  calc
    returnMap0CaseIIXY (m := m) ((4 : ZMod m), k)
        = toXY (m := m) (returnMap0CaseII (m := m) (i, k)) := by
            simp [returnMap0CaseIIXY, hxy]
    _ = toXY (m := m) (i - 2, k + 1) := by rw [hret]
    _ = ((4 : ZMod m), k + 1) := by
          ext
          · calc
              (i - 2) + 2 * (k + 1) = i + 2 * k := by ring
              _ = (4 : ZMod m) := hi2k
          · rfl
    _ = ((4 : ZMod m), (((y + 1 : ℕ) : ZMod m))) := by
          simp [k, Nat.cast_add]

theorem iterate_returnMap0CaseIIXY_four_column_lower_partial [Fact (9 < m)] (hm : m % 12 = 10)
    {t : ℕ} (ht : t ≤ m / 2 - 2) :
    ((returnMap0CaseIIXY (m := m)^[t]) ((4 : ZMod m), (4 : ZMod m))) =
      ((4 : ZMod m), (((4 + t : ℕ) : ZMod m))) := by
  induction t with
  | zero =>
      simp
  | succ t iht =>
      have ht' : t ≤ m / 2 - 2 := Nat.le_of_succ_le ht
      have hstep :
          returnMap0CaseIIXY (m := m) ((4 : ZMod m), (((4 + t : ℕ) : ZMod m))) =
            ((4 : ZMod m), (((4 + t + 1 : ℕ) : ZMod m))) := by
        have hy4 : 4 ≤ 4 + t := by omega
        have hyle : 4 + t ≤ m / 2 + 1 := by omega
        simpa [Nat.add_assoc] using
          returnMap0CaseIIXY_four_column_lower_step (m := m) hm (y := 4 + t) hy4 hyle
      calc
        ((returnMap0CaseIIXY (m := m)^[t.succ]) ((4 : ZMod m), (4 : ZMod m)))
            = returnMap0CaseIIXY (m := m)
                (((returnMap0CaseIIXY (m := m)^[t]) ((4 : ZMod m), (4 : ZMod m)))) := by
                    rw [Function.iterate_succ_apply']
        _ = returnMap0CaseIIXY (m := m) ((4 : ZMod m), (((4 + t : ℕ) : ZMod m))) := by rw [iht ht']
        _ = ((4 : ZMod m), (((4 + t + 1 : ℕ) : ZMod m))) := hstep
        _ = ((4 : ZMod m), (((4 + t.succ : ℕ) : ZMod m))) := by
              simp [Nat.succ_eq_add_one, Nat.add_assoc]

theorem iterate_returnMap0CaseIIXY_four_column_to_upper_start [Fact (9 < m)] (hm : m % 12 = 10) :
    ((returnMap0CaseIIXY (m := m)^[m / 2 - 1]) ((4 : ZMod m), (4 : ZMod m))) =
      ((4 : ZMod m), (((m / 2 + 3 : ℕ) : ZMod m))) := by
  have hm2 : 2 ≤ m / 2 := by
    have hm9 : 9 < m := Fact.out
    omega
  calc
    ((returnMap0CaseIIXY (m := m)^[m / 2 - 1]) ((4 : ZMod m), (4 : ZMod m)))
        = returnMap0CaseIIXY (m := m)
            (((returnMap0CaseIIXY (m := m)^[m / 2 - 2]) ((4 : ZMod m), (4 : ZMod m)))) := by
                rw [show m / 2 - 1 = (m / 2 - 2) + 1 by omega, Function.iterate_succ_apply']
    _ = returnMap0CaseIIXY (m := m) ((4 : ZMod m), (((m / 2 + 2 : ℕ) : ZMod m))) := by
          rw [iterate_returnMap0CaseIIXY_four_column_lower_partial (m := m) hm
            (t := m / 2 - 2) le_rfl]
          have hsum : 4 + (m / 2 - 2) = m / 2 + 2 := by omega
          simp [hsum]
    _ = ((4 : ZMod m), (((m / 2 + 3 : ℕ) : ZMod m))) := by
          exact returnMap0CaseIIXY_four_column_mid_step (m := m) hm

theorem iterate_returnMap0CaseIIXY_four_column_upper_partial [Fact (9 < m)] (hm : m % 12 = 10)
    {t : ℕ} (ht : t ≤ m / 2 - 5) :
    ((returnMap0CaseIIXY (m := m)^[t]) ((4 : ZMod m), (((m / 2 + 3 : ℕ) : ZMod m)))) =
      ((4 : ZMod m), (((m / 2 + 3 + t : ℕ) : ZMod m))) := by
  induction t with
  | zero =>
      simp
  | succ t iht =>
      have ht' : t ≤ m / 2 - 5 := Nat.le_of_succ_le ht
      have hstep :
          returnMap0CaseIIXY (m := m) ((4 : ZMod m), (((m / 2 + 3 + t : ℕ) : ZMod m))) =
            ((4 : ZMod m), (((m / 2 + 3 + t + 1 : ℕ) : ZMod m))) := by
        have hymid : m / 2 + 3 ≤ m / 2 + 3 + t := by omega
        have hyle : m / 2 + 3 + t ≤ m - 3 := by omega
        simpa [Nat.add_assoc] using
          returnMap0CaseIIXY_four_column_upper_step (m := m) hm
            (y := m / 2 + 3 + t) hymid hyle
      calc
        ((returnMap0CaseIIXY (m := m)^[t.succ]) ((4 : ZMod m), (((m / 2 + 3 : ℕ) : ZMod m))))
            = returnMap0CaseIIXY (m := m)
                (((returnMap0CaseIIXY (m := m)^[t]) ((4 : ZMod m), (((m / 2 + 3 : ℕ) : ZMod m))))) := by
                    rw [Function.iterate_succ_apply']
        _ = returnMap0CaseIIXY (m := m) ((4 : ZMod m), (((m / 2 + 3 + t : ℕ) : ZMod m))) := by
              rw [iht ht']
        _ = ((4 : ZMod m), (((m / 2 + 3 + t + 1 : ℕ) : ZMod m))) := hstep
        _ = ((4 : ZMod m), (((m / 2 + 3 + t.succ : ℕ) : ZMod m))) := by
              simp [Nat.succ_eq_add_one, Nat.add_assoc]

theorem returnMap0CaseIIXY_four_column_m_sub_two [Fact (9 < m)] (hm : m % 12 = 10) :
    returnMap0CaseIIXY (m := m) ((4 : ZMod m), (((m - 2 : ℕ) : ZMod m))) =
      ((4 : ZMod m), (((m - 1 : ℕ) : ZMod m))) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let preTop : QCoord m := ((((8 : ℕ) : ZMod m)), (-2 : ZMod m))
  have hxy : fromXY (m := m) ((4 : ZMod m), (((m - 2 : ℕ) : ZMod m))) = preTop := by
    ext <;> simp [preTop, fromXY, cast_sub_two_eq_neg_two (m := m) (by omega)]
    all_goals ring_nf
  have h8ne0 : (((8 : ℕ) : ZMod m)) ≠ 0 :=
    natCast_ne_zero_of_pos_lt (m := m) (n := 8) (by omega) (by omega)
  have h8ne1 : (((8 : ℕ) : ZMod m)) ≠ 1 :=
    natCast_ne_one_of_two_le_lt (m := m) (n := 8) (by omega) (by omega)
  have h8ne2 : (((8 : ℕ) : ZMod m)) ≠ 2 :=
    natCast_ne_two_of_three_le_lt (m := m) (n := 8) (by omega) (by omega)
  have h8ne3 : (((8 : ℕ) : ZMod m)) ≠ 3 := by
    intro h83
    have hmod := (ZMod.natCast_eq_natCast_iff' 8 3 m).1 (by simpa using h83)
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
    omega
  have hdir :
      dir0CaseIILayerZero (m := m) preTop = 1 :=
    dir0CaseIILayerZero_eq_one_of_k_neg_two_generic (m := m) h8ne0 h8ne1 h8ne2
  have hsum1 : (((8 : ℕ) : ZMod m)) + (-2 : ZMod m) ≠ 1 := by
    intro h
    have h' := congrArg (fun z : ZMod m => z + 2) h
    have h'' : (((8 : ℕ) : ZMod m)) = (3 : ZMod m) := by
      have h1 : (((8 : ℕ) : ZMod m)) + ((-2 : ZMod m) + 2) = (1 : ZMod m) + 2 := by
        simpa using h'
      calc
        (((8 : ℕ) : ZMod m)) = (((8 : ℕ) : ZMod m)) + ((-2 : ZMod m) + 2) := by ring
        _ = (1 : ZMod m) + 2 := h1
        _ = (3 : ZMod m) := by ring
    exact h8ne3 h''
  have hret := returnMap0CaseII_of_dir1_generic (m := m) (u := preTop) hdir h8ne0 hsum1
  calc
    returnMap0CaseIIXY (m := m) ((4 : ZMod m), (((m - 2 : ℕ) : ZMod m)))
        = toXY (m := m) (returnMap0CaseII (m := m) preTop) := by
            simp [returnMap0CaseIIXY, hxy]
    _ = toXY (m := m) (preTop.1 - 2, preTop.2 + 1) := by
          simpa using congrArg (toXY (m := m)) hret
    _ = ((4 : ZMod m), (-1 : ZMod m)) := by
          ext <;> simp [toXY, preTop]
          all_goals ring_nf
    _ = ((4 : ZMod m), (((m - 1 : ℕ) : ZMod m))) := by
          rw [cast_sub_one_eq_neg_one (m := m) (by omega)]

theorem returnMap0CaseIIXY_four_column_m_sub_one [Fact (9 < m)] (hm : m % 12 = 10) :
    returnMap0CaseIIXY (m := m) ((4 : ZMod m), (((m - 1 : ℕ) : ZMod m))) =
      ((4 : ZMod m), (0 : ZMod m)) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let preTop : QCoord m := ((((6 : ℕ) : ZMod m)), (-1 : ZMod m))
  have hxy : fromXY (m := m) ((4 : ZMod m), (((m - 1 : ℕ) : ZMod m))) = preTop := by
    ext <;> simp [preTop, fromXY, cast_sub_one_eq_neg_one (m := m) (by omega)]
    all_goals ring_nf
  have h6ne0 : (((6 : ℕ) : ZMod m)) ≠ 0 :=
    natCast_ne_zero_of_pos_lt (m := m) (n := 6) (by omega) (by omega)
  have h6ne1 : (((6 : ℕ) : ZMod m)) ≠ 1 :=
    natCast_ne_one_of_two_le_lt (m := m) (n := 6) (by omega) (by omega)
  have h6ne2 : (((6 : ℕ) : ZMod m)) ≠ 2 :=
    natCast_ne_two_of_three_le_lt (m := m) (n := 6) (by omega) (by omega)
  have hdir :
      dir0CaseIILayerZero (m := m) preTop = 1 :=
    dir0CaseIILayerZero_eq_one_of_k_neg_one_generic (m := m) h6ne0 h6ne1 h6ne2
  have hsum1 : (((6 : ℕ) : ZMod m)) + (-1 : ZMod m) ≠ 1 := by
    intro h
    have h' := congrArg (fun z : ZMod m => z + 1) h
    have h'' : (((6 : ℕ) : ZMod m)) = (2 : ZMod m) := by
      have h1 : (((6 : ℕ) : ZMod m)) + ((-1 : ZMod m) + 1) = (1 : ZMod m) + 1 := by
        simpa using h'
      calc
        (((6 : ℕ) : ZMod m)) = (((6 : ℕ) : ZMod m)) + ((-1 : ZMod m) + 1) := by ring
        _ = (1 : ZMod m) + 1 := h1
        _ = (2 : ZMod m) := by ring
    exact h6ne2 h''
  have hret := returnMap0CaseII_of_dir1_generic (m := m) (u := preTop) hdir h6ne0 hsum1
  calc
    returnMap0CaseIIXY (m := m) ((4 : ZMod m), (((m - 1 : ℕ) : ZMod m)))
        = toXY (m := m) (returnMap0CaseII (m := m) preTop) := by
            simp [returnMap0CaseIIXY, hxy]
    _ = toXY (m := m) (preTop.1 - 2, preTop.2 + 1) := by
          simpa using congrArg (toXY (m := m)) hret
    _ = ((4 : ZMod m), (0 : ZMod m)) := by
          ext <;> simp [toXY, preTop]
          all_goals ring_nf

theorem iterate_returnMap0CaseIIXY_four_column_to_zero [Fact (9 < m)] (hm : m % 12 = 10) :
    ((returnMap0CaseIIXY (m := m)^[m - 4]) ((4 : ZMod m), (4 : ZMod m))) =
      ((4 : ZMod m), (0 : ZMod m)) := by
  let F := returnMap0CaseIIXY (m := m)
  have hupper :
      ((F^[m / 2 - 5]) ((4 : ZMod m), (((m / 2 + 3 : ℕ) : ZMod m)))) =
        ((4 : ZMod m), (((m - 2 : ℕ) : ZMod m))) := by
    rw [iterate_returnMap0CaseIIXY_four_column_upper_partial (m := m) hm
      (t := m / 2 - 5) le_rfl]
    have hsum : m / 2 + 3 + (m / 2 - 5) = m - 2 := by omega
    simp [hsum]
  calc
    ((F^[m - 4]) ((4 : ZMod m), (4 : ZMod m)))
        = ((F^[2]) ((F^[m / 2 - 5]) ((F^[m / 2 - 1]) ((4 : ZMod m), (4 : ZMod m))))) := by
            rw [show m - 4 = 2 + ((m / 2 - 5) + (m / 2 - 1)) by omega]
            rw [Function.iterate_add_apply, Function.iterate_add_apply]
    _ = ((F^[2]) ((F^[m / 2 - 5]) ((4 : ZMod m), (((m / 2 + 3 : ℕ) : ZMod m))))) := by
          rw [iterate_returnMap0CaseIIXY_four_column_to_upper_start (m := m) hm]
    _ = ((F^[2]) ((4 : ZMod m), (((m - 2 : ℕ) : ZMod m)))) := by rw [hupper]
    _ = F (F ((4 : ZMod m), (((m - 2 : ℕ) : ZMod m)))) := by
          simp [Function.iterate_succ_apply']
    _ = F ((4 : ZMod m), (((m - 1 : ℕ) : ZMod m))) := by
          simpa [F] using congrArg F (returnMap0CaseIIXY_four_column_m_sub_two (m := m) hm)
    _ = ((4 : ZMod m), (0 : ZMod m)) := by
          simpa [F] using returnMap0CaseIIXY_four_column_m_sub_one (m := m) hm

theorem firstReturn_line_one_caseII_mod_ten [Fact (9 < m)] (hm : m % 12 = 10) :
    ((returnMap0CaseIIXY (m := m)^[m - 2])
        (linePoint0 (m := m) (⟨1, by omega⟩ : Fin m))) =
      linePoint0 (m := m) (⟨4, by omega⟩ : Fin m) := by
  let F := returnMap0CaseIIXY (m := m)
  let xFin : Fin m := ⟨1, by omega⟩
  have h1 :
      ((F^[1]) (linePoint0 (m := m) xFin)) = ((3 : ZMod m), (2 : ZMod m)) := by
    simpa [Function.iterate_one, linePoint0, xFin] using returnMap0CaseIIXY_one_zero (m := m)
  have h2 :
      ((F^[2]) (linePoint0 (m := m) xFin)) = ((4 : ZMod m), (4 : ZMod m)) := by
    calc
      ((F^[2]) (linePoint0 (m := m) xFin))
          = F (((F^[1]) (linePoint0 (m := m) xFin))) := by
              simp [Function.iterate_succ_apply']
      _ = F ((3 : ZMod m), (2 : ZMod m)) := by rw [h1]
      _ = ((4 : ZMod m), (4 : ZMod m)) := returnMap0CaseIIXY_three_two (m := m)
  calc
    ((F^[m - 2]) (linePoint0 (m := m) xFin))
        = ((F^[m - 4]) ((F^[2]) (linePoint0 (m := m) xFin))) := by
            rw [show m - 2 = (m - 4) + 2 by omega, Function.iterate_add_apply]
    _ = ((F^[m - 4]) ((4 : ZMod m), (4 : ZMod m))) := by rw [h2]
    _ = ((4 : ZMod m), (0 : ZMod m)) := iterate_returnMap0CaseIIXY_four_column_to_zero (m := m) hm
    _ = linePoint0 (m := m) (⟨4, by
          have hm9 : 9 < m := Fact.out
          omega⟩ : Fin m) := by
            simp [linePoint0]

theorem fromXY_six_column_lower [Fact (9 < m)] (hm : m % 12 = 10) {y : ℕ}
    (_hy6 : 6 ≤ y) (hyle : y ≤ m / 2 + 2) :
    fromXY (m := m) ((6 : ZMod m), (((y : ℕ) : ZMod m))) =
      ((((m + 6 - 2 * y : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))) := by
  ext <;> simp [fromXY]
  · have hle : 2 * y ≤ m + 6 := by omega
    rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul]
    simp

theorem fromXY_six_column_mid [Fact (9 < m)] (hm : m % 12 = 10) :
    fromXY (m := m) ((6 : ZMod m), (((m / 2 + 3 : ℕ) : ZMod m))) =
      ((0 : ZMod m), (((m / 2 + 3 : ℕ) : ZMod m))) := by
  ext <;> simp [fromXY]
  · have h2k : (2 : ZMod m) * (((m / 2 + 3 : ℕ) : ZMod m)) = (6 : ZMod m) := by
      calc
        (2 : ZMod m) * (((m / 2 + 3 : ℕ) : ZMod m))
            = (((2 * (m / 2 + 3) : ℕ) : ZMod m)) := by
                simp [Nat.cast_mul]
        _ = (((m + 6 : ℕ) : ZMod m)) := by
              have hmid : 2 * (m / 2 + 3) = m + 6 := by omega
              rw [hmid]
        _ = (6 : ZMod m) := by
              simp [Nat.cast_add]
    simpa [Nat.cast_add, Nat.cast_mul] using h2k.symm

theorem fromXY_six_column_upper [Fact (9 < m)] (hm : m % 12 = 10) {y : ℕ}
    (_hymid : m / 2 + 4 ≤ y) (hyle : y ≤ m - 1) :
    fromXY (m := m) ((6 : ZMod m), (((y : ℕ) : ZMod m))) =
      ((((2 * m + 6 - 2 * y : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))) := by
  ext <;> simp [fromXY]
  · have hle : 2 * y ≤ 2 * m + 6 := by omega
    rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul]
    simp

theorem returnMap0CaseIIXY_six_column_mid_step [Fact (9 < m)] (hm : m % 12 = 10) :
    returnMap0CaseIIXY (m := m) ((6 : ZMod m), (((m / 2 + 3 : ℕ) : ZMod m))) =
      ((6 : ZMod m), (((m / 2 + 4 : ℕ) : ZMod m))) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let midK : ZMod m := (((m / 2 + 3 : ℕ) : ZMod m))
  have hxy : fromXY (m := m) ((6 : ZMod m), midK) = ((0 : ZMod m), midK) := by
    simpa [midK] using fromXY_six_column_mid (m := m) hm
  have hmid_lt : m / 2 + 3 < m := by omega
  have hmid_ne_zero : midK ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := m / 2 + 3) (by omega) hmid_lt
  have hmid_ne_neg_one : midK ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := m / 2 + 3) (by omega)
  have hdir :
      dir0CaseIILayerZero (m := m) ((0 : ZMod m), midK) = 2 :=
    dir0CaseIILayerZero_eq_two_of_i_zero (m := m) hmid_ne_zero hmid_ne_neg_one
  have hmid_ne_one : midK ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := m / 2 + 3) (by omega) hmid_lt
  have hret := returnMap0CaseII_of_dir2_i_zero_generic (m := m) (k := midK) hdir hmid_ne_one
  have h2k : 2 * midK = (6 : ZMod m) := by
    change (2 : ZMod m) * (((m / 2 + 3 : ℕ) : ZMod m)) = (6 : ZMod m)
    calc
      (2 : ZMod m) * (((m / 2 + 3 : ℕ) : ZMod m))
          = (((2 * (m / 2 + 3) : ℕ) : ZMod m)) := by
              simp [Nat.cast_mul]
      _ = (((m + 6 : ℕ) : ZMod m)) := by
        have hmid : 2 * (m / 2 + 3) = m + 6 := by omega
        rw [hmid]
      _ = (6 : ZMod m) := by
        simp [Nat.cast_add]
  calc
    returnMap0CaseIIXY (m := m) ((6 : ZMod m), midK)
        = toXY (m := m) (returnMap0CaseII (m := m) ((0 : ZMod m), midK)) := by
            simp [returnMap0CaseIIXY, hxy]
    _ = toXY (m := m) ((-2 : ZMod m), midK + 1) := by rw [hret]
    _ = ((6 : ZMod m), midK + 1) := by
          have h2k' : midK * 2 = (6 : ZMod m) := by simpa [mul_comm] using h2k
          ext
          · calc
              (-2 : ZMod m) + 2 * (midK + 1) = midK * 2 := by ring
              _ = (6 : ZMod m) := h2k'
          · rfl
    _ = ((6 : ZMod m), (((m / 2 + 4 : ℕ) : ZMod m))) := by
          change ((6 : ZMod m), ((((m / 2 + 3 : ℕ) : ZMod m)) + 1)) =
            ((6 : ZMod m), (((m / 2 + 4 : ℕ) : ZMod m)))
          ext
          · rfl
          · simp [Nat.cast_add]
            ring_nf

theorem returnMap0CaseIIXY_six_column_lower_step [Fact (9 < m)] (hm : m % 12 = 10) {y : ℕ}
    (hy6 : 6 ≤ y) (hyle : y ≤ m / 2 + 2) :
    returnMap0CaseIIXY (m := m) ((6 : ZMod m), (((y : ℕ) : ZMod m))) =
      ((6 : ZMod m), (((y + 1 : ℕ) : ZMod m))) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let k : ZMod m := (((y : ℕ) : ZMod m))
  let i : ZMod m := (((m + 6 - 2 * y : ℕ) : ZMod m))
  have hylt : y < m := by omega
  have hilt : m + 6 - 2 * y < m := by omega
  have hipos : 0 < m + 6 - 2 * y := by omega
  have hitwo : 2 ≤ m + 6 - 2 * y := by omega
  have hxy : fromXY (m := m) ((6 : ZMod m), k) = (i, k) := by
    simpa [i, k] using fromXY_six_column_lower (m := m) hm (y := y) hy6 hyle
  have hi0 : i ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := m + 6 - 2 * y) hipos hilt
  have hi1 : i ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := m + 6 - 2 * y) hitwo hilt
  have hk0 : k ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := y) (by omega) hylt
  have hk1 : k ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := y) (by omega) hylt
  have hkneg1 : k ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := y) (by omega)
  have hkneg2 : k ≠ (-2 : ZMod m) := by
    exact natCast_ne_neg_two_of_lt (m := m) (n := y) (by omega)
  have hdir :
      dir0CaseIILayerZero (m := m) (i, k) = 1 :=
    dir0CaseIILayerZero_eq_one_of_generic (m := m) hi0 hi1 hk0 hk1 hkneg1 hkneg2
  have hi2k : i + 2 * k = (6 : ZMod m) := by
    have h := congrArg (fun u : P0Coord m => u.1 + 2 * u.2) hxy
    simpa [fromXY] using h.symm
  have hsum1 : i + k ≠ 1 := by
    intro h
    have hk5 : k = (5 : ZMod m) := by
      calc
        k = (i + 2 * k) - (i + k) := by ring
        _ = (6 : ZMod m) - 1 := by rw [hi2k, h]
        _ = (5 : ZMod m) := by ring
    have hcast : (((y : ℕ) : ZMod m)) = (5 : ZMod m) := by simpa [k] using hk5
    have hmod := (ZMod.natCast_eq_natCast_iff' y 5 m).1 hcast
    have h5lt : 5 < m := by omega
    rw [Nat.mod_eq_of_lt hylt, Nat.mod_eq_of_lt h5lt] at hmod
    omega
  have hret := returnMap0CaseII_of_dir1_generic (m := m) (u := (i, k)) hdir hi0 hsum1
  calc
    returnMap0CaseIIXY (m := m) ((6 : ZMod m), k)
        = toXY (m := m) (returnMap0CaseII (m := m) (i, k)) := by
            simp [returnMap0CaseIIXY, hxy]
    _ = toXY (m := m) (i - 2, k + 1) := by rw [hret]
    _ = ((6 : ZMod m), k + 1) := by
          ext
          · calc
              (i - 2) + 2 * (k + 1) = i + 2 * k := by ring
              _ = (6 : ZMod m) := hi2k
          · rfl
    _ = ((6 : ZMod m), (((y + 1 : ℕ) : ZMod m))) := by
          simp [k, Nat.cast_add]

theorem returnMap0CaseIIXY_six_column_upper_step [Fact (9 < m)] (hm : m % 12 = 10) {y : ℕ}
    (hymid : m / 2 + 4 ≤ y) (hyle : y ≤ m - 3) :
    returnMap0CaseIIXY (m := m) ((6 : ZMod m), (((y : ℕ) : ZMod m))) =
      ((6 : ZMod m), (((y + 1 : ℕ) : ZMod m))) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let k : ZMod m := (((y : ℕ) : ZMod m))
  let i : ZMod m := (((2 * m + 6 - 2 * y : ℕ) : ZMod m))
  have hylt : y < m := by omega
  have hilt : 2 * m + 6 - 2 * y < m := by omega
  have hipos : 0 < 2 * m + 6 - 2 * y := by omega
  have hitwo : 2 ≤ 2 * m + 6 - 2 * y := by omega
  have hxy : fromXY (m := m) ((6 : ZMod m), k) = (i, k) := by
    simpa [i, k] using fromXY_six_column_upper (m := m) hm (y := y) hymid (by omega)
  have hi0 : i ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := 2 * m + 6 - 2 * y) hipos hilt
  have hi1 : i ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := 2 * m + 6 - 2 * y) hitwo hilt
  have hk0 : k ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := y) (by omega) hylt
  have hk1 : k ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := y) (by omega) hylt
  have hkneg1 : k ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := y) (by omega)
  have hkneg2 : k ≠ (-2 : ZMod m) := by
    exact natCast_ne_neg_two_of_lt (m := m) (n := y) (by omega)
  have hdir :
      dir0CaseIILayerZero (m := m) (i, k) = 1 :=
    dir0CaseIILayerZero_eq_one_of_generic (m := m) hi0 hi1 hk0 hk1 hkneg1 hkneg2
  have hi2k : i + 2 * k = (6 : ZMod m) := by
    have h := congrArg (fun u : P0Coord m => u.1 + 2 * u.2) hxy
    simpa [fromXY] using h.symm
  have hsum1 : i + k ≠ 1 := by
    intro h
    have hk5 : k = (5 : ZMod m) := by
      calc
        k = (i + 2 * k) - (i + k) := by ring
        _ = (6 : ZMod m) - 1 := by rw [hi2k, h]
        _ = (5 : ZMod m) := by ring
    have hcast : (((y : ℕ) : ZMod m)) = (5 : ZMod m) := by simpa [k] using hk5
    have hmod := (ZMod.natCast_eq_natCast_iff' y 5 m).1 hcast
    have h5lt : 5 < m := by omega
    rw [Nat.mod_eq_of_lt hylt, Nat.mod_eq_of_lt h5lt] at hmod
    omega
  have hret := returnMap0CaseII_of_dir1_generic (m := m) (u := (i, k)) hdir hi0 hsum1
  calc
    returnMap0CaseIIXY (m := m) ((6 : ZMod m), k)
        = toXY (m := m) (returnMap0CaseII (m := m) (i, k)) := by
            simp [returnMap0CaseIIXY, hxy]
    _ = toXY (m := m) (i - 2, k + 1) := by rw [hret]
    _ = ((6 : ZMod m), k + 1) := by
          ext
          · calc
              (i - 2) + 2 * (k + 1) = i + 2 * k := by ring
              _ = (6 : ZMod m) := hi2k
          · rfl
    _ = ((6 : ZMod m), (((y + 1 : ℕ) : ZMod m))) := by
          simp [k, Nat.cast_add]

theorem iterate_returnMap0CaseIIXY_six_column_lower_partial [Fact (9 < m)] (hm : m % 12 = 10)
    {t : ℕ} (ht : t ≤ m / 2 - 3) :
    ((returnMap0CaseIIXY (m := m)^[t]) ((6 : ZMod m), (6 : ZMod m))) =
      ((6 : ZMod m), (((6 + t : ℕ) : ZMod m))) := by
  induction t with
  | zero =>
      simp
  | succ t iht =>
      have ht' : t ≤ m / 2 - 3 := Nat.le_of_succ_le ht
      have hstep :
          returnMap0CaseIIXY (m := m) ((6 : ZMod m), (((6 + t : ℕ) : ZMod m))) =
            ((6 : ZMod m), (((6 + t + 1 : ℕ) : ZMod m))) := by
        have hy6 : 6 ≤ 6 + t := by omega
        have hyle : 6 + t ≤ m / 2 + 2 := by omega
        simpa [Nat.add_assoc] using
          returnMap0CaseIIXY_six_column_lower_step (m := m) hm (y := 6 + t) hy6 hyle
      calc
        ((returnMap0CaseIIXY (m := m)^[t.succ]) ((6 : ZMod m), (6 : ZMod m)))
            = returnMap0CaseIIXY (m := m)
                (((returnMap0CaseIIXY (m := m)^[t]) ((6 : ZMod m), (6 : ZMod m)))) := by
                    rw [Function.iterate_succ_apply']
        _ = returnMap0CaseIIXY (m := m) ((6 : ZMod m), (((6 + t : ℕ) : ZMod m))) := by rw [iht ht']
        _ = ((6 : ZMod m), (((6 + t + 1 : ℕ) : ZMod m))) := hstep
        _ = ((6 : ZMod m), (((6 + t.succ : ℕ) : ZMod m))) := by
              simp [Nat.succ_eq_add_one, Nat.add_assoc]

theorem iterate_returnMap0CaseIIXY_six_column_to_upper_start [Fact (9 < m)] (hm : m % 12 = 10) :
    ((returnMap0CaseIIXY (m := m)^[m / 2 - 2]) ((6 : ZMod m), (6 : ZMod m))) =
      ((6 : ZMod m), (((m / 2 + 4 : ℕ) : ZMod m))) := by
  have hm3 : 3 ≤ m / 2 := by
    have hm9 : 9 < m := Fact.out
    omega
  calc
    ((returnMap0CaseIIXY (m := m)^[m / 2 - 2]) ((6 : ZMod m), (6 : ZMod m)))
        = returnMap0CaseIIXY (m := m)
            (((returnMap0CaseIIXY (m := m)^[m / 2 - 3]) ((6 : ZMod m), (6 : ZMod m)))) := by
                rw [show m / 2 - 2 = (m / 2 - 3) + 1 by omega, Function.iterate_succ_apply']
    _ = returnMap0CaseIIXY (m := m) ((6 : ZMod m), (((m / 2 + 3 : ℕ) : ZMod m))) := by
          rw [iterate_returnMap0CaseIIXY_six_column_lower_partial (m := m) hm
            (t := m / 2 - 3) le_rfl]
          have hsum : 6 + (m / 2 - 3) = m / 2 + 3 := by omega
          simp [hsum]
    _ = ((6 : ZMod m), (((m / 2 + 4 : ℕ) : ZMod m))) := by
          exact returnMap0CaseIIXY_six_column_mid_step (m := m) hm

theorem iterate_returnMap0CaseIIXY_six_column_upper_partial [Fact (9 < m)] (hm : m % 12 = 10)
    {t : ℕ} (ht : t ≤ m / 2 - 6) :
    ((returnMap0CaseIIXY (m := m)^[t]) ((6 : ZMod m), (((m / 2 + 4 : ℕ) : ZMod m)))) =
      ((6 : ZMod m), (((m / 2 + 4 + t : ℕ) : ZMod m))) := by
  induction t with
  | zero =>
      simp
  | succ t iht =>
      have ht' : t ≤ m / 2 - 6 := Nat.le_of_succ_le ht
      have hstep :
          returnMap0CaseIIXY (m := m) ((6 : ZMod m), (((m / 2 + 4 + t : ℕ) : ZMod m))) =
            ((6 : ZMod m), (((m / 2 + 4 + t + 1 : ℕ) : ZMod m))) := by
        have hymid : m / 2 + 4 ≤ m / 2 + 4 + t := by omega
        have hyle : m / 2 + 4 + t ≤ m - 3 := by omega
        simpa [Nat.add_assoc] using
          returnMap0CaseIIXY_six_column_upper_step (m := m) hm
            (y := m / 2 + 4 + t) hymid hyle
      calc
        ((returnMap0CaseIIXY (m := m)^[t.succ]) ((6 : ZMod m), (((m / 2 + 4 : ℕ) : ZMod m))))
            = returnMap0CaseIIXY (m := m)
                (((returnMap0CaseIIXY (m := m)^[t]) ((6 : ZMod m), (((m / 2 + 4 : ℕ) : ZMod m))))) := by
                    rw [Function.iterate_succ_apply']
        _ = returnMap0CaseIIXY (m := m) ((6 : ZMod m), (((m / 2 + 4 + t : ℕ) : ZMod m))) := by
              rw [iht ht']
        _ = ((6 : ZMod m), (((m / 2 + 4 + t + 1 : ℕ) : ZMod m))) := hstep
        _ = ((6 : ZMod m), (((m / 2 + 4 + t.succ : ℕ) : ZMod m))) := by
              simp [Nat.succ_eq_add_one, Nat.add_assoc]

theorem returnMap0CaseIIXY_six_column_m_sub_two [Fact (9 < m)] (hm : m % 12 = 10) :
    returnMap0CaseIIXY (m := m) ((6 : ZMod m), (((m - 2 : ℕ) : ZMod m))) =
      ((6 : ZMod m), (((m - 1 : ℕ) : ZMod m))) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  by_cases hm10 : m = 10
  · subst hm10
    let preTop : QCoord 10 := ((0 : ZMod 10), (((10 - 2 : ℕ) : ZMod 10)))
    have hxy : fromXY (m := 10) ((6 : ZMod 10), (((10 - 2 : ℕ) : ZMod 10))) = preTop := by
      decide
    have hdir :
        dir0CaseIILayerZero (m := 10) preTop = 2 := by
      have hk0 : preTop.2 ≠ 0 := by
        exact natCast_ne_zero_of_pos_lt (m := 10) (n := 8) (by decide) (by decide)
      have hkneg1 : preTop.2 ≠ (-1 : ZMod 10) := by
        exact natCast_ne_neg_one_of_lt (m := 10) (n := 8) (by decide)
      exact dir0CaseIILayerZero_eq_two_of_i_zero (m := 10) hk0 hkneg1
    have hk1 : preTop.2 ≠ 1 := by
      exact natCast_ne_one_of_two_le_lt (m := 10) (n := 8) (by decide) (by decide)
    have hret := returnMap0CaseII_of_dir2_i_zero_generic (m := 10) (k := preTop.2) hdir hk1
    calc
      returnMap0CaseIIXY (m := 10) ((6 : ZMod 10), (((10 - 2 : ℕ) : ZMod 10)))
          = toXY (m := 10) (returnMap0CaseII (m := 10) (fromXY (m := 10) ((6 : ZMod 10), (((10 - 2 : ℕ) : ZMod 10))))) := by
              simp [returnMap0CaseIIXY]
      _ = toXY (m := 10) (returnMap0CaseII (m := 10) preTop) := by rw [hxy]
      _ = toXY (m := 10) ((-2 : ZMod 10), preTop.2 + 1) := by rw [hret]
      _ = ((6 : ZMod 10), (((10 - 1 : ℕ) : ZMod 10))) := by
            decide
  · have hm10lt : 10 < m := by
      have hm9 : 9 < m := Fact.out
      omega
    let preTop : QCoord m := ((((10 : ℕ) : ZMod m)), (-2 : ZMod m))
    have hxy : fromXY (m := m) ((6 : ZMod m), (((m - 2 : ℕ) : ZMod m))) = preTop := by
      ext <;> simp [preTop, fromXY, cast_sub_two_eq_neg_two (m := m) (by omega)]
      all_goals ring_nf
    have h10ne0 : (((10 : ℕ) : ZMod m)) ≠ 0 :=
      natCast_ne_zero_of_pos_lt (m := m) (n := 10) (by omega) hm10lt
    have h10ne1 : (((10 : ℕ) : ZMod m)) ≠ 1 :=
      natCast_ne_one_of_two_le_lt (m := m) (n := 10) (by omega) hm10lt
    have h10ne2 : (((10 : ℕ) : ZMod m)) ≠ 2 :=
      natCast_ne_two_of_three_le_lt (m := m) (n := 10) (by omega) hm10lt
    have hdir :
        dir0CaseIILayerZero (m := m) preTop = 1 :=
      dir0CaseIILayerZero_eq_one_of_k_neg_two_generic (m := m) h10ne0 h10ne1 h10ne2
    have h8ne1 : (8 : ZMod m) ≠ 1 :=
      natCast_ne_one_of_two_le_lt (m := m) (n := 8) (by omega) (by omega)
    have hsum1 : (((10 : ℕ) : ZMod m)) + (-2 : ZMod m) ≠ 1 := by
      intro h
      have : (8 : ZMod m) = 1 := by
        calc
          (8 : ZMod m) = (((10 : ℕ) : ZMod m)) + (-2 : ZMod m) := by ring
          _ = 1 := h
      exact h8ne1 this
    have hret := returnMap0CaseII_of_dir1_generic (m := m) (u := preTop) hdir h10ne0 hsum1
    calc
      returnMap0CaseIIXY (m := m) ((6 : ZMod m), (((m - 2 : ℕ) : ZMod m)))
          = toXY (m := m) (returnMap0CaseII (m := m) (fromXY (m := m) ((6 : ZMod m), (((m - 2 : ℕ) : ZMod m))))) := by
              simp [returnMap0CaseIIXY]
      _ = toXY (m := m) (returnMap0CaseII (m := m) preTop) := by rw [hxy]
      _ = toXY (m := m) (preTop.1 - 2, preTop.2 + 1) := by
            simpa using congrArg (toXY (m := m)) hret
      _ = ((6 : ZMod m), (-1 : ZMod m)) := by
            ext <;> simp [toXY, preTop]
            all_goals ring_nf
      _ = ((6 : ZMod m), (((m - 1 : ℕ) : ZMod m))) := by
            rw [cast_sub_one_eq_neg_one (m := m) (by omega)]

theorem returnMap0CaseIIXY_six_column_m_sub_one [Fact (9 < m)] :
    returnMap0CaseIIXY (m := m) ((6 : ZMod m), (((m - 1 : ℕ) : ZMod m))) =
      ((6 : ZMod m), (0 : ZMod m)) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  have hm9 : 9 < m := Fact.out
  let preTop : QCoord m := ((((8 : ℕ) : ZMod m)), (-1 : ZMod m))
  have hxy : fromXY (m := m) ((6 : ZMod m), (((m - 1 : ℕ) : ZMod m))) = preTop := by
    ext <;> simp [preTop, fromXY, cast_sub_one_eq_neg_one (m := m) (by omega)]
    all_goals ring_nf
  have h8ne0 : (((8 : ℕ) : ZMod m)) ≠ 0 :=
    natCast_ne_zero_of_pos_lt (m := m) (n := 8) (by omega) (by omega)
  have h8ne1 : (((8 : ℕ) : ZMod m)) ≠ 1 :=
    natCast_ne_one_of_two_le_lt (m := m) (n := 8) (by omega) (by omega)
  have h8ne2 : (((8 : ℕ) : ZMod m)) ≠ 2 :=
    natCast_ne_two_of_three_le_lt (m := m) (n := 8) (by omega) (by omega)
  have hdir :
      dir0CaseIILayerZero (m := m) preTop = 1 :=
    dir0CaseIILayerZero_eq_one_of_k_neg_one_generic (m := m) h8ne0 h8ne1 h8ne2
  have h7ne1 : (7 : ZMod m) ≠ 1 :=
    natCast_ne_one_of_two_le_lt (m := m) (n := 7) (by omega) (by omega)
  have hsum1 : (((8 : ℕ) : ZMod m)) + (-1 : ZMod m) ≠ 1 := by
    intro h
    have hbad : (7 : ZMod m) = 1 := by
      calc
        (7 : ZMod m) = (((8 : ℕ) : ZMod m)) + (-1 : ZMod m) := by ring
        _ = 1 := h
    exact h7ne1 hbad
  have hret := returnMap0CaseII_of_dir1_generic (m := m) (u := preTop) hdir h8ne0 hsum1
  calc
    returnMap0CaseIIXY (m := m) ((6 : ZMod m), (((m - 1 : ℕ) : ZMod m)))
        = toXY (m := m) (returnMap0CaseII (m := m) (fromXY (m := m) ((6 : ZMod m), (((m - 1 : ℕ) : ZMod m))))) := by
            simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) preTop) := by rw [hxy]
    _ = toXY (m := m) (preTop.1 - 2, preTop.2 + 1) := by
          simpa using congrArg (toXY (m := m)) hret
    _ = ((6 : ZMod m), (0 : ZMod m)) := by
          ext <;> simp [toXY, preTop]
          all_goals ring_nf

theorem iterate_returnMap0CaseIIXY_six_column_to_zero [Fact (9 < m)] (hm : m % 12 = 10) :
    ((returnMap0CaseIIXY (m := m)^[m - 6]) ((6 : ZMod m), (6 : ZMod m))) =
      ((6 : ZMod m), (0 : ZMod m)) := by
  let F := returnMap0CaseIIXY (m := m)
  by_cases hm10 : m = 10
  · subst hm10
    calc
      ((F^[10 - 6]) ((6 : ZMod 10), (6 : ZMod 10)))
          = F (((F^[10 / 2 - 2]) ((6 : ZMod 10), (6 : ZMod 10)))) := by
              rw [show 10 - 6 = (10 / 2 - 2) + 1 by norm_num, Function.iterate_add_apply]
              simp
      _ = F ((6 : ZMod 10), (((10 / 2 + 4 : ℕ) : ZMod 10))) := by
            rw [iterate_returnMap0CaseIIXY_six_column_to_upper_start (m := 10) hm]
      _ = ((6 : ZMod 10), (0 : ZMod 10)) := by
            simpa using returnMap0CaseIIXY_six_column_m_sub_one (m := 10)
  · have hm22 : 22 ≤ m := by
      have hm9 : 9 < m := Fact.out
      omega
    have hupper :
        ((F^[m / 2 - 6]) ((6 : ZMod m), (((m / 2 + 4 : ℕ) : ZMod m)))) =
          ((6 : ZMod m), (((m - 2 : ℕ) : ZMod m))) := by
      rw [iterate_returnMap0CaseIIXY_six_column_upper_partial (m := m) hm
        (t := m / 2 - 6) le_rfl]
      have hsum : m / 2 + 4 + (m / 2 - 6) = m - 2 := by omega
      simp [hsum]
    calc
      ((F^[m - 6]) ((6 : ZMod m), (6 : ZMod m)))
          = ((F^[2]) ((F^[m / 2 - 6]) ((F^[m / 2 - 2]) ((6 : ZMod m), (6 : ZMod m))))) := by
              rw [show m - 6 = 2 + ((m / 2 - 6) + (m / 2 - 2)) by omega]
              rw [Function.iterate_add_apply, Function.iterate_add_apply]
      _ = ((F^[2]) ((F^[m / 2 - 6]) ((6 : ZMod m), (((m / 2 + 4 : ℕ) : ZMod m))))) := by
            rw [iterate_returnMap0CaseIIXY_six_column_to_upper_start (m := m) hm]
      _ = ((F^[2]) ((6 : ZMod m), (((m - 2 : ℕ) : ZMod m)))) := by rw [hupper]
      _ = F (F ((6 : ZMod m), (((m - 2 : ℕ) : ZMod m)))) := by
            simp [Function.iterate_succ_apply']
      _ = F ((6 : ZMod m), (((m - 1 : ℕ) : ZMod m))) := by
            simpa [F] using congrArg F (returnMap0CaseIIXY_six_column_m_sub_two (m := m) hm)
      _ = ((6 : ZMod m), (0 : ZMod m)) := by
            simpa [F] using returnMap0CaseIIXY_six_column_m_sub_one (m := m)

theorem firstReturn_line_two_caseII_mod_ten [Fact (9 < m)] (hm : m % 12 = 10) :
    ((returnMap0CaseIIXY (m := m)^[m - 2])
        (linePoint0 (m := m) (⟨2, by omega⟩ : Fin m))) =
      linePoint0 (m := m) (⟨6, by omega⟩ : Fin m) := by
  let F := returnMap0CaseIIXY (m := m)
  let xFin : Fin m := ⟨2, by omega⟩
  have h1 :
      ((F^[1]) (linePoint0 (m := m) xFin)) = ((3 : ZMod m), (1 : ZMod m)) := by
    simpa [Function.iterate_one, linePoint0, xFin] using
      returnMap0CaseIIXY_line_start_generic (m := m) (x := 2) (by omega) (by omega)
  have h2 :
      ((F^[2]) (linePoint0 (m := m) xFin)) = ((5 : ZMod m), (3 : ZMod m)) := by
    calc
      ((F^[2]) (linePoint0 (m := m) xFin))
          = F (((F^[1]) (linePoint0 (m := m) xFin))) := by
              simp [Function.iterate_succ_apply']
      _ = F ((3 : ZMod m), (1 : ZMod m)) := by rw [h1]
      _ = ((5 : ZMod m), (3 : ZMod m)) := by
            simpa using returnMap0CaseIIXY_R_line (m := m) (y := 1) (by omega)
  have h3 :
      ((F^[3]) (linePoint0 (m := m) xFin)) = ((5 : ZMod m), (4 : ZMod m)) := by
    calc
      ((F^[3]) (linePoint0 (m := m) xFin))
          = F (((F^[2]) (linePoint0 (m := m) xFin))) := by
              simp [Function.iterate_succ_apply']
      _ = F ((5 : ZMod m), (3 : ZMod m)) := by rw [h2]
      _ = ((5 : ZMod m), (4 : ZMod m)) := returnMap0CaseIIXY_five_three (m := m)
  have h4 :
      ((F^[4]) (linePoint0 (m := m) xFin)) = ((6 : ZMod m), (6 : ZMod m)) := by
    calc
      ((F^[4]) (linePoint0 (m := m) xFin))
          = F (((F^[3]) (linePoint0 (m := m) xFin))) := by
              simp [Function.iterate_succ_apply']
      _ = F ((5 : ZMod m), (4 : ZMod m)) := by rw [h3]
      _ = ((6 : ZMod m), (6 : ZMod m)) := returnMap0CaseIIXY_five_four (m := m)
  calc
    ((F^[m - 2]) (linePoint0 (m := m) xFin))
        = ((F^[m - 6]) ((F^[4]) (linePoint0 (m := m) xFin))) := by
            rw [show m - 2 = (m - 6) + 4 by omega, Function.iterate_add_apply]
    _ = ((F^[m - 6]) ((6 : ZMod m), (6 : ZMod m))) := by rw [h4]
    _ = ((6 : ZMod m), (0 : ZMod m)) := iterate_returnMap0CaseIIXY_six_column_to_zero (m := m) hm
    _ = linePoint0 (m := m) (⟨6, by
          have hm9 : 9 < m := Fact.out
          omega⟩ : Fin m) := by
            simp [linePoint0]

theorem fromXY_two_column_lower [Fact (9 < m)] (hm : m % 12 = 10) {y : ℕ}
    (_hy2 : 2 ≤ y) (hyle : y ≤ m / 2) :
    fromXY (m := m) ((2 : ZMod m), (((y : ℕ) : ZMod m))) =
      ((((m + 2 - 2 * y : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))) := by
  ext <;> simp [fromXY]
  · have hle : 2 * y ≤ m + 2 := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq] at hyle ⊢
      omega
    rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul]
    simp

theorem fromXY_two_column_mid [Fact (9 < m)] (hm : m % 12 = 10) :
    fromXY (m := m) ((2 : ZMod m), (((m / 2 + 1 : ℕ) : ZMod m))) =
      ((0 : ZMod m), (((m / 2 + 1 : ℕ) : ZMod m))) := by
  ext <;> simp [fromXY]
  · have h2k :
        (2 : ZMod m) * (((m / 2 + 1 : ℕ) : ZMod m)) = (2 : ZMod m) := by
      calc
        (2 : ZMod m) * (((m / 2 + 1 : ℕ) : ZMod m))
            = (((2 * (m / 2 + 1) : ℕ) : ZMod m)) := by
                simp [Nat.cast_mul]
        _ = (((m + 2 : ℕ) : ZMod m)) := by
              have hnat : 2 * (m / 2 + 1) = m + 2 := by
                rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
                rw [hq]
                omega
              rw [hnat]
        _ = (2 : ZMod m) := by
              simp [Nat.cast_add]
    simpa [Nat.cast_mul, Nat.cast_add] using h2k.symm

theorem fromXY_two_column_upper [Fact (9 < m)] {y : ℕ}
    (hyl : m / 2 + 2 ≤ y) (hyu : y ≤ m - 1) :
    fromXY (m := m) ((2 : ZMod m), (((y : ℕ) : ZMod m))) =
      ((((2 * m + 2 - 2 * y : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))) := by
  ext <;> simp [fromXY]
  · have hle : 2 * y ≤ 2 * m + 2 := by omega
    rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul]
    simp

theorem returnMap0CaseIIXY_two_column_lower_step [Fact (9 < m)] (hm : m % 12 = 10) {y : ℕ}
    (hy2 : 2 ≤ y) (hyle : y ≤ m / 2) :
    returnMap0CaseIIXY (m := m) ((2 : ZMod m), (((y : ℕ) : ZMod m))) =
      ((2 : ZMod m), (((y + 1 : ℕ) : ZMod m))) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let k : ZMod m := (((y : ℕ) : ZMod m))
  let i : ZMod m := (((m + 2 - 2 * y : ℕ) : ZMod m))
  have hylt : y < m := by omega
  have hilt : m + 2 - 2 * y < m := by omega
  have hipos : 0 < m + 2 - 2 * y := by
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rw [hq] at hyle ⊢
    omega
  have hitwo : 2 ≤ m + 2 - 2 * y := by
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rw [hq] at hyle ⊢
    omega
  have hxy : fromXY (m := m) ((2 : ZMod m), k) = (i, k) := by
    simpa [i, k] using fromXY_two_column_lower (m := m) hm (y := y) hy2 hyle
  have hi0 : i ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := m + 2 - 2 * y) hipos hilt
  have hi1 : i ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := m + 2 - 2 * y) hitwo hilt
  have hk0 : k ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := y) (by omega) hylt
  have hk1 : k ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := y) hy2 hylt
  have hkneg1 : k ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := y) (by omega)
  have hkneg2 : k ≠ (-2 : ZMod m) := by
    exact natCast_ne_neg_two_of_lt (m := m) (n := y) (by omega)
  have hdir :
      dir0CaseIILayerZero (m := m) (i, k) = 1 :=
    dir0CaseIILayerZero_eq_one_of_generic (m := m) hi0 hi1 hk0 hk1 hkneg1 hkneg2
  have hi2k : i + 2 * k = (2 : ZMod m) := by
    have h := congrArg (fun u : P0Coord m => u.1 + 2 * u.2) hxy
    simpa [fromXY] using h.symm
  have hsum1 : i + k ≠ 1 := by
    intro h
    have hkone : k = (1 : ZMod m) := by
      calc
        k = (i + 2 * k) - (i + k) := by ring
        _ = (2 : ZMod m) - 1 := by rw [hi2k, h]
        _ = 1 := by ring
    have hy_ne_one : (((y : ℕ) : ZMod m)) ≠ 1 := by
      exact natCast_ne_one_of_two_le_lt (m := m) (n := y) hy2 hylt
    exact hy_ne_one (by simpa [k] using hkone)
  have hret := returnMap0CaseII_of_dir1_generic (m := m) (u := (i, k)) hdir hi0 hsum1
  calc
    returnMap0CaseIIXY (m := m) ((2 : ZMod m), k)
        = toXY (m := m)
            (returnMap0CaseII (m := m)
              (fromXY (m := m) ((2 : ZMod m), k))) := by
                simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) (i, k)) := by rw [hxy]
    _ = toXY (m := m) (i - 2, k + 1) := by rw [hret]
    _ = ((2 : ZMod m), k + 1) := by
          ext
          · calc
              (i - 2) + 2 * (k + 1) = i + 2 * k := by ring
              _ = (2 : ZMod m) := hi2k
          · rfl
    _ = ((2 : ZMod m), (((y + 1 : ℕ) : ZMod m))) := by
          simp [k, Nat.cast_add]

theorem returnMap0CaseIIXY_two_column_mid_step [Fact (9 < m)] (hm : m % 12 = 10) :
    returnMap0CaseIIXY (m := m) ((2 : ZMod m), (((m / 2 + 1 : ℕ) : ZMod m))) =
      ((2 : ZMod m), (((m / 2 + 2 : ℕ) : ZMod m))) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let midK : ZMod m := (((m / 2 + 1 : ℕ) : ZMod m))
  have hxy : fromXY (m := m) ((2 : ZMod m), midK) = ((0 : ZMod m), midK) := by
    simpa [midK] using fromXY_two_column_mid (m := m) hm
  have hmid_lt : m / 2 + 1 < m := by
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rw [hq]
    omega
  have hmid_ne_zero : midK ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := m / 2 + 1) (by omega) hmid_lt
  have hmid_ne_neg_one : midK ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := m / 2 + 1) (by omega)
  have hdir :
      dir0CaseIILayerZero (m := m) ((0 : ZMod m), midK) = 2 :=
    dir0CaseIILayerZero_eq_two_of_i_zero (m := m) hmid_ne_zero hmid_ne_neg_one
  have hmid_ne_one : midK ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := m / 2 + 1) (by omega) hmid_lt
  have hret := returnMap0CaseII_of_dir2_i_zero_generic (m := m) (k := midK) hdir hmid_ne_one
  have h2k : 2 * midK = (2 : ZMod m) := by
    change (2 : ZMod m) * (((m / 2 + 1 : ℕ) : ZMod m)) = (2 : ZMod m)
    calc
      (2 : ZMod m) * (((m / 2 + 1 : ℕ) : ZMod m))
          = (((2 * (m / 2 + 1) : ℕ) : ZMod m)) := by
              simp [Nat.cast_mul]
      _ = (((m + 2 : ℕ) : ZMod m)) := by
            have hnat : 2 * (m / 2 + 1) = m + 2 := by
              rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
              rw [hq]
              omega
            rw [hnat]
      _ = (2 : ZMod m) := by
            simp [Nat.cast_add]
  calc
    returnMap0CaseIIXY (m := m) ((2 : ZMod m), midK)
        = toXY (m := m)
            (returnMap0CaseII (m := m) (fromXY (m := m) ((2 : ZMod m), midK))) := by
                simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) ((0 : ZMod m), midK)) := by rw [hxy]
    _ = toXY (m := m) ((-2 : ZMod m), midK + 1) := by rw [hret]
    _ = ((2 : ZMod m), midK + 1) := by
          have h2k' : midK * 2 = (2 : ZMod m) := by simpa [mul_comm] using h2k
          ext
          · calc
              (-2 : ZMod m) + 2 * (midK + 1) = midK * 2 := by ring
              _ = (2 : ZMod m) := h2k'
          · rfl
    _ = ((2 : ZMod m), (((m / 2 + 2 : ℕ) : ZMod m))) := by
          change ((2 : ZMod m), ((((m / 2 + 1 : ℕ) : ZMod m)) + 1)) =
            ((2 : ZMod m), (((m / 2 + 2 : ℕ) : ZMod m)))
          ext
          · rfl
          · simp [Nat.cast_add]
            ring_nf

theorem returnMap0CaseIIXY_two_column_upper_step [Fact (9 < m)] {y : ℕ}
    (hyl : m / 2 + 2 ≤ y) (hyu : y ≤ m - 3) :
    returnMap0CaseIIXY (m := m) ((2 : ZMod m), (((y : ℕ) : ZMod m))) =
      ((2 : ZMod m), (((y + 1 : ℕ) : ZMod m))) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let k : ZMod m := (((y : ℕ) : ZMod m))
  let i : ZMod m := (((2 * m + 2 - 2 * y : ℕ) : ZMod m))
  have hylt : y < m := by omega
  have hilt : 2 * m + 2 - 2 * y < m := by
    have hm9 : 9 < m := Fact.out
    omega
  have hipos : 0 < 2 * m + 2 - 2 * y := by omega
  have hitwo : 2 ≤ 2 * m + 2 - 2 * y := by omega
  have hxy : fromXY (m := m) ((2 : ZMod m), k) = (i, k) := by
    simpa [i, k] using fromXY_two_column_upper (m := m) (y := y) hyl (by omega)
  have hi0 : i ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := 2 * m + 2 - 2 * y) hipos hilt
  have hi1 : i ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := 2 * m + 2 - 2 * y) hitwo hilt
  have hk0 : k ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := y) (by omega) hylt
  have hk1 : k ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := y) (by omega) hylt
  have hkneg1 : k ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := y) (by omega)
  have hkneg2 : k ≠ (-2 : ZMod m) := by
    exact natCast_ne_neg_two_of_lt (m := m) (n := y) (by omega)
  have hdir :
      dir0CaseIILayerZero (m := m) (i, k) = 1 :=
    dir0CaseIILayerZero_eq_one_of_generic (m := m) hi0 hi1 hk0 hk1 hkneg1 hkneg2
  have hi2k : i + 2 * k = (2 : ZMod m) := by
    have h := congrArg (fun u : P0Coord m => u.1 + 2 * u.2) hxy
    simpa [fromXY] using h.symm
  have hsum1 : i + k ≠ 1 := by
    intro h
    have hkone : k = (1 : ZMod m) := by
      calc
        k = (i + 2 * k) - (i + k) := by ring
        _ = (2 : ZMod m) - 1 := by rw [hi2k, h]
        _ = 1 := by ring
    have hy_ne_one : (((y : ℕ) : ZMod m)) ≠ 1 := by
      exact natCast_ne_one_of_two_le_lt (m := m) (n := y) (by omega) hylt
    exact hy_ne_one (by simpa [k] using hkone)
  have hret := returnMap0CaseII_of_dir1_generic (m := m) (u := (i, k)) hdir hi0 hsum1
  calc
    returnMap0CaseIIXY (m := m) ((2 : ZMod m), k)
        = toXY (m := m)
            (returnMap0CaseII (m := m)
              (fromXY (m := m) ((2 : ZMod m), k))) := by
                simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) (i, k)) := by rw [hxy]
    _ = toXY (m := m) (i - 2, k + 1) := by rw [hret]
    _ = ((2 : ZMod m), k + 1) := by
          ext
          · calc
              (i - 2) + 2 * (k + 1) = i + 2 * k := by ring
              _ = (2 : ZMod m) := hi2k
          · rfl
    _ = ((2 : ZMod m), (((y + 1 : ℕ) : ZMod m))) := by
          simp [k, Nat.cast_add]

theorem iterate_returnMap0CaseIIXY_two_column_lower_partial [Fact (9 < m)] (hm : m % 12 = 10)
    {t : ℕ} (ht : t ≤ m / 2 - 1) :
    ((returnMap0CaseIIXY (m := m)^[t]) ((2 : ZMod m), (2 : ZMod m))) =
      ((2 : ZMod m), (((2 + t : ℕ) : ZMod m))) := by
  induction t with
  | zero =>
      simp
  | succ t iht =>
      have ht' : t ≤ m / 2 - 1 := Nat.le_of_succ_le ht
      have hstep :
          returnMap0CaseIIXY (m := m) ((2 : ZMod m), (((2 + t : ℕ) : ZMod m))) =
            ((2 : ZMod m), (((2 + t + 1 : ℕ) : ZMod m))) := by
        have hy2 : 2 ≤ 2 + t := by omega
        have hyle : 2 + t ≤ m / 2 := by omega
        simpa [Nat.add_assoc] using
          returnMap0CaseIIXY_two_column_lower_step (m := m) hm (y := 2 + t) hy2 hyle
      calc
        ((returnMap0CaseIIXY (m := m)^[t.succ]) ((2 : ZMod m), (2 : ZMod m)))
            = returnMap0CaseIIXY (m := m)
                (((returnMap0CaseIIXY (m := m)^[t]) ((2 : ZMod m), (2 : ZMod m)))) := by
                    rw [Function.iterate_succ_apply']
        _ = returnMap0CaseIIXY (m := m) ((2 : ZMod m), (((2 + t : ℕ) : ZMod m))) := by
              rw [iht ht']
        _ = ((2 : ZMod m), (((2 + t + 1 : ℕ) : ZMod m))) := hstep
        _ = ((2 : ZMod m), (((2 + t.succ : ℕ) : ZMod m))) := by
              simp [Nat.succ_eq_add_one, Nat.add_assoc]

theorem iterate_returnMap0CaseIIXY_two_column_to_upper_start [Fact (9 < m)] (hm : m % 12 = 10) :
    ((returnMap0CaseIIXY (m := m)^[m / 2]) ((2 : ZMod m), (2 : ZMod m))) =
      ((2 : ZMod m), (((m / 2 + 2 : ℕ) : ZMod m))) := by
  calc
    ((returnMap0CaseIIXY (m := m)^[m / 2]) ((2 : ZMod m), (2 : ZMod m)))
        = returnMap0CaseIIXY (m := m)
            (((returnMap0CaseIIXY (m := m)^[m / 2 - 1]) ((2 : ZMod m), (2 : ZMod m)))) := by
                simpa [show 1 + (m / 2 - 1) = m / 2 by omega] using
                  (Function.iterate_add_apply (returnMap0CaseIIXY (m := m)) 1 (m / 2 - 1)
                    ((2 : ZMod m), (2 : ZMod m)))
    _ = returnMap0CaseIIXY (m := m) ((2 : ZMod m), (((m / 2 + 1 : ℕ) : ZMod m))) := by
          rw [iterate_returnMap0CaseIIXY_two_column_lower_partial (m := m) hm
            (t := m / 2 - 1) le_rfl]
          have hsum : 2 + (m / 2 - 1) = m / 2 + 1 := by omega
          simp [hsum]
    _ = ((2 : ZMod m), (((m / 2 + 2 : ℕ) : ZMod m))) := by
          exact returnMap0CaseIIXY_two_column_mid_step (m := m) hm

theorem iterate_returnMap0CaseIIXY_two_column_upper_partial [Fact (9 < m)] {t : ℕ}
    (ht : t ≤ m / 2 - 4) :
    ((returnMap0CaseIIXY (m := m)^[t]) ((2 : ZMod m), (((m / 2 + 2 : ℕ) : ZMod m)))) =
      ((2 : ZMod m), (((m / 2 + 2 + t : ℕ) : ZMod m))) := by
  induction t with
  | zero =>
      simp
  | succ t iht =>
      have ht' : t ≤ m / 2 - 4 := Nat.le_of_succ_le ht
      have hstep :
          returnMap0CaseIIXY (m := m) ((2 : ZMod m), (((m / 2 + 2 + t : ℕ) : ZMod m))) =
            ((2 : ZMod m), (((m / 2 + 2 + t + 1 : ℕ) : ZMod m))) := by
        have hyl : m / 2 + 2 ≤ m / 2 + 2 + t := by omega
        have hyu : m / 2 + 2 + t ≤ m - 3 := by omega
        simpa [Nat.add_assoc] using
          returnMap0CaseIIXY_two_column_upper_step (m := m) (y := m / 2 + 2 + t) hyl hyu
      calc
        ((returnMap0CaseIIXY (m := m)^[t.succ]) ((2 : ZMod m), (((m / 2 + 2 : ℕ) : ZMod m))))
            = returnMap0CaseIIXY (m := m)
                (((returnMap0CaseIIXY (m := m)^[t]) ((2 : ZMod m), (((m / 2 + 2 : ℕ) : ZMod m))))) := by
                    rw [Function.iterate_succ_apply']
        _ = returnMap0CaseIIXY (m := m) ((2 : ZMod m), (((m / 2 + 2 + t : ℕ) : ZMod m))) := by
              rw [iht ht']
        _ = ((2 : ZMod m), (((m / 2 + 2 + t + 1 : ℕ) : ZMod m))) := hstep
        _ = ((2 : ZMod m), (((m / 2 + 2 + t.succ : ℕ) : ZMod m))) := by
              simp [Nat.succ_eq_add_one, Nat.add_assoc]

theorem returnMap0CaseIIXY_two_column_m_sub_two [Fact (9 < m)] :
    returnMap0CaseIIXY (m := m) ((2 : ZMod m), (((m - 2 : ℕ) : ZMod m))) =
      ((2 : ZMod m), (((m - 1 : ℕ) : ZMod m))) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let preTop : QCoord m := ((((6 : ℕ) : ZMod m)), (-2 : ZMod m))
  have hxy : fromXY (m := m) ((2 : ZMod m), (((m - 2 : ℕ) : ZMod m))) = preTop := by
    ext <;> simp [preTop, fromXY, cast_sub_two_eq_neg_two (m := m) (by omega)]
    all_goals ring_nf
  have h6lt : 6 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  have hi0 : preTop.1 ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := 6) (by omega) h6lt
  have hi1 : preTop.1 ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := 6) (by omega) h6lt
  have hi2 : preTop.1 ≠ 2 := by
    exact natCast_ne_two_of_three_le_lt (m := m) (n := 6) (by omega) h6lt
  have hdir :
      dir0CaseIILayerZero (m := m) preTop = 1 :=
    dir0CaseIILayerZero_eq_one_of_k_neg_two_generic (m := m) hi0 hi1 hi2
  have hsum1 : preTop.1 + preTop.2 ≠ 1 := by
    intro h
    have hbad : (4 : ZMod m) = 1 := by
      calc
        (4 : ZMod m) = preTop.1 + preTop.2 := by
          simp [preTop]
          ring
        _ = 1 := h
    exact natCast_ne_one_of_two_le_lt (m := m) (n := 4) (by omega) (by omega) hbad
  have hret := returnMap0CaseII_of_dir1_generic (m := m) (u := preTop) hdir hi0 hsum1
  calc
    returnMap0CaseIIXY (m := m) ((2 : ZMod m), (((m - 2 : ℕ) : ZMod m)))
        = toXY (m := m)
            (returnMap0CaseII (m := m)
              (fromXY (m := m) ((2 : ZMod m), (((m - 2 : ℕ) : ZMod m))))) := by
                simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) preTop) := by rw [hxy]
    _ = toXY (m := m) (preTop.1 - 2, preTop.2 + 1) := by
          simpa using congrArg (toXY (m := m)) hret
    _ = ((2 : ZMod m), (-1 : ZMod m)) := by
          ext <;> simp [toXY, preTop]
          all_goals ring_nf
    _ = ((2 : ZMod m), (((m - 1 : ℕ) : ZMod m))) := by
          rw [cast_sub_one_eq_neg_one (m := m) (by omega)]

theorem returnMap0CaseIIXY_two_column_m_sub_one [Fact (9 < m)] :
    returnMap0CaseIIXY (m := m) ((2 : ZMod m), (((m - 1 : ℕ) : ZMod m))) =
      ((2 : ZMod m), (0 : ZMod m)) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let preTop : QCoord m := ((((4 : ℕ) : ZMod m)), (-1 : ZMod m))
  have hxy : fromXY (m := m) ((2 : ZMod m), (((m - 1 : ℕ) : ZMod m))) = preTop := by
    ext <;> simp [preTop, fromXY, cast_sub_one_eq_neg_one (m := m) (by omega)]
    all_goals ring_nf
  have h4lt : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  have hi0 : preTop.1 ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := 4) (by omega) h4lt
  have hi1 : preTop.1 ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := 4) (by omega) h4lt
  have hi2 : preTop.1 ≠ 2 := by
    exact natCast_ne_two_of_three_le_lt (m := m) (n := 4) (by omega) h4lt
  have hdir :
      dir0CaseIILayerZero (m := m) preTop = 1 :=
    dir0CaseIILayerZero_eq_one_of_k_neg_one_generic (m := m) hi0 hi1 hi2
  have hsum1 : preTop.1 + preTop.2 ≠ 1 := by
    intro h
    have hbad : (3 : ZMod m) = 1 := by
      calc
        (3 : ZMod m) = preTop.1 + preTop.2 := by
          simp [preTop]
          ring
        _ = 1 := h
    exact natCast_ne_one_of_two_le_lt (m := m) (n := 3) (by omega) (by omega) hbad
  have hret := returnMap0CaseII_of_dir1_generic (m := m) (u := preTop) hdir hi0 hsum1
  calc
    returnMap0CaseIIXY (m := m) ((2 : ZMod m), (((m - 1 : ℕ) : ZMod m)))
        = toXY (m := m)
            (returnMap0CaseII (m := m)
              (fromXY (m := m) ((2 : ZMod m), (((m - 1 : ℕ) : ZMod m))))) := by
                simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) preTop) := by rw [hxy]
    _ = toXY (m := m) (preTop.1 - 2, preTop.2 + 1) := by
          simpa using congrArg (toXY (m := m)) hret
    _ = ((2 : ZMod m), (0 : ZMod m)) := by
          ext <;> simp [toXY, preTop]
          all_goals ring_nf

theorem iterate_returnMap0CaseIIXY_two_column_to_zero_core [Fact (9 < m)]
    (hhalf : 2 * (m / 2) = m)
    (hupperStart :
      ((returnMap0CaseIIXY (m := m)^[m / 2]) ((2 : ZMod m), (2 : ZMod m))) =
        ((2 : ZMod m), (((m / 2 + 2 : ℕ) : ZMod m)))) :
    ((returnMap0CaseIIXY (m := m)^[m - 2]) ((2 : ZMod m), (2 : ZMod m))) =
      ((2 : ZMod m), (0 : ZMod m)) := by
  let F := returnMap0CaseIIXY (m := m)
  have hhalf' : m / 2 + m / 2 = m := by
    simpa [two_mul, add_comm, add_left_comm, add_assoc] using hhalf
  have hm10 : 10 ≤ m := by
    have hm9 : 9 < m := Fact.out
    omega
  have hupper :
      ((F^[m / 2 - 4]) ((2 : ZMod m), (((m / 2 + 2 : ℕ) : ZMod m)))) =
        ((2 : ZMod m), (((m - 2 : ℕ) : ZMod m))) := by
    rw [iterate_returnMap0CaseIIXY_two_column_upper_partial (m := m) (t := m / 2 - 4) le_rfl]
    have hsum : m / 2 + 2 + (m / 2 - 4) = m - 2 := by
      calc
        m / 2 + 2 + (m / 2 - 4) = (m / 2 + m / 2) - 2 := by
          omega
        _ = m - 2 := by rw [hhalf']
    simp [hsum]
  calc
    ((F^[m - 2]) ((2 : ZMod m), (2 : ZMod m)))
        = ((F^[2]) ((F^[m / 2 - 4]) ((F^[m / 2]) ((2 : ZMod m), (2 : ZMod m))))) := by
            have hsplit : m - 2 = 2 + ((m / 2 - 4) + m / 2) := by
              calc
                m - 2 = (m / 2 + m / 2) - 2 := by rw [hhalf']
                _ = 2 + ((m / 2 - 4) + m / 2) := by
                  omega
            rw [hsplit]
            rw [Function.iterate_add_apply, Function.iterate_add_apply]
    _ = ((F^[2]) ((F^[m / 2 - 4]) ((2 : ZMod m), (((m / 2 + 2 : ℕ) : ZMod m))))) := by
          rw [hupperStart]
    _ = ((F^[2]) ((2 : ZMod m), (((m - 2 : ℕ) : ZMod m)))) := by rw [hupper]
    _ = F (F ((2 : ZMod m), (((m - 2 : ℕ) : ZMod m)))) := by
          simp [Function.iterate_succ_apply']
    _ = F ((2 : ZMod m), (((m - 1 : ℕ) : ZMod m))) := by
          simpa [F] using congrArg F (returnMap0CaseIIXY_two_column_m_sub_two (m := m))
    _ = ((2 : ZMod m), (0 : ZMod m)) := by
          simpa [F] using returnMap0CaseIIXY_two_column_m_sub_one (m := m)

theorem iterate_returnMap0CaseIIXY_two_column_to_zero [Fact (9 < m)] (hm : m % 12 = 10) :
    ((returnMap0CaseIIXY (m := m)^[m - 2]) ((2 : ZMod m), (2 : ZMod m))) =
      ((2 : ZMod m), (0 : ZMod m)) := by
  have hhalf : 2 * (m / 2) = m := by
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rw [hq]
    omega
  exact iterate_returnMap0CaseIIXY_two_column_to_zero_core (m := m) hhalf
    (iterate_returnMap0CaseIIXY_two_column_to_upper_start (m := m) hm)

theorem returnMap0CaseIIXY_A_line [Fact (9 < m)] {y : ℕ}
    (hy2 : 2 ≤ y) (hyle : y ≤ m - 3) :
    returnMap0CaseIIXY (m := m) ((((y + 1 : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))) =
      ((((y + 2 : ℕ) : ZMod m)), (((y + 2 : ℕ) : ZMod m))) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let preA : QCoord m := ((((m + 1 - y : ℕ) : ZMod m)), (((y : ℕ) : ZMod m)))
  have hxy : fromXY (m := m) ((((y + 1 : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))) = preA := by
    ext <;> simp [preA, fromXY]
    · have hle : y ≤ m + 1 := by omega
      rw [Nat.cast_sub hle, Nat.cast_add]
      simp
      ring_nf
  have hipos : 0 < m + 1 - y := by omega
  have hilt : m + 1 - y < m := by omega
  have hitwo : 2 ≤ m + 1 - y := by omega
  have hi0 : preA.1 ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := m + 1 - y) hipos hilt
  have hi1 : preA.1 ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := m + 1 - y) hitwo hilt
  have hk0 : preA.2 ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := y) (by omega) (by omega)
  have hk1 : preA.2 ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := y) hy2 (by omega)
  have hkneg1 : preA.2 ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := y) (by omega)
  have hkneg2 : preA.2 ≠ (-2 : ZMod m) := by
    exact natCast_ne_neg_two_of_lt (m := m) (n := y) (by omega)
  have hdir :
      dir0CaseIILayerZero (m := m) preA = 1 :=
    dir0CaseIILayerZero_eq_one_of_generic (m := m) hi0 hi1 hk0 hk1 hkneg1 hkneg2
  have hsum1 : preA.1 + preA.2 = 1 := by
    change ((((m + 1 - y : ℕ) : ZMod m)) + (((y : ℕ) : ZMod m))) = (1 : ZMod m)
    have hnat : (m + 1 - y) + y = m + 1 := by omega
    calc
      ((((m + 1 - y : ℕ) : ZMod m)) + (((y : ℕ) : ZMod m)))
          = (((m + 1 : ℕ) : ZMod m)) := by
              simpa [Nat.cast_add] using congrArg (fun n : ℕ => (((n : ℕ) : ZMod m))) hnat
      _ = (1 : ZMod m) := by simp [Nat.cast_add]
  have hi2k : preA.1 + 2 * preA.2 = ((((y + 1 : ℕ) : ZMod m))) := by
    have h := congrArg (fun u : P0Coord m => u.1 + 2 * u.2) hxy
    simpa [fromXY] using h.symm
  have hret := returnMap0CaseII_of_dir1_sum_one (m := m) (u := preA) hdir hi0 hsum1
  calc
    returnMap0CaseIIXY (m := m) ((((y + 1 : ℕ) : ZMod m)), (((y : ℕ) : ZMod m)))
        = toXY (m := m)
            (returnMap0CaseII (m := m) (fromXY (m := m) ((((y + 1 : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))))) := by
              simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) preA) := by rw [hxy]
    _ = toXY (m := m) (preA.1 - 3, preA.2 + 2) := by
          simpa using congrArg (toXY (m := m)) hret
    _ = ((((y + 2 : ℕ) : ZMod m)), (((y + 2 : ℕ) : ZMod m))) := by
          ext
          · calc
              (preA.1 - 3) + 2 * (preA.2 + 2) = preA.1 + 2 * preA.2 + 1 := by ring
              _ = ((((y + 1 : ℕ) : ZMod m))) + 1 := by rw [hi2k]
              _ = ((((y + 2 : ℕ) : ZMod m))) := by
                    rw [show (((y + 1 : ℕ) : ZMod m)) = (((y : ℕ) : ZMod m)) + 1 by
                      simp [Nat.cast_add]]
                    simp [Nat.cast_add]
                    ring_nf
          · change ((((y : ℕ) : ZMod m)) + 2) = ((((y + 2 : ℕ) : ZMod m)))
            simp [Nat.cast_add]

theorem returnMap0CaseIIXY_odd_generic_even_column_one_step [Fact (9 < m)] {x : ℕ}
    (hx3 : 3 ≤ x) (hxle : x ≤ m - 3) (hxodd : Odd x) :
    returnMap0CaseIIXY (m := m) ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m)) =
      ((((x + 1 : ℕ) : ZMod m)), (2 : ZMod m)) := by
  let _ := hxodd
  have hm4 : 4 < m := by omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let pre : QCoord m := ((((x - 1 : ℕ) : ZMod m)), (1 : ZMod m))
  have hxy : fromXY (m := m) ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m)) = pre := by
    ext <;> simp [pre, fromXY]
    · calc
        (((x : ℕ) : ZMod m)) + 1 - 2 = (((x : ℕ) : ZMod m)) - 1 := by ring
        _ = (((x - 1 : ℕ) : ZMod m)) := by
              rw [Nat.cast_sub (by omega)]
              simp
  have hi0 : pre.1 ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := x - 1) (by omega) (by omega)
  have hi1 : pre.1 ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := x - 1) (by omega) (by omega)
  have hineg1 : pre.1 ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := x - 1) (by omega)
  have hineg2 : pre.1 ≠ (-2 : ZMod m) := by
    exact natCast_ne_neg_two_of_lt (m := m) (n := x - 1) (by omega)
  have hdir :
      dir0CaseIILayerZero (m := m) pre = 1 :=
    dir0CaseIILayerZero_eq_one_of_k_one_generic (m := m) hi0 hi1 hineg1 hineg2
  have hsum1 : pre.1 + pre.2 ≠ 1 := by
    have hxne1 : (((x : ℕ) : ZMod m)) ≠ 1 := by
      exact natCast_ne_one_of_two_le_lt (m := m) (n := x) (by omega) (by omega)
    intro h
    have hcast : (((x : ℕ) : ZMod m)) = 1 := by
      change ((((x - 1 : ℕ) : ZMod m)) + (1 : ZMod m)) = 1 at h
      calc
        (((x : ℕ) : ZMod m))
            = (((x - 1 : ℕ) : ZMod m)) + (1 : ZMod m) := by
                have hnat : x = (x - 1) + 1 := by omega
                simpa [Nat.cast_add] using congrArg (fun n : ℕ => (((n : ℕ) : ZMod m))) hnat
        _ = 1 := h
    exact hxne1 hcast
  have hi2k : pre.1 + 2 * pre.2 = (((x + 1 : ℕ) : ZMod m)) := by
    have h := congrArg (fun u : P0Coord m => u.1 + 2 * u.2) hxy
    simpa [fromXY] using h.symm
  have hret := returnMap0CaseII_of_dir1_generic (m := m) (u := pre) hdir hi0 hsum1
  calc
    returnMap0CaseIIXY (m := m) ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m))
        = toXY (m := m)
            (returnMap0CaseII (m := m) (fromXY (m := m) ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m)))) := by
              simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) pre) := by rw [hxy]
    _ = toXY (m := m) (pre.1 - 2, pre.2 + 1) := by
          simpa using congrArg (toXY (m := m)) hret
    _ = ((((x + 1 : ℕ) : ZMod m)), (2 : ZMod m)) := by
          ext
          · calc
              (pre.1 - 2) + 2 * (pre.2 + 1) = pre.1 + 2 * pre.2 := by ring
              _ = (((x + 1 : ℕ) : ZMod m)) := hi2k
          · norm_num [toXY, pre]

theorem returnMap0CaseIIXY_odd_generic_even_column_lower_step [Fact (9 < m)] {x y : ℕ}
    (hx3 : 3 ≤ x) (hxle : x ≤ m - 3) (hxodd : Odd x)
    (hy2 : 2 ≤ y) (hyle : y ≤ (x - 1) / 2) :
    returnMap0CaseIIXY (m := m) ((((x + 1 : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))) =
      ((((x + 1 : ℕ) : ZMod m)), (((y + 1 : ℕ) : ZMod m))) := by
  let _ := hxodd
  have hm4 : 4 < m := by omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let pre : QCoord m := ((((x + 1 - 2 * y : ℕ) : ZMod m)), (((y : ℕ) : ZMod m)))
  have hxy : fromXY (m := m) ((((x + 1 : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))) = pre := by
    ext <;> simp [pre, fromXY]
    · have hle : 2 * y ≤ x + 1 := by omega
      rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul]
      simp
  have hi0 : pre.1 ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := x + 1 - 2 * y) (by omega) (by omega)
  have hi1 : pre.1 ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := x + 1 - 2 * y) (by omega) (by omega)
  have hk0 : pre.2 ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := y) (by omega) (by omega)
  have hk1 : pre.2 ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := y) hy2 (by omega)
  have hkneg1 : pre.2 ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := y) (by omega)
  have hkneg2 : pre.2 ≠ (-2 : ZMod m) := by
    exact natCast_ne_neg_two_of_lt (m := m) (n := y) (by omega)
  have hdir :
      dir0CaseIILayerZero (m := m) pre = 1 :=
    dir0CaseIILayerZero_eq_one_of_generic (m := m) hi0 hi1 hk0 hk1 hkneg1 hkneg2
  have hsum1 : pre.1 + pre.2 ≠ 1 := by
    intro h
    have hcast : (((x + 1 - y : ℕ) : ZMod m)) = 1 := by
      calc
        (((x + 1 - y : ℕ) : ZMod m))
            = ((((x + 1 - 2 * y : ℕ) : ZMod m)) + (((y : ℕ) : ZMod m))) := by
                have hnat : x + 1 - y = (x + 1 - 2 * y) + y := by omega
                simpa [Nat.cast_add] using congrArg (fun n : ℕ => (((n : ℕ) : ZMod m))) hnat
        _ = 1 := h
    have hxny_ne : (((x + 1 - y : ℕ) : ZMod m)) ≠ 1 := by
      exact natCast_ne_one_of_two_le_lt (m := m) (n := x + 1 - y) (by omega) (by omega)
    exact hxny_ne hcast
  have hi2k : pre.1 + 2 * pre.2 = (((x + 1 : ℕ) : ZMod m)) := by
    have h := congrArg (fun u : P0Coord m => u.1 + 2 * u.2) hxy
    simpa [fromXY] using h.symm
  have hret := returnMap0CaseII_of_dir1_generic (m := m) (u := pre) hdir hi0 hsum1
  calc
    returnMap0CaseIIXY (m := m) ((((x + 1 : ℕ) : ZMod m)), (((y : ℕ) : ZMod m)))
        = toXY (m := m)
            (returnMap0CaseII (m := m) (fromXY (m := m) ((((x + 1 : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))))) := by
              simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) pre) := by rw [hxy]
    _ = toXY (m := m) (pre.1 - 2, pre.2 + 1) := by
          simpa using congrArg (toXY (m := m)) hret
    _ = ((((x + 1 : ℕ) : ZMod m)), (((y + 1 : ℕ) : ZMod m))) := by
          ext
          · calc
              (pre.1 - 2) + 2 * (pre.2 + 1) = pre.1 + 2 * pre.2 := by ring
              _ = (((x + 1 : ℕ) : ZMod m)) := hi2k
          · simp [toXY, pre, Nat.cast_add]

theorem iterate_returnMap0CaseIIXY_odd_generic_even_column_lower_partial [Fact (9 < m)] {x t : ℕ}
    (hx3 : 3 ≤ x) (hxle : x ≤ m - 3) (hxodd : Odd x)
    (ht : t ≤ (x - 1) / 2 - 1) :
    ((returnMap0CaseIIXY (m := m)^[t]) ((((x + 1 : ℕ) : ZMod m)), (2 : ZMod m))) =
      ((((x + 1 : ℕ) : ZMod m)), (((2 + t : ℕ) : ZMod m))) := by
  induction t with
  | zero =>
      simp
  | succ t iht =>
      have ht' : t ≤ (x - 1) / 2 - 1 := Nat.le_of_succ_le ht
      have hstep :
          returnMap0CaseIIXY (m := m) ((((x + 1 : ℕ) : ZMod m)), (((2 + t : ℕ) : ZMod m))) =
            ((((x + 1 : ℕ) : ZMod m)), (((2 + t + 1 : ℕ) : ZMod m))) := by
        have hy2 : 2 ≤ 2 + t := by omega
        have hyle : 2 + t ≤ (x - 1) / 2 := by omega
        simpa [Nat.add_assoc] using
          returnMap0CaseIIXY_odd_generic_even_column_lower_step (m := m) hx3 hxle hxodd
            (y := 2 + t) hy2 hyle
      calc
        ((returnMap0CaseIIXY (m := m)^[t.succ]) ((((x + 1 : ℕ) : ZMod m)), (2 : ZMod m)))
            = returnMap0CaseIIXY (m := m)
                (((returnMap0CaseIIXY (m := m)^[t]) ((((x + 1 : ℕ) : ZMod m)), (2 : ZMod m)))) := by
                    rw [Function.iterate_succ_apply']
        _ = returnMap0CaseIIXY (m := m) ((((x + 1 : ℕ) : ZMod m)), (((2 + t : ℕ) : ZMod m))) := by
              rw [iht ht']
        _ = ((((x + 1 : ℕ) : ZMod m)), (((2 + t + 1 : ℕ) : ZMod m))) := hstep
        _ = ((((x + 1 : ℕ) : ZMod m)), (((2 + t.succ : ℕ) : ZMod m))) := by
              simp [Nat.succ_eq_add_one, Nat.add_assoc]

theorem returnMap0CaseIIXY_odd_generic_even_column_mid_step [Fact (9 < m)] {x : ℕ}
    (hx3 : 3 ≤ x) (hxle : x ≤ m - 3) (hxodd : Odd x) :
    returnMap0CaseIIXY (m := m)
      ((((x + 1 : ℕ) : ZMod m)), ((((x - 1) / 2 + 1 : ℕ) : ZMod m))) =
        ((((x + 1 : ℕ) : ZMod m)), ((((x - 1) / 2 + 2 : ℕ) : ZMod m))) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let midK : ZMod m := ((((x - 1) / 2 + 1 : ℕ) : ZMod m))
  have hxy : fromXY (m := m) ((((x + 1 : ℕ) : ZMod m)), midK) = ((0 : ZMod m), midK) := by
    ext <;> simp [midK, fromXY]
    · rcases hxodd with ⟨r, hr⟩
      rw [hr]
      have hnat : (2 * r + 1) + 1 = 2 * (((2 * r + 1 - 1) / 2) + 1) := by omega
      simpa [Nat.cast_add, Nat.cast_mul] using congrArg (fun n : ℕ => (((n : ℕ) : ZMod m))) hnat
  have hk0 : midK ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := (x - 1) / 2 + 1) (by omega) (by omega)
  have hkneg1 : midK ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := (x - 1) / 2 + 1) (by omega)
  have hdir :
      dir0CaseIILayerZero (m := m) ((0 : ZMod m), midK) = 2 :=
    dir0CaseIILayerZero_eq_two_of_i_zero (m := m) hk0 hkneg1
  have hk1 : midK ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := (x - 1) / 2 + 1) (by omega) (by omega)
  have hret := returnMap0CaseII_of_dir2_i_zero_generic (m := m) (k := midK) hdir hk1
  have h2k : 2 * midK = (((x + 1 : ℕ) : ZMod m)) := by
    change (2 : ZMod m) * ((((x - 1) / 2 + 1 : ℕ) : ZMod m)) = (((x + 1 : ℕ) : ZMod m))
    rcases hxodd with ⟨r, hr⟩
    rw [hr]
    have hnat : 2 * (((2 * r + 1 - 1) / 2) + 1) = (2 * r + 1) + 1 := by omega
    simpa [Nat.cast_add, Nat.cast_mul] using congrArg (fun n : ℕ => (((n : ℕ) : ZMod m))) hnat
  calc
    returnMap0CaseIIXY (m := m) ((((x + 1 : ℕ) : ZMod m)), midK)
        = toXY (m := m)
            (returnMap0CaseII (m := m) (fromXY (m := m) ((((x + 1 : ℕ) : ZMod m)), midK))) := by
              simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) ((0 : ZMod m), midK)) := by rw [hxy]
    _ = toXY (m := m) ((-2 : ZMod m), midK + 1) := by rw [hret]
    _ = ((((x + 1 : ℕ) : ZMod m)), midK + 1) := by
          have h2k' : midK * 2 = (((x + 1 : ℕ) : ZMod m)) := by simpa [mul_comm] using h2k
          ext
          · calc
              (-2 : ZMod m) + 2 * (midK + 1) = midK * 2 := by ring
              _ = (((x + 1 : ℕ) : ZMod m)) := h2k'
          · rfl
    _ = ((((x + 1 : ℕ) : ZMod m)), ((((x - 1) / 2 + 2 : ℕ) : ZMod m))) := by
          change ((((x + 1 : ℕ) : ZMod m)), ((((x - 1) / 2 + 1 : ℕ) : ZMod m) + 1)) =
            ((((x + 1 : ℕ) : ZMod m)), ((((x - 1) / 2 + 2 : ℕ) : ZMod m)))
          ext
          · rfl
          · simp [Nat.cast_add]
            ring_nf

theorem returnMap0CaseIIXY_odd_generic_even_column_upper_step [Fact (9 < m)] {x y : ℕ}
    (hx3 : 3 ≤ x) (hxle : x ≤ m - 3) (hxodd : Odd x)
    (hyl : (x - 1) / 2 + 2 ≤ y) (hyu : y ≤ x - 1) :
    returnMap0CaseIIXY (m := m) ((((x + 1 : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))) =
      ((((x + 1 : ℕ) : ZMod m)), (((y + 1 : ℕ) : ZMod m))) := by
  let _ := hxodd
  have hm4 : 4 < m := by omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let pre : QCoord m := ((((m + x + 1 - 2 * y : ℕ) : ZMod m)), (((y : ℕ) : ZMod m)))
  have hxy : fromXY (m := m) ((((x + 1 : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))) = pre := by
    ext <;> simp [pre, fromXY]
    · have hle : 2 * y ≤ m + x + 1 := by omega
      rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul]
      simp
  have hi0 : pre.1 ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := m + x + 1 - 2 * y) (by omega) (by omega)
  have hi1 : pre.1 ≠ 1 := by
    have hitwo : 2 ≤ m + x + 1 - 2 * y := by
      have hbase : 2 ≤ m - x + 3 := by omega
      have hlow : m - x + 3 ≤ m + x + 1 - 2 * y := by omega
      omega
    exact natCast_ne_one_of_two_le_lt (m := m) (n := m + x + 1 - 2 * y) hitwo (by omega)
  have hk0 : pre.2 ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := y) (by omega) (by omega)
  have hk1 : pre.2 ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := y) (by omega) (by omega)
  have hkneg1 : pre.2 ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := y) (by omega)
  have hkneg2 : pre.2 ≠ (-2 : ZMod m) := by
    exact natCast_ne_neg_two_of_lt (m := m) (n := y) (by omega)
  have hdir :
      dir0CaseIILayerZero (m := m) pre = 1 :=
    dir0CaseIILayerZero_eq_one_of_generic (m := m) hi0 hi1 hk0 hk1 hkneg1 hkneg2
  have hsum1 : pre.1 + pre.2 ≠ 1 := by
    intro h
    have hxny_ne : (((m + x + 1 - y : ℕ) : ZMod m)) ≠ 1 := by
      intro h1
      have hred : (((x + 1 - y : ℕ) : ZMod m)) = 1 := by
        have hnat : m + x + 1 - y = m + (x + 1 - y) := by omega
        calc
          (((x + 1 - y : ℕ) : ZMod m)) = (((m + (x + 1 - y) : ℕ) : ZMod m)) := by
              rw [Nat.cast_add]
              simp
          _ = (((m + x + 1 - y : ℕ) : ZMod m)) := by rw [hnat]
          _ = 1 := h1
      exact natCast_ne_one_of_two_le_lt (m := m) (n := x + 1 - y) (by omega) (by omega) hred
    have hcast : (((m + x + 1 - y : ℕ) : ZMod m)) = 1 := by
      calc
        (((m + x + 1 - y : ℕ) : ZMod m))
            = ((((m + x + 1 - 2 * y : ℕ) : ZMod m)) + (((y : ℕ) : ZMod m))) := by
                have hnat : m + x + 1 - y = (m + x + 1 - 2 * y) + y := by omega
                simpa [Nat.cast_add] using congrArg (fun n : ℕ => (((n : ℕ) : ZMod m))) hnat
        _ = 1 := h
    exact hxny_ne hcast
  have hi2k : pre.1 + 2 * pre.2 = (((x + 1 : ℕ) : ZMod m)) := by
    have h := congrArg (fun u : P0Coord m => u.1 + 2 * u.2) hxy
    simpa [fromXY] using h.symm
  have hret := returnMap0CaseII_of_dir1_generic (m := m) (u := pre) hdir hi0 hsum1
  calc
    returnMap0CaseIIXY (m := m) ((((x + 1 : ℕ) : ZMod m)), (((y : ℕ) : ZMod m)))
        = toXY (m := m)
            (returnMap0CaseII (m := m) (fromXY (m := m) ((((x + 1 : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))))) := by
              simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) pre) := by rw [hxy]
    _ = toXY (m := m) (pre.1 - 2, pre.2 + 1) := by
          simpa using congrArg (toXY (m := m)) hret
    _ = ((((x + 1 : ℕ) : ZMod m)), (((y + 1 : ℕ) : ZMod m))) := by
          ext
          · calc
              (pre.1 - 2) + 2 * (pre.2 + 1) = pre.1 + 2 * pre.2 := by ring
              _ = (((x + 1 : ℕ) : ZMod m)) := hi2k
          · simp [toXY, pre, Nat.cast_add]

theorem iterate_returnMap0CaseIIXY_odd_generic_even_column_upper_partial [Fact (9 < m)] {x t : ℕ}
    (hx3 : 3 ≤ x) (hxle : x ≤ m - 3) (hxodd : Odd x)
    (ht : t ≤ (x - 1) / 2 - 1) :
    ((returnMap0CaseIIXY (m := m)^[t])
      ((((x + 1 : ℕ) : ZMod m)), ((((x - 1) / 2 + 2 : ℕ) : ZMod m)))) =
      ((((x + 1 : ℕ) : ZMod m)), (((((x - 1) / 2 + 2) + t : ℕ) : ZMod m))) := by
  induction t with
  | zero =>
      simp
  | succ t iht =>
      have ht' : t ≤ (x - 1) / 2 - 1 := Nat.le_of_succ_le ht
      have hstep :
          returnMap0CaseIIXY (m := m)
            ((((x + 1 : ℕ) : ZMod m)), (((((x - 1) / 2 + 2) + t : ℕ) : ZMod m))) =
              ((((x + 1 : ℕ) : ZMod m)), (((((x - 1) / 2 + 2) + t + 1 : ℕ) : ZMod m))) := by
        have hyl : (x - 1) / 2 + 2 ≤ ((x - 1) / 2 + 2) + t := by omega
        have hyu : ((x - 1) / 2 + 2) + t ≤ x - 1 := by omega
        simpa [Nat.add_assoc] using
          returnMap0CaseIIXY_odd_generic_even_column_upper_step (m := m) hx3 hxle hxodd
            (y := ((x - 1) / 2 + 2) + t) hyl hyu
      calc
        ((returnMap0CaseIIXY (m := m)^[t.succ])
            ((((x + 1 : ℕ) : ZMod m)), ((((x - 1) / 2 + 2 : ℕ) : ZMod m))))
            = returnMap0CaseIIXY (m := m)
                (((returnMap0CaseIIXY (m := m)^[t])
                  ((((x + 1 : ℕ) : ZMod m)), ((((x - 1) / 2 + 2 : ℕ) : ZMod m))))) := by
                    rw [Function.iterate_succ_apply']
        _ = returnMap0CaseIIXY (m := m)
              ((((x + 1 : ℕ) : ZMod m)), (((((x - 1) / 2 + 2) + t : ℕ) : ZMod m))) := by
                rw [iht ht']
        _ = ((((x + 1 : ℕ) : ZMod m)), (((((x - 1) / 2 + 2) + t + 1 : ℕ) : ZMod m))) := hstep
        _ = ((((x + 1 : ℕ) : ZMod m)), (((((x - 1) / 2 + 2) + t.succ : ℕ) : ZMod m))) := by
              simp [Nat.succ_eq_add_one, Nat.add_assoc]

theorem iterate_returnMap0CaseIIXY_odd_generic_to_A [Fact (9 < m)] {x : ℕ}
    (hx3 : 3 ≤ x) (hxle : x ≤ m - 3) (hxodd : Odd x) :
    ((returnMap0CaseIIXY (m := m)^[x - 1]) ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m))) =
      ((((x + 1 : ℕ) : ZMod m)), (((x : ℕ) : ZMod m))) := by
  let F := returnMap0CaseIIXY (m := m)
  let b : ℕ := (x - 1) / 2
  have hb1 : 1 ≤ b := by
    dsimp [b]
    rcases hxodd with ⟨r, hr⟩
    rw [hr]
    omega
  have h1 :
      ((F^[1]) ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m))) =
        ((((x + 1 : ℕ) : ZMod m)), (2 : ZMod m)) := by
    simpa [Function.iterate_one] using
      returnMap0CaseIIXY_odd_generic_even_column_one_step (m := m) hx3 hxle hxodd
  have h2 :
      ((F^[b]) ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m))) =
        ((((x + 1 : ℕ) : ZMod m)), (((b + 1 : ℕ) : ZMod m))) := by
    have hb_split : b = (b - 1) + 1 := by omega
    have hsplit :
        ((F^[b]) ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m))) =
          ((F^[b - 1]) ((F^[1]) ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m)))) := by
      rw [hb_split]
      exact Function.iterate_add_apply F (b - 1) 1 ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m))
    calc
      ((F^[b]) ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m)))
          = ((F^[b - 1]) ((F^[1]) ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m)))) := hsplit
      _ = ((F^[b - 1]) ((((x + 1 : ℕ) : ZMod m)), (2 : ZMod m))) := by rw [h1]
      _ = ((((x + 1 : ℕ) : ZMod m)), (((2 + (b - 1) : ℕ) : ZMod m))) := by
            rw [iterate_returnMap0CaseIIXY_odd_generic_even_column_lower_partial
              (m := m) hx3 hxle hxodd (t := b - 1) le_rfl]
      _ = ((((x + 1 : ℕ) : ZMod m)), (((b + 1 : ℕ) : ZMod m))) := by
            have hsum : 2 + (b - 1) = b + 1 := by omega
            simp [hsum]
  have h3 :
      ((F^[b + 1]) ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m))) =
        ((((x + 1 : ℕ) : ZMod m)), (((b + 2 : ℕ) : ZMod m))) := by
    calc
      ((F^[b + 1]) ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m)))
          = ((F^[1 + b]) ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m))) := by
              rw [show b + 1 = 1 + b by omega]
      _ = (F^[1]) (((F^[b]) ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m)))) := by
            rw [Function.iterate_add_apply]
      _ = F (((F^[b]) ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m)))) := by
            simp
      _ = F ((((x + 1 : ℕ) : ZMod m)), (((b + 1 : ℕ) : ZMod m))) := by rw [h2]
      _ = ((((x + 1 : ℕ) : ZMod m)), (((b + 2 : ℕ) : ZMod m))) := by
            dsimp [b]
            simpa using returnMap0CaseIIXY_odd_generic_even_column_mid_step
              (m := m) hx3 hxle hxodd
  have h4 :
      ((F^[2 * b]) ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m))) =
        ((((x + 1 : ℕ) : ZMod m)), (((2 * b + 1 : ℕ) : ZMod m))) := by
    calc
      ((F^[2 * b]) ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m)))
          = ((F^[(b - 1) + (b + 1)]) ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m))) := by
              rw [show 2 * b = (b - 1) + (b + 1) by omega]
      _ = ((F^[b - 1]) ((F^[b + 1]) ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m)))) := by
            rw [Function.iterate_add_apply]
      _ = ((F^[b - 1]) ((((x + 1 : ℕ) : ZMod m)), (((b + 2 : ℕ) : ZMod m)))) := by rw [h3]
      _ = ((((x + 1 : ℕ) : ZMod m)), ((((b + 2) + (b - 1) : ℕ) : ZMod m))) := by
            dsimp [b]
            rw [iterate_returnMap0CaseIIXY_odd_generic_even_column_upper_partial
              (m := m) hx3 hxle hxodd (t := b - 1) le_rfl]
      _ = ((((x + 1 : ℕ) : ZMod m)), (((2 * b + 1 : ℕ) : ZMod m))) := by
            have hsum : (b + 2) + (b - 1) = 2 * b + 1 := by omega
            simp [hsum]
  calc
    ((F^[x - 1]) ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m)))
        = ((F^[2 * b]) ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m))) := by
            dsimp [b]
            rcases hxodd with ⟨r, hr⟩
            rw [hr]
            norm_num
    _ = ((((x + 1 : ℕ) : ZMod m)), (((2 * b + 1 : ℕ) : ZMod m))) := h4
    _ = ((((x + 1 : ℕ) : ZMod m)), (((x : ℕ) : ZMod m))) := by
          dsimp [b]
          rcases hxodd with ⟨r, hr⟩
          rw [hr]
          norm_num

theorem returnMap0CaseIIXY_upper_column_step [Fact (9 < m)] {c y : ℕ}
    (hc4 : 4 ≤ c) (hcle : c ≤ m - 3)
    (hyl : c ≤ y) (hyu : y ≤ (m + c - 3) / 2) :
    returnMap0CaseIIXY (m := m) ((((c : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))) =
      ((((c : ℕ) : ZMod m)), (((y + 1 : ℕ) : ZMod m))) := by
  let _ := hcle
  have hm4 : 4 < m := by omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let pre : QCoord m := ((((m + c - 2 * y : ℕ) : ZMod m)), (((y : ℕ) : ZMod m)))
  have hxy : fromXY (m := m) ((((c : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))) = pre := by
    ext <;> simp [pre, fromXY]
    · have hle : 2 * y ≤ m + c := by omega
      rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul]
      simp
  have hi0 : pre.1 ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := m + c - 2 * y) (by omega) (by omega)
  have hi1 : pre.1 ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := m + c - 2 * y) (by omega) (by omega)
  have hk0 : pre.2 ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := y) (by omega) (by omega)
  have hk1 : pre.2 ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := y) (by omega) (by omega)
  have hkneg1 : pre.2 ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := y) (by omega)
  have hkneg2 : pre.2 ≠ (-2 : ZMod m) := by
    exact natCast_ne_neg_two_of_lt (m := m) (n := y) (by omega)
  have hdir :
      dir0CaseIILayerZero (m := m) pre = 1 :=
    dir0CaseIILayerZero_eq_one_of_generic (m := m) hi0 hi1 hk0 hk1 hkneg1 hkneg2
  have hi2k : pre.1 + 2 * pre.2 = (((c : ℕ) : ZMod m)) := by
    have h := congrArg (fun u : P0Coord m => u.1 + 2 * u.2) hxy
    simpa [fromXY] using h.symm
  have hsum1 : pre.1 + pre.2 ≠ 1 := by
    intro h
    have hkcm1 : (((y : ℕ) : ZMod m)) = (((c - 1 : ℕ) : ZMod m)) := by
      calc
        (((y : ℕ) : ZMod m)) = (pre.1 + 2 * pre.2) - (pre.1 + pre.2) := by ring
        _ = (((c : ℕ) : ZMod m)) - 1 := by rw [hi2k, h]
        _ = (((c - 1 : ℕ) : ZMod m)) := by
              rw [Nat.cast_sub (by omega)]
              simp
    have hmod := (ZMod.natCast_eq_natCast_iff' y (c - 1) m).1 hkcm1
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
    omega
  have hret := returnMap0CaseII_of_dir1_generic (m := m) (u := pre) hdir hi0 hsum1
  calc
    returnMap0CaseIIXY (m := m) ((((c : ℕ) : ZMod m)), (((y : ℕ) : ZMod m)))
        = toXY (m := m)
            (returnMap0CaseII (m := m) (fromXY (m := m) ((((c : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))))) := by
              simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) pre) := by rw [hxy]
    _ = toXY (m := m) (pre.1 - 2, pre.2 + 1) := by
          simpa using congrArg (toXY (m := m)) hret
    _ = ((((c : ℕ) : ZMod m)), (((y + 1 : ℕ) : ZMod m))) := by
          ext
          · calc
              (pre.1 - 2) + 2 * (pre.2 + 1) = pre.1 + 2 * pre.2 := by ring
              _ = (((c : ℕ) : ZMod m)) := hi2k
          · simp [toXY, pre, Nat.cast_add]

theorem iterate_returnMap0CaseIIXY_upper_column_partial [Fact (9 < m)] {c y0 t : ℕ}
    (hc4 : 4 ≤ c) (hcle : c ≤ m - 3)
    (hy0l : c ≤ y0) (hy0u : y0 ≤ (m + c - 1) / 2)
    (ht : t ≤ (m + c - 1) / 2 - y0) :
    ((returnMap0CaseIIXY (m := m)^[t]) ((((c : ℕ) : ZMod m)), (((y0 : ℕ) : ZMod m)))) =
      ((((c : ℕ) : ZMod m)), (((y0 + t : ℕ) : ZMod m))) := by
  induction t with
  | zero =>
      simp
  | succ t iht =>
      have ht' : t ≤ (m + c - 1) / 2 - y0 := Nat.le_of_succ_le ht
      have hstep :
          returnMap0CaseIIXY (m := m)
            ((((c : ℕ) : ZMod m)), (((y0 + t : ℕ) : ZMod m))) =
              ((((c : ℕ) : ZMod m)), (((y0 + t + 1 : ℕ) : ZMod m))) := by
        have hyl : c ≤ y0 + t := by omega
        have hyu : y0 + t ≤ (m + c - 3) / 2 := by omega
        simpa [Nat.add_assoc] using
          returnMap0CaseIIXY_upper_column_step (m := m) (c := c) (y := y0 + t)
            hc4 hcle hyl hyu
      calc
        ((returnMap0CaseIIXY (m := m)^[t.succ])
            ((((c : ℕ) : ZMod m)), (((y0 : ℕ) : ZMod m))))
            = returnMap0CaseIIXY (m := m)
                (((returnMap0CaseIIXY (m := m)^[t])
                  ((((c : ℕ) : ZMod m)), (((y0 : ℕ) : ZMod m))))) := by
                    rw [Function.iterate_succ_apply']
        _ = returnMap0CaseIIXY (m := m)
              ((((c : ℕ) : ZMod m)), (((y0 + t : ℕ) : ZMod m))) := by
                rw [iht ht']
        _ = ((((c : ℕ) : ZMod m)), (((y0 + t + 1 : ℕ) : ZMod m))) := hstep
        _ = ((((c : ℕ) : ZMod m)), (((y0 + t.succ : ℕ) : ZMod m))) := by
              simp [Nat.succ_eq_add_one, Nat.add_assoc]

theorem iterate_returnMap0CaseIIXY_odd_generic_after_A_to_R [Fact (9 < m)] {x : ℕ}
    (hx3 : 3 ≤ x) (hxle : x ≤ m - 7) (hxodd : Odd x) :
    ((returnMap0CaseIIXY (m := m)^[(m - x - 3) / 2])
      ((((x + 2 : ℕ) : ZMod m)), (((x + 2 : ℕ) : ZMod m)))) =
      ((((x + 2 : ℕ) : ZMod m)), ((((m + x + 1) / 2 : ℕ) : ZMod m))) := by
  let _ := hxodd
  have hc4 : 4 ≤ x + 2 := by omega
  have hcle : x + 2 ≤ m - 3 := by omega
  have hy0u : x + 2 ≤ (m + (x + 2) - 1) / 2 := by omega
  have hmain := iterate_returnMap0CaseIIXY_upper_column_partial (m := m)
    (c := x + 2) (y0 := x + 2) (t := (m - x - 3) / 2) hc4 hcle (by omega) hy0u (by omega)
  rw [hmain]
  have hsum : x + 2 + (m - x - 3) / 2 = (m + x + 1) / 2 := by omega
  simp [hsum]

theorem returnMap0CaseIIXY_odd_generic_R_step [Fact (9 < m)] (hm : m % 12 = 10) {x : ℕ}
    (hx3 : 3 ≤ x) (hxle : x ≤ m - 7) (hxodd : Odd x) :
    returnMap0CaseIIXY (m := m)
      ((((x + 2 : ℕ) : ZMod m)), ((((m + x + 1) / 2 : ℕ) : ZMod m))) =
        ((((x + 4 : ℕ) : ZMod m)), ((((m + x + 5) / 2 : ℕ) : ZMod m))) := by
  rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, rfl⟩
  rcases hxodd with ⟨r, rfl⟩
  let M : ℕ := 12 * q + 10
  let yR : ℕ := 6 * q + r + 6
  have hy : yR ≤ M - 3 := by
    dsimp [yR, M]
    omega
  have hsrc :
      ((((1 + 2 * yR : ℕ) : ZMod M)), (((yR : ℕ) : ZMod M))) =
        ((((2 * r + 3 : ℕ) : ZMod M)), (((M + (2 * r + 1) + 1) / 2 : ℕ) : ZMod M)) := by
    ext
    · have hnat : 1 + 2 * yR = M + (2 * r + 3) := by
        dsimp [yR, M]
        omega
      calc
        (((1 + 2 * yR : ℕ) : ZMod M)) = (((M + (2 * r + 3) : ℕ) : ZMod M)) := by
            simpa [Nat.cast_add] using congrArg (fun n : ℕ => (((n : ℕ) : ZMod M))) hnat
        _ = (((2 * r + 3 : ℕ) : ZMod M)) := by
            simp [M, Nat.cast_add]
    · have hnat : yR = (M + (2 * r + 1) + 1) / 2 := by
        dsimp [yR, M]
        omega
      rw [hnat]
  have hdst :
      ((((3 + 2 * yR : ℕ) : ZMod M)), (((yR + 2 : ℕ) : ZMod M))) =
        ((((2 * r + 5 : ℕ) : ZMod M)), ((((M + (2 * r + 1) + 5) / 2 : ℕ) : ZMod M))) := by
    ext
    · have hnat : 3 + 2 * yR = M + (2 * r + 5) := by
        dsimp [yR, M]
        omega
      calc
        (((3 + 2 * yR : ℕ) : ZMod M)) = (((M + (2 * r + 5) : ℕ) : ZMod M)) := by
            simpa [Nat.cast_add] using congrArg (fun n : ℕ => (((n : ℕ) : ZMod M))) hnat
        _ = (((2 * r + 5 : ℕ) : ZMod M)) := by
            simp [M, Nat.cast_add]
    · have hnat : yR + 2 = (M + (2 * r + 1) + 5) / 2 := by
        dsimp [yR, M]
        omega
      rw [hnat]
  calc
    returnMap0CaseIIXY (m := M)
      ((((2 * r + 3 : ℕ) : ZMod M)), ((((M + (2 * r + 1) + 1) / 2 : ℕ) : ZMod M)))
        = returnMap0CaseIIXY (m := M) ((((1 + 2 * yR : ℕ) : ZMod M)), (((yR : ℕ) : ZMod M))) := by
            rw [hsrc]
    _ = ((((3 + 2 * yR : ℕ) : ZMod M)), (((yR + 2 : ℕ) : ZMod M))) := by
          exact returnMap0CaseIIXY_R_line (m := M) (y := yR) hy
    _ = ((((2 * r + 5 : ℕ) : ZMod M)), ((((M + (2 * r + 1) + 5) / 2 : ℕ) : ZMod M))) := hdst

theorem returnMap0CaseIIXY_wrapped_upper_column_step [Fact (9 < m)] (hm : m % 12 = 10)
    {c y : ℕ} (hc1 : 1 ≤ c) (hcle : c ≤ m - 7) (hcodd : Odd c)
    (hyl : (m + c + 1) / 2 ≤ y) (hyu : y ≤ m - 3) :
    returnMap0CaseIIXY (m := m) ((((c : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))) =
      ((((c : ℕ) : ZMod m)), (((y + 1 : ℕ) : ZMod m))) := by
  let _ := hcle
  have hm4 : 4 < m := by omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let pre : QCoord m := ((((2 * m + c - 2 * y : ℕ) : ZMod m)), (((y : ℕ) : ZMod m)))
  have hxy : fromXY (m := m) ((((c : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))) = pre := by
    ext <;> simp [pre, fromXY]
    · have hle : 2 * y ≤ 2 * m + c := by omega
      rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul]
      simp
  have hilt : 2 * m + c - 2 * y < m := by
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rcases hcodd with ⟨r, hr⟩
    rw [hq] at hyl hyu hcle ⊢
    rw [hr] at hyl hcle ⊢
    omega
  have hipos : 0 < 2 * m + c - 2 * y := by omega
  have hitwo : 2 ≤ 2 * m + c - 2 * y := by
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rcases hcodd with ⟨r, hr⟩
    rw [hq] at hyl hyu hcle ⊢
    rw [hr] at hyl hcle ⊢
    omega
  have hi0 : pre.1 ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := 2 * m + c - 2 * y) hipos hilt
  have hi1 : pre.1 ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := 2 * m + c - 2 * y) hitwo hilt
  have hk0 : pre.2 ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := y) (by omega) (by omega)
  have hk1 : pre.2 ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := y) (by omega) (by omega)
  have hkneg1 : pre.2 ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := y) (by omega)
  have hkneg2 : pre.2 ≠ (-2 : ZMod m) := by
    exact natCast_ne_neg_two_of_lt (m := m) (n := y) (by omega)
  have hdir :
      dir0CaseIILayerZero (m := m) pre = 1 :=
    dir0CaseIILayerZero_eq_one_of_generic (m := m) hi0 hi1 hk0 hk1 hkneg1 hkneg2
  have hi2k : pre.1 + 2 * pre.2 = (((c : ℕ) : ZMod m)) := by
    have h := congrArg (fun u : P0Coord m => u.1 + 2 * u.2) hxy
    simpa [fromXY] using h.symm
  have hsum1 : pre.1 + pre.2 ≠ 1 := by
    intro h
    have hkcm1 : (((y : ℕ) : ZMod m)) = (((c - 1 : ℕ) : ZMod m)) := by
      calc
        (((y : ℕ) : ZMod m)) = (pre.1 + 2 * pre.2) - (pre.1 + pre.2) := by ring
        _ = (((c : ℕ) : ZMod m)) - 1 := by rw [hi2k, h]
        _ = (((c - 1 : ℕ) : ZMod m)) := by
              rw [Nat.cast_sub (by omega)]
              simp
    have hmod := (ZMod.natCast_eq_natCast_iff' y (c - 1) m).1 hkcm1
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
    omega
  have hret := returnMap0CaseII_of_dir1_generic (m := m) (u := pre) hdir hi0 hsum1
  calc
    returnMap0CaseIIXY (m := m) ((((c : ℕ) : ZMod m)), (((y : ℕ) : ZMod m)))
        = toXY (m := m)
            (returnMap0CaseII (m := m) (fromXY (m := m) ((((c : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))))) := by
              simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) pre) := by rw [hxy]
    _ = toXY (m := m) (pre.1 - 2, pre.2 + 1) := by
          simpa using congrArg (toXY (m := m)) hret
    _ = ((((c : ℕ) : ZMod m)), (((y + 1 : ℕ) : ZMod m))) := by
          ext
          · calc
              (pre.1 - 2) + 2 * (pre.2 + 1) = pre.1 + 2 * pre.2 := by ring
              _ = (((c : ℕ) : ZMod m)) := hi2k
          · simp [toXY, pre, Nat.cast_add]

theorem iterate_returnMap0CaseIIXY_wrapped_upper_column_partial [Fact (9 < m)] (hm : m % 12 = 10)
    {c y0 t : ℕ} (hc1 : 1 ≤ c) (hcle : c ≤ m - 7) (hcodd : Odd c)
    (hy0l : (m + c + 1) / 2 ≤ y0) (hy0u : y0 ≤ m - 2)
    (ht : t ≤ m - 2 - y0) :
    ((returnMap0CaseIIXY (m := m)^[t]) ((((c : ℕ) : ZMod m)), (((y0 : ℕ) : ZMod m)))) =
      ((((c : ℕ) : ZMod m)), (((y0 + t : ℕ) : ZMod m))) := by
  let _ := hy0u
  induction t with
  | zero =>
      simp
  | succ t iht =>
      have ht' : t ≤ m - 2 - y0 := Nat.le_of_succ_le ht
      have hstep :
          returnMap0CaseIIXY (m := m)
            ((((c : ℕ) : ZMod m)), (((y0 + t : ℕ) : ZMod m))) =
              ((((c : ℕ) : ZMod m)), (((y0 + t + 1 : ℕ) : ZMod m))) := by
        have hyl : (m + c + 1) / 2 ≤ y0 + t := by omega
        have hyu : y0 + t ≤ m - 3 := by omega
        simpa [Nat.add_assoc] using
          returnMap0CaseIIXY_wrapped_upper_column_step (m := m) hm (c := c) (y := y0 + t)
            hc1 hcle hcodd hyl hyu
      calc
        ((returnMap0CaseIIXY (m := m)^[t.succ])
            ((((c : ℕ) : ZMod m)), (((y0 : ℕ) : ZMod m))))
            = returnMap0CaseIIXY (m := m)
                (((returnMap0CaseIIXY (m := m)^[t])
                  ((((c : ℕ) : ZMod m)), (((y0 : ℕ) : ZMod m))))) := by
                    rw [Function.iterate_succ_apply']
        _ = returnMap0CaseIIXY (m := m)
              ((((c : ℕ) : ZMod m)), (((y0 + t : ℕ) : ZMod m))) := by
                rw [iht ht']
        _ = ((((c : ℕ) : ZMod m)), (((y0 + t + 1 : ℕ) : ZMod m))) := hstep
        _ = ((((c : ℕ) : ZMod m)), (((y0 + t.succ : ℕ) : ZMod m))) := by
              simp [Nat.succ_eq_add_one, Nat.add_assoc]

theorem returnMap0CaseIIXY_wrapped_upper_column_m_sub_two [Fact (9 < m)] {c : ℕ}
    (hc1 : 1 ≤ c) (hcle : c ≤ m - 5) :
    returnMap0CaseIIXY (m := m) ((((c : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) =
      ((((c : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let preTop : QCoord m := ((((c + 4 : ℕ) : ZMod m)), (-2 : ZMod m))
  have hxy :
      fromXY (m := m) ((((c : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) = preTop := by
    ext <;> simp [preTop, fromXY, cast_sub_two_eq_neg_two (m := m) (by omega), Nat.cast_add]
    all_goals ring_nf
  have hc4lt : c + 4 < m := by omega
  have hi0 : preTop.1 ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := c + 4) (by omega) hc4lt
  have hi1 : preTop.1 ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := c + 4) (by omega) hc4lt
  have hi2 : preTop.1 ≠ 2 := by
    exact natCast_ne_two_of_three_le_lt (m := m) (n := c + 4) (by omega) hc4lt
  have h3ne : preTop.1 ≠ 3 := by
    intro h
    have hmod := (ZMod.natCast_eq_natCast_iff' (c + 4) 3 m).1 (by simpa [preTop] using h)
    rw [Nat.mod_eq_of_lt hc4lt, Nat.mod_eq_of_lt (by omega)] at hmod
    omega
  have hdir :
      dir0CaseIILayerZero (m := m) preTop = 1 :=
    dir0CaseIILayerZero_eq_one_of_k_neg_two_generic (m := m) hi0 hi1 hi2
  have hsum1 : preTop.1 + preTop.2 ≠ 1 := by
    intro h
    have h' : preTop.1 + preTop.2 + 2 = (1 : ZMod m) + 2 := by
      simpa using congrArg (fun z : ZMod m => z + 2) h
    have hbad : preTop.1 = 3 := by
      calc
        preTop.1 = preTop.1 + preTop.2 + 2 := by
          simp [preTop]
        _ = (1 : ZMod m) + 2 := h'
        _ = 3 := by ring
    exact h3ne hbad
  have hret := returnMap0CaseII_of_dir1_generic (m := m) (u := preTop) hdir hi0 hsum1
  calc
    returnMap0CaseIIXY (m := m) ((((c : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m)))
        = toXY (m := m)
            (returnMap0CaseII (m := m)
              (fromXY (m := m) ((((c : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))))) := by
              simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) preTop) := by rw [hxy]
    _ = toXY (m := m) (preTop.1 - 2, preTop.2 + 1) := by
          simpa using congrArg (toXY (m := m)) hret
    _ = ((((c : ℕ) : ZMod m)), (-1 : ZMod m)) := by
          ext <;> simp [toXY, preTop, Nat.cast_add]
          all_goals ring_nf
    _ = ((((c : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) := by
          rw [cast_sub_one_eq_neg_one (m := m) (by omega)]

theorem returnMap0CaseIIXY_wrapped_upper_column_m_sub_one [Fact (9 < m)] {c : ℕ}
    (hc1 : 1 ≤ c) (hcle : c ≤ m - 3) :
    returnMap0CaseIIXY (m := m) ((((c : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) =
      ((((c : ℕ) : ZMod m)), (0 : ZMod m)) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let preTop : QCoord m := ((((c + 2 : ℕ) : ZMod m)), (-1 : ZMod m))
  have hxy :
      fromXY (m := m) ((((c : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) = preTop := by
    ext <;> simp [preTop, fromXY, cast_sub_one_eq_neg_one (m := m) (by omega), Nat.cast_add]
  have hc2lt : c + 2 < m := by omega
  have hi0 : preTop.1 ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := c + 2) (by omega) hc2lt
  have hi1 : preTop.1 ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := c + 2) (by omega) hc2lt
  have hi2 : preTop.1 ≠ 2 := by
    exact natCast_ne_two_of_three_le_lt (m := m) (n := c + 2) (by omega) hc2lt
  have hdir :
      dir0CaseIILayerZero (m := m) preTop = 1 :=
    dir0CaseIILayerZero_eq_one_of_k_neg_one_generic (m := m) hi0 hi1 hi2
  have hsum1 : preTop.1 + preTop.2 ≠ 1 := by
    intro h
    have h' : preTop.1 + preTop.2 + 1 = (1 : ZMod m) + 1 := by
      simpa using congrArg (fun z : ZMod m => z + 1) h
    have hbad : preTop.1 = 2 := by
      calc
        preTop.1 = preTop.1 + preTop.2 + 1 := by
          simp [preTop]
        _ = (1 : ZMod m) + 1 := h'
        _ = 2 := by ring
    exact hi2 hbad
  have hret := returnMap0CaseII_of_dir1_generic (m := m) (u := preTop) hdir hi0 hsum1
  calc
    returnMap0CaseIIXY (m := m) ((((c : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m)))
        = toXY (m := m)
            (returnMap0CaseII (m := m)
              (fromXY (m := m) ((((c : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))))) := by
              simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) preTop) := by rw [hxy]
    _ = toXY (m := m) (preTop.1 - 2, preTop.2 + 1) := by
          simpa using congrArg (toXY (m := m)) hret
    _ = ((((c : ℕ) : ZMod m)), (0 : ZMod m)) := by
          ext <;> simp [toXY, preTop, Nat.cast_add]

theorem iterate_returnMap0CaseIIXY_wrapped_upper_column_to_zero [Fact (9 < m)] (hm : m % 12 = 10)
    {c y0 : ℕ} (hc1 : 1 ≤ c) (hcle : c ≤ m - 7) (hcodd : Odd c)
    (hy0l : (m + c + 1) / 2 ≤ y0) (hy0u : y0 ≤ m - 2) :
    ((returnMap0CaseIIXY (m := m)^[m - y0]) ((((c : ℕ) : ZMod m)), (((y0 : ℕ) : ZMod m)))) =
      ((((c : ℕ) : ZMod m)), (0 : ZMod m)) := by
  let F := returnMap0CaseIIXY (m := m)
  have htail :
    ((F^[m - 2 - y0]) ((((c : ℕ) : ZMod m)), (((y0 : ℕ) : ZMod m)))) =
        ((((c : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) := by
    rw [iterate_returnMap0CaseIIXY_wrapped_upper_column_partial
      (m := m) hm (c := c) (y0 := y0) (t := m - 2 - y0) hc1 hcle hcodd hy0l hy0u le_rfl]
    have hsum : y0 + (m - 2 - y0) = m - 2 := by omega
    simp [hsum]
  calc
    ((F^[m - y0]) ((((c : ℕ) : ZMod m)), (((y0 : ℕ) : ZMod m))))
        = ((F^[2]) ((F^[m - 2 - y0]) ((((c : ℕ) : ZMod m)), (((y0 : ℕ) : ZMod m))))) := by
            rw [show m - y0 = 2 + (m - 2 - y0) by omega, Function.iterate_add_apply]
    _ = ((F^[2]) ((((c : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m)))) := by rw [htail]
    _ = F (F ((((c : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m)))) := by
          simp [Function.iterate_succ_apply']
    _ = F ((((c : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) := by
          simpa [F] using congrArg F
            (returnMap0CaseIIXY_wrapped_upper_column_m_sub_two (m := m) hc1 (by omega))
    _ = ((((c : ℕ) : ZMod m)), (0 : ZMod m)) := by
          simpa [F] using returnMap0CaseIIXY_wrapped_upper_column_m_sub_one
            (m := m) hc1 (by omega)

theorem iterate_returnMap0CaseIIXY_odd_generic_after_R_to_zero [Fact (9 < m)] (hm : m % 12 = 10)
    {x : ℕ} (hx3 : 3 ≤ x) (hxle : x ≤ m - 11) (hxodd : Odd x) :
    ((returnMap0CaseIIXY (m := m)^[(m - x - 5) / 2])
      ((((x + 4 : ℕ) : ZMod m)), ((((m + x + 5) / 2 : ℕ) : ZMod m)))) =
      ((((x + 4 : ℕ) : ZMod m)), (0 : ZMod m)) := by
  have hmain := iterate_returnMap0CaseIIXY_wrapped_upper_column_to_zero (m := m)
    hm (c := x + 4) (y0 := (m + x + 5) / 2) (by omega) (by omega)
    (by
      rcases hxodd with ⟨r, hr⟩
      refine ⟨r + 2, ?_⟩
      omega) (by omega) (by omega)
  have hsteps : m - ((m + x + 5) / 2) = (m - x - 5) / 2 := by
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rcases hxodd with ⟨r, hr⟩
    rw [hq, hr]
    omega
  rw [hsteps] at hmain
  exact hmain

theorem iterate_returnMap0CaseIIXY_odd_generic_to_R [Fact (9 < m)] (hm : m % 12 = 10)
    {x : ℕ} (hx3 : 3 ≤ x) (hxle : x ≤ m - 7) (hxodd : Odd x) :
    ((returnMap0CaseIIXY (m := m)^[x + 2 + (m - x - 3) / 2])
        (linePoint0 (m := m) (⟨x, by omega⟩ : Fin m))) =
      ((((x + 4 : ℕ) : ZMod m)), ((((m + x + 5) / 2 : ℕ) : ZMod m))) := by
  let F := returnMap0CaseIIXY (m := m)
  let xFin : Fin m := ⟨x, by omega⟩
  have h1 :
      ((F^[1]) (linePoint0 (m := m) xFin)) =
        ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m)) := by
    simpa [Function.iterate_one, linePoint0, xFin] using
      returnMap0CaseIIXY_line_start_generic (m := m) (x := x) (by omega) (by omega)
  have hprefix :
      ((F^[x]) (linePoint0 (m := m) xFin)) =
        ((((x + 1 : ℕ) : ZMod m)), (((x : ℕ) : ZMod m))) := by
    have hsplit :
        ((F^[x]) (linePoint0 (m := m) xFin)) =
          ((F^[x - 1]) ((F^[1]) (linePoint0 (m := m) xFin))) := by
      rw [show x = (x - 1) + 1 by omega]
      exact Function.iterate_add_apply F (x - 1) 1 (linePoint0 (m := m) xFin)
    calc
      ((F^[x]) (linePoint0 (m := m) xFin))
          = ((F^[x - 1]) ((F^[1]) (linePoint0 (m := m) xFin))) := hsplit
      _ = ((F^[x - 1]) ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m))) := by rw [h1]
      _ = ((((x + 1 : ℕ) : ZMod m)), (((x : ℕ) : ZMod m))) := by
            exact iterate_returnMap0CaseIIXY_odd_generic_to_A (m := m) hx3 (by omega) hxodd
  have hA :
      ((F^[x + 1]) (linePoint0 (m := m) xFin)) =
        ((((x + 2 : ℕ) : ZMod m)), (((x + 2 : ℕ) : ZMod m))) := by
    calc
      ((F^[x + 1]) (linePoint0 (m := m) xFin))
          = F (((F^[x]) (linePoint0 (m := m) xFin))) := by
              rw [show x + 1 = 1 + x by omega, Function.iterate_add_apply]
              simp
      _ = F ((((x + 1 : ℕ) : ZMod m)), (((x : ℕ) : ZMod m))) := by rw [hprefix]
      _ = ((((x + 2 : ℕ) : ZMod m)), (((x + 2 : ℕ) : ZMod m))) := by
            simpa using returnMap0CaseIIXY_A_line (m := m) (y := x) (by omega) (by omega)
  have hRstart :
      ((F^[x + 1 + (m - x - 3) / 2]) (linePoint0 (m := m) xFin)) =
        ((((x + 2 : ℕ) : ZMod m)), ((((m + x + 1) / 2 : ℕ) : ZMod m))) := by
    calc
      ((F^[x + 1 + (m - x - 3) / 2]) (linePoint0 (m := m) xFin))
          = ((F^[(m - x - 3) / 2]) ((F^[x + 1]) (linePoint0 (m := m) xFin))) := by
              rw [show x + 1 + (m - x - 3) / 2 = (m - x - 3) / 2 + (x + 1) by omega,
                Function.iterate_add_apply]
      _ = ((F^[(m - x - 3) / 2]) ((((x + 2 : ℕ) : ZMod m)), (((x + 2 : ℕ) : ZMod m)))) := by
            rw [hA]
      _ = ((((x + 2 : ℕ) : ZMod m)), ((((m + x + 1) / 2 : ℕ) : ZMod m))) := by
            exact iterate_returnMap0CaseIIXY_odd_generic_after_A_to_R (m := m) hx3 hxle hxodd
  calc
    ((F^[x + 2 + (m - x - 3) / 2]) (linePoint0 (m := m) xFin))
        = F (((F^[x + 1 + (m - x - 3) / 2]) (linePoint0 (m := m) xFin))) := by
            rw [show x + 2 + (m - x - 3) / 2 = 1 + (x + 1 + (m - x - 3) / 2) by omega,
              Function.iterate_add_apply]
            simp
    _ = F ((((x + 2 : ℕ) : ZMod m)), ((((m + x + 1) / 2 : ℕ) : ZMod m))) := by rw [hRstart]
    _ = ((((x + 4 : ℕ) : ZMod m)), ((((m + x + 5) / 2 : ℕ) : ZMod m))) := by
          exact returnMap0CaseIIXY_odd_generic_R_step (m := m) hm hx3 hxle hxodd

theorem returnMap0CaseIIXY_m_sub_three_m_sub_two [Fact (9 < m)] :
    returnMap0CaseIIXY (m := m)
      ((((m - 3 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) =
        ((((m - 2 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let pre : QCoord m := ((1 : ZMod m), (((m - 2 : ℕ) : ZMod m)))
  have hneg3cast : (((m - 3 : ℕ) : ZMod m)) = (-3 : ZMod m) :=
    by
      rw [Nat.cast_sub (by omega)]
      simp
  have hneg2cast : (((m - 2 : ℕ) : ZMod m)) = (-2 : ZMod m) :=
    cast_sub_two_eq_neg_two (m := m) (by omega)
  have hneg1cast : (((m - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) :=
    cast_sub_one_eq_neg_one (m := m) (by omega)
  have hxy :
      fromXY (m := m) ((((m - 3 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) = pre := by
    ext
    · simp [pre, fromXY, hneg3cast, hneg2cast]
      ring_nf
    · simp [pre, fromXY, hneg2cast]
  have hdir : dir0CaseIILayerZero (m := m) pre = 0 := by
    simpa [pre, hneg2cast] using dir0CaseIILayerZero_eq_zero_one_neg_two (m := m)
  have hi : pre.1 ≠ (-1 : ZMod m) := by
    simpa [pre] using one_ne_neg_one (m := m)
  have hsum0 : pre.1 + pre.2 ≠ 0 := by
    intro h
    have : (-1 : ZMod m) = 0 := by
      calc
        (-1 : ZMod m) = (1 : ZMod m) + (-2 : ZMod m) := by ring
        _ = pre.1 + pre.2 := by simp [pre, hneg2cast]
        _ = 0 := h
    exact neg_ne_zero.mpr (one_ne_zero (m := m)) this
  have hret := returnMap0CaseII_of_dir0_generic (m := m) (u := pre) hdir hi hsum0
  calc
    returnMap0CaseIIXY (m := m)
        ((((m - 3 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m)))
        = toXY (m := m)
            (returnMap0CaseII (m := m)
              (fromXY (m := m)
                ((((m - 3 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))))) := by
                  simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) pre) := by rw [hxy]
    _ = toXY (m := m) (pre.1 - 1, pre.2 + 1) := by
          simpa using congrArg (toXY (m := m)) hret
    _ = ((((m - 2 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) := by
          ext <;> simp [toXY, pre, hneg2cast, hneg1cast]
          all_goals ring_nf

theorem returnMap0CaseIIXY_m_sub_two_m_sub_one [Fact (9 < m)] :
    returnMap0CaseIIXY (m := m)
      ((((m - 2 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) =
        ((((m - 1 : ℕ) : ZMod m)), (0 : ZMod m)) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let pre : QCoord m := ((0 : ZMod m), (((m - 1 : ℕ) : ZMod m)))
  have hneg2cast : (((m - 2 : ℕ) : ZMod m)) = (-2 : ZMod m) :=
    cast_sub_two_eq_neg_two (m := m) (by omega)
  have hneg1cast : (((m - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) :=
    cast_sub_one_eq_neg_one (m := m) (by omega)
  have hxy :
      fromXY (m := m) ((((m - 2 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) = pre := by
    ext
    · simp [pre, fromXY, hneg2cast, hneg1cast]
    · simp [pre, fromXY, hneg1cast]
  have hdir : dir0CaseIILayerZero (m := m) pre = 0 := by
    simpa [pre, hneg1cast] using dir0CaseIILayerZero_eq_zero_zero_neg_one (m := m)
  have hi : pre.1 ≠ (-1 : ZMod m) := by
    change (0 : ZMod m) ≠ (-1 : ZMod m)
    exact (neg_ne_zero.mpr (one_ne_zero (m := m))).symm
  have hsum0 : pre.1 + pre.2 ≠ 0 := by
    intro h
    have : (-1 : ZMod m) = 0 := by
      calc
        (-1 : ZMod m) = (0 : ZMod m) + (-1 : ZMod m) := by ring
        _ = pre.1 + pre.2 := by simp [pre, hneg1cast]
        _ = 0 := h
    exact neg_ne_zero.mpr (one_ne_zero (m := m)) this
  have hret := returnMap0CaseII_of_dir0_generic (m := m) (u := pre) hdir hi hsum0
  calc
    returnMap0CaseIIXY (m := m)
        ((((m - 2 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m)))
        = toXY (m := m)
            (returnMap0CaseII (m := m)
              (fromXY (m := m)
                ((((m - 2 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))))) := by
                  simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) pre) := by rw [hxy]
    _ = toXY (m := m) (pre.1 - 1, pre.2 + 1) := by
          simpa using congrArg (toXY (m := m)) hret
    _ = ((((m - 1 : ℕ) : ZMod m)), (0 : ZMod m)) := by
          ext <;> simp [toXY, pre, hneg1cast]

theorem firstReturn_line_m_sub_five_caseII_mod_ten [Fact (9 < m)] (hm : m % 12 = 10) :
    ((returnMap0CaseIIXY (m := m)^[m - 1])
        (linePoint0 (m := m) (⟨m - 5, by omega⟩ : Fin m))) =
      linePoint0 (m := m) (⟨m - 1, by omega⟩ : Fin m) := by
  let F := returnMap0CaseIIXY (m := m)
  have hxodd : Odd (m - 5) := by
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rw [hq]
    refine ⟨6 * q + 2, ?_⟩
    omega
  have h1 :
      ((F^[1]) (linePoint0 (m := m) (⟨m - 5, by omega⟩ : Fin m))) =
        ((((m - 4 : ℕ) : ZMod m)), (1 : ZMod m)) := by
    simpa [F, Function.iterate_one, linePoint0, show m - 5 + 1 = m - 4 by omega] using
      returnMap0CaseIIXY_line_start_generic (m := m) (x := m - 5) (by omega) (by omega)
  have hcol :
      ((F^[m - 6]) ((((m - 4 : ℕ) : ZMod m)), (1 : ZMod m))) =
        ((((m - 4 : ℕ) : ZMod m)), (((m - 5 : ℕ) : ZMod m))) := by
    have hmain := iterate_returnMap0CaseIIXY_odd_generic_to_A
      (m := m) (x := m - 5) (by omega) (by omega) hxodd
    simpa [F, show (m - 5) - 1 = m - 6 by omega, show m - 5 + 1 = m - 4 by omega] using hmain
  have hA :
      F ((((m - 4 : ℕ) : ZMod m)), (((m - 5 : ℕ) : ZMod m))) =
        ((((m - 3 : ℕ) : ZMod m)), (((m - 3 : ℕ) : ZMod m))) := by
    simpa [F, show m - 5 + 1 = m - 4 by omega, show m - 5 + 2 = m - 3 by omega] using
      returnMap0CaseIIXY_A_line (m := m) (y := m - 5) (by omega) (by omega)
  have hup :
      F ((((m - 3 : ℕ) : ZMod m)), (((m - 3 : ℕ) : ZMod m))) =
        ((((m - 3 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) := by
    simpa [F, show m - 3 + 1 = m - 2 by omega] using
      returnMap0CaseIIXY_upper_column_step (m := m)
      (c := m - 3) (y := m - 3) (by omega) (by omega) (by omega) (by omega)
  have hsplit :
      ((F^[m - 5]) (linePoint0 (m := m) (⟨m - 5, by omega⟩ : Fin m))) =
        ((((m - 4 : ℕ) : ZMod m)), (((m - 5 : ℕ) : ZMod m))) := by
    let p : P0Coord m := linePoint0 (m := m) (⟨m - 5, by omega⟩ : Fin m)
    have hstep :
        ((F^[m - 5]) p) = ((F^[m - 6]) ((F^[1]) p)) := by
      simpa [p, show (m - 6) + 1 = m - 5 by omega] using
        (Function.iterate_add_apply F (m - 6) 1 p)
    calc
      ((F^[m - 5]) p)
          = ((F^[m - 6]) ((F^[1]) p)) := hstep
      _ = ((F^[m - 6]) ((((m - 4 : ℕ) : ZMod m)), (1 : ZMod m))) := by rw [h1]
      _ = ((((m - 4 : ℕ) : ZMod m)), (((m - 5 : ℕ) : ZMod m))) := hcol
  calc
    ((F^[m - 1]) (linePoint0 (m := m) (⟨m - 5, by omega⟩ : Fin m)))
        = ((F^[4]) ((F^[m - 5]) (linePoint0 (m := m) (⟨m - 5, by omega⟩ : Fin m)))) := by
            simpa [show 4 + (m - 5) = m - 1 by omega] using
              (Function.iterate_add_apply F 4 (m - 5)
                (linePoint0 (m := m) (⟨m - 5, by omega⟩ : Fin m)))
    _ = ((F^[4]) ((((m - 4 : ℕ) : ZMod m)), (((m - 5 : ℕ) : ZMod m)))) := by rw [hsplit]
    _ = (F^[3]) (F ((((m - 4 : ℕ) : ZMod m)), (((m - 5 : ℕ) : ZMod m)))) := by
          rw [Function.iterate_succ_apply]
    _ = ((F^[3]) ((((m - 3 : ℕ) : ZMod m)), (((m - 3 : ℕ) : ZMod m)))) := by rw [hA]
    _ = (F^[2]) (F ((((m - 3 : ℕ) : ZMod m)), (((m - 3 : ℕ) : ZMod m)))) := by
          rw [Function.iterate_succ_apply]
    _ = ((F^[2]) ((((m - 3 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m)))) := by rw [hup]
    _ = F (F ((((m - 3 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m)))) := by
          rw [Function.iterate_succ_apply]
          simp
    _ = F ((((m - 2 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) := by
          simpa [F] using congrArg F (returnMap0CaseIIXY_m_sub_three_m_sub_two (m := m))
    _ = ((((m - 1 : ℕ) : ZMod m)), (0 : ZMod m)) := by
          exact returnMap0CaseIIXY_m_sub_two_m_sub_one (m := m)
    _ = linePoint0 (m := m) (⟨m - 1, by omega⟩ : Fin m) := by
          simp [linePoint0]

theorem firstReturn_line_m_sub_nine_caseII_mod_ten [Fact (9 < m)] (hm : m % 12 = 10)
    (hm10 : 10 < m) :
    ((returnMap0CaseIIXY (m := m)^[m - 2])
        (linePoint0 (m := m) (⟨m - 9, by omega⟩ : Fin m))) =
      linePoint0 (m := m) (⟨m - 5, by omega⟩ : Fin m) := by
  let F := returnMap0CaseIIXY (m := m)
  have hxodd : Odd (m - 9) := by
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rw [hq]
    refine ⟨6 * q, ?_⟩
    omega
  have hR :
      ((F^[m - 4]) (linePoint0 (m := m) (⟨m - 9, by omega⟩ : Fin m))) =
        ((((m - 5 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) := by
    have hmain := iterate_returnMap0CaseIIXY_odd_generic_to_R (m := m) hm
      (x := m - 9) (by omega) (by omega) hxodd
    have hsteps : m - 9 + 2 + (m - (m - 9) - 3) / 2 = m - 4 := by omega
    have hfst : m - 9 + 4 = m - 5 := by omega
    have hsnd : (m + (m - 9) + 5) / 2 = m - 2 := by omega
    simpa [hsteps, hfst, hsnd] using hmain
  calc
    ((F^[m - 2]) (linePoint0 (m := m) (⟨m - 9, by omega⟩ : Fin m)))
        = ((F^[2]) ((F^[m - 4]) (linePoint0 (m := m) (⟨m - 9, by omega⟩ : Fin m)))) := by
            rw [show m - 2 = 2 + (m - 4) by omega, Function.iterate_add_apply]
    _ = ((F^[2]) ((((m - 5 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m)))) := by rw [hR]
    _ = F (F ((((m - 5 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m)))) := by
          simp [Function.iterate_succ_apply']
    _ = F ((((m - 5 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) := by
          simpa [F] using congrArg F
            (returnMap0CaseIIXY_wrapped_upper_column_m_sub_two (m := m) (c := m - 5) (by omega) (by omega))
    _ = ((((m - 5 : ℕ) : ZMod m)), (0 : ZMod m)) := by
          simpa [F] using returnMap0CaseIIXY_wrapped_upper_column_m_sub_one
            (m := m) (c := m - 5) (by omega) (by omega)
    _ = linePoint0 (m := m) (⟨m - 5, by omega⟩ : Fin m) := by
          simp [linePoint0]

theorem firstReturn_line_m_sub_seven_caseII_mod_ten [Fact (9 < m)] (hm : m % 12 = 10) :
    ((returnMap0CaseIIXY (m := m)^[m - 2])
        (linePoint0 (m := m) (⟨m - 7, by omega⟩ : Fin m))) =
      linePoint0 (m := m) (⟨m - 3, by omega⟩ : Fin m) := by
  let F := returnMap0CaseIIXY (m := m)
  have hxodd : Odd (m - 7) := by
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rw [hq]
    refine ⟨6 * q + 1, ?_⟩
    omega
  have hR :
      ((F^[m - 3]) (linePoint0 (m := m) (⟨m - 7, by omega⟩ : Fin m))) =
        ((((m - 3 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) := by
    have hmain := iterate_returnMap0CaseIIXY_odd_generic_to_R (m := m) hm
      (x := m - 7) (by omega) (by omega) hxodd
    have hsteps : m - 7 + 2 + (m - (m - 7) - 3) / 2 = m - 3 := by omega
    have hfst : m - 7 + 4 = m - 3 := by omega
    have hsnd : (m + (m - 7) + 5) / 2 = m - 1 := by omega
    simpa [hsteps, hfst, hsnd] using hmain
  calc
    ((F^[m - 2]) (linePoint0 (m := m) (⟨m - 7, by omega⟩ : Fin m)))
        = F (((F^[m - 3]) (linePoint0 (m := m) (⟨m - 7, by omega⟩ : Fin m)))) := by
            rw [show m - 2 = 1 + (m - 3) by omega, Function.iterate_add_apply]
            simp
    _ = F ((((m - 3 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) := by rw [hR]
    _ = ((((m - 3 : ℕ) : ZMod m)), (0 : ZMod m)) := by
          simpa using returnMap0CaseIIXY_wrapped_upper_column_m_sub_one
            (m := m) (c := m - 3) (by omega) (by omega)
    _ = linePoint0 (m := m) (⟨m - 3, by omega⟩ : Fin m) := by
          simp [linePoint0]

private theorem firstReturn_line_odd_generic_caseII_mod_ten_boundary [Fact (9 < m)] (hm : m % 12 = 10)
    {x : ℕ} (hx3 : 3 ≤ x) (hxle : x ≤ m - 7) (hxodd : Odd x) (hsafe : ¬ x ≤ m - 11) :
    ((returnMap0CaseIIXY (m := m)^[m - 2])
        (linePoint0 (m := m) (⟨x, by omega⟩ : Fin m))) =
      linePoint0 (m := m) (⟨x + 4, by omega⟩ : Fin m) := by
  have hcases : x = m - 9 ∨ x = m - 7 := by
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rcases hxodd with ⟨r, hr⟩
    rw [hq] at hxle hsafe ⊢
    rw [hr] at hxle hsafe ⊢
    omega
  rcases hcases with hxm9 | hxm7
  · subst hxm9
    have hm10 : 10 < m := by omega
    simpa [show m - 9 + 4 = m - 5 by omega] using
      firstReturn_line_m_sub_nine_caseII_mod_ten (m := m) hm hm10
  · subst hxm7
    simpa [show m - 7 + 4 = m - 3 by omega] using
      firstReturn_line_m_sub_seven_caseII_mod_ten (m := m) hm

theorem firstReturn_line_odd_generic_caseII_mod_ten_safe [Fact (9 < m)] (hm : m % 12 = 10)
    {x : ℕ} (hx3 : 3 ≤ x) (hxle : x ≤ m - 11) (hxodd : Odd x) :
    ((returnMap0CaseIIXY (m := m)^[m - 2])
        (linePoint0 (m := m) (⟨x, by omega⟩ : Fin m))) =
      linePoint0 (m := m) (⟨x + 4, by omega⟩ : Fin m) := by
  let F := returnMap0CaseIIXY (m := m)
  let xFin : Fin m := ⟨x, by omega⟩
  have h1 :
      ((F^[1]) (linePoint0 (m := m) xFin)) =
        ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m)) := by
    simpa [Function.iterate_one, linePoint0, xFin] using
      returnMap0CaseIIXY_line_start_generic (m := m) (x := x) (by omega) (by omega)
  have hprefix :
      ((F^[x]) (linePoint0 (m := m) xFin)) =
        ((((x + 1 : ℕ) : ZMod m)), (((x : ℕ) : ZMod m))) := by
    have hsplit :
        ((F^[x]) (linePoint0 (m := m) xFin)) =
          ((F^[x - 1]) ((F^[1]) (linePoint0 (m := m) xFin))) := by
      rw [show x = (x - 1) + 1 by omega]
      exact Function.iterate_add_apply F (x - 1) 1 (linePoint0 (m := m) xFin)
    calc
      ((F^[x]) (linePoint0 (m := m) xFin))
          = ((F^[x - 1]) ((F^[1]) (linePoint0 (m := m) xFin))) := hsplit
      _ = ((F^[x - 1]) ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m))) := by rw [h1]
      _ = ((((x + 1 : ℕ) : ZMod m)), (((x : ℕ) : ZMod m))) := by
            exact iterate_returnMap0CaseIIXY_odd_generic_to_A (m := m) hx3 (by omega) hxodd
  have hA :
      ((F^[x + 1]) (linePoint0 (m := m) xFin)) =
        ((((x + 2 : ℕ) : ZMod m)), (((x + 2 : ℕ) : ZMod m))) := by
    calc
      ((F^[x + 1]) (linePoint0 (m := m) xFin))
          = F (((F^[x]) (linePoint0 (m := m) xFin))) := by
              rw [show x + 1 = 1 + x by omega, Function.iterate_add_apply]
              simp
      _ = F ((((x + 1 : ℕ) : ZMod m)), (((x : ℕ) : ZMod m))) := by rw [hprefix]
      _ = ((((x + 2 : ℕ) : ZMod m)), (((x + 2 : ℕ) : ZMod m))) := by
            simpa using returnMap0CaseIIXY_A_line (m := m) (y := x) (by omega) (by omega)
  have hRstart :
      ((F^[x + 1 + (m - x - 3) / 2]) (linePoint0 (m := m) xFin)) =
        ((((x + 2 : ℕ) : ZMod m)), ((((m + x + 1) / 2 : ℕ) : ZMod m))) := by
    calc
      ((F^[x + 1 + (m - x - 3) / 2]) (linePoint0 (m := m) xFin))
          = ((F^[(m - x - 3) / 2]) ((F^[x + 1]) (linePoint0 (m := m) xFin))) := by
              rw [show x + 1 + (m - x - 3) / 2 = (m - x - 3) / 2 + (x + 1) by omega,
                Function.iterate_add_apply]
      _ = ((F^[(m - x - 3) / 2]) ((((x + 2 : ℕ) : ZMod m)), (((x + 2 : ℕ) : ZMod m)))) := by
            rw [hA]
      _ = ((((x + 2 : ℕ) : ZMod m)), ((((m + x + 1) / 2 : ℕ) : ZMod m))) := by
            exact iterate_returnMap0CaseIIXY_odd_generic_after_A_to_R (m := m) hx3 (by omega) hxodd
  have hR :
      ((F^[x + 2 + (m - x - 3) / 2]) (linePoint0 (m := m) xFin)) =
        ((((x + 4 : ℕ) : ZMod m)), ((((m + x + 5) / 2 : ℕ) : ZMod m))) := by
    calc
      ((F^[x + 2 + (m - x - 3) / 2]) (linePoint0 (m := m) xFin))
          = F (((F^[x + 1 + (m - x - 3) / 2]) (linePoint0 (m := m) xFin))) := by
              rw [show x + 2 + (m - x - 3) / 2 = 1 + (x + 1 + (m - x - 3) / 2) by omega,
                Function.iterate_add_apply]
              simp
      _ = F ((((x + 2 : ℕ) : ZMod m)), ((((m + x + 1) / 2 : ℕ) : ZMod m))) := by rw [hRstart]
      _ = ((((x + 4 : ℕ) : ZMod m)), ((((m + x + 5) / 2 : ℕ) : ZMod m))) := by
            exact returnMap0CaseIIXY_odd_generic_R_step (m := m) hm hx3 (by omega) hxodd
  calc
    ((F^[m - 2]) (linePoint0 (m := m) xFin))
        = ((F^[(m - x - 5) / 2])
            ((F^[x + 2 + (m - x - 3) / 2]) (linePoint0 (m := m) xFin))) := by
              have hsteps : m - 2 = (m - x - 5) / 2 + (x + 2 + (m - x - 3) / 2) := by
                rcases hxodd with ⟨r, hr⟩
                rw [hr]
                omega
              rw [hsteps,
                Function.iterate_add_apply]
    _ = ((F^[(m - x - 5) / 2])
          ((((x + 4 : ℕ) : ZMod m)), ((((m + x + 5) / 2 : ℕ) : ZMod m)))) := by
            rw [hR]
    _ = ((((x + 4 : ℕ) : ZMod m)), (0 : ZMod m)) := by
          exact iterate_returnMap0CaseIIXY_odd_generic_after_R_to_zero
            (m := m) hm hx3 hxle hxodd
    _ = linePoint0 (m := m) (⟨x + 4, by omega⟩ : Fin m) := by
          simp [linePoint0]

theorem firstReturn_line_odd_generic_caseII_mod_ten [Fact (9 < m)] (hm : m % 12 = 10)
    {x : ℕ} (hx3 : 3 ≤ x) (hxle : x ≤ m - 7) (hxodd : Odd x) :
    ((returnMap0CaseIIXY (m := m)^[m - 2])
        (linePoint0 (m := m) (⟨x, by omega⟩ : Fin m))) =
      linePoint0 (m := m) (⟨x + 4, by omega⟩ : Fin m) := by
  by_cases hsafe : x ≤ m - 11
  · simpa using firstReturn_line_odd_generic_caseII_mod_ten_safe (m := m) hm hx3 hsafe hxodd
  · exact firstReturn_line_odd_generic_caseII_mod_ten_boundary
      (m := m) hm hx3 hxle hxodd hsafe

theorem firstReturn_line_zero_caseII_mod_ten [Fact (9 < m)] :
    ((returnMap0CaseIIXY (m := m)^[1])
        (linePoint0 (m := m) (0 : Fin m))) =
      linePoint0 (m := m) (⟨m - 2, by
        have hm9 : 9 < m := Fact.out
        omega⟩ : Fin m) := by
  have hm2 : 2 ≤ m := by
    have hm9 : 9 < m := Fact.out
    omega
  have hm2lt : m - 2 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  calc
    ((returnMap0CaseIIXY (m := m)^[1]) (linePoint0 (m := m) (0 : Fin m)))
        = ((-2 : ZMod m), (0 : ZMod m)) := by
            simpa [Function.iterate_one, linePoint0] using returnMap0CaseIIXY_zero_zero (m := m)
    _ = linePoint0 (m := m) (⟨m - 2, hm2lt⟩ : Fin m) := by
          simp [linePoint0, cast_sub_two_eq_neg_two (m := m) hm2]

theorem returnMap0CaseIIXY_even_generic_odd_column_one_step [Fact (9 < m)] {x : ℕ}
    (hx4 : 4 ≤ x) (hxle : x ≤ m - 2) :
    returnMap0CaseIIXY (m := m) ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m)) =
      ((((x + 1 : ℕ) : ZMod m)), (2 : ZMod m)) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let pre : QCoord m := ((((x - 1 : ℕ) : ZMod m)), (1 : ZMod m))
  have hxy : fromXY (m := m) ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m)) = pre := by
    ext <;> simp [pre, fromXY]
    · calc
        (((x : ℕ) : ZMod m)) + 1 - 2 = (((x : ℕ) : ZMod m)) - 1 := by ring
        _ = (((x - 1 : ℕ) : ZMod m)) := by
              rw [Nat.cast_sub (by omega)]
              simp
  have hi0 : pre.1 ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := x - 1) (by omega) (by omega)
  have hi1 : pre.1 ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := x - 1) (by omega) (by omega)
  have hineg1 : pre.1 ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := x - 1) (by omega)
  have hineg2 : pre.1 ≠ (-2 : ZMod m) := by
    exact natCast_ne_neg_two_of_lt (m := m) (n := x - 1) (by omega)
  have hdir :
      dir0CaseIILayerZero (m := m) pre = 1 :=
    dir0CaseIILayerZero_eq_one_of_k_one_generic (m := m) hi0 hi1 hineg1 hineg2
  have hsum1 : pre.1 + pre.2 ≠ 1 := by
    have hxne1 : (((x : ℕ) : ZMod m)) ≠ 1 := by
      exact natCast_ne_one_of_two_le_lt (m := m) (n := x) (by omega) (by omega)
    intro h
    have hcast : (((x : ℕ) : ZMod m)) = 1 := by
      change ((((x - 1 : ℕ) : ZMod m)) + (1 : ZMod m)) = 1 at h
      calc
        (((x : ℕ) : ZMod m))
            = (((x - 1 : ℕ) : ZMod m)) + (1 : ZMod m) := by
                have hnat : x = (x - 1) + 1 := by omega
                simpa [Nat.cast_add] using congrArg (fun n : ℕ => (((n : ℕ) : ZMod m))) hnat
        _ = 1 := h
    exact hxne1 hcast
  have hi2k : pre.1 + 2 * pre.2 = (((x + 1 : ℕ) : ZMod m)) := by
    have h := congrArg (fun u : P0Coord m => u.1 + 2 * u.2) hxy
    simpa [fromXY] using h.symm
  have hret := returnMap0CaseII_of_dir1_generic (m := m) (u := pre) hdir hi0 hsum1
  calc
    returnMap0CaseIIXY (m := m) ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m))
        = toXY (m := m)
            (returnMap0CaseII (m := m) (fromXY (m := m) ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m)))) := by
              simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) pre) := by rw [hxy]
    _ = toXY (m := m) (pre.1 - 2, pre.2 + 1) := by
          simpa using congrArg (toXY (m := m)) hret
    _ = ((((x + 1 : ℕ) : ZMod m)), (2 : ZMod m)) := by
          ext
          · calc
              (pre.1 - 2) + 2 * (pre.2 + 1) = pre.1 + 2 * pre.2 := by ring
              _ = (((x + 1 : ℕ) : ZMod m)) := hi2k
          · norm_num [toXY, pre]

theorem returnMap0CaseIIXY_even_generic_odd_column_lower_step [Fact (9 < m)] {x y : ℕ}
    (hx4 : 4 ≤ x) (hxle : x ≤ m - 2)
    (hy2 : 2 ≤ y) (hyle : y ≤ x / 2 - 1) :
    returnMap0CaseIIXY (m := m) ((((x + 1 : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))) =
      ((((x + 1 : ℕ) : ZMod m)), (((y + 1 : ℕ) : ZMod m))) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let pre : QCoord m := ((((x + 1 - 2 * y : ℕ) : ZMod m)), (((y : ℕ) : ZMod m)))
  have hxy : fromXY (m := m) ((((x + 1 : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))) = pre := by
    ext <;> simp [pre, fromXY]
    · have hle : 2 * y ≤ x + 1 := by omega
      rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul]
      simp
  have hi0 : pre.1 ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := x + 1 - 2 * y) (by omega) (by omega)
  have hi1 : pre.1 ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := x + 1 - 2 * y) (by omega) (by omega)
  have hk0 : pre.2 ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := y) (by omega) (by omega)
  have hk1 : pre.2 ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := y) hy2 (by omega)
  have hkneg1 : pre.2 ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := y) (by omega)
  have hkneg2 : pre.2 ≠ (-2 : ZMod m) := by
    exact natCast_ne_neg_two_of_lt (m := m) (n := y) (by omega)
  have hdir :
      dir0CaseIILayerZero (m := m) pre = 1 :=
    dir0CaseIILayerZero_eq_one_of_generic (m := m) hi0 hi1 hk0 hk1 hkneg1 hkneg2
  have hsum1 : pre.1 + pre.2 ≠ 1 := by
    intro h
    have hcast : (((x + 1 - y : ℕ) : ZMod m)) = 1 := by
      calc
        (((x + 1 - y : ℕ) : ZMod m))
            = ((((x + 1 - 2 * y : ℕ) : ZMod m)) + (((y : ℕ) : ZMod m))) := by
                have hnat : x + 1 - y = (x + 1 - 2 * y) + y := by omega
                simpa [Nat.cast_add] using congrArg (fun n : ℕ => (((n : ℕ) : ZMod m))) hnat
        _ = 1 := h
    have hxny_ne : (((x + 1 - y : ℕ) : ZMod m)) ≠ 1 := by
      exact natCast_ne_one_of_two_le_lt (m := m) (n := x + 1 - y) (by omega) (by omega)
    exact hxny_ne hcast
  have hi2k : pre.1 + 2 * pre.2 = (((x + 1 : ℕ) : ZMod m)) := by
    have h := congrArg (fun u : P0Coord m => u.1 + 2 * u.2) hxy
    simpa [fromXY] using h.symm
  have hret := returnMap0CaseII_of_dir1_generic (m := m) (u := pre) hdir hi0 hsum1
  calc
    returnMap0CaseIIXY (m := m) ((((x + 1 : ℕ) : ZMod m)), (((y : ℕ) : ZMod m)))
        = toXY (m := m)
            (returnMap0CaseII (m := m) (fromXY (m := m) ((((x + 1 : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))))) := by
              simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) pre) := by rw [hxy]
    _ = toXY (m := m) (pre.1 - 2, pre.2 + 1) := by
          simpa using congrArg (toXY (m := m)) hret
    _ = ((((x + 1 : ℕ) : ZMod m)), (((y + 1 : ℕ) : ZMod m))) := by
          ext
          · calc
              (pre.1 - 2) + 2 * (pre.2 + 1) = pre.1 + 2 * pre.2 := by ring
              _ = (((x + 1 : ℕ) : ZMod m)) := hi2k
          · simp [toXY, pre, Nat.cast_add]

theorem iterate_returnMap0CaseIIXY_even_generic_odd_column_lower_partial [Fact (9 < m)] {x t : ℕ}
    (hx4 : 4 ≤ x) (hxle : x ≤ m - 2)
    (ht : t ≤ x / 2 - 2) :
    ((returnMap0CaseIIXY (m := m)^[t]) ((((x + 1 : ℕ) : ZMod m)), (2 : ZMod m))) =
      ((((x + 1 : ℕ) : ZMod m)), (((2 + t : ℕ) : ZMod m))) := by
  induction t with
  | zero =>
      simp
  | succ t iht =>
      have ht' : t ≤ x / 2 - 2 := Nat.le_of_succ_le ht
      have hstep :
          returnMap0CaseIIXY (m := m) ((((x + 1 : ℕ) : ZMod m)), (((2 + t : ℕ) : ZMod m))) =
            ((((x + 1 : ℕ) : ZMod m)), (((2 + t + 1 : ℕ) : ZMod m))) := by
        have hy2 : 2 ≤ 2 + t := by omega
        have hyle : 2 + t ≤ x / 2 - 1 := by omega
        simpa [Nat.add_assoc] using
          returnMap0CaseIIXY_even_generic_odd_column_lower_step (m := m) hx4 hxle
            (y := 2 + t) hy2 hyle
      calc
        ((returnMap0CaseIIXY (m := m)^[t.succ]) ((((x + 1 : ℕ) : ZMod m)), (2 : ZMod m)))
            = returnMap0CaseIIXY (m := m)
                (((returnMap0CaseIIXY (m := m)^[t]) ((((x + 1 : ℕ) : ZMod m)), (2 : ZMod m)))) := by
                    rw [Function.iterate_succ_apply']
        _ = returnMap0CaseIIXY (m := m) ((((x + 1 : ℕ) : ZMod m)), (((2 + t : ℕ) : ZMod m))) := by
              rw [iht ht']
        _ = ((((x + 1 : ℕ) : ZMod m)), (((2 + t + 1 : ℕ) : ZMod m))) := hstep
        _ = ((((x + 1 : ℕ) : ZMod m)), (((2 + t.succ : ℕ) : ZMod m))) := by
              simp [Nat.succ_eq_add_one, Nat.add_assoc]

theorem iterate_returnMap0CaseIIXY_even_generic_to_R [Fact (9 < m)] {x : ℕ}
    (hx4 : 4 ≤ x) (hxle : x ≤ m - 4) (hxeven : Even x) :
    ((returnMap0CaseIIXY (m := m)^[x / 2 + 1])
      (linePoint0 (m := m) (⟨x, by omega⟩ : Fin m))) =
      ((((x + 3 : ℕ) : ZMod m)), (((x / 2 + 2 : ℕ) : ZMod m))) := by
  let F := returnMap0CaseIIXY (m := m)
  let xFin : Fin m := ⟨x, by omega⟩
  have h1 :
      ((F^[1]) (linePoint0 (m := m) xFin)) =
        ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m)) := by
    simpa [Function.iterate_one, linePoint0, xFin] using
      returnMap0CaseIIXY_line_start_generic (m := m) (x := x) (by omega) (by omega)
  have h2 :
      ((F^[2]) (linePoint0 (m := m) xFin)) =
        ((((x + 1 : ℕ) : ZMod m)), (2 : ZMod m)) := by
    calc
      ((F^[2]) (linePoint0 (m := m) xFin))
          = F (((F^[1]) (linePoint0 (m := m) xFin))) := by
              simp [Function.iterate_succ_apply']
      _ = F ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m)) := by rw [h1]
      _ = ((((x + 1 : ℕ) : ZMod m)), (2 : ZMod m)) := by
            exact returnMap0CaseIIXY_even_generic_odd_column_one_step (m := m) hx4 (by omega)
  have hmid :
      ((F^[x / 2]) (linePoint0 (m := m) xFin)) =
        ((((x + 1 : ℕ) : ZMod m)), (((x / 2 : ℕ) : ZMod m))) := by
    by_cases hx4eq : x = 4
    · subst hx4eq
      simpa using h2
    · have hx6 : 6 ≤ x := by
        rcases hxeven with ⟨r, hr⟩
        rw [hr]
        omega
      have hxhalf2 : 2 ≤ x / 2 := by
        rcases hxeven with ⟨r, hr⟩
        rw [hr]
        omega
      have hpartial :
          ((F^[x / 2 - 2]) ((((x + 1 : ℕ) : ZMod m)), (2 : ZMod m))) =
            ((((x + 1 : ℕ) : ZMod m)), (((2 + (x / 2 - 2) : ℕ) : ZMod m))) := by
        exact iterate_returnMap0CaseIIXY_even_generic_odd_column_lower_partial
          (m := m) hx4 (by omega) (x := x) (t := x / 2 - 2) le_rfl
      have hsplit :
          ((F^[x / 2]) (linePoint0 (m := m) xFin)) =
            ((F^[x / 2 - 2]) (((F^[2]) (linePoint0 (m := m) xFin)))) := by
        rw [show x / 2 = (x / 2 - 2) + 2 by exact (Nat.sub_add_cancel hxhalf2).symm]
        exact Function.iterate_add_apply F (x / 2 - 2) 2 (linePoint0 (m := m) xFin)
      calc
        ((F^[x / 2]) (linePoint0 (m := m) xFin))
            = ((F^[x / 2 - 2]) (((F^[2]) (linePoint0 (m := m) xFin)))) := hsplit
        _ = ((F^[x / 2 - 2]) ((((x + 1 : ℕ) : ZMod m)), (2 : ZMod m))) := by
              simpa using congrArg (fun z => (F^[x / 2 - 2]) z) h2
        _ = ((((x + 1 : ℕ) : ZMod m)), (((2 + (x / 2 - 2) : ℕ) : ZMod m))) := hpartial
        _ = ((((x + 1 : ℕ) : ZMod m)), (((x / 2 : ℕ) : ZMod m))) := by
              have hsum : 2 + (x / 2 - 2) = x / 2 := by omega
              simp [hsum]
  calc
    ((F^[x / 2 + 1]) (linePoint0 (m := m) xFin))
        = F (((F^[x / 2]) (linePoint0 (m := m) xFin))) := by
            rw [show x / 2 + 1 = 1 + x / 2 by omega, Function.iterate_add_apply]
            simp
    _ = F ((((x + 1 : ℕ) : ZMod m)), (((x / 2 : ℕ) : ZMod m))) := by rw [hmid]
    _ = ((((x + 3 : ℕ) : ZMod m)), (((x / 2 + 2 : ℕ) : ZMod m))) := by
          have hx1 : 1 + 2 * (x / 2) = x + 1 := by
            rcases hxeven with ⟨r, hr⟩
            rw [hr]
            omega
          have hx3 : 3 + 2 * (x / 2) = x + 3 := by
            rcases hxeven with ⟨r, hr⟩
            rw [hr]
            omega
          simpa [hx1, hx3] using
            returnMap0CaseIIXY_R_line (m := m) (y := x / 2) (by omega)

theorem returnMap0CaseIIXY_even_generic_after_R_step [Fact (9 < m)] {x y : ℕ}
    (hx4 : 4 ≤ x) (hxle : x ≤ m - 4) (hxeven : Even x)
    (hyl : x / 2 + 2 ≤ y) (hyu : y ≤ x + 1) :
    returnMap0CaseIIXY (m := m) ((((x + 3 : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))) =
      ((((x + 3 : ℕ) : ZMod m)), (((y + 1 : ℕ) : ZMod m))) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let pre : QCoord m := ((((m + x + 3 - 2 * y : ℕ) : ZMod m)), (((y : ℕ) : ZMod m)))
  have hxy : fromXY (m := m) ((((x + 3 : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))) = pre := by
    ext <;> simp [pre, fromXY]
    · have hle : 2 * y ≤ m + x + 3 := by omega
      rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul]
      simp
  have hilt : m + x + 3 - 2 * y < m := by
    rcases hxeven with ⟨r, hr⟩
    rw [hr] at hyl hyu ⊢
    omega
  have hipos : 0 < m + x + 3 - 2 * y := by
    rcases hxeven with ⟨r, hr⟩
    rw [hr] at hyl hyu ⊢
    omega
  have hitwo : 2 ≤ m + x + 3 - 2 * y := by
    rcases hxeven with ⟨r, hr⟩
    rw [hr] at hyl hyu ⊢
    omega
  have hi0 : pre.1 ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := m + x + 3 - 2 * y) hipos hilt
  have hi1 : pre.1 ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := m + x + 3 - 2 * y) hitwo hilt
  have hk0 : pre.2 ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := y) (by omega) (by omega)
  have hk1 : pre.2 ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := y) (by omega) (by omega)
  have hkneg1 : pre.2 ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := y) (by omega)
  have hkneg2 : pre.2 ≠ (-2 : ZMod m) := by
    exact natCast_ne_neg_two_of_lt (m := m) (n := y) (by omega)
  have hdir :
      dir0CaseIILayerZero (m := m) pre = 1 :=
    dir0CaseIILayerZero_eq_one_of_generic (m := m) hi0 hi1 hk0 hk1 hkneg1 hkneg2
  have hsum1 : pre.1 + pre.2 ≠ 1 := by
    intro h
    have hcast : (((m + x + 3 - y : ℕ) : ZMod m)) = 1 := by
      calc
        (((m + x + 3 - y : ℕ) : ZMod m))
            = ((((m + x + 3 - 2 * y : ℕ) : ZMod m)) + (((y : ℕ) : ZMod m))) := by
                have hnat : m + x + 3 - y = (m + x + 3 - 2 * y) + y := by omega
                simpa [Nat.cast_add] using congrArg (fun n : ℕ => (((n : ℕ) : ZMod m))) hnat
        _ = 1 := h
    have hxny_ne : (((m + x + 3 - y : ℕ) : ZMod m)) ≠ 1 := by
      intro h1
      have hred : (((x + 3 - y : ℕ) : ZMod m)) = 1 := by
        have hnat : m + x + 3 - y = m + (x + 3 - y) := by omega
        calc
          (((x + 3 - y : ℕ) : ZMod m)) = (((m + (x + 3 - y) : ℕ) : ZMod m)) := by
              rw [Nat.cast_add]
              simp
          _ = (((m + x + 3 - y : ℕ) : ZMod m)) := by rw [hnat]
          _ = 1 := h1
      exact natCast_ne_one_of_two_le_lt (m := m) (n := x + 3 - y) (by omega) (by omega) hred
    exact hxny_ne hcast
  have hi2k : pre.1 + 2 * pre.2 = (((x + 3 : ℕ) : ZMod m)) := by
    have h := congrArg (fun u : P0Coord m => u.1 + 2 * u.2) hxy
    simpa [fromXY] using h.symm
  have hret := returnMap0CaseII_of_dir1_generic (m := m) (u := pre) hdir hi0 hsum1
  calc
    returnMap0CaseIIXY (m := m) ((((x + 3 : ℕ) : ZMod m)), (((y : ℕ) : ZMod m)))
        = toXY (m := m)
            (returnMap0CaseII (m := m) (fromXY (m := m) ((((x + 3 : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))))) := by
              simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) pre) := by rw [hxy]
    _ = toXY (m := m) (pre.1 - 2, pre.2 + 1) := by
          simpa using congrArg (toXY (m := m)) hret
    _ = ((((x + 3 : ℕ) : ZMod m)), (((y + 1 : ℕ) : ZMod m))) := by
          ext
          · calc
              (pre.1 - 2) + 2 * (pre.2 + 1) = pre.1 + 2 * pre.2 := by ring
              _ = (((x + 3 : ℕ) : ZMod m)) := hi2k
          · simp [toXY, pre, Nat.cast_add]

theorem iterate_returnMap0CaseIIXY_even_generic_after_R_partial [Fact (9 < m)] {x t : ℕ}
    (hx4 : 4 ≤ x) (hxle : x ≤ m - 4) (hxeven : Even x)
    (ht : t ≤ x / 2) :
    ((returnMap0CaseIIXY (m := m)^[t])
      ((((x + 3 : ℕ) : ZMod m)), (((x / 2 + 2 : ℕ) : ZMod m)))) =
      ((((x + 3 : ℕ) : ZMod m)), (((x / 2 + 2 + t : ℕ) : ZMod m))) := by
  induction t with
  | zero =>
      simp
  | succ t iht =>
      have ht' : t ≤ x / 2 := Nat.le_of_succ_le ht
      have hstep :
          returnMap0CaseIIXY (m := m)
            ((((x + 3 : ℕ) : ZMod m)), (((x / 2 + 2 + t : ℕ) : ZMod m))) =
              ((((x + 3 : ℕ) : ZMod m)), (((x / 2 + 2 + t + 1 : ℕ) : ZMod m))) := by
        have hyl : x / 2 + 2 ≤ x / 2 + 2 + t := by omega
        have hyu : x / 2 + 2 + t ≤ x + 1 := by omega
        simpa [Nat.add_assoc] using
          returnMap0CaseIIXY_even_generic_after_R_step (m := m) hx4 hxle hxeven
            (y := x / 2 + 2 + t) hyl hyu
      calc
        ((returnMap0CaseIIXY (m := m)^[t.succ])
            ((((x + 3 : ℕ) : ZMod m)), (((x / 2 + 2 : ℕ) : ZMod m))))
            = returnMap0CaseIIXY (m := m)
                (((returnMap0CaseIIXY (m := m)^[t])
                  ((((x + 3 : ℕ) : ZMod m)), (((x / 2 + 2 : ℕ) : ZMod m))))) := by
                    rw [Function.iterate_succ_apply']
        _ = returnMap0CaseIIXY (m := m)
              ((((x + 3 : ℕ) : ZMod m)), (((x / 2 + 2 + t : ℕ) : ZMod m))) := by
                rw [iht ht']
        _ = ((((x + 3 : ℕ) : ZMod m)), (((x / 2 + 2 + t + 1 : ℕ) : ZMod m))) := hstep
        _ = ((((x + 3 : ℕ) : ZMod m)), (((x / 2 + 2 + t.succ : ℕ) : ZMod m))) := by
              simp [Nat.succ_eq_add_one, Nat.add_assoc]

theorem iterate_returnMap0CaseIIXY_even_generic_to_A [Fact (9 < m)] {x : ℕ}
    (hx4 : 4 ≤ x) (hxle : x ≤ m - 8) (hxeven : Even x) :
    ((returnMap0CaseIIXY (m := m)^[x + 2])
      (linePoint0 (m := m) (⟨x, by omega⟩ : Fin m))) =
      ((((x + 4 : ℕ) : ZMod m)), (((x + 4 : ℕ) : ZMod m))) := by
  let F := returnMap0CaseIIXY (m := m)
  let xFin : Fin m := ⟨x, by omega⟩
  have hR :
      ((F^[x / 2 + 1]) (linePoint0 (m := m) xFin)) =
        ((((x + 3 : ℕ) : ZMod m)), (((x / 2 + 2 : ℕ) : ZMod m))) := by
    exact iterate_returnMap0CaseIIXY_even_generic_to_R (m := m) hx4 (by omega) hxeven
  have hpreA :
      ((F^[x / 2]) ((((x + 3 : ℕ) : ZMod m)), (((x / 2 + 2 : ℕ) : ZMod m)))) =
        ((((x + 3 : ℕ) : ZMod m)), (((x + 2 : ℕ) : ZMod m))) := by
    have hmain := iterate_returnMap0CaseIIXY_even_generic_after_R_partial
      (m := m) (x := x) (t := x / 2) hx4 (by omega) hxeven le_rfl
    have hsum : x / 2 + 2 + x / 2 = x + 2 := by
      rcases hxeven with ⟨r, hr⟩
      rw [hr]
      omega
    simpa [hsum] using hmain
  calc
    ((F^[x + 2]) (linePoint0 (m := m) xFin))
        = F (((F^[x + 1]) (linePoint0 (m := m) xFin))) := by
            rw [show x + 2 = 1 + (x + 1) by omega, Function.iterate_add_apply]
            simp
    _ = F (((F^[x / 2]) ((((x + 3 : ℕ) : ZMod m)), (((x / 2 + 2 : ℕ) : ZMod m))))) := by
          rw [show x + 1 = x / 2 + (x / 2 + 1) by
            rcases hxeven with ⟨r, hr⟩
            rw [hr]
            omega, Function.iterate_add_apply, hR]
    _ = F ((((x + 3 : ℕ) : ZMod m)), (((x + 2 : ℕ) : ZMod m))) := by rw [hpreA]
    _ = ((((x + 4 : ℕ) : ZMod m)), (((x + 4 : ℕ) : ZMod m))) := by
          simpa [show x + 2 + 1 = x + 3 by omega, show x + 2 + 2 = x + 4 by omega] using
            returnMap0CaseIIXY_A_line (m := m) (y := x + 2) (by omega) (by omega)

theorem returnMap0CaseIIXY_m_sub_one_m_sub_two_zero [Fact (9 < m)] :
    returnMap0CaseIIXY (m := m)
      ((((m - 1 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) =
        ((0 : ZMod m), (0 : ZMod m)) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let preA : QCoord m := ((3 : ZMod m), (-2 : ZMod m))
  have hneg1cast : (((m - 1 : ℕ) : ZMod m)) = (-1 : ZMod m) :=
    cast_sub_one_eq_neg_one (m := m) (by omega)
  have hneg2cast : (((m - 2 : ℕ) : ZMod m)) = (-2 : ZMod m) :=
    cast_sub_two_eq_neg_two (m := m) (by omega)
  have hxy :
      fromXY (m := m) ((((m - 1 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) = preA := by
    ext
    · simp [preA, fromXY, hneg1cast, hneg2cast]
      ring_nf
    · simp [preA, fromXY, hneg2cast]
  have h3ne0 : (3 : ZMod m) ≠ 0 :=
    natCast_ne_zero_of_pos_lt (m := m) (n := 3) (by omega) (by omega)
  have h3ne1 : (3 : ZMod m) ≠ 1 :=
    natCast_ne_one_of_two_le_lt (m := m) (n := 3) (by omega) (by omega)
  have h3ne2 : (3 : ZMod m) ≠ 2 := by
    exact natCast_ne_two_of_three_le_lt (m := m) (n := 3) (by omega) (by omega)
  have hdir :
      dir0CaseIILayerZero (m := m) preA = 1 :=
    dir0CaseIILayerZero_eq_one_of_k_neg_two_generic (m := m) h3ne0 h3ne1 h3ne2
  have hi0 : preA.1 ≠ 0 := by simpa [preA] using h3ne0
  have hsum1 : preA.1 + preA.2 = 1 := by
    change (3 : ZMod m) + (-2 : ZMod m) = (1 : ZMod m)
    ring
  have hret := returnMap0CaseII_of_dir1_sum_one (m := m) (u := preA) hdir hi0 hsum1
  calc
    returnMap0CaseIIXY (m := m) ((((m - 1 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m)))
        = toXY (m := m)
            (returnMap0CaseII (m := m)
              (fromXY (m := m) ((((m - 1 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))))) := by
                simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) preA) := by rw [hxy]
    _ = toXY (m := m) (preA.1 - 3, preA.2 + 2) := by
          simpa using congrArg (toXY (m := m)) hret
    _ = ((0 : ZMod m), (0 : ZMod m)) := by
          simp [toXY, preA]

theorem firstReturn_line_m_sub_four_caseII_mod_ten [Fact (9 < m)] (hm : m % 12 = 10) :
    ((returnMap0CaseIIXY (m := m)^[m - 2])
        (linePoint0 (m := m) (⟨m - 4, by omega⟩ : Fin m))) =
      linePoint0 (m := m) (0 : Fin m) := by
  have hm4lt : m - 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  have hx4 : 4 ≤ m - 4 := by
    have hm9 : 9 < m := Fact.out
    omega
  have hxle : m - 4 ≤ m - 4 := le_rfl
  have hxeven : Even (m - 4) := by
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rw [hq]
    refine ⟨6 * q + 3, ?_⟩
    omega
  have hR :
      ((returnMap0CaseIIXY (m := m)^[m / 2 - 1])
          (linePoint0 (m := m) (⟨m - 4, hm4lt⟩ : Fin m))) =
        ((((m - 1 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m))) := by
    have hmainR := iterate_returnMap0CaseIIXY_even_generic_to_R
      (m := m) (x := m - 4) hx4 hxle hxeven
    simpa [show (m - 4) / 2 + 1 = m / 2 - 1 by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega,
      show (m - 4) + 3 = m - 1 by omega,
      show (m - 4) / 2 + 2 = m / 2 by
        rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
        rw [hq]
        omega] using hmainR
  have hpreA :
      ((returnMap0CaseIIXY (m := m)^[m / 2 - 2])
          ((((m - 1 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m)))) =
        ((((m - 1 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) := by
    have hhalf : (m - 4) / 2 = m / 2 - 2 := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega
    have htpre : m / 2 - 2 ≤ (m - 4) / 2 := by
      rw [hhalf]
    have hmainPre := iterate_returnMap0CaseIIXY_even_generic_after_R_partial
      (m := m) (x := m - 4) (t := m / 2 - 2) hx4 hxle hxeven htpre
    have hstartNat : (m / 2 - 2) + 2 = m / 2 := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega
    have hendNat : m / 2 + (m / 2 - 2) = m - 2 := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega
    simpa [hhalf,
      show (m - 4) + 3 = m - 1 by omega,
      hstartNat, hendNat, Nat.cast_add] using hmainPre
  have hsplit :
      ((returnMap0CaseIIXY (m := m)^[m - 3])
          (linePoint0 (m := m) (⟨m - 4, hm4lt⟩ : Fin m))) =
        ((((m - 1 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) := by
    have hiter :
        ((returnMap0CaseIIXY (m := m)^[m - 3])
            (linePoint0 (m := m) (⟨m - 4, hm4lt⟩ : Fin m))) =
          ((returnMap0CaseIIXY (m := m)^[m / 2 - 2])
            (((returnMap0CaseIIXY (m := m)^[m / 2 - 1])
              (linePoint0 (m := m) (⟨m - 4, hm4lt⟩ : Fin m))))) := by
      simpa [show (m / 2 - 2) + (m / 2 - 1) = m - 3 by
        rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
        rw [hq]
        omega] using
        (Function.iterate_add_apply (returnMap0CaseIIXY (m := m)) (m / 2 - 2) (m / 2 - 1)
          (linePoint0 (m := m) (⟨m - 4, hm4lt⟩ : Fin m)))
    calc
      ((returnMap0CaseIIXY (m := m)^[m - 3])
          (linePoint0 (m := m) (⟨m - 4, hm4lt⟩ : Fin m)))
          = ((returnMap0CaseIIXY (m := m)^[m / 2 - 2])
              (((returnMap0CaseIIXY (m := m)^[m / 2 - 1])
                (linePoint0 (m := m) (⟨m - 4, hm4lt⟩ : Fin m))))) := hiter
      _ = ((returnMap0CaseIIXY (m := m)^[m / 2 - 2])
            ((((m - 1 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m)))) := by rw [hR]
      _ = ((((m - 1 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) := hpreA
  calc
    ((returnMap0CaseIIXY (m := m)^[m - 2])
        (linePoint0 (m := m) (⟨m - 4, hm4lt⟩ : Fin m)))
        = returnMap0CaseIIXY (m := m)
            (((returnMap0CaseIIXY (m := m)^[m - 3])
              (linePoint0 (m := m) (⟨m - 4, hm4lt⟩ : Fin m)))) := by
                simpa [show 1 + (m - 3) = m - 2 by omega] using
                  (Function.iterate_add_apply (returnMap0CaseIIXY (m := m)) 1 (m - 3)
                    (linePoint0 (m := m) (⟨m - 4, hm4lt⟩ : Fin m)))
    _ = returnMap0CaseIIXY (m := m)
          ((((m - 1 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) := by rw [hsplit]
    _ = ((0 : ZMod m), (0 : ZMod m)) := by
          exact returnMap0CaseIIXY_m_sub_one_m_sub_two_zero (m := m)
    _ = linePoint0 (m := m) (0 : Fin m) := by
          simp [linePoint0]

theorem returnMap0CaseIIXY_m_sub_one_zero_one [Fact (9 < m)] :
    returnMap0CaseIIXY (m := m) ((((m - 1 : ℕ) : ZMod m)), (0 : ZMod m)) =
      ((((m - 1 : ℕ) : ZMod m)), (1 : ZMod m)) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let pre : QCoord m := ((-1 : ZMod m), (0 : ZMod m))
  have hxy :
      fromXY (m := m) ((((m - 1 : ℕ) : ZMod m)), (0 : ZMod m)) = pre := by
    ext <;> simp [pre, fromXY, cast_sub_one_eq_neg_one (m := m) (by omega)]
  have hi0 : pre.1 ≠ 0 := by
    exact neg_ne_zero.mpr (one_ne_zero (m := m))
  have hneg1ne1 : (-1 : ZMod m) ≠ 1 := by
    intro h
    exact one_ne_neg_one (m := m) h.symm
  have hneg1ne2 : (-1 : ZMod m) ≠ 2 := by
    intro h
    have hm4' : 4 < m := Fact.out
    exact natCast_ne_neg_one_of_lt (m := m) (n := 2) (by omega) h.symm
  have h1ne2 : (1 : ZMod m) ≠ 2 := by
    exact (two_ne_one (m := m)).symm
  have hdir : dir0CaseIILayerZero (m := m) pre = 1 := by
    simp [pre, dir0CaseIILayerZero, one_ne_zero (m := m), two_ne_zero (m := m),
      hneg1ne1, hneg1ne2, h1ne2]
  have hsum1 : pre.1 + pre.2 ≠ 1 := by
    simpa [pre] using hneg1ne1
  have hret := returnMap0CaseII_of_dir1_generic (m := m) (u := pre) hdir hi0 hsum1
  calc
    returnMap0CaseIIXY (m := m) ((((m - 1 : ℕ) : ZMod m)), (0 : ZMod m))
        = toXY (m := m)
            (returnMap0CaseII (m := m)
              (fromXY (m := m) ((((m - 1 : ℕ) : ZMod m)), (0 : ZMod m)))) := by
                simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) pre) := by rw [hxy]
    _ = toXY (m := m) (pre.1 - 2, pre.2 + 1) := by
          simpa using congrArg (toXY (m := m)) hret
    _ = ((-1 : ZMod m), (1 : ZMod m)) := by
          ext <;> simp [toXY, pre]
    _ = ((((m - 1 : ℕ) : ZMod m)), (1 : ZMod m)) := by
          rw [cast_sub_one_eq_neg_one (m := m) (by omega)]

theorem returnMap0CaseIIXY_m_sub_one_m_sub_one [Fact (9 < m)] :
    returnMap0CaseIIXY (m := m)
      ((((m - 1 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) =
        ((2 : ZMod m), (2 : ZMod m)) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let pre : QCoord m := ((1 : ZMod m), (-1 : ZMod m))
  have hxy :
      fromXY (m := m)
        ((((m - 1 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) = pre := by
    ext <;> simp [pre, fromXY, cast_sub_one_eq_neg_one (m := m) (by omega)]
    all_goals ring_nf
  have hneg1ne_neg2 : (-1 : ZMod m) ≠ (-2 : ZMod m) := by
    intro h
    have : (1 : ZMod m) = 0 := by
      calc
        (1 : ZMod m) = (-1 : ZMod m) + 2 := by ring
        _ = (-2 : ZMod m) + 2 := by rw [h]
        _ = 0 := by ring
    exact one_ne_zero (m := m) this
  have hdir :
      dir0CaseIILayerZero (m := m) pre = 2 :=
    dir0CaseIILayerZero_eq_two_of_i_one (m := m) (k := (-1 : ZMod m)) hneg1ne_neg2
  have hi0 : pre.1 ≠ 0 := by
    change (1 : ZMod m) ≠ 0
    exact one_ne_zero (m := m)
  have hsum0 : pre.1 + pre.2 = 0 := by
    change (1 : ZMod m) + (-1 : ZMod m) = 0
    ring
  have hret := returnMap0CaseII_of_dir2_i_ne_zero_sum_zero (m := m) (u := pre) hdir hi0 hsum0
  calc
    returnMap0CaseIIXY (m := m)
        ((((m - 1 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m)))
        = toXY (m := m)
            (returnMap0CaseII (m := m)
              (fromXY (m := m)
                ((((m - 1 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))))) := by
                  simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) pre) := by rw [hxy]
    _ = toXY (m := m) (pre.1 - 3, pre.2 + 3) := by
          simpa using congrArg (toXY (m := m)) hret
    _ = ((2 : ZMod m), (2 : ZMod m)) := by
          ext <;> simp [toXY, pre]
          all_goals ring_nf

theorem returnMap0CaseIIXY_m_sub_two_m_sub_two [Fact (9 < m)] :
    returnMap0CaseIIXY (m := m)
      ((((m - 2 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) =
        ((1 : ZMod m), (1 : ZMod m)) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let pre : QCoord m := ((2 : ZMod m), (-2 : ZMod m))
  have hxy :
      fromXY (m := m)
        ((((m - 2 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) = pre := by
    ext <;> simp [pre, fromXY, cast_sub_two_eq_neg_two (m := m) (by omega)]
    all_goals ring_nf
  have hdir : dir0CaseIILayerZero (m := m) pre = 2 := by
    simpa [pre] using dir0CaseIILayerZero_eq_two_two_neg_two (m := m)
  have hi0 : pre.1 ≠ 0 := by
    simpa [pre] using two_ne_zero (m := m)
  have hsum0 : pre.1 + pre.2 = 0 := by
    change (2 : ZMod m) + (-2 : ZMod m) = 0
    ring
  have hret := returnMap0CaseII_of_dir2_i_ne_zero_sum_zero (m := m) (u := pre) hdir hi0 hsum0
  calc
    returnMap0CaseIIXY (m := m)
        ((((m - 2 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m)))
        = toXY (m := m)
            (returnMap0CaseII (m := m)
              (fromXY (m := m)
                ((((m - 2 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))))) := by
                  simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) pre) := by rw [hxy]
    _ = toXY (m := m) (pre.1 - 3, pre.2 + 3) := by
          simpa using congrArg (toXY (m := m)) hret
    _ = ((1 : ZMod m), (1 : ZMod m)) := by
          ext <;> simp [toXY, pre]
          all_goals ring_nf

theorem firstReturn_line_m_sub_one_caseII_mod_ten [Fact (9 < m)] (hm : m % 12 = 10) :
    ((returnMap0CaseIIXY (m := m)^[m - 1])
        (linePoint0 (m := m) (⟨m - 1, by omega⟩ : Fin m))) =
      linePoint0 (m := m) (1 : Fin m) := by
  let F := returnMap0CaseIIXY (m := m)
  let start : P0Coord m := linePoint0 (m := m) (⟨m - 1, by omega⟩ : Fin m)
  have hstep1 : F start = ((((m - 1 : ℕ) : ZMod m)), (1 : ZMod m)) := by
    simpa [F, start] using returnMap0CaseIIXY_m_sub_one_zero_one (m := m)
  have hstep2 :
      F ((((m - 1 : ℕ) : ZMod m)), (1 : ZMod m)) = ((((m - 1 : ℕ) : ZMod m)), (2 : ZMod m)) := by
    simpa [show (m - 2) + 1 = m - 1 by omega] using
      returnMap0CaseIIXY_even_generic_odd_column_one_step (m := m) (x := m - 2) (by omega)
        (by omega)
  have htail :
      ((F^[m / 2 - 3]) ((((m - 1 : ℕ) : ZMod m)), (2 : ZMod m))) =
        ((((m - 1 : ℕ) : ZMod m)), (((m / 2 - 1 : ℕ) : ZMod m))) := by
    have ht : m / 2 - 3 ≤ (m - 2) / 2 - 2 := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega
    have hmain := iterate_returnMap0CaseIIXY_even_generic_odd_column_lower_partial
      (m := m) (x := m - 2) (t := m / 2 - 3) (by omega) (by omega) ht
    have hsum : 2 + (m / 2 - 3) = m / 2 - 1 := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega
    simpa [F, show (m - 2) + 1 = m - 1 by omega, hsum] using hmain
  have hprefix :
      ((F^[m / 2 - 1]) start) = ((((m - 1 : ℕ) : ZMod m)), (((m / 2 - 1 : ℕ) : ZMod m))) := by
    have h12 :
        ((F^[2]) start) = ((((m - 1 : ℕ) : ZMod m)), (2 : ZMod m)) := by
      calc
        ((F^[2]) start) = F (F start) := by simp [Function.iterate_succ_apply']
        _ = F ((((m - 1 : ℕ) : ZMod m)), (1 : ZMod m)) := by rw [hstep1]
        _ = ((((m - 1 : ℕ) : ZMod m)), (2 : ZMod m)) := hstep2
    calc
      ((F^[m / 2 - 1]) start) = ((F^[m / 2 - 3]) ((F^[2]) start)) := by
        rw [show m / 2 - 1 = (m / 2 - 3) + 2 by
          rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
          rw [hq]
          omega,
          Function.iterate_add_apply]
      _ = ((F^[m / 2 - 3]) ((((m - 1 : ℕ) : ZMod m)), (2 : ZMod m))) := by rw [h12]
      _ = ((((m - 1 : ℕ) : ZMod m)), (((m / 2 - 1 : ℕ) : ZMod m))) := htail
  have hR :
      F ((((m - 1 : ℕ) : ZMod m)), (((m / 2 - 1 : ℕ) : ZMod m))) =
        ((1 : ZMod m), (((m / 2 + 1 : ℕ) : ZMod m))) := by
    have hy : m / 2 - 1 ≤ m - 3 := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega
    have hmain := returnMap0CaseIIXY_R_line (m := m) (y := m / 2 - 1) hy
    have hxnat : 1 + 2 * (m / 2 - 1) = m - 1 := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega
    have hxdst : 3 + 2 * (m / 2 - 1) = m + 1 := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega
    have hynat : (m / 2 - 1) + 2 = m / 2 + 1 := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega
    calc
      F ((((m - 1 : ℕ) : ZMod m)), (((m / 2 - 1 : ℕ) : ZMod m)))
          = ((((m + 1 : ℕ) : ZMod m)), (((m / 2 + 1 : ℕ) : ZMod m))) := by
              simpa [F, hxnat, hxdst, hynat, Nat.cast_add] using hmain
      _ = ((1 : ZMod m), (((m / 2 + 1 : ℕ) : ZMod m))) := by
            simp [Nat.cast_add]
  have hzero :
      ((F^[m / 2 - 1]) ((1 : ZMod m), (((m / 2 + 1 : ℕ) : ZMod m)))) =
        ((1 : ZMod m), (0 : ZMod m)) := by
    have hy0l : (m + 1 + 1) / 2 ≤ m / 2 + 1 := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega
    have hy0u : m / 2 + 1 ≤ m - 2 := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega
    simpa [F, show m - (m / 2 + 1) = m / 2 - 1 by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega] using
      iterate_returnMap0CaseIIXY_wrapped_upper_column_to_zero (m := m) hm
        (c := 1) (y0 := m / 2 + 1) (by omega) (by omega) (by exact ⟨0, by omega⟩)
        hy0l hy0u
  have hafterR :
      ((F^[m / 2]) start) = ((1 : ZMod m), (((m / 2 + 1 : ℕ) : ZMod m))) := by
    calc
      ((F^[m / 2]) start) = F (((F^[m / 2 - 1]) start)) := by
        simpa [show 1 + (m / 2 - 1) = m / 2 by
          rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
          rw [hq]
          omega] using
          (Function.iterate_add_apply F 1 (m / 2 - 1) start)
      _ = F ((((m - 1 : ℕ) : ZMod m)), (((m / 2 - 1 : ℕ) : ZMod m))) := by rw [hprefix]
      _ = ((1 : ZMod m), (((m / 2 + 1 : ℕ) : ZMod m))) := hR
  calc
    ((F^[m - 1]) start) = ((F^[m / 2 - 1]) ((F^[m / 2]) start)) := by
      simpa [show (m / 2 - 1) + m / 2 = m - 1 by
        rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
        rw [hq]
        omega] using
        (Function.iterate_add_apply F (m / 2 - 1) (m / 2) start)
    _ = ((F^[m / 2 - 1]) ((1 : ZMod m), (((m / 2 + 1 : ℕ) : ZMod m)))) := by rw [hafterR]
    _ = ((1 : ZMod m), (0 : ZMod m)) := hzero
    _ = linePoint0 (m := m) (1 : Fin m) := by
          simp [linePoint0]

theorem firstReturn_line_m_sub_three_caseII_mod_ten [Fact (9 < m)] (hm : m % 12 = 10) :
    ((returnMap0CaseIIXY (m := m)^[2 * m - 3])
        (linePoint0 (m := m) (⟨m - 3, by omega⟩ : Fin m))) =
      linePoint0 (m := m) (2 : Fin m) := by
  let F := returnMap0CaseIIXY (m := m)
  let start : P0Coord m := linePoint0 (m := m) (⟨m - 3, by omega⟩ : Fin m)
  have hxodd : Odd (m - 3) := by
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rw [hq]
    refine ⟨6 * q + 3, ?_⟩
    omega
  have h1 : F start = ((((m - 2 : ℕ) : ZMod m)), (1 : ZMod m)) := by
    change returnMap0CaseIIXY (m := m) ((((m - 3 : ℕ) : ZMod m)), (0 : ZMod m)) =
      ((((m - 2 : ℕ) : ZMod m)), (1 : ZMod m))
    simpa [show (m - 3) + 1 = m - 2 by omega] using
      returnMap0CaseIIXY_line_start_generic (m := m) (x := m - 3) (by omega) (by omega)
  have hAcol :
      ((F^[m - 4]) ((((m - 2 : ℕ) : ZMod m)), (1 : ZMod m))) =
        ((((m - 2 : ℕ) : ZMod m)), (((m - 3 : ℕ) : ZMod m))) := by
    have hmain := iterate_returnMap0CaseIIXY_odd_generic_to_A
      (m := m) (x := m - 3) (by omega) (by omega) hxodd
    simpa [F, show (m - 3) + 1 = m - 2 by omega] using hmain
  have hprefix :
      ((F^[m - 3]) start) =
        ((((m - 2 : ℕ) : ZMod m)), (((m - 3 : ℕ) : ZMod m))) := by
    calc
      ((F^[m - 3]) start) = ((F^[m - 4]) (F start)) := by
        simpa [show (m - 4) + 1 = m - 3 by omega] using
          (Function.iterate_add_apply F (m - 4) 1 start)
      _ = ((F^[m - 4]) ((((m - 2 : ℕ) : ZMod m)), (1 : ZMod m))) := by rw [h1]
      _ = ((((m - 2 : ℕ) : ZMod m)), (((m - 3 : ℕ) : ZMod m))) := hAcol
  have hAstep :
      F ((((m - 2 : ℕ) : ZMod m)), (((m - 3 : ℕ) : ZMod m))) =
        ((((m - 1 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) := by
    simpa [F, show (m - 3) + 1 = m - 2 by omega, show (m - 3) + 2 = m - 1 by omega] using
      returnMap0CaseIIXY_A_line (m := m) (y := m - 3) (by omega) (by omega)
  have hafterA :
      ((F^[m - 2]) start) =
        ((((m - 1 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) := by
    calc
      ((F^[m - 2]) start) = F (((F^[m - 3]) start)) := by
        simpa [show 1 + (m - 3) = m - 2 by omega] using
          (Function.iterate_add_apply F 1 (m - 3) start)
      _ = F ((((m - 2 : ℕ) : ZMod m)), (((m - 3 : ℕ) : ZMod m))) := by rw [hprefix]
      _ = ((((m - 1 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) := hAstep
  have hafterQ :
      ((F^[m - 1]) start) = ((2 : ZMod m), (2 : ZMod m)) := by
    calc
      ((F^[m - 1]) start) = F (((F^[m - 2]) start)) := by
        simpa [show 1 + (m - 2) = m - 1 by omega] using
          (Function.iterate_add_apply F 1 (m - 2) start)
      _ = F ((((m - 1 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) := by rw [hafterA]
      _ = ((2 : ZMod m), (2 : ZMod m)) := by
            exact returnMap0CaseIIXY_m_sub_one_m_sub_one (m := m)
  calc
    ((F^[2 * m - 3]) start) = ((F^[m - 2]) ((F^[m - 1]) start)) := by
      simpa [show (m - 2) + (m - 1) = 2 * m - 3 by omega] using
        (Function.iterate_add_apply F (m - 2) (m - 1) start)
    _ = ((F^[m - 2]) ((2 : ZMod m), (2 : ZMod m))) := by rw [hafterQ]
    _ = ((2 : ZMod m), (0 : ZMod m)) := by
          exact iterate_returnMap0CaseIIXY_two_column_to_zero (m := m) hm
    _ = linePoint0 (m := m) (2 : Fin m) := by
          simp [linePoint0]

theorem firstReturn_line_m_sub_six_caseII_mod_ten [Fact (9 < m)] (hm : m % 12 = 10) :
    ((returnMap0CaseIIXY (m := m)^[2 * m - 4])
        (linePoint0 (m := m) (⟨m - 6, by omega⟩ : Fin m))) =
      linePoint0 (m := m) (3 : Fin m) := by
  let F := returnMap0CaseIIXY (m := m)
  let start : P0Coord m := linePoint0 (m := m) (⟨m - 6, by omega⟩ : Fin m)
  have hx4 : 4 ≤ m - 6 := by
    have hm9 : 9 < m := Fact.out
    omega
  have hxleR : m - 6 ≤ m - 4 := by omega
  have hxeven : Even (m - 6) := by
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rw [hq]
    refine ⟨6 * q + 2, ?_⟩
    omega
  have hR :
      ((F^[m / 2 - 2]) start) =
        ((((m - 3 : ℕ) : ZMod m)), (((m / 2 - 1 : ℕ) : ZMod m))) := by
    have hmain := iterate_returnMap0CaseIIXY_even_generic_to_R
      (m := m) (x := m - 6) hx4 hxleR hxeven
    have hsteps : (m - 6) / 2 + 1 = m / 2 - 2 := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega
    have hfst : (m - 6) + 3 = m - 3 := by omega
    have hsnd : (m - 6) / 2 + 2 = m / 2 - 1 := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega
    simpa [linePoint0, hsteps, hfst, hsnd] using hmain
  have hpreA :
      ((F^[m / 2 - 3]) ((((m - 3 : ℕ) : ZMod m)), (((m / 2 - 1 : ℕ) : ZMod m)))) =
        ((((m - 3 : ℕ) : ZMod m)), (((m - 4 : ℕ) : ZMod m))) := by
    have hmain := iterate_returnMap0CaseIIXY_even_generic_after_R_partial
      (m := m) (x := m - 6) (t := m / 2 - 3) hx4 hxleR hxeven
        (by
          rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
          rw [hq]
          omega)
    have hstart : (m - 6) / 2 + 2 = m / 2 - 1 := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega
    have hend : (m - 6) / 2 + 2 + (m / 2 - 3) = m - 4 := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega
    calc
      ((F^[m / 2 - 3]) ((((m - 3 : ℕ) : ZMod m)), (((m / 2 - 1 : ℕ) : ZMod m))))
          = ((returnMap0CaseIIXY (m := m)^[m / 2 - 3])
              ((((m - 6 + 3 : ℕ) : ZMod m)), ((((m - 6) / 2 + 2 : ℕ) : ZMod m)))) := by
                simp [F, hstart, show (m - 6 + 3 = m - 3) by omega]
      _ = ((((m - 6 + 3 : ℕ) : ZMod m)), ((((m - 6) / 2 + 2 + (m / 2 - 3) : ℕ) : ZMod m))) := hmain
      _ = ((((m - 3 : ℕ) : ZMod m)), (((m - 4 : ℕ) : ZMod m))) := by
            simp [hend, show (m - 6 + 3 = m - 3) by omega]
  have hA :
      F ((((m - 3 : ℕ) : ZMod m)), (((m - 4 : ℕ) : ZMod m))) =
        ((((m - 2 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) := by
    simpa [F, show (m - 4) + 1 = m - 3 by omega, show (m - 4) + 2 = m - 2 by omega] using
      returnMap0CaseIIXY_A_line (m := m) (y := m - 4) (by omega) (by omega)
  have hafterA :
      ((F^[m - 4]) start) =
        ((((m - 2 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) := by
    calc
      ((F^[m - 4]) start)
          = F ((F^[m - 5]) start) := by
              simpa [show 1 + (m - 5) = m - 4 by omega] using
                (Function.iterate_add_apply F 1 (m - 5) start)
      _ = F ((((m - 3 : ℕ) : ZMod m)), (((m - 4 : ℕ) : ZMod m))) := by
            have hsplit :
                ((F^[m - 5]) start) =
                  ((F^[m / 2 - 3]) ((F^[m / 2 - 2]) start)) := by
                    simpa [show (m / 2 - 3) + (m / 2 - 2) = m - 5 by
                      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
                      rw [hq]
                      omega] using
                      (Function.iterate_add_apply F (m / 2 - 3) (m / 2 - 2) start)
            rw [hsplit, hR, hpreA]
      _ = ((((m - 2 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) := hA
  have htail1 :
      F ((((m - 2 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) = ((1 : ZMod m), (1 : ZMod m)) := by
    exact returnMap0CaseIIXY_m_sub_two_m_sub_two (m := m)
  have htail2 :
      F ((1 : ZMod m), (1 : ZMod m)) = ((0 : ZMod m), (1 : ZMod m)) := by
    exact returnMap0CaseIIXY_one_one (m := m)
  have htail3 :
      F ((0 : ZMod m), (1 : ZMod m)) = ((1 : ZMod m), (2 : ZMod m)) := by
    exact returnMap0CaseIIXY_zero_one (m := m)
  have hcol1 :
      ((F^[m / 2 - 2]) ((1 : ZMod m), (2 : ZMod m))) =
        ((1 : ZMod m), (((m / 2 : ℕ) : ZMod m))) := by
    have hmain := iterate_returnMap0CaseIIXY_one_column_lower_partial
      (m := m) hm (t := m / 2 - 2) le_rfl
    have hsum : 2 + (m / 2 - 2) = m / 2 := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega
    simpa [hsum] using hmain
  have hmid :
      F ((1 : ZMod m), (((m / 2 : ℕ) : ZMod m))) =
        ((3 : ZMod m), (((m / 2 + 2 : ℕ) : ZMod m))) := by
    exact returnMap0CaseIIXY_one_column_mid_step (m := m) hm
  have hzero :
      ((F^[m / 2 - 2]) ((3 : ZMod m), (((m / 2 + 2 : ℕ) : ZMod m)))) =
        ((3 : ZMod m), (0 : ZMod m)) := by
    have hy0l : (m + 3 + 1) / 2 ≤ m / 2 + 2 := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega
    have hy0u : m / 2 + 2 ≤ m - 2 := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega
    simpa [show m - (m / 2 + 2) = m / 2 - 2 by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega] using
      iterate_returnMap0CaseIIXY_wrapped_upper_column_to_zero (m := m) hm
        (c := 3) (y0 := m / 2 + 2) (by omega) (by omega) (by exact ⟨1, by omega⟩)
        hy0l hy0u
  calc
    ((F^[2 * m - 4]) start)
        = ((F^[m]) ((F^[m - 4]) start)) := by
            simpa [show m + (m - 4) = 2 * m - 4 by omega] using
              (Function.iterate_add_apply F m (m - 4) start)
    _ = ((F^[m]) ((((m - 2 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m)))) := by rw [hafterA]
    _ = ((F^[m - 1]) (F ((((m - 2 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))))) := by
          simpa [show (m - 1) + 1 = m by omega] using
            (Function.iterate_add_apply F (m - 1) 1
              ((((m - 2 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))))
    _ = ((F^[m - 1]) ((1 : ZMod m), (1 : ZMod m))) := by rw [htail1]
    _ = ((F^[m - 2]) (F ((1 : ZMod m), (1 : ZMod m)))) := by
          simpa [show (m - 2) + 1 = m - 1 by omega] using
            (Function.iterate_add_apply F (m - 2) 1 ((1 : ZMod m), (1 : ZMod m)))
    _ = ((F^[m - 2]) ((0 : ZMod m), (1 : ZMod m))) := by rw [htail2]
    _ = ((F^[m - 3]) (F ((0 : ZMod m), (1 : ZMod m)))) := by
          simpa [show (m - 3) + 1 = m - 2 by omega] using
            (Function.iterate_add_apply F (m - 3) 1 ((0 : ZMod m), (1 : ZMod m)))
    _ = ((F^[m - 3]) ((1 : ZMod m), (2 : ZMod m))) := by rw [htail3]
    _ = ((F^[m / 2 - 1]) ((F^[m / 2 - 2]) ((1 : ZMod m), (2 : ZMod m)))) := by
          simpa [show (m / 2 - 1) + (m / 2 - 2) = m - 3 by
            rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
            rw [hq]
            omega] using
            (Function.iterate_add_apply F (m / 2 - 1) (m / 2 - 2) ((1 : ZMod m), (2 : ZMod m)))
    _ = ((F^[m / 2 - 1]) ((1 : ZMod m), (((m / 2 : ℕ) : ZMod m)))) := by rw [hcol1]
    _ = ((F^[m / 2 - 2]) (F ((1 : ZMod m), (((m / 2 : ℕ) : ZMod m))))) := by
          simpa [show (m / 2 - 2) + 1 = m / 2 - 1 by
            rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
            rw [hq]
            omega] using
            (Function.iterate_add_apply F (m / 2 - 2) 1 ((1 : ZMod m), (((m / 2 : ℕ) : ZMod m))))
    _ = ((F^[m / 2 - 2]) ((3 : ZMod m), (((m / 2 + 2 : ℕ) : ZMod m)))) := by rw [hmid]
    _ = ((3 : ZMod m), (0 : ZMod m)) := hzero
    _ = linePoint0 (m := m) (3 : Fin m) := by
          simp [linePoint0]

theorem returnMap0CaseIIXY_m_sub_two_zero [Fact (9 < m)] :
    returnMap0CaseIIXY (m := m) ((((m - 2 : ℕ) : ZMod m)), (0 : ZMod m)) =
      ((0 : ZMod m), (2 : ZMod m)) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let pre : QCoord m := ((-2 : ZMod m), (0 : ZMod m))
  have hxy :
      fromXY (m := m) ((((m - 2 : ℕ) : ZMod m)), (0 : ZMod m)) = pre := by
    ext <;> simp [pre, fromXY, cast_sub_two_eq_neg_two (m := m) (by omega)]
  have hdir :
      dir0CaseIILayerZero (m := m) pre = 2 := by
    simpa [pre] using dir0CaseIILayerZero_eq_two_neg_two_zero (m := m)
  have hi0 : pre.1 ≠ 0 := by
    simpa [pre] using neg_ne_zero.mpr (two_ne_zero (m := m))
  have hsum0 : pre.1 + pre.2 ≠ 0 := by
    simpa [pre] using neg_ne_zero.mpr (two_ne_zero (m := m))
  have hret := returnMap0CaseII_of_dir2_i_ne_zero_generic (m := m) (u := pre) hdir hi0 hsum0
  calc
    returnMap0CaseIIXY (m := m) ((((m - 2 : ℕ) : ZMod m)), (0 : ZMod m))
        = toXY (m := m)
            (returnMap0CaseII (m := m)
              (fromXY (m := m) ((((m - 2 : ℕ) : ZMod m)), (0 : ZMod m)))) := by
              simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) pre) := by rw [hxy]
    _ = toXY (m := m) (pre.1 - 2, pre.2 + 2) := by
          simpa using congrArg (toXY (m := m)) hret
    _ = ((0 : ZMod m), (2 : ZMod m)) := by
          ext <;> simp [toXY, pre]
          ring_nf

theorem fromXY_zero_column_lower [Fact (9 < m)] {y : ℕ}
    (_hy2 : 2 ≤ y) (hyle : y ≤ m / 2) :
    fromXY (m := m) ((0 : ZMod m), (((y : ℕ) : ZMod m))) =
      ((((m - 2 * y : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))) := by
  ext <;> simp [fromXY]
  · have hle : 2 * y ≤ m := by omega
    rw [Nat.cast_sub hle, Nat.cast_mul]
    simp

theorem fromXY_zero_column_mid [Fact (9 < m)] (hm : m % 12 = 10) :
    fromXY (m := m) ((0 : ZMod m), (((m / 2 : ℕ) : ZMod m))) =
      ((0 : ZMod m), (((m / 2 : ℕ) : ZMod m))) := by
  ext <;> simp [fromXY]
  · have hhalf : 2 * (m / 2) = m := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega
    have hcast : (2 : ZMod m) * (((m / 2 : ℕ) : ZMod m)) = 0 := by
      calc
        (2 : ZMod m) * (((m / 2 : ℕ) : ZMod m))
            = (((2 * (m / 2) : ℕ) : ZMod m)) := by
                simp [Nat.cast_mul]
        _ = (((m : ℕ) : ZMod m)) := by rw [hhalf]
        _ = 0 := by simp
    simpa using hcast

theorem fromXY_zero_column_upper [Fact (9 < m)] {y : ℕ}
    (hymid : m / 2 + 1 ≤ y) (hyle : y ≤ m - 1) :
    fromXY (m := m) ((0 : ZMod m), (((y : ℕ) : ZMod m))) =
      ((((2 * m - 2 * y : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))) := by
  ext <;> simp [fromXY]
  · have hle : 2 * y ≤ 2 * m := by omega
    rw [Nat.cast_sub hle, Nat.cast_mul]
    simp

theorem returnMap0CaseIIXY_zero_column_lower_step [Fact (9 < m)] {y : ℕ}
    (hy2 : 2 ≤ y) (hyle : y ≤ m / 2 - 1) :
    returnMap0CaseIIXY (m := m) ((0 : ZMod m), (((y : ℕ) : ZMod m))) =
      ((0 : ZMod m), (((y + 1 : ℕ) : ZMod m))) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let pre : QCoord m := ((((m - 2 * y : ℕ) : ZMod m)), (((y : ℕ) : ZMod m)))
  have hxy :
      fromXY (m := m) ((0 : ZMod m), (((y : ℕ) : ZMod m))) = pre := by
    simpa [pre] using fromXY_zero_column_lower (m := m) (y := y) hy2 (by omega)
  have hi0 : pre.1 ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := m - 2 * y) (by omega) (by omega)
  have hi1 : pre.1 ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := m - 2 * y) (by omega) (by omega)
  have hk0 : pre.2 ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := y) (by omega) (by omega)
  have hk1 : pre.2 ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := y) hy2 (by omega)
  have hkneg1 : pre.2 ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := y) (by omega)
  have hkneg2 : pre.2 ≠ (-2 : ZMod m) := by
    exact natCast_ne_neg_two_of_lt (m := m) (n := y) (by omega)
  have hdir :
      dir0CaseIILayerZero (m := m) pre = 1 :=
    dir0CaseIILayerZero_eq_one_of_generic (m := m) hi0 hi1 hk0 hk1 hkneg1 hkneg2
  have hi2k : pre.1 + 2 * pre.2 = 0 := by
    have h := congrArg (fun u : P0Coord m => u.1 + 2 * u.2) hxy
    simpa [fromXY] using h.symm
  have hsum1 : pre.1 + pre.2 ≠ 1 := by
    intro h
    have hkbad : pre.2 = (-1 : ZMod m) := by
      calc
        pre.2 = (pre.1 + 2 * pre.2) - (pre.1 + pre.2) := by ring
        _ = (0 : ZMod m) - 1 := by rw [hi2k, h]
        _ = (-1 : ZMod m) := by ring
    exact hkneg1 hkbad
  have hret := returnMap0CaseII_of_dir1_generic (m := m) (u := pre) hdir hi0 hsum1
  calc
    returnMap0CaseIIXY (m := m) ((0 : ZMod m), (((y : ℕ) : ZMod m)))
        = toXY (m := m)
            (returnMap0CaseII (m := m)
              (fromXY (m := m) ((0 : ZMod m), (((y : ℕ) : ZMod m))))) := by
              simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) pre) := by rw [hxy]
    _ = toXY (m := m) (pre.1 - 2, pre.2 + 1) := by
          simpa using congrArg (toXY (m := m)) hret
    _ = ((0 : ZMod m), (((y + 1 : ℕ) : ZMod m))) := by
          ext
          · calc
              (pre.1 - 2) + 2 * (pre.2 + 1) = pre.1 + 2 * pre.2 := by ring
              _ = 0 := hi2k
          · simp [toXY, pre, Nat.cast_add]

theorem iterate_returnMap0CaseIIXY_zero_column_lower_partial [Fact (9 < m)] {t : ℕ}
    (ht : t ≤ m / 2 - 2) :
    ((returnMap0CaseIIXY (m := m)^[t]) ((0 : ZMod m), (2 : ZMod m))) =
      ((0 : ZMod m), (((2 + t : ℕ) : ZMod m))) := by
  induction t with
  | zero =>
      simp
  | succ t iht =>
      have ht' : t ≤ m / 2 - 2 := Nat.le_of_succ_le ht
      have hstep :
          returnMap0CaseIIXY (m := m) ((0 : ZMod m), (((2 + t : ℕ) : ZMod m))) =
            ((0 : ZMod m), (((2 + t + 1 : ℕ) : ZMod m))) := by
        have hy2 : 2 ≤ 2 + t := by omega
        have hyle : 2 + t ≤ m / 2 - 1 := by omega
        simpa [Nat.add_assoc] using
          returnMap0CaseIIXY_zero_column_lower_step (m := m) (y := 2 + t) hy2 hyle
      calc
        ((returnMap0CaseIIXY (m := m)^[t.succ]) ((0 : ZMod m), (2 : ZMod m)))
            = returnMap0CaseIIXY (m := m)
                (((returnMap0CaseIIXY (m := m)^[t]) ((0 : ZMod m), (2 : ZMod m)))) := by
                    rw [Function.iterate_succ_apply']
        _ = returnMap0CaseIIXY (m := m) ((0 : ZMod m), (((2 + t : ℕ) : ZMod m))) := by
              rw [iht ht']
        _ = ((0 : ZMod m), (((2 + t + 1 : ℕ) : ZMod m))) := hstep
        _ = ((0 : ZMod m), (((2 + t.succ : ℕ) : ZMod m))) := by
              simp [Nat.succ_eq_add_one, Nat.add_assoc]

theorem returnMap0CaseIIXY_zero_column_mid_step [Fact (9 < m)] (hm : m % 12 = 10) :
    returnMap0CaseIIXY (m := m) ((0 : ZMod m), (((m / 2 : ℕ) : ZMod m))) =
      ((0 : ZMod m), (((m / 2 + 1 : ℕ) : ZMod m))) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let midK : ZMod m := (((m / 2 : ℕ) : ZMod m))
  have hxy :
      fromXY (m := m) ((0 : ZMod m), midK) = ((0 : ZMod m), midK) := by
    simpa [midK] using fromXY_zero_column_mid (m := m) hm
  have hmid_lt : m / 2 < m := by omega
  have hmid_ne_zero : midK ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := m / 2) (by omega) hmid_lt
  have hmid_ne_neg_one : midK ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := m / 2) (by omega)
  have hdir :
      dir0CaseIILayerZero (m := m) ((0 : ZMod m), midK) = 2 :=
    dir0CaseIILayerZero_eq_two_of_i_zero (m := m) hmid_ne_zero hmid_ne_neg_one
  have hmid_ne_one : midK ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := m / 2) (by omega) hmid_lt
  have hret := returnMap0CaseII_of_dir2_i_zero_generic (m := m) (k := midK) hdir hmid_ne_one
  have h2k : 2 * midK = 0 := by
    change (2 : ZMod m) * (((m / 2 : ℕ) : ZMod m)) = 0
    calc
      (2 : ZMod m) * (((m / 2 : ℕ) : ZMod m))
          = (((2 * (m / 2) : ℕ) : ZMod m)) := by simp [Nat.cast_mul]
      _ = (((m : ℕ) : ZMod m)) := by
            have hhalf : 2 * (m / 2) = m := by
              rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
              rw [hq]
              omega
            rw [hhalf]
      _ = 0 := by simp
  calc
    returnMap0CaseIIXY (m := m) ((0 : ZMod m), midK)
        = toXY (m := m) (returnMap0CaseII (m := m) ((0 : ZMod m), midK)) := by
            simp [returnMap0CaseIIXY, hxy]
    _ = toXY (m := m) ((-2 : ZMod m), midK + 1) := by rw [hret]
    _ = ((0 : ZMod m), midK + 1) := by
          ext
          · calc
              (-2 : ZMod m) + 2 * (midK + 1) = 2 * midK := by ring
              _ = 0 := h2k
          · rfl
    _ = ((0 : ZMod m), (((m / 2 + 1 : ℕ) : ZMod m))) := by
          ext
          · rfl
          · simp [midK, Nat.cast_add]

theorem returnMap0CaseIIXY_zero_column_upper_step [Fact (9 < m)] (hm : m % 12 = 10) {y : ℕ}
    (hymid : m / 2 + 1 ≤ y) (hyle : y ≤ m - 2) :
    returnMap0CaseIIXY (m := m) ((0 : ZMod m), (((y : ℕ) : ZMod m))) =
      ((0 : ZMod m), (((y + 1 : ℕ) : ZMod m))) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let pre : QCoord m := ((((2 * m - 2 * y : ℕ) : ZMod m)), (((y : ℕ) : ZMod m)))
  have hxy :
      fromXY (m := m) ((0 : ZMod m), (((y : ℕ) : ZMod m))) = pre := by
    simpa [pre] using fromXY_zero_column_upper (m := m) (y := y) hymid (by omega)
  have hilt : 2 * m - 2 * y < m := by omega
  have hi0 : pre.1 ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := 2 * m - 2 * y) (by omega) hilt
  have hi1 : pre.1 ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := 2 * m - 2 * y) (by omega) hilt
  have hi2 : pre.1 ≠ 2 := by
    exact natCast_ne_two_of_three_le_lt (m := m) (n := 2 * m - 2 * y) (by omega) hilt
  have hk0 : pre.2 ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := y) (by omega) (by omega)
  have hk1 : pre.2 ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := y) (by omega) (by omega)
  have hkneg1 : pre.2 ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := y) (by omega)
  have hdir :
      dir0CaseIILayerZero (m := m) pre = 1 := by
    simp [dir0CaseIILayerZero, pre, hi0, hi1, hi2, hk0, hk1, hkneg1]
  have hi2k : pre.1 + 2 * pre.2 = 0 := by
    have h := congrArg (fun u : P0Coord m => u.1 + 2 * u.2) hxy
    simpa [fromXY] using h.symm
  have hsum1 : pre.1 + pre.2 ≠ 1 := by
    intro h
    have hkbad : pre.2 = (-1 : ZMod m) := by
      calc
        pre.2 = (pre.1 + 2 * pre.2) - (pre.1 + pre.2) := by ring
        _ = (0 : ZMod m) - 1 := by rw [hi2k, h]
        _ = (-1 : ZMod m) := by ring
    exact hkneg1 hkbad
  have hret := returnMap0CaseII_of_dir1_generic (m := m) (u := pre) hdir hi0 hsum1
  calc
    returnMap0CaseIIXY (m := m) ((0 : ZMod m), (((y : ℕ) : ZMod m)))
        = toXY (m := m)
            (returnMap0CaseII (m := m)
              (fromXY (m := m) ((0 : ZMod m), (((y : ℕ) : ZMod m))))) := by
              simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) pre) := by rw [hxy]
    _ = toXY (m := m) (pre.1 - 2, pre.2 + 1) := by
          simpa using congrArg (toXY (m := m)) hret
    _ = ((0 : ZMod m), (((y + 1 : ℕ) : ZMod m))) := by
          ext
          · calc
              (pre.1 - 2) + 2 * (pre.2 + 1) = pre.1 + 2 * pre.2 := by ring
              _ = 0 := hi2k
          · simp [toXY, pre, Nat.cast_add]

theorem iterate_returnMap0CaseIIXY_zero_column_to_upper_start [Fact (9 < m)] (hm : m % 12 = 10) :
    ((returnMap0CaseIIXY (m := m)^[m / 2 - 1]) ((0 : ZMod m), (2 : ZMod m))) =
      ((0 : ZMod m), (((m / 2 + 1 : ℕ) : ZMod m))) := by
  calc
    ((returnMap0CaseIIXY (m := m)^[m / 2 - 1]) ((0 : ZMod m), (2 : ZMod m)))
        = returnMap0CaseIIXY (m := m)
            (((returnMap0CaseIIXY (m := m)^[m / 2 - 2]) ((0 : ZMod m), (2 : ZMod m)))) := by
                rw [show m / 2 - 1 = 1 + (m / 2 - 2) by omega, Function.iterate_add_apply]
                rfl
    _ = returnMap0CaseIIXY (m := m) ((0 : ZMod m), (((m / 2 : ℕ) : ZMod m))) := by
          rw [iterate_returnMap0CaseIIXY_zero_column_lower_partial (m := m)
            (t := m / 2 - 2) le_rfl]
          have hsum : 2 + (m / 2 - 2) = m / 2 := by omega
          simp [hsum]
    _ = ((0 : ZMod m), (((m / 2 + 1 : ℕ) : ZMod m))) := by
          exact returnMap0CaseIIXY_zero_column_mid_step (m := m) hm

theorem iterate_returnMap0CaseIIXY_zero_column_upper_partial [Fact (9 < m)] (hm : m % 12 = 10) {t : ℕ}
    (ht : t ≤ m / 2 - 2) :
    ((returnMap0CaseIIXY (m := m)^[t]) ((0 : ZMod m), (((m / 2 + 1 : ℕ) : ZMod m)))) =
      ((0 : ZMod m), (((m / 2 + 1 + t : ℕ) : ZMod m))) := by
  induction t with
  | zero =>
      simp
  | succ t iht =>
      have ht' : t ≤ m / 2 - 2 := Nat.le_of_succ_le ht
      have hstep :
          returnMap0CaseIIXY (m := m) ((0 : ZMod m), (((m / 2 + 1 + t : ℕ) : ZMod m))) =
            ((0 : ZMod m), (((m / 2 + 1 + t + 1 : ℕ) : ZMod m))) := by
        have hymid : m / 2 + 1 ≤ m / 2 + 1 + t := by omega
        have hyle : m / 2 + 1 + t ≤ m - 2 := by omega
        simpa [Nat.add_assoc] using
          returnMap0CaseIIXY_zero_column_upper_step (m := m) hm (y := m / 2 + 1 + t) hymid hyle
      calc
        ((returnMap0CaseIIXY (m := m)^[t.succ]) ((0 : ZMod m), (((m / 2 + 1 : ℕ) : ZMod m))))
            = returnMap0CaseIIXY (m := m)
                (((returnMap0CaseIIXY (m := m)^[t]) ((0 : ZMod m), (((m / 2 + 1 : ℕ) : ZMod m))))) := by
                    rw [Function.iterate_succ_apply']
        _ = returnMap0CaseIIXY (m := m) ((0 : ZMod m), (((m / 2 + 1 + t : ℕ) : ZMod m))) := by
              rw [iht ht']
        _ = ((0 : ZMod m), (((m / 2 + 1 + t + 1 : ℕ) : ZMod m))) := hstep
        _ = ((0 : ZMod m), (((m / 2 + 1 + t.succ : ℕ) : ZMod m))) := by
              simp [Nat.succ_eq_add_one, Nat.add_assoc]

theorem iterate_returnMap0CaseIIXY_zero_column_to_top [Fact (9 < m)] (hm : m % 12 = 10) :
    ((returnMap0CaseIIXY (m := m)^[m - 3]) ((0 : ZMod m), (2 : ZMod m))) =
      ((0 : ZMod m), (((m - 1 : ℕ) : ZMod m))) := by
  calc
    ((returnMap0CaseIIXY (m := m)^[m - 3]) ((0 : ZMod m), (2 : ZMod m)))
        = ((returnMap0CaseIIXY (m := m)^[m / 2 - 2])
            (((returnMap0CaseIIXY (m := m)^[m / 2 - 1]) ((0 : ZMod m), (2 : ZMod m))))) := by
              simpa [show (m / 2 - 2) + (m / 2 - 1) = m - 3 by
                rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
                rw [hq]
                omega] using
                (Function.iterate_add_apply (returnMap0CaseIIXY (m := m)) (m / 2 - 2) (m / 2 - 1)
                  ((0 : ZMod m), (2 : ZMod m)))
    _ = ((returnMap0CaseIIXY (m := m)^[m / 2 - 2])
          ((0 : ZMod m), (((m / 2 + 1 : ℕ) : ZMod m)))) := by
            rw [iterate_returnMap0CaseIIXY_zero_column_to_upper_start (m := m) hm]
    _ = ((0 : ZMod m), (((m - 1 : ℕ) : ZMod m))) := by
          rw [iterate_returnMap0CaseIIXY_zero_column_upper_partial (m := m) hm
            (t := m / 2 - 2) le_rfl]
          have hsum : m / 2 + 1 + (m / 2 - 2) = m - 1 := by
            rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
            rw [hq]
            omega
          simp [hsum]

theorem returnMap0CaseIIXY_zero_m_sub_one [Fact (9 < m)] :
    returnMap0CaseIIXY (m := m) ((0 : ZMod m), (((m - 1 : ℕ) : ZMod m))) =
      ((2 : ZMod m), (1 : ZMod m)) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let pre : QCoord m := ((2 : ZMod m), (-1 : ZMod m))
  have hxy :
      fromXY (m := m) ((0 : ZMod m), (((m - 1 : ℕ) : ZMod m))) = pre := by
    ext <;> simp [pre, fromXY, cast_sub_one_eq_neg_one (m := m) (by omega)]
  have hdir :
      dir0CaseIILayerZero (m := m) pre = 2 := by
    simpa [pre] using dir0CaseIILayerZero_eq_two_two_neg_one (m := m)
  have hi0 : pre.1 ≠ 0 := by
    simpa [pre] using two_ne_zero (m := m)
  have hsum0 : pre.1 + pre.2 ≠ 0 := by
    change (2 : ZMod m) + (-1 : ZMod m) ≠ 0
    intro h
    have : (1 : ZMod m) = 0 := by
      calc
        (1 : ZMod m) = (2 : ZMod m) + (-1 : ZMod m) := by ring
        _ = 0 := h
    exact one_ne_zero (m := m) this
  have hret := returnMap0CaseII_of_dir2_i_ne_zero_generic (m := m) (u := pre) hdir hi0 hsum0
  calc
    returnMap0CaseIIXY (m := m) ((0 : ZMod m), (((m - 1 : ℕ) : ZMod m)))
        = toXY (m := m)
            (returnMap0CaseII (m := m)
              (fromXY (m := m) ((0 : ZMod m), (((m - 1 : ℕ) : ZMod m))))) := by
              simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) pre) := by rw [hxy]
    _ = toXY (m := m) (pre.1 - 2, pre.2 + 2) := by
          simpa using congrArg (toXY (m := m)) hret
    _ = ((2 : ZMod m), (1 : ZMod m)) := by
          ext
          · change (2 : ZMod m) - 2 + 2 * ((-1 : ZMod m) + 2) = 2
            ring
          · change (-1 : ZMod m) + 2 = 1
            ring

theorem fromXY_three_column_lower [Fact (9 < m)] {y : ℕ}
    (_hy3 : 3 ≤ y) (hyle : y ≤ m / 2 + 1) :
    fromXY (m := m) ((3 : ZMod m), (((y : ℕ) : ZMod m))) =
      ((((m + 3 - 2 * y : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))) := by
  ext <;> simp [fromXY]
  · have hle : 2 * y ≤ m + 3 := by omega
    rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul]
    simp

theorem returnMap0CaseIIXY_three_column_lower_step [Fact (9 < m)] {y : ℕ}
    (hy3 : 3 ≤ y) (hyle : y ≤ m / 2) :
    returnMap0CaseIIXY (m := m) ((3 : ZMod m), (((y : ℕ) : ZMod m))) =
      ((3 : ZMod m), (((y + 1 : ℕ) : ZMod m))) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let pre : QCoord m := ((((m + 3 - 2 * y : ℕ) : ZMod m)), (((y : ℕ) : ZMod m)))
  have hxy :
      fromXY (m := m) ((3 : ZMod m), (((y : ℕ) : ZMod m))) = pre := by
    simpa [pre] using fromXY_three_column_lower (m := m) (y := y) hy3 (by omega)
  have hi0 : pre.1 ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := m + 3 - 2 * y) (by omega) (by omega)
  have hi1 : pre.1 ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := m + 3 - 2 * y) (by omega) (by omega)
  have hk0 : pre.2 ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := y) (by omega) (by omega)
  have hk1 : pre.2 ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := y) (by omega) (by omega)
  have hk2 : pre.2 ≠ 2 := by
    exact natCast_ne_two_of_three_le_lt (m := m) (n := y) hy3 (by omega)
  have hkneg1 : pre.2 ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := y) (by omega)
  have hkneg2 : pre.2 ≠ (-2 : ZMod m) := by
    exact natCast_ne_neg_two_of_lt (m := m) (n := y) (by omega)
  have hdir :
      dir0CaseIILayerZero (m := m) pre = 1 :=
    dir0CaseIILayerZero_eq_one_of_generic (m := m) hi0 hi1 hk0 hk1 hkneg1 hkneg2
  have hi2k : pre.1 + 2 * pre.2 = (3 : ZMod m) := by
    have h := congrArg (fun u : P0Coord m => u.1 + 2 * u.2) hxy
    simpa [fromXY] using h.symm
  have hsum1 : pre.1 + pre.2 ≠ 1 := by
    intro h
    have hkbad : pre.2 = (2 : ZMod m) := by
      calc
        pre.2 = (pre.1 + 2 * pre.2) - (pre.1 + pre.2) := by ring
        _ = (3 : ZMod m) - 1 := by rw [hi2k, h]
        _ = (2 : ZMod m) := by ring
    exact hk2 hkbad
  have hret := returnMap0CaseII_of_dir1_generic (m := m) (u := pre) hdir hi0 hsum1
  calc
    returnMap0CaseIIXY (m := m) ((3 : ZMod m), (((y : ℕ) : ZMod m)))
        = toXY (m := m)
            (returnMap0CaseII (m := m)
              (fromXY (m := m) ((3 : ZMod m), (((y : ℕ) : ZMod m))))) := by
              simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) pre) := by rw [hxy]
    _ = toXY (m := m) (pre.1 - 2, pre.2 + 1) := by
          simpa using congrArg (toXY (m := m)) hret
    _ = ((3 : ZMod m), (((y + 1 : ℕ) : ZMod m))) := by
          ext
          · calc
              (pre.1 - 2) + 2 * (pre.2 + 1) = pre.1 + 2 * pre.2 := by ring
              _ = (3 : ZMod m) := hi2k
          · simp [toXY, pre, Nat.cast_add]

theorem iterate_returnMap0CaseIIXY_three_column_lower_partial [Fact (9 < m)] {t : ℕ}
    (ht : t ≤ m / 2 - 2) :
    ((returnMap0CaseIIXY (m := m)^[t]) ((3 : ZMod m), (3 : ZMod m))) =
      ((3 : ZMod m), (((3 + t : ℕ) : ZMod m))) := by
  induction t with
  | zero =>
      simp
  | succ t iht =>
      have ht' : t ≤ m / 2 - 2 := Nat.le_of_succ_le ht
      have hstep :
          returnMap0CaseIIXY (m := m) ((3 : ZMod m), (((3 + t : ℕ) : ZMod m))) =
            ((3 : ZMod m), (((3 + t + 1 : ℕ) : ZMod m))) := by
        have hy3 : 3 ≤ 3 + t := by omega
        have hyle : 3 + t ≤ m / 2 := by omega
        simpa [Nat.add_assoc] using
          returnMap0CaseIIXY_three_column_lower_step (m := m) (y := 3 + t) hy3 hyle
      calc
        ((returnMap0CaseIIXY (m := m)^[t.succ]) ((3 : ZMod m), (3 : ZMod m)))
            = returnMap0CaseIIXY (m := m)
                (((returnMap0CaseIIXY (m := m)^[t]) ((3 : ZMod m), (3 : ZMod m)))) := by
                    rw [Function.iterate_succ_apply']
        _ = returnMap0CaseIIXY (m := m) ((3 : ZMod m), (((3 + t : ℕ) : ZMod m))) := by
              rw [iht ht']
        _ = ((3 : ZMod m), (((3 + t + 1 : ℕ) : ZMod m))) := hstep
        _ = ((3 : ZMod m), (((3 + t.succ : ℕ) : ZMod m))) := by
              simp [Nat.succ_eq_add_one, Nat.add_assoc]

theorem iterate_returnMap0CaseIIXY_five_column_to_zero_from_mid [Fact (9 < m)] (hm : m % 12 = 10) :
    ((returnMap0CaseIIXY (m := m)^[m - (m / 2 + 3)])
      ((5 : ZMod m), (((m / 2 + 3 : ℕ) : ZMod m)))) =
      ((5 : ZMod m), (0 : ZMod m)) := by
  let F := returnMap0CaseIIXY (m := m)
  by_cases hm10 : m = 10
  · subst hm10
    calc
      ((F^[10 - (10 / 2 + 3)]) ((5 : ZMod 10), (((10 / 2 + 3 : ℕ) : ZMod 10))))
          = ((F^[2]) ((5 : ZMod 10), (((10 - 2 : ℕ) : ZMod 10)))) := by decide
      _ = F (F ((5 : ZMod 10), (((10 - 2 : ℕ) : ZMod 10)))) := by
            simp [Function.iterate_succ_apply']
      _ = F ((5 : ZMod 10), (((10 - 1 : ℕ) : ZMod 10))) := by
            simpa [F] using congrArg F
              (returnMap0CaseIIXY_wrapped_upper_column_m_sub_two (m := 10) (c := 5) (by omega) (by omega))
      _ = ((5 : ZMod 10), (0 : ZMod 10)) := by
            simpa [F] using
              returnMap0CaseIIXY_wrapped_upper_column_m_sub_one (m := 10) (c := 5) (by omega) (by omega)
  · have hmain := iterate_returnMap0CaseIIXY_wrapped_upper_column_to_zero (m := m)
      hm (c := 5) (y0 := m / 2 + 3) (by omega) (by omega) (by exact ⟨2, by omega⟩)
      (by
        rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
        rw [hq]
        omega)
      (by
        rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
        rw [hq]
        omega)
    simpa using hmain

theorem firstReturn_line_m_sub_two_caseII_mod_ten [Fact (9 < m)] (hm : m % 12 = 10) :
    ((returnMap0CaseIIXY (m := m)^[2 * m - 4])
        (linePoint0 (m := m) (⟨m - 2, by omega⟩ : Fin m))) =
      linePoint0 (m := m) (5 : Fin m) := by
  let F := returnMap0CaseIIXY (m := m)
  let start : P0Coord m := linePoint0 (m := m) (⟨m - 2, by omega⟩ : Fin m)
  have h1 :
      ((F^[1]) start) = ((0 : ZMod m), (2 : ZMod m)) := by
    simpa [Function.iterate_one, F, start, linePoint0] using returnMap0CaseIIXY_m_sub_two_zero (m := m)
  have hafterZero :
      ((F^[m - 2]) start) = ((0 : ZMod m), (((m - 1 : ℕ) : ZMod m))) := by
    calc
      ((F^[m - 2]) start) = ((F^[m - 3]) ((F^[1]) start)) := by
        simpa [show (m - 3) + 1 = m - 2 by omega] using
          (Function.iterate_add_apply F (m - 3) 1 start)
      _ = ((F^[m - 3]) ((0 : ZMod m), (2 : ZMod m))) := by rw [h1]
      _ = ((0 : ZMod m), (((m - 1 : ℕ) : ZMod m))) := by
            exact iterate_returnMap0CaseIIXY_zero_column_to_top (m := m) hm
  have hafterCorner :
      ((F^[m - 1]) start) = ((2 : ZMod m), (1 : ZMod m)) := by
    calc
      ((F^[m - 1]) start) = F (((F^[m - 2]) start)) := by
        simpa [show 1 + (m - 2) = m - 1 by omega] using
          (Function.iterate_add_apply F 1 (m - 2) start)
      _ = F ((0 : ZMod m), (((m - 1 : ℕ) : ZMod m))) := by rw [hafterZero]
      _ = ((2 : ZMod m), (1 : ZMod m)) := by
            exact returnMap0CaseIIXY_zero_m_sub_one (m := m)
  have hafterThree :
      ((F^[m]) start) = ((3 : ZMod m), (3 : ZMod m)) := by
    calc
      ((F^[m]) start) = F (((F^[m - 1]) start)) := by
        simpa [show 1 + (m - 1) = m by omega] using
          (Function.iterate_add_apply F 1 (m - 1) start)
      _ = F ((2 : ZMod m), (1 : ZMod m)) := by rw [hafterCorner]
      _ = ((3 : ZMod m), (3 : ZMod m)) := by
            exact returnMap0CaseIIXY_two_one (m := m)
  have hafterCol3 :
      ((F^[m + (m / 2 - 2)]) start) =
        ((3 : ZMod m), (((m / 2 + 1 : ℕ) : ZMod m))) := by
    calc
      ((F^[m + (m / 2 - 2)]) start)
          = ((F^[m / 2 - 2]) ((F^[m]) start)) := by
              simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
                Function.iterate_add_apply F (m / 2 - 2) m start
      _ = ((F^[m / 2 - 2]) ((3 : ZMod m), (3 : ZMod m))) := by rw [hafterThree]
      _ = ((3 : ZMod m), (((3 + (m / 2 - 2) : ℕ) : ZMod m))) := by
            rw [iterate_returnMap0CaseIIXY_three_column_lower_partial (m := m)
              (t := m / 2 - 2) le_rfl]
      _ = ((3 : ZMod m), (((m / 2 + 1 : ℕ) : ZMod m))) := by
            have hsum : 3 + (m / 2 - 2) = m / 2 + 1 := by omega
            simp [hsum]
  have hafterR :
      ((F^[m + (m / 2 - 1)]) start) =
        ((5 : ZMod m), (((m / 2 + 3 : ℕ) : ZMod m))) := by
    calc
      ((F^[m + (m / 2 - 1)]) start) = F (((F^[m + (m / 2 - 2)]) start)) := by
        have hsum : 1 + (m + (m / 2 - 2)) = m + (m / 2 - 1) := by omega
        simpa [hsum] using
          (Function.iterate_add_apply F 1 (m + (m / 2 - 2)) start)
      _ = F ((3 : ZMod m), (((m / 2 + 1 : ℕ) : ZMod m))) := by rw [hafterCol3]
      _ = ((5 : ZMod m), (((m / 2 + 3 : ℕ) : ZMod m))) := by
            have hR := returnMap0CaseIIXY_R_line (m := m) (y := m / 2 + 1) (by omega)
            simpa [show 1 + 2 * (m / 2 + 1) = m + 3 by omega,
              show 3 + 2 * (m / 2 + 1) = m + 5 by omega,
              show (m / 2 + 1) + 2 = m / 2 + 3 by omega,
              Nat.cast_add] using hR
  calc
    ((F^[2 * m - 4]) start)
        = ((F^[m - (m / 2 + 3)]) ((F^[m + (m / 2 - 1)]) start)) := by
            simpa [show (m - (m / 2 + 3)) + (m + (m / 2 - 1)) = 2 * m - 4 by omega] using
              (Function.iterate_add_apply F (m - (m / 2 + 3)) (m + (m / 2 - 1)) start)
    _ = ((F^[m - (m / 2 + 3)]) ((5 : ZMod m), (((m / 2 + 3 : ℕ) : ZMod m)))) := by
          rw [hafterR]
    _ = ((5 : ZMod m), (0 : ZMod m)) := by
          exact iterate_returnMap0CaseIIXY_five_column_to_zero_from_mid (m := m) hm
    _ = linePoint0 (m := m) (5 : Fin m) := by
          simp [linePoint0]

theorem fromXY_even_generic_final_column_lower [Fact (9 < m)] (hm : m % 12 = 10) {x y : ℕ}
    (_hx4 : 4 ≤ x) (_hxle : x ≤ m - 8) (hxeven : Even x)
    (_hyl : x + 4 ≤ y) (hyu : y ≤ m / 2 + x / 2 + 1) :
    fromXY (m := m) ((((x + 4 : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))) =
      ((((m + x + 4 - 2 * y : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))) := by
  ext <;> simp [fromXY]
  · have hle : 2 * y ≤ m + x + 4 := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rcases hxeven with ⟨r, hr⟩
      rw [hq, hr] at hyu ⊢
      omega
    rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul]
    simp

theorem fromXY_even_generic_final_column_mid [Fact (9 < m)] (hm : m % 12 = 10) {x : ℕ}
    (_hx4 : 4 ≤ x) (_hxle : x ≤ m - 8) (hxeven : Even x) :
    fromXY (m := m)
      ((((x + 4 : ℕ) : ZMod m)), ((((m / 2 + x / 2 + 2 : ℕ) : ZMod m)))) =
        ((0 : ZMod m), (((m / 2 + x / 2 + 2 : ℕ) : ZMod m))) := by
  ext <;> simp [fromXY]
  · have h2k :
        (2 : ZMod m) * (((m / 2 + x / 2 + 2 : ℕ) : ZMod m)) =
          (((x + 4 : ℕ) : ZMod m)) := by
      calc
        (2 : ZMod m) * (((m / 2 + x / 2 + 2 : ℕ) : ZMod m))
            = (((2 * (m / 2 + x / 2 + 2) : ℕ) : ZMod m)) := by
                simp [Nat.cast_mul]
        _ = (((m + x + 4 : ℕ) : ZMod m)) := by
              have hmid_nat : 2 * (m / 2 + x / 2 + 2) = m + x + 4 := by
                rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
                rcases hxeven with ⟨r, hr⟩
                omega
              rw [hmid_nat]
        _ = (((x + 4 : ℕ) : ZMod m)) := by
              simp [Nat.cast_add]
    simpa [Nat.cast_add] using h2k.symm

theorem fromXY_even_generic_final_column_upper [Fact (9 < m)] (hm : m % 12 = 10) {x y : ℕ}
    (_hx4 : 4 ≤ x) (_hxle : x ≤ m - 12) (_hxeven : Even x)
    (_hyl : m / 2 + x / 2 + 3 ≤ y) (hyu : y ≤ m - 1) :
    fromXY (m := m) ((((x + 4 : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))) =
      ((((2 * m + x + 4 - 2 * y : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))) := by
  ext <;> simp [fromXY]
  · have hle : 2 * y ≤ 2 * m + x + 4 := by omega
    rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul]
    simp

theorem returnMap0CaseIIXY_even_generic_final_column_lower_step [Fact (9 < m)]
    (hm : m % 12 = 10) {x y : ℕ}
    (hx4 : 4 ≤ x) (hxle : x ≤ m - 8) (hxeven : Even x)
    (hyl : x + 4 ≤ y) (hyu : y ≤ m / 2 + x / 2 + 1) :
    returnMap0CaseIIXY (m := m) ((((x + 4 : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))) =
      ((((x + 4 : ℕ) : ZMod m)), (((y + 1 : ℕ) : ZMod m))) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let k : ZMod m := (((y : ℕ) : ZMod m))
  let i : ZMod m := (((m + x + 4 - 2 * y : ℕ) : ZMod m))
  have hylt : y < m := by omega
  have hilt : m + x + 4 - 2 * y < m := by
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rcases hxeven with ⟨r, hr⟩
    omega
  have hipos : 0 < m + x + 4 - 2 * y := by
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rcases hxeven with ⟨r, hr⟩
    omega
  have hitwo : 2 ≤ m + x + 4 - 2 * y := by
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rcases hxeven with ⟨r, hr⟩
    omega
  have hxy : fromXY (m := m) ((((x + 4 : ℕ) : ZMod m)), k) = (i, k) := by
    simpa [i, k] using
      fromXY_even_generic_final_column_lower (m := m) hm hx4 hxle hxeven hyl hyu
  have hi0 : i ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := m + x + 4 - 2 * y) hipos hilt
  have hi1 : i ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := m + x + 4 - 2 * y) hitwo hilt
  have hk0 : k ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := y) (by omega) hylt
  have hk1 : k ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := y) (by omega) hylt
  have hkneg1 : k ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := y) (by omega)
  have hkneg2 : k ≠ (-2 : ZMod m) := by
    exact natCast_ne_neg_two_of_lt (m := m) (n := y) (by omega)
  have hdir :
      dir0CaseIILayerZero (m := m) (i, k) = 1 :=
    dir0CaseIILayerZero_eq_one_of_generic (m := m) hi0 hi1 hk0 hk1 hkneg1 hkneg2
  have hi2k : i + 2 * k = (((x + 4 : ℕ) : ZMod m)) := by
    have h := congrArg (fun u : P0Coord m => u.1 + 2 * u.2) hxy
    simpa [fromXY] using h.symm
  have hsum1 : i + k ≠ 1 := by
    intro h
    have hkx3 : k = (((x + 3 : ℕ) : ZMod m)) := by
      have hx4sub : (((x + 4 : ℕ) : ZMod m)) + (-1 : ZMod m) = (((x + 3 : ℕ) : ZMod m)) := by
        calc
          (((x + 4 : ℕ) : ZMod m)) + (-1 : ZMod m)
              = (((x + 3 : ℕ) : ZMod m)) + (1 : ZMod m) + (-1 : ZMod m) := by
                  have hnat : x + 4 = (x + 3) + 1 := by omega
                  rw [hnat, Nat.cast_add]
                  norm_num
          _ = (((x + 3 : ℕ) : ZMod m)) := by ring
      calc
        k = (i + 2 * k) - (i + k) := by ring
        _ = (((x + 4 : ℕ) : ZMod m)) - 1 := by rw [hi2k, h]
        _ = (((x + 4 : ℕ) : ZMod m)) + (-1 : ZMod m) := by ring
        _ = (((x + 3 : ℕ) : ZMod m)) := hx4sub
    have hcast : (((y : ℕ) : ZMod m)) = (((x + 3 : ℕ) : ZMod m)) := by simpa [k] using hkx3
    have hmod := (ZMod.natCast_eq_natCast_iff' y (x + 3) m).1 hcast
    rw [Nat.mod_eq_of_lt hylt, Nat.mod_eq_of_lt (by omega)] at hmod
    omega
  have hret := returnMap0CaseII_of_dir1_generic (m := m) (u := (i, k)) hdir hi0 hsum1
  calc
    returnMap0CaseIIXY (m := m) ((((x + 4 : ℕ) : ZMod m)), k)
        = toXY (m := m)
            (returnMap0CaseII (m := m)
              (fromXY (m := m) ((((x + 4 : ℕ) : ZMod m)), k))) := by
              simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) (i, k)) := by rw [hxy]
    _ = toXY (m := m) (i - 2, k + 1) := by rw [hret]
    _ = ((((x + 4 : ℕ) : ZMod m)), k + 1) := by
          ext
          · calc
              (i - 2) + 2 * (k + 1) = i + 2 * k := by ring
              _ = (((x + 4 : ℕ) : ZMod m)) := hi2k
          · rfl
    _ = ((((x + 4 : ℕ) : ZMod m)), (((y + 1 : ℕ) : ZMod m))) := by
          simp [k, Nat.cast_add]

theorem returnMap0CaseIIXY_even_generic_final_column_mid_step [Fact (9 < m)]
    (hm : m % 12 = 10) {x : ℕ}
    (hx4 : 4 ≤ x) (hxle : x ≤ m - 8) (hxeven : Even x) :
    returnMap0CaseIIXY (m := m)
      ((((x + 4 : ℕ) : ZMod m)), ((((m / 2 + x / 2 + 2 : ℕ) : ZMod m)))) =
        ((((x + 4 : ℕ) : ZMod m)), ((((m / 2 + x / 2 + 3 : ℕ) : ZMod m)))) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let midK : ZMod m := (((m / 2 + x / 2 + 2 : ℕ) : ZMod m))
  have hxy : fromXY (m := m) ((((x + 4 : ℕ) : ZMod m)), midK) = ((0 : ZMod m), midK) := by
    simpa [midK] using fromXY_even_generic_final_column_mid (m := m) hm hx4 hxle hxeven
  have hmid_lt : m / 2 + x / 2 + 2 < m := by
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rcases hxeven with ⟨r, hr⟩
    rw [hq, hr] at hxle ⊢
    omega
  have hmid_ne_zero : midK ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := m / 2 + x / 2 + 2) (by omega) hmid_lt
  have hmid_ne_neg_one : midK ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := m / 2 + x / 2 + 2) (by omega)
  have hdir :
      dir0CaseIILayerZero (m := m) ((0 : ZMod m), midK) = 2 :=
    dir0CaseIILayerZero_eq_two_of_i_zero (m := m) hmid_ne_zero hmid_ne_neg_one
  have hmid_ne_one : midK ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := m / 2 + x / 2 + 2) (by omega) hmid_lt
  have hret := returnMap0CaseII_of_dir2_i_zero_generic (m := m) (k := midK) hdir hmid_ne_one
  have h2k : 2 * midK = (((x + 4 : ℕ) : ZMod m)) := by
    change (2 : ZMod m) * (((m / 2 + x / 2 + 2 : ℕ) : ZMod m)) = (((x + 4 : ℕ) : ZMod m))
    calc
      (2 : ZMod m) * (((m / 2 + x / 2 + 2 : ℕ) : ZMod m))
          = (((2 * (m / 2 + x / 2 + 2) : ℕ) : ZMod m)) := by
              simp [Nat.cast_mul]
      _ = (((m + x + 4 : ℕ) : ZMod m)) := by
            have hmid_nat : 2 * (m / 2 + x / 2 + 2) = m + x + 4 := by
              rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
              rcases hxeven with ⟨r, hr⟩
              omega
            rw [hmid_nat]
      _ = (((x + 4 : ℕ) : ZMod m)) := by
            simp [Nat.cast_add]
  calc
    returnMap0CaseIIXY (m := m) ((((x + 4 : ℕ) : ZMod m)), midK)
        = toXY (m := m)
            (returnMap0CaseII (m := m)
              (fromXY (m := m) ((((x + 4 : ℕ) : ZMod m)), midK))) := by
              simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) ((0 : ZMod m), midK)) := by rw [hxy]
    _ = toXY (m := m) ((-2 : ZMod m), midK + 1) := by rw [hret]
    _ = ((((x + 4 : ℕ) : ZMod m)), midK + 1) := by
          have h2k' : midK * 2 = (((x + 4 : ℕ) : ZMod m)) := by simpa [mul_comm] using h2k
          ext
          · calc
              (-2 : ZMod m) + 2 * (midK + 1) = midK * 2 := by ring
              _ = (((x + 4 : ℕ) : ZMod m)) := h2k'
          · rfl
    _ = ((((x + 4 : ℕ) : ZMod m)), ((((m / 2 + x / 2 + 3 : ℕ) : ZMod m)))) := by
          change
            ((((x + 4 : ℕ) : ZMod m)), ((((m / 2 + x / 2 + 2 : ℕ) : ZMod m)) + 1)) =
              ((((x + 4 : ℕ) : ZMod m)), ((((m / 2 + x / 2 + 3 : ℕ) : ZMod m))))
          ext
          · rfl
          · simp [Nat.cast_add]
            ring_nf

theorem returnMap0CaseIIXY_even_generic_final_column_upper_step [Fact (9 < m)]
    (hm : m % 12 = 10) {x y : ℕ}
    (hx4 : 4 ≤ x) (hxle : x ≤ m - 12) (hxeven : Even x)
    (hyl : m / 2 + x / 2 + 3 ≤ y) (hyu : y ≤ m - 3) :
    returnMap0CaseIIXY (m := m) ((((x + 4 : ℕ) : ZMod m)), (((y : ℕ) : ZMod m))) =
      ((((x + 4 : ℕ) : ZMod m)), (((y + 1 : ℕ) : ZMod m))) := by
  have hm4 : 4 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (4 < m) := ⟨hm4⟩
  let k : ZMod m := (((y : ℕ) : ZMod m))
  let i : ZMod m := (((2 * m + x + 4 - 2 * y : ℕ) : ZMod m))
  have hylt : y < m := by omega
  have hilt : 2 * m + x + 4 - 2 * y < m := by
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rcases hxeven with ⟨r, hr⟩
    omega
  have hipos : 0 < 2 * m + x + 4 - 2 * y := by
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rcases hxeven with ⟨r, hr⟩
    omega
  have hitwo : 2 ≤ 2 * m + x + 4 - 2 * y := by
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rcases hxeven with ⟨r, hr⟩
    omega
  have hxy : fromXY (m := m) ((((x + 4 : ℕ) : ZMod m)), k) = (i, k) := by
    simpa [i, k] using
      fromXY_even_generic_final_column_upper (m := m) hm hx4 hxle hxeven hyl (by omega)
  have hi0 : i ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := 2 * m + x + 4 - 2 * y) hipos hilt
  have hi1 : i ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := 2 * m + x + 4 - 2 * y) hitwo hilt
  have hk0 : k ≠ 0 := by
    exact natCast_ne_zero_of_pos_lt (m := m) (n := y) (by omega) hylt
  have hk1 : k ≠ 1 := by
    exact natCast_ne_one_of_two_le_lt (m := m) (n := y) (by omega) hylt
  have hkneg1 : k ≠ (-1 : ZMod m) := by
    exact natCast_ne_neg_one_of_lt (m := m) (n := y) (by omega)
  have hkneg2 : k ≠ (-2 : ZMod m) := by
    exact natCast_ne_neg_two_of_lt (m := m) (n := y) (by omega)
  have hdir :
      dir0CaseIILayerZero (m := m) (i, k) = 1 :=
    dir0CaseIILayerZero_eq_one_of_generic (m := m) hi0 hi1 hk0 hk1 hkneg1 hkneg2
  have hi2k : i + 2 * k = (((x + 4 : ℕ) : ZMod m)) := by
    have h := congrArg (fun u : P0Coord m => u.1 + 2 * u.2) hxy
    simpa [fromXY] using h.symm
  have hsum1 : i + k ≠ 1 := by
    intro h
    have hkx3 : k = (((x + 3 : ℕ) : ZMod m)) := by
      have hx4sub : (((x + 4 : ℕ) : ZMod m)) + (-1 : ZMod m) = (((x + 3 : ℕ) : ZMod m)) := by
        calc
          (((x + 4 : ℕ) : ZMod m)) + (-1 : ZMod m)
              = (((x + 3 : ℕ) : ZMod m)) + (1 : ZMod m) + (-1 : ZMod m) := by
                  have hnat : x + 4 = (x + 3) + 1 := by omega
                  rw [hnat, Nat.cast_add]
                  norm_num
          _ = (((x + 3 : ℕ) : ZMod m)) := by ring
      calc
        k = (i + 2 * k) - (i + k) := by ring
        _ = (((x + 4 : ℕ) : ZMod m)) - 1 := by rw [hi2k, h]
        _ = (((x + 4 : ℕ) : ZMod m)) + (-1 : ZMod m) := by ring
        _ = (((x + 3 : ℕ) : ZMod m)) := hx4sub
    have hcast : (((y : ℕ) : ZMod m)) = (((x + 3 : ℕ) : ZMod m)) := by simpa [k] using hkx3
    have hmod := (ZMod.natCast_eq_natCast_iff' y (x + 3) m).1 hcast
    rw [Nat.mod_eq_of_lt hylt, Nat.mod_eq_of_lt (by omega)] at hmod
    omega
  have hret := returnMap0CaseII_of_dir1_generic (m := m) (u := (i, k)) hdir hi0 hsum1
  calc
    returnMap0CaseIIXY (m := m) ((((x + 4 : ℕ) : ZMod m)), k)
        = toXY (m := m)
            (returnMap0CaseII (m := m)
              (fromXY (m := m) ((((x + 4 : ℕ) : ZMod m)), k))) := by
              simp [returnMap0CaseIIXY]
    _ = toXY (m := m) (returnMap0CaseII (m := m) (i, k)) := by rw [hxy]
    _ = toXY (m := m) (i - 2, k + 1) := by rw [hret]
    _ = ((((x + 4 : ℕ) : ZMod m)), k + 1) := by
          ext
          · calc
              (i - 2) + 2 * (k + 1) = i + 2 * k := by ring
              _ = (((x + 4 : ℕ) : ZMod m)) := hi2k
          · rfl
    _ = ((((x + 4 : ℕ) : ZMod m)), (((y + 1 : ℕ) : ZMod m))) := by
          simp [k, Nat.cast_add]

theorem iterate_returnMap0CaseIIXY_even_generic_final_column_lower_partial [Fact (9 < m)]
    (hm : m % 12 = 10) {x t : ℕ}
    (hx4 : 4 ≤ x) (hxle : x ≤ m - 8) (hxeven : Even x)
    (ht : t ≤ m / 2 - x / 2 - 2) :
    ((returnMap0CaseIIXY (m := m)^[t])
      ((((x + 4 : ℕ) : ZMod m)), (((x + 4 : ℕ) : ZMod m)))) =
      ((((x + 4 : ℕ) : ZMod m)), (((x + 4 + t : ℕ) : ZMod m))) := by
  induction t with
  | zero =>
      simp
  | succ t iht =>
      have ht' : t ≤ m / 2 - x / 2 - 2 := Nat.le_of_succ_le ht
      have hstep :
          returnMap0CaseIIXY (m := m) ((((x + 4 : ℕ) : ZMod m)), (((x + 4 + t : ℕ) : ZMod m))) =
            ((((x + 4 : ℕ) : ZMod m)), (((x + 4 + t + 1 : ℕ) : ZMod m))) := by
        have hyl : x + 4 ≤ x + 4 + t := by omega
        have hyu : x + 4 + t ≤ m / 2 + x / 2 + 1 := by
          rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
          rcases hxeven with ⟨r, hr⟩
          omega
        simpa [Nat.add_assoc] using
          returnMap0CaseIIXY_even_generic_final_column_lower_step (m := m) hm
            hx4 hxle hxeven (y := x + 4 + t) hyl hyu
      calc
        ((returnMap0CaseIIXY (m := m)^[t.succ])
            ((((x + 4 : ℕ) : ZMod m)), (((x + 4 : ℕ) : ZMod m))))
            = returnMap0CaseIIXY (m := m)
                (((returnMap0CaseIIXY (m := m)^[t])
                  ((((x + 4 : ℕ) : ZMod m)), (((x + 4 : ℕ) : ZMod m))))) := by
                    rw [Function.iterate_succ_apply']
        _ = returnMap0CaseIIXY (m := m)
              ((((x + 4 : ℕ) : ZMod m)), (((x + 4 + t : ℕ) : ZMod m))) := by
                rw [iht ht']
        _ = ((((x + 4 : ℕ) : ZMod m)), (((x + 4 + t + 1 : ℕ) : ZMod m))) := hstep
        _ = ((((x + 4 : ℕ) : ZMod m)), (((x + 4 + t.succ : ℕ) : ZMod m))) := by
              simp [Nat.succ_eq_add_one, Nat.add_assoc]

theorem iterate_returnMap0CaseIIXY_even_generic_final_column_to_upper_start [Fact (9 < m)]
    (hm : m % 12 = 10) {x : ℕ}
    (hx4 : 4 ≤ x) (hxle : x ≤ m - 8) (hxeven : Even x) :
    ((returnMap0CaseIIXY (m := m)^[m / 2 - x / 2 - 1])
      ((((x + 4 : ℕ) : ZMod m)), (((x + 4 : ℕ) : ZMod m)))) =
      ((((x + 4 : ℕ) : ZMod m)), ((((m / 2 + x / 2 + 3 : ℕ) : ZMod m)))) := by
  have hmain :
      ((returnMap0CaseIIXY (m := m)^[m / 2 - x / 2 - 2])
        ((((x + 4 : ℕ) : ZMod m)), (((x + 4 : ℕ) : ZMod m)))) =
        ((((x + 4 : ℕ) : ZMod m)), ((((m / 2 + x / 2 + 2 : ℕ) : ZMod m)))) := by
    rw [iterate_returnMap0CaseIIXY_even_generic_final_column_lower_partial
      (m := m) hm hx4 hxle hxeven (t := m / 2 - x / 2 - 2)]
    · have hsum : x + 4 + (m / 2 - x / 2 - 2) = m / 2 + x / 2 + 2 := by
        rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
        rcases hxeven with ⟨r, hr⟩
        rw [hq, hr]
        omega
      simp [hsum]
    · rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rcases hxeven with ⟨r, hr⟩
      omega
  calc
    ((returnMap0CaseIIXY (m := m)^[m / 2 - x / 2 - 1])
      ((((x + 4 : ℕ) : ZMod m)), (((x + 4 : ℕ) : ZMod m))))
        = returnMap0CaseIIXY (m := m)
            (((returnMap0CaseIIXY (m := m)^[m / 2 - x / 2 - 2])
              ((((x + 4 : ℕ) : ZMod m)), (((x + 4 : ℕ) : ZMod m))))) := by
                rw [show m / 2 - x / 2 - 1 = (m / 2 - x / 2 - 2) + 1 by
                      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
                      rcases hxeven with ⟨r, hr⟩
                      omega,
                    Function.iterate_succ_apply']
    _ = returnMap0CaseIIXY (m := m)
          ((((x + 4 : ℕ) : ZMod m)), ((((m / 2 + x / 2 + 2 : ℕ) : ZMod m)))) := by
            rw [hmain]
    _ = ((((x + 4 : ℕ) : ZMod m)), ((((m / 2 + x / 2 + 3 : ℕ) : ZMod m)))) := by
          exact returnMap0CaseIIXY_even_generic_final_column_mid_step (m := m) hm hx4 hxle hxeven

theorem iterate_returnMap0CaseIIXY_even_generic_final_column_upper_partial [Fact (9 < m)]
    (hm : m % 12 = 10) {x t : ℕ}
    (hx4 : 4 ≤ x) (hxle : x ≤ m - 12) (hxeven : Even x)
    (ht : t ≤ m / 2 - x / 2 - 5) :
    ((returnMap0CaseIIXY (m := m)^[t])
      ((((x + 4 : ℕ) : ZMod m)), ((((m / 2 + x / 2 + 3 : ℕ) : ZMod m))))) =
      ((((x + 4 : ℕ) : ZMod m)), ((((m / 2 + x / 2 + 3 + t : ℕ) : ZMod m)))) := by
  induction t with
  | zero =>
      simp
  | succ t iht =>
      have ht' : t ≤ m / 2 - x / 2 - 5 := Nat.le_of_succ_le ht
      have hstep :
          returnMap0CaseIIXY (m := m)
            ((((x + 4 : ℕ) : ZMod m)), ((((m / 2 + x / 2 + 3 + t : ℕ) : ZMod m)))) =
              ((((x + 4 : ℕ) : ZMod m)), ((((m / 2 + x / 2 + 3 + t + 1 : ℕ) : ZMod m)))) := by
        have hyl : m / 2 + x / 2 + 3 ≤ m / 2 + x / 2 + 3 + t := by omega
        have hyu : m / 2 + x / 2 + 3 + t ≤ m - 3 := by omega
        simpa [Nat.add_assoc] using
          returnMap0CaseIIXY_even_generic_final_column_upper_step (m := m) hm
            hx4 hxle hxeven (y := m / 2 + x / 2 + 3 + t) hyl hyu
      calc
        ((returnMap0CaseIIXY (m := m)^[t.succ])
            ((((x + 4 : ℕ) : ZMod m)), ((((m / 2 + x / 2 + 3 : ℕ) : ZMod m)))))
            = returnMap0CaseIIXY (m := m)
                (((returnMap0CaseIIXY (m := m)^[t])
                  ((((x + 4 : ℕ) : ZMod m)), ((((m / 2 + x / 2 + 3 : ℕ) : ZMod m)))))) := by
                    rw [Function.iterate_succ_apply']
        _ = returnMap0CaseIIXY (m := m)
              ((((x + 4 : ℕ) : ZMod m)), ((((m / 2 + x / 2 + 3 + t : ℕ) : ZMod m)))) := by
                rw [iht ht']
        _ = ((((x + 4 : ℕ) : ZMod m)), ((((m / 2 + x / 2 + 3 + t + 1 : ℕ) : ZMod m)))) := hstep
        _ = ((((x + 4 : ℕ) : ZMod m)), ((((m / 2 + x / 2 + 3 + t.succ : ℕ) : ZMod m)))) := by
              simp [Nat.succ_eq_add_one, Nat.add_assoc]

theorem iterate_returnMap0CaseIIXY_even_generic_final_column_to_zero_safe [Fact (9 < m)]
    (hm : m % 12 = 10) {x : ℕ}
    (hx4 : 4 ≤ x) (hxle : x ≤ m - 12) (hxeven : Even x) :
    ((returnMap0CaseIIXY (m := m)^[m - x - 4])
      ((((x + 4 : ℕ) : ZMod m)), (((x + 4 : ℕ) : ZMod m)))) =
      ((((x + 4 : ℕ) : ZMod m)), (0 : ZMod m)) := by
  let F := returnMap0CaseIIXY (m := m)
  let start : P0Coord m := ((((x + 4 : ℕ) : ZMod m)), (((x + 4 : ℕ) : ZMod m)))
  let upperStart : P0Coord m := ((((x + 4 : ℕ) : ZMod m)), ((((m / 2 + x / 2 + 3 : ℕ) : ZMod m))))
  let top1 : P0Coord m := ((((x + 4 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m)))
  let top2 : P0Coord m := ((((x + 4 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m)))
  have hupper :
      ((F^[m / 2 - x / 2 - 5]) upperStart) = top1 := by
    rw [iterate_returnMap0CaseIIXY_even_generic_final_column_upper_partial
      (m := m) hm hx4 hxle hxeven (t := m / 2 - x / 2 - 5) le_rfl]
    have hsum : m / 2 + x / 2 + 3 + (m / 2 - x / 2 - 5) = m - 2 := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rcases hxeven with ⟨r, hr⟩
      rw [hq, hr]
      omega
    simp [hsum, top1]
  have hsplit :
      ((F^[m - x - 4]) start) =
        ((F^[2]) ((F^[m / 2 - x / 2 - 5]) ((F^[m / 2 - x / 2 - 1]) start))) := by
    rw [show m - x - 4 = 2 + ((m / 2 - x / 2 - 5) + (m / 2 - x / 2 - 1)) by
          rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
          rcases hxeven with ⟨r, hr⟩
          omega]
    rw [Function.iterate_add_apply, Function.iterate_add_apply]
  have hcorner1 :
      F top1 = top2 := by
    dsimp [F]
    simpa [top1, top2] using
      returnMap0CaseIIXY_wrapped_upper_column_m_sub_two (m := m) (c := x + 4)
        (by omega) (by omega)
  have hcorner2 :
      F top2 = ((((x + 4 : ℕ) : ZMod m)), (0 : ZMod m)) := by
    dsimp [F]
    simpa [top2] using
      returnMap0CaseIIXY_wrapped_upper_column_m_sub_one (m := m) (c := x + 4)
        (by omega) (by omega)
  have hxle' : x ≤ m - 8 := by
    omega
  calc
    ((F^[m - x - 4]) start)
        = ((F^[2]) ((F^[m / 2 - x / 2 - 5]) ((F^[m / 2 - x / 2 - 1]) start))) := hsplit
    _ = ((F^[2])
          ((F^[m / 2 - x / 2 - 5]) upperStart)) := by
              rw [iterate_returnMap0CaseIIXY_even_generic_final_column_to_upper_start
                (m := m) hm hx4 hxle' hxeven]
    _ = ((F^[2]) top1) := by
          rw [hupper]
    _ = F (F top1) := by
          simp [Function.iterate_succ_apply']
    _ = F top2 := by
          rw [hcorner1]
    _ = ((((x + 4 : ℕ) : ZMod m)), (0 : ZMod m)) := by
          exact hcorner2

theorem firstReturn_line_even_generic_caseII_mod_ten_safe [Fact (9 < m)] (hm : m % 12 = 10)
    {x : ℕ} (hx4 : 4 ≤ x) (hxle : x ≤ m - 12) (hxeven : Even x) :
    ((returnMap0CaseIIXY (m := m)^[m - 2])
      (linePoint0 (m := m) (⟨x, by omega⟩ : Fin m))) =
      linePoint0 (m := m) (⟨x + 4, by omega⟩ : Fin m) := by
  let F := returnMap0CaseIIXY (m := m)
  let xFin : Fin m := ⟨x, by omega⟩
  calc
    ((F^[m - 2]) (linePoint0 (m := m) xFin))
        = ((F^[m - x - 4]) ((F^[x + 2]) (linePoint0 (m := m) xFin))) := by
            rw [show m - 2 = (m - x - 4) + (x + 2) by omega, Function.iterate_add_apply]
    _ = ((F^[m - x - 4]) ((((x + 4 : ℕ) : ZMod m)), (((x + 4 : ℕ) : ZMod m)))) := by
          rw [iterate_returnMap0CaseIIXY_even_generic_to_A (m := m)
            (x := x) (hx4 := hx4) (hxle := by omega) (hxeven := hxeven)]
    _ = ((((x + 4 : ℕ) : ZMod m)), (0 : ZMod m)) := by
          exact iterate_returnMap0CaseIIXY_even_generic_final_column_to_zero_safe
            (m := m) hm hx4 hxle hxeven
    _ = linePoint0 (m := m) (⟨x + 4, by omega⟩ : Fin m) := by
          simp [linePoint0]

theorem firstReturn_line_m_sub_ten_caseII_mod_ten [Fact (9 < m)] (hm : m % 12 = 10)
    (hm10 : 10 < m) :
    ((returnMap0CaseIIXY (m := m)^[m - 2])
        (linePoint0 (m := m) (⟨m - 10, by omega⟩ : Fin m))) =
      linePoint0 (m := m) (⟨m - 6, by omega⟩ : Fin m) := by
  let F := returnMap0CaseIIXY (m := m)
  have hxeven : Even (m - 10) := by
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rw [hq]
    refine ⟨6 * q, ?_⟩
    omega
  have hA :
      ((F^[m - 8]) (linePoint0 (m := m) (⟨m - 10, by omega⟩ : Fin m))) =
        ((((m - 6 : ℕ) : ZMod m)), (((m - 6 : ℕ) : ZMod m))) := by
    have hmain := iterate_returnMap0CaseIIXY_even_generic_to_A
      (m := m) (x := m - 10) (by omega) (by omega) hxeven
    have hsteps : m - 10 + 2 = m - 8 := by omega
    have hdst : m - 10 + 4 = m - 6 := by omega
    simpa [linePoint0, hsteps, hdst] using hmain
  have hupper :
      ((F^[4]) ((((m - 6 : ℕ) : ZMod m)), (((m - 6 : ℕ) : ZMod m)))) =
        ((((m - 6 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) := by
    have hmain := iterate_returnMap0CaseIIXY_even_generic_final_column_to_upper_start
      (m := m) hm (x := m - 10) (by omega) (by omega) hxeven
    have hsteps : m / 2 - (m - 10) / 2 - 1 = 4 := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega
    have hfst : m - 10 + 4 = m - 6 := by omega
    have hsnd : m / 2 + (m - 10) / 2 + 3 = m - 2 := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega
    simpa [hsteps, hfst, hsnd] using hmain
  have hcorner1 :
      F ((((m - 6 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) =
        ((((m - 6 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) := by
    dsimp [F]
    simpa using returnMap0CaseIIXY_wrapped_upper_column_m_sub_two
      (m := m) (c := m - 6) (by omega) (by omega)
  have hcorner2 :
      F ((((m - 6 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) =
        ((((m - 6 : ℕ) : ZMod m)), (0 : ZMod m)) := by
    dsimp [F]
    simpa using returnMap0CaseIIXY_wrapped_upper_column_m_sub_one
      (m := m) (c := m - 6) (by omega) (by omega)
  calc
    ((F^[m - 2]) (linePoint0 (m := m) (⟨m - 10, by omega⟩ : Fin m)))
        = ((F^[6]) ((F^[m - 8]) (linePoint0 (m := m) (⟨m - 10, by omega⟩ : Fin m)))) := by
            rw [show m - 2 = 6 + (m - 8) by omega, Function.iterate_add_apply]
    _ = ((F^[6]) ((((m - 6 : ℕ) : ZMod m)), (((m - 6 : ℕ) : ZMod m)))) := by rw [hA]
    _ = ((F^[2]) ((F^[4]) ((((m - 6 : ℕ) : ZMod m)), (((m - 6 : ℕ) : ZMod m))))) := by
          rw [show 6 = 2 + 4 by omega, Function.iterate_add_apply]
    _ = ((F^[2]) ((((m - 6 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m)))) := by rw [hupper]
    _ = F (F ((((m - 6 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m)))) := by
          simp [Function.iterate_succ_apply']
    _ = F ((((m - 6 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) := by rw [hcorner1]
    _ = ((((m - 6 : ℕ) : ZMod m)), (0 : ZMod m)) := by rw [hcorner2]
    _ = linePoint0 (m := m) (⟨m - 6, by omega⟩ : Fin m) := by
          simp [linePoint0]

theorem firstReturn_line_m_sub_eight_caseII_mod_ten [Fact (9 < m)] (hm : m % 12 = 10)
    (hm10 : 10 < m) :
    ((returnMap0CaseIIXY (m := m)^[m - 2])
        (linePoint0 (m := m) (⟨m - 8, by omega⟩ : Fin m))) =
      linePoint0 (m := m) (⟨m - 4, by omega⟩ : Fin m) := by
  let F := returnMap0CaseIIXY (m := m)
  have hxeven : Even (m - 8) := by
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rw [hq]
    refine ⟨6 * q + 1, ?_⟩
    omega
  have hA :
      ((F^[m - 6]) (linePoint0 (m := m) (⟨m - 8, by omega⟩ : Fin m))) =
        ((((m - 4 : ℕ) : ZMod m)), (((m - 4 : ℕ) : ZMod m))) := by
    have hmain := iterate_returnMap0CaseIIXY_even_generic_to_A
      (m := m) (x := m - 8) (by omega) (by omega) hxeven
    have hsteps : m - 8 + 2 = m - 6 := by omega
    have hdst : m - 8 + 4 = m - 4 := by omega
    simpa [linePoint0, hsteps, hdst] using hmain
  have hupper :
      ((F^[3]) ((((m - 4 : ℕ) : ZMod m)), (((m - 4 : ℕ) : ZMod m)))) =
        ((((m - 4 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) := by
    have hmain := iterate_returnMap0CaseIIXY_even_generic_final_column_to_upper_start
      (m := m) hm (x := m - 8) (by omega) (by omega) hxeven
    have hsteps : m / 2 - (m - 8) / 2 - 1 = 3 := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega
    have hfst : m - 8 + 4 = m - 4 := by omega
    have hsnd : m / 2 + (m - 8) / 2 + 3 = m - 1 := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega
    simpa [hsteps, hfst, hsnd] using hmain
  have hcorner :
      F ((((m - 4 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) =
        ((((m - 4 : ℕ) : ZMod m)), (0 : ZMod m)) := by
    dsimp [F]
    simpa using returnMap0CaseIIXY_wrapped_upper_column_m_sub_one
      (m := m) (c := m - 4) (by omega) (by omega)
  calc
    ((F^[m - 2]) (linePoint0 (m := m) (⟨m - 8, by omega⟩ : Fin m)))
        = ((F^[4]) ((F^[m - 6]) (linePoint0 (m := m) (⟨m - 8, by omega⟩ : Fin m)))) := by
            rw [show m - 2 = 4 + (m - 6) by omega, Function.iterate_add_apply]
    _ = ((F^[4]) ((((m - 4 : ℕ) : ZMod m)), (((m - 4 : ℕ) : ZMod m)))) := by rw [hA]
    _ = F ((F^[3]) ((((m - 4 : ℕ) : ZMod m)), (((m - 4 : ℕ) : ZMod m)))) := by
          rw [show 4 = 1 + 3 by omega, Function.iterate_add_apply]
          simp
    _ = F ((((m - 4 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) := by rw [hupper]
    _ = ((((m - 4 : ℕ) : ZMod m)), (0 : ZMod m)) := by rw [hcorner]
    _ = linePoint0 (m := m) (⟨m - 4, by omega⟩ : Fin m) := by
          simp [linePoint0]

private theorem firstReturn_line_even_generic_caseII_mod_ten_boundary [Fact (9 < m)]
    (hm : m % 12 = 10) {x : ℕ}
    (hx4 : 4 ≤ x) (hxle : x ≤ m - 8) (hxeven : Even x) (hsafe : ¬ x ≤ m - 12) :
    ((returnMap0CaseIIXY (m := m)^[m - 2])
        (linePoint0 (m := m) (⟨x, by omega⟩ : Fin m))) =
      linePoint0 (m := m) (⟨x + 4, by omega⟩ : Fin m) := by
  have hm10 : 10 < m := by
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rw [hq]
    omega
  have hcases : x = m - 10 ∨ x = m - 8 := by
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rcases hxeven with ⟨r, hr⟩
    rw [hq] at hxle hsafe ⊢
    rw [hr] at hxle hsafe ⊢
    omega
  rcases hcases with hxm10 | hxm8
  · subst hxm10
    simpa [show m - 10 + 4 = m - 6 by omega] using
      firstReturn_line_m_sub_ten_caseII_mod_ten (m := m) hm hm10
  · subst hxm8
    simpa [show m - 8 + 4 = m - 4 by omega] using
      firstReturn_line_m_sub_eight_caseII_mod_ten (m := m) hm hm10

theorem firstReturn_line_even_generic_caseII_mod_ten [Fact (9 < m)] (hm : m % 12 = 10)
    {x : ℕ} (hx4 : 4 ≤ x) (hxle : x ≤ m - 8) (hxeven : Even x) :
    ((returnMap0CaseIIXY (m := m)^[m - 2])
        (linePoint0 (m := m) (⟨x, by omega⟩ : Fin m))) =
      linePoint0 (m := m) (⟨x + 4, by omega⟩ : Fin m) := by
  by_cases hsafe : x ≤ m - 12
  · simpa using firstReturn_line_even_generic_caseII_mod_ten_safe (m := m) hm hx4 hsafe hxeven
  · exact firstReturn_line_even_generic_caseII_mod_ten_boundary
      (m := m) hm hx4 hxle hxeven hsafe

theorem mod_six_eq_four_of_mod_twelve_eq_ten [Fact (9 < m)] (hm : m % 12 = 10) :
    m % 6 = 4 := by
  rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
  rw [hq]
  omega

theorem hreturn_line_case0_caseII_mod_ten_core [Fact (9 < m)]
    (hm : m % 12 = 10) (hm6 : m % 6 = 4) (x : Fin m) :
    ((returnMap0CaseIIXY (m := m)^[rho0CaseII (m := m) x]) (linePoint0 (m := m) x)) =
      linePoint0 (m := m) (TorusD3Even.T0CaseII (m := m) hm6 x) := by
  by_cases hx0 : x.1 = 0
  · let x0 : Fin m := 0
    have hx' : x = x0 := Fin.ext hx0
    subst hx'
    have hT : TorusD3Even.T0CaseII (m := m) hm6 (0 : Fin m) = (⟨m - 2, by omega⟩ : Fin m) := by
      apply Fin.ext
      simpa using TorusD3Even.T0CaseII_eq_m_sub_two_of_val_eq_zero (m := m) hm6 rfl
    simpa [rho0CaseII_zero, Function.iterate_one, hT]
      using firstReturn_line_zero_caseII_mod_ten (m := m)
  by_cases hx1 : x.1 = 1
  · let x0 : Fin m := ⟨1, by omega⟩
    let xT : Fin m := ⟨4, by omega⟩
    have hx' : x = x0 := by
      apply Fin.ext
      simpa [x0] using hx1
    have hT : TorusD3Even.T0CaseII (m := m) hm6 x = xT := by
      apply Fin.ext
      simpa [xT] using
        TorusD3Even.T0CaseII_eq_four_of_val_eq_one (m := m) hm6 hx1
    have hrho : rho0CaseII (m := m) x0 = m - 2 := by
      simpa [hx'] using rho0CaseII_other (m := m) (x := 1) (by
        have hm9 : 9 < m := Fact.out
        omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    calc
      ((returnMap0CaseIIXY (m := m)^[rho0CaseII (m := m) x]) (linePoint0 (m := m) x))
          = ((returnMap0CaseIIXY (m := m)^[rho0CaseII (m := m) x0]) (linePoint0 (m := m) x0)) := by
              rw [hx']
      _ = ((returnMap0CaseIIXY (m := m)^[m - 2]) (linePoint0 (m := m) x0)) := by rw [hrho]
      _ = linePoint0 (m := m) xT := by
            simpa [x0, xT] using firstReturn_line_one_caseII_mod_ten (m := m) hm
      _ = linePoint0 (m := m) (TorusD3Even.T0CaseII (m := m) hm6 x) := by rw [hT.symm]
  by_cases hx2 : x.1 = 2
  · let x0 : Fin m := ⟨2, by omega⟩
    let xT : Fin m := ⟨6, by omega⟩
    have hx' : x = x0 := by
      apply Fin.ext
      simpa [x0] using hx2
    have hT : TorusD3Even.T0CaseII (m := m) hm6 x = xT := by
      apply Fin.ext
      simpa [xT] using
        TorusD3Even.T0CaseII_eq_six_of_val_eq_two (m := m) hm6 hx2
    have hrho : rho0CaseII (m := m) x0 = m - 2 := by
      simpa [hx'] using rho0CaseII_other (m := m) (x := 2) (by
        have hm9 : 9 < m := Fact.out
        omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    calc
      ((returnMap0CaseIIXY (m := m)^[rho0CaseII (m := m) x]) (linePoint0 (m := m) x))
          = ((returnMap0CaseIIXY (m := m)^[rho0CaseII (m := m) x0]) (linePoint0 (m := m) x0)) := by
              rw [hx']
      _ = ((returnMap0CaseIIXY (m := m)^[m - 2]) (linePoint0 (m := m) x0)) := by rw [hrho]
      _ = linePoint0 (m := m) xT := by
            simpa [x0, xT] using firstReturn_line_two_caseII_mod_ten (m := m) hm
      _ = linePoint0 (m := m) (TorusD3Even.T0CaseII (m := m) hm6 x) := by rw [hT.symm]
  by_cases hxm6 : x.1 = m - 6
  · let x0 : Fin m := ⟨m - 6, by omega⟩
    let xT : Fin m := ⟨3, by omega⟩
    have hx' : x = x0 := Fin.ext hxm6
    have hT : TorusD3Even.T0CaseII (m := m) hm6 x = xT := by
      apply Fin.ext
      simpa [xT] using
        TorusD3Even.T0CaseII_eq_three_of_val_eq_m_sub_six (m := m) hm6 hxm6
    have hxT : xT = (3 : Fin m) := by
      apply Fin.ext
      show 3 = 3 % m
      symm
      exact Nat.mod_eq_of_lt (by
        have hm9 : 9 < m := Fact.out
        omega)
    have hrho : rho0CaseII (m := m) x0 = 2 * m - 4 := by
      simpa [hx'] using rho0CaseII_eq_two_mul_sub_four_of_val_eq_m_sub_six (m := m) hxm6
    calc
      ((returnMap0CaseIIXY (m := m)^[rho0CaseII (m := m) x]) (linePoint0 (m := m) x))
          = ((returnMap0CaseIIXY (m := m)^[rho0CaseII (m := m) x0]) (linePoint0 (m := m) x0)) := by rw [hx']
      _ = ((returnMap0CaseIIXY (m := m)^[2 * m - 4]) (linePoint0 (m := m) x0)) := by rw [hrho]
      _ = linePoint0 (m := m) (3 : Fin m) := by
            simpa [x0] using firstReturn_line_m_sub_six_caseII_mod_ten (m := m) hm
      _ = linePoint0 (m := m) xT := by rw [hxT]
      _ = linePoint0 (m := m) (TorusD3Even.T0CaseII (m := m) hm6 x) := by rw [hT.symm]
  by_cases hxm5 : x.1 = m - 5
  · let x0 : Fin m := ⟨m - 5, by omega⟩
    have hx' : x = x0 := Fin.ext hxm5
    have hT : TorusD3Even.T0CaseII (m := m) hm6 x = (⟨m - 1, by omega⟩ : Fin m) := by
      apply Fin.ext
      simpa using TorusD3Even.T0CaseII_eq_m_sub_one_of_val_eq_m_sub_five (m := m) hm6 hxm5
    have hrho : rho0CaseII (m := m) x0 = m - 1 := by
      simpa [hx'] using rho0CaseII_eq_sub_one_of_val_eq_m_sub_five (m := m) hxm5
    calc
      ((returnMap0CaseIIXY (m := m)^[rho0CaseII (m := m) x]) (linePoint0 (m := m) x))
          = ((returnMap0CaseIIXY (m := m)^[rho0CaseII (m := m) x0]) (linePoint0 (m := m) x0)) := by rw [hx']
      _ = ((returnMap0CaseIIXY (m := m)^[m - 1]) (linePoint0 (m := m) x0)) := by rw [hrho]
      _ = linePoint0 (m := m) (⟨m - 1, by omega⟩ : Fin m) := by
            simpa [x0] using firstReturn_line_m_sub_five_caseII_mod_ten (m := m) hm
      _ = linePoint0 (m := m) (TorusD3Even.T0CaseII (m := m) hm6 x) := by rw [hT.symm]
  by_cases hxm4 : x.1 = m - 4
  · let x0 : Fin m := ⟨m - 4, by omega⟩
    have hx' : x = x0 := Fin.ext hxm4
    have hT : TorusD3Even.T0CaseII (m := m) hm6 x = (0 : Fin m) := by
      apply Fin.ext
      simpa using TorusD3Even.T0CaseII_eq_zero_of_val_eq_m_sub_four (m := m) hm6 hxm4
    calc
      ((returnMap0CaseIIXY (m := m)^[rho0CaseII (m := m) x]) (linePoint0 (m := m) x))
          = ((returnMap0CaseIIXY (m := m)^[rho0CaseII (m := m) x0]) (linePoint0 (m := m) x0)) := by rw [hx']
      _ = ((returnMap0CaseIIXY (m := m)^[m - 2]) (linePoint0 (m := m) x0)) := by
            rw [rho0CaseII_other (m := m) (x := m - 4) (by omega) (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega)]
      _ = linePoint0 (m := m) (0 : Fin m) := by
            simpa [x0] using firstReturn_line_m_sub_four_caseII_mod_ten (m := m) hm
      _ = linePoint0 (m := m) (TorusD3Even.T0CaseII (m := m) hm6 x) := by rw [hT.symm]
  by_cases hxm3 : x.1 = m - 3
  · let x0 : Fin m := ⟨m - 3, by omega⟩
    let xT : Fin m := ⟨2, by omega⟩
    have hx' : x = x0 := Fin.ext hxm3
    have hT : TorusD3Even.T0CaseII (m := m) hm6 x = xT := by
      apply Fin.ext
      simpa [xT] using
        TorusD3Even.T0CaseII_eq_two_of_val_eq_m_sub_three (m := m) hm6 hxm3
    have hxT : xT = (2 : Fin m) := by
      apply Fin.ext
      show 2 = 2 % m
      symm
      exact Nat.mod_eq_of_lt (by
        have hm9 : 9 < m := Fact.out
        omega)
    have hrho : rho0CaseII (m := m) x0 = 2 * m - 3 := by
      simpa [hx'] using rho0CaseII_eq_two_mul_sub_three_of_val_eq_m_sub_three (m := m) hxm3
    calc
      ((returnMap0CaseIIXY (m := m)^[rho0CaseII (m := m) x]) (linePoint0 (m := m) x))
          = ((returnMap0CaseIIXY (m := m)^[rho0CaseII (m := m) x0]) (linePoint0 (m := m) x0)) := by rw [hx']
      _ = ((returnMap0CaseIIXY (m := m)^[2 * m - 3]) (linePoint0 (m := m) x0)) := by rw [hrho]
      _ = linePoint0 (m := m) (2 : Fin m) := by
            simpa [x0] using firstReturn_line_m_sub_three_caseII_mod_ten (m := m) hm
      _ = linePoint0 (m := m) xT := by rw [hxT]
      _ = linePoint0 (m := m) (TorusD3Even.T0CaseII (m := m) hm6 x) := by rw [hT.symm]
  by_cases hxm2 : x.1 = m - 2
  · let x0 : Fin m := ⟨m - 2, by omega⟩
    let xT : Fin m := ⟨5, by omega⟩
    have hx' : x = x0 := Fin.ext hxm2
    have hT : TorusD3Even.T0CaseII (m := m) hm6 x = xT := by
      apply Fin.ext
      simpa [xT] using
        TorusD3Even.T0CaseII_eq_five_of_val_eq_m_sub_two (m := m) hm6 hxm2
    have hxT : xT = (5 : Fin m) := by
      apply Fin.ext
      show 5 = 5 % m
      symm
      exact Nat.mod_eq_of_lt (by
        have hm9 : 9 < m := Fact.out
        omega)
    have hrho : rho0CaseII (m := m) x0 = 2 * m - 4 := by
      simpa [hx'] using rho0CaseII_eq_two_mul_sub_four_of_val_eq_m_sub_two (m := m) hxm2
    calc
      ((returnMap0CaseIIXY (m := m)^[rho0CaseII (m := m) x]) (linePoint0 (m := m) x))
          = ((returnMap0CaseIIXY (m := m)^[rho0CaseII (m := m) x0]) (linePoint0 (m := m) x0)) := by rw [hx']
      _ = ((returnMap0CaseIIXY (m := m)^[2 * m - 4]) (linePoint0 (m := m) x0)) := by rw [hrho]
      _ = linePoint0 (m := m) (5 : Fin m) := by
            simpa [x0] using firstReturn_line_m_sub_two_caseII_mod_ten (m := m) hm
      _ = linePoint0 (m := m) xT := by rw [hxT]
      _ = linePoint0 (m := m) (TorusD3Even.T0CaseII (m := m) hm6 x) := by rw [hT.symm]
  by_cases hxm1 : x.1 = m - 1
  · let x0 : Fin m := ⟨m - 1, by omega⟩
    let xT : Fin m := ⟨1, by omega⟩
    have hx' : x = x0 := Fin.ext hxm1
    have hT : TorusD3Even.T0CaseII (m := m) hm6 x = xT := by
      apply Fin.ext
      simpa [xT] using
        TorusD3Even.T0CaseII_eq_one_of_val_eq_m_sub_one (m := m) hm6 hxm1
    have hxT : xT = (1 : Fin m) := by
      apply Fin.ext
      show 1 = 1 % m
      symm
      exact Nat.mod_eq_of_lt (by
        have hm9 : 9 < m := Fact.out
        omega)
    have hrho : rho0CaseII (m := m) x0 = m - 1 := by
      simpa [hx'] using rho0CaseII_eq_sub_one_of_val_eq_m_sub_one (m := m) hxm1
    calc
      ((returnMap0CaseIIXY (m := m)^[rho0CaseII (m := m) x]) (linePoint0 (m := m) x))
          = ((returnMap0CaseIIXY (m := m)^[rho0CaseII (m := m) x0]) (linePoint0 (m := m) x0)) := by rw [hx']
      _ = ((returnMap0CaseIIXY (m := m)^[m - 1]) (linePoint0 (m := m) x0)) := by rw [hrho]
      _ = linePoint0 (m := m) (1 : Fin m) := by
            simpa [x0] using firstReturn_line_m_sub_one_caseII_mod_ten (m := m) hm
      _ = linePoint0 (m := m) xT := by rw [hxT]
      _ = linePoint0 (m := m) (TorusD3Even.T0CaseII (m := m) hm6 x) := by rw [hT.symm]
  have hmEven : Even m := by
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rw [hq]
    exact ⟨6 * q + 5, by omega⟩
  rcases Nat.even_or_odd x.1 with hxeven | hxodd
  · have hx4 : 4 ≤ x.1 := by
      rcases hxeven with ⟨k, hk⟩
      omega
    have hxle : x.1 ≤ m - 8 := by
      rcases hxeven with ⟨k, hk⟩
      rcases hmEven with ⟨r, hr⟩
      omega
    have hTval := TorusD3Even.T0CaseII_eq_add_four_of_ne_special (m := m) hm6
      hx0 hx1 hx2 hxm6 hxm5 hxm4 hxm3 hxm2 hxm1
    have hT : TorusD3Even.T0CaseII (m := m) hm6 x = ⟨x.1 + 4, by omega⟩ := by
      apply Fin.ext
      simpa using hTval
    calc
      ((returnMap0CaseIIXY (m := m)^[rho0CaseII (m := m) x]) (linePoint0 (m := m) x))
          = ((returnMap0CaseIIXY (m := m)^[m - 2]) (linePoint0 (m := m) x)) := by
              rw [rho0CaseII_other (m := m) (x := x.1) x.2 hx0 hxm6 hxm5 hxm3 hxm2 hxm1]
      _ = linePoint0 (m := m) (⟨x.1 + 4, by omega⟩ : Fin m) := by
            simpa using firstReturn_line_even_generic_caseII_mod_ten (m := m) hm
              (x := x.1) hx4 hxle hxeven
      _ = linePoint0 (m := m) (TorusD3Even.T0CaseII (m := m) hm6 x) := by rw [hT.symm]
  · have hx3 : 3 ≤ x.1 := by
      rcases hxodd with ⟨k, hk⟩
      omega
    have hxle : x.1 ≤ m - 7 := by
      rcases hxodd with ⟨k, hk⟩
      rcases hmEven with ⟨r, hr⟩
      omega
    have hTval := TorusD3Even.T0CaseII_eq_add_four_of_ne_special (m := m) hm6
      hx0 hx1 hx2 hxm6 hxm5 hxm4 hxm3 hxm2 hxm1
    have hT : TorusD3Even.T0CaseII (m := m) hm6 x = ⟨x.1 + 4, by omega⟩ := by
      apply Fin.ext
      simpa using hTval
    calc
      ((returnMap0CaseIIXY (m := m)^[rho0CaseII (m := m) x]) (linePoint0 (m := m) x))
          = ((returnMap0CaseIIXY (m := m)^[m - 2]) (linePoint0 (m := m) x)) := by
              rw [rho0CaseII_other (m := m) (x := x.1) x.2 hx0 hxm6 hxm5 hxm3 hxm2 hxm1]
      _ = linePoint0 (m := m) (⟨x.1 + 4, by omega⟩ : Fin m) := by
            simpa using firstReturn_line_odd_generic_caseII_mod_ten (m := m) hm
              (x := x.1) hx3 hxle hxodd
      _ = linePoint0 (m := m) (TorusD3Even.T0CaseII (m := m) hm6 x) := by rw [hT.symm]

theorem hreturn_line_case0_caseII_mod_ten [Fact (9 < m)] (hm : m % 12 = 10) (x : Fin m) :
    ((returnMap0CaseIIXY (m := m)^[rho0CaseII (m := m) x]) (linePoint0 (m := m) x)) =
      linePoint0 (m := m)
        (TorusD3Even.T0CaseII (m := m) (mod_six_eq_four_of_mod_twelve_eq_ten (m := m) hm) x) := by
  simpa using hreturn_line_case0_caseII_mod_ten_core (m := m) hm
    (mod_six_eq_four_of_mod_twelve_eq_ten (m := m) hm) x

theorem hsum_case0_caseII_mod_ten [Fact (9 < m)] (hm : m % 12 = 10) :
    TorusD3Even.blockTime
        (TorusD3Even.T0CaseII (m := m) (mod_six_eq_four_of_mod_twelve_eq_ten (m := m) hm))
        (rho0CaseII (m := m))
        ⟨0, by omega⟩
        m = m ^ 2 := by
  have hm0 : 0 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  let hm6 : m % 6 = 4 := mod_six_eq_four_of_mod_twelve_eq_ten (m := m) hm
  let x0 : Fin m := ⟨0, hm0⟩
  let e : Fin m ≃ Fin m :=
    Equiv.ofBijective
      (fun i : Fin m => (((TorusD3Even.T0CaseII (m := m) hm6)^[i.1]) x0))
      (cycleOn_laneMap0_caseII_mod_ten (m := m) hm).1
  calc
    TorusD3Even.blockTime
        (TorusD3Even.T0CaseII (m := m) hm6)
        (rho0CaseII (m := m))
        x0
        m
        = Finset.sum (Finset.range m) (fun i =>
            rho0CaseII (m := m) ((((TorusD3Even.T0CaseII (m := m) hm6)^[i]) x0))) := by
            simpa using
              blockTime_eq_sum_range
                (TorusD3Even.T0CaseII (m := m) hm6)
                (rho0CaseII (m := m))
                x0
                m
    _ = ∑ i : Fin m, rho0CaseII (m := m) (e i) := by
          rw [← Fin.sum_univ_eq_sum_range]
          rfl
    _ = ∑ x : Fin m, rho0CaseII (m := m) x := by
          exact Equiv.sum_comp e (fun x : Fin m => rho0CaseII (m := m) x)
    _ = m ^ 2 := sum_rho0CaseII (m := m)

private theorem hfirst_zero_column_to_top [Fact (9 < m)] (hm : m % 12 = 10) :
    ∀ n, 0 < n → n < m - 2 →
      (returnMap0CaseIIXY (m := m)^[n]) ((0 : ZMod m), (2 : ZMod m)) ∉
        Set.range (linePoint0 (m := m)) := by
  let F := returnMap0CaseIIXY (m := m)
  let start : P0Coord m := ((0 : ZMod m), (2 : ZMod m))
  let upperStart : P0Coord m := ((0 : ZMod m), (((m / 2 + 1 : ℕ) : ZMod m)))
  let a : ℕ := m / 2 - 1
  intro n hn0 hnlt
  have hm0 : 0 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (0 < m) := ⟨hm0⟩
  by_cases hlow : n ≤ m / 2 - 2
  · have hiter :
      ((F^[n]) start) = ((0 : ZMod m), (((2 + n : ℕ) : ZMod m))) := by
      dsimp [F, start]
      simpa using iterate_returnMap0CaseIIXY_zero_column_lower_partial (m := m) (t := n) hlow
    rw [hiter]
    exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (0 : ZMod m))
      (by omega) (by
        have hm9 : 9 < m := Fact.out
        omega)
  · by_cases hEq : n = a
    · rw [hEq]
      have hiter : ((F^[a]) start) = upperStart := by
        dsimp [F, start, upperStart, a]
        simpa using iterate_returnMap0CaseIIXY_zero_column_to_upper_start (m := m) hm
      rw [hiter]
      exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (0 : ZMod m))
        (by
          have hm9 : 9 < m := Fact.out
          omega) (by
          have hm9 : 9 < m := Fact.out
          omega)
    · have hgt : a < n := by
        dsimp [a] at *
        omega
      let s : ℕ := n - a
      have hs_pos : 0 < s := by
        dsimp [s, a]
        omega
      have hsle : s ≤ m / 2 - 2 := by
        dsimp [s, a]
        rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
        rw [hq] at hnlt ⊢
        omega
      have hnEq' : n = s + a := by
        dsimp [s, a]
        omega
      have hiter :
          ((F^[n]) start) = ((0 : ZMod m), (((m / 2 + 1 + s : ℕ) : ZMod m))) := by
        calc
          ((F^[n]) start) = ((F^[s]) ((F^[a]) start)) := by
            rw [hnEq', Function.iterate_add_apply]
          _ = ((F^[s]) upperStart) := by
            dsimp [F, start, upperStart, a]
            rw [iterate_returnMap0CaseIIXY_zero_column_to_upper_start (m := m) hm]
          _ = ((0 : ZMod m), (((m / 2 + 1 + s : ℕ) : ZMod m))) := by
            dsimp [upperStart]
            rw [iterate_returnMap0CaseIIXY_zero_column_upper_partial (m := m) hm (t := s) hsle]
      have hnot :
          ((0 : ZMod m), (((m / 2 + 1 + s : ℕ) : ZMod m))) ∉ Set.range (linePoint0 (m := m)) := by
        exact not_mem_range_linePoint0_of_nat_snd_pos_lt
          (m := m) (a := (0 : ZMod m)) (n := m / 2 + 1 + s)
          (by
            have hm9 : 9 < m := Fact.out
            omega) (by
            have hm9 : 9 < m := Fact.out
            omega)
      rw [hiter]
      exact hnot

theorem hfirst_two_column_to_zero_core [Fact (9 < m)]
    (hhalf : 2 * (m / 2) = m)
    (hlower :
      ∀ {t : ℕ}, t ≤ m / 2 - 1 →
        ((returnMap0CaseIIXY (m := m)^[t]) ((2 : ZMod m), (2 : ZMod m))) =
          ((2 : ZMod m), (((2 + t : ℕ) : ZMod m))))
    (hupperStart :
      ((returnMap0CaseIIXY (m := m)^[m / 2]) ((2 : ZMod m), (2 : ZMod m))) =
        ((2 : ZMod m), (((m / 2 + 2 : ℕ) : ZMod m)))) :
    ∀ n, 0 < n → n < m - 2 →
      (returnMap0CaseIIXY (m := m)^[n]) ((2 : ZMod m), (2 : ZMod m)) ∉
        Set.range (linePoint0 (m := m)) := by
  let F := returnMap0CaseIIXY (m := m)
  let start : P0Coord m := ((2 : ZMod m), (2 : ZMod m))
  let upperStart : P0Coord m := ((2 : ZMod m), (((m / 2 + 2 : ℕ) : ZMod m)))
  let a : ℕ := m / 2
  let b : ℕ := m / 2 - 4
  intro n hn0 hnlt
  have hm0 : 0 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (0 < m) := ⟨hm0⟩
  by_cases hlow : n ≤ m / 2 - 1
  · have hiter :
      ((F^[n]) start) = ((2 : ZMod m), (((2 + n : ℕ) : ZMod m))) := by
      dsimp [F, start]
      simpa using hlower (t := n) hlow
    rw [hiter]
    exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (2 : ZMod m))
      (by omega) (by
        have hm9 : 9 < m := Fact.out
        omega)
  · by_cases hEq : n = a
    · rw [hEq]
      have hiter : ((F^[a]) start) = upperStart := by
        dsimp [F, start, upperStart, a]
        simpa using hupperStart
      rw [hiter]
      exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (2 : ZMod m))
        (by
          have hm9 : 9 < m := Fact.out
          omega) (by
          have hm9 : 9 < m := Fact.out
          omega)
    · have hgt : a < n := by
        dsimp [a] at *
        omega
      let s : ℕ := n - a
      have hs_pos : 0 < s := by
        dsimp [s, a]
        omega
      by_cases hsle : s ≤ b
      · have hiter :
          ((F^[n]) start) = ((2 : ZMod m), (((m / 2 + 2 + s : ℕ) : ZMod m))) := by
          have hnEq' : n = s + a := by
            dsimp [s, a] at *
            omega
          calc
            ((F^[n]) start) = ((F^[s]) ((F^[a]) start)) := by
              rw [hnEq', Function.iterate_add_apply]
            _ = ((F^[s]) upperStart) := by
              dsimp [F, start, upperStart, a]
              rw [hupperStart]
            _ = ((2 : ZMod m), (((m / 2 + 2 + s : ℕ) : ZMod m))) := by
              dsimp [upperStart]
              rw [iterate_returnMap0CaseIIXY_two_column_upper_partial (m := m) (t := s) hsle]
        rw [hiter]
        exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (2 : ZMod m))
          (by
            have hm9 : 9 < m := Fact.out
            dsimp [s]
            omega) (by
            have hm9 : 9 < m := Fact.out
            dsimp [s]
            omega)
      · have hsEq : s = b + 1 := by
          dsimp [b, s, a] at *
          omega
        have hupper :
          ((F^[b]) upperStart) = ((2 : ZMod m), (((m - 2 : ℕ) : ZMod m))) := by
          dsimp [upperStart, b, F]
          rw [iterate_returnMap0CaseIIXY_two_column_upper_partial (m := m) (t := b) le_rfl]
          have hsum : m / 2 + 2 + b = m - 2 := by omega
          simp [hsum]
        have hiter :
          ((F^[n]) start) = ((2 : ZMod m), (((m - 1 : ℕ) : ZMod m))) := by
          have hnEq' : n = (b + 1) + a := by
            dsimp [b, s, a] at *
            omega
          calc
            ((F^[n]) start) = ((F^[b + 1]) ((F^[a]) start)) := by
              rw [hnEq', Function.iterate_add_apply]
            _ = ((F^[b + 1]) upperStart) := by
              dsimp [F, start, upperStart, a]
              rw [hupperStart]
            _ = F ((F^[b]) upperStart) := by
              rw [Function.iterate_succ_apply']
            _ = F ((2 : ZMod m), (((m - 2 : ℕ) : ZMod m))) := by
              rw [hupper]
            _ = ((2 : ZMod m), (((m - 1 : ℕ) : ZMod m))) := by
              dsimp [F]
              simpa using returnMap0CaseIIXY_two_column_m_sub_two (m := m)
        rw [hiter]
        exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (2 : ZMod m))
          (by
            have hm9 : 9 < m := Fact.out
            omega) (by
            have hm9 : 9 < m := Fact.out
            omega)

private theorem hfirst_two_column_to_zero [Fact (9 < m)] (hm : m % 12 = 10) :
    ∀ n, 0 < n → n < m - 2 →
      (returnMap0CaseIIXY (m := m)^[n]) ((2 : ZMod m), (2 : ZMod m)) ∉
        Set.range (linePoint0 (m := m)) := by
  have hhalf : 2 * (m / 2) = m := by
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rw [hq]
    omega
  exact hfirst_two_column_to_zero_core (m := m) hhalf
    (fun {t} ht => iterate_returnMap0CaseIIXY_two_column_lower_partial (m := m) hm (t := t) ht)
    (iterate_returnMap0CaseIIXY_two_column_to_upper_start (m := m) hm)

private theorem hfirst_four_column_to_zero [Fact (9 < m)] (hm : m % 12 = 10) :
    ∀ n, 0 < n → n < m - 4 →
      (returnMap0CaseIIXY (m := m)^[n]) ((4 : ZMod m), (4 : ZMod m)) ∉
        Set.range (linePoint0 (m := m)) := by
  let F := returnMap0CaseIIXY (m := m)
  let start : P0Coord m := ((4 : ZMod m), (4 : ZMod m))
  let upperStart : P0Coord m := ((4 : ZMod m), (((m / 2 + 3 : ℕ) : ZMod m)))
  let a : ℕ := m / 2 - 1
  let b : ℕ := m / 2 - 5
  intro n hn0 hnlt
  have hm0 : 0 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (0 < m) := ⟨hm0⟩
  by_cases hlow : n ≤ m / 2 - 2
  · have hiter :
      ((F^[n]) start) = ((4 : ZMod m), (((4 + n : ℕ) : ZMod m))) := by
        dsimp [F, start]
        simpa using iterate_returnMap0CaseIIXY_four_column_lower_partial (m := m) hm (t := n) hlow
    rw [hiter]
    exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (4 : ZMod m))
      (by omega) (by
        have hm9 : 9 < m := Fact.out
        omega)
  · by_cases hEq : n = a
    · rw [hEq]
      have hiter : ((F^[a]) start) = upperStart := by
        dsimp [F, start, upperStart, a]
        simpa using iterate_returnMap0CaseIIXY_four_column_to_upper_start (m := m) hm
      rw [hiter]
      exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (4 : ZMod m))
        (by
          have hm9 : 9 < m := Fact.out
          omega) (by
          have hm9 : 9 < m := Fact.out
          omega)
    · have hgt : a < n := by
        dsimp [a] at *
        omega
      let s : ℕ := n - a
      have hs_pos : 0 < s := by
        dsimp [s, a]
        omega
      by_cases hsle : s ≤ b
      · have hiter :
          ((F^[n]) start) = ((4 : ZMod m), (((m / 2 + 3 + s : ℕ) : ZMod m))) := by
          have hnEq' : n = s + a := by
            dsimp [s, a] at *
            omega
          calc
            ((F^[n]) start) = ((F^[s]) ((F^[a]) start)) := by
              rw [hnEq', Function.iterate_add_apply]
            _ = ((F^[s]) upperStart) := by
              dsimp [F, start, upperStart, a]
              rw [iterate_returnMap0CaseIIXY_four_column_to_upper_start (m := m) hm]
            _ = ((4 : ZMod m), (((m / 2 + 3 + s : ℕ) : ZMod m))) := by
              dsimp [upperStart]
              rw [iterate_returnMap0CaseIIXY_four_column_upper_partial (m := m) hm (t := s) hsle]
        rw [hiter]
        exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (4 : ZMod m))
          (by
            have hm9 : 9 < m := Fact.out
            omega) (by
            have hm9 : 9 < m := Fact.out
            omega)
      · have hsEq : s = b + 1 := by
          dsimp [b, s, a] at *
          omega
        have hupper :
          ((F^[b]) upperStart) = ((4 : ZMod m), (((m - 2 : ℕ) : ZMod m))) := by
          dsimp [upperStart, b, F]
          rw [iterate_returnMap0CaseIIXY_four_column_upper_partial (m := m) hm
            (t := b) le_rfl]
          have hsum : m / 2 + 3 + b = m - 2 := by omega
          simp [hsum]
        have hiter :
          ((F^[n]) start) = ((4 : ZMod m), (((m - 1 : ℕ) : ZMod m))) := by
          have hnEq' : n = (b + 1) + a := by
            dsimp [b, s, a] at *
            omega
          calc
            ((F^[n]) start) = ((F^[b + 1]) ((F^[a]) start)) := by
              rw [hnEq', Function.iterate_add_apply]
            _ = ((F^[b + 1]) upperStart) := by
              dsimp [F, start, upperStart, a]
              rw [iterate_returnMap0CaseIIXY_four_column_to_upper_start (m := m) hm]
            _ = F ((F^[b]) upperStart) := by
              rw [Function.iterate_succ_apply']
            _ = F ((4 : ZMod m), (((m - 2 : ℕ) : ZMod m))) := by
              rw [hupper]
            _ = ((4 : ZMod m), (((m - 1 : ℕ) : ZMod m))) := by
              dsimp [F]
              simpa using returnMap0CaseIIXY_four_column_m_sub_two (m := m) hm
        rw [hiter]
        exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (4 : ZMod m))
          (by
            have hm9 : 9 < m := Fact.out
            omega) (by
            have hm9 : 9 < m := Fact.out
            omega)

private theorem hfirst_six_column_to_zero [Fact (9 < m)] (hm : m % 12 = 10) :
    ∀ n, 0 < n → n < m - 6 →
      (returnMap0CaseIIXY (m := m)^[n]) ((6 : ZMod m), (6 : ZMod m)) ∉
        Set.range (linePoint0 (m := m)) := by
  let F := returnMap0CaseIIXY (m := m)
  let start : P0Coord m := ((6 : ZMod m), (6 : ZMod m))
  let upperStart : P0Coord m := ((6 : ZMod m), (((m / 2 + 4 : ℕ) : ZMod m)))
  let a : ℕ := m / 2 - 2
  let b : ℕ := m / 2 - 6
  intro n hn0 hnlt
  have hm0 : 0 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (0 < m) := ⟨hm0⟩
  by_cases hlow : n ≤ m / 2 - 3
  · have hiter :
      ((F^[n]) start) = ((6 : ZMod m), (((6 + n : ℕ) : ZMod m))) := by
      dsimp [F, start]
      simpa using iterate_returnMap0CaseIIXY_six_column_lower_partial (m := m) hm (t := n) hlow
    rw [hiter]
    exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (6 : ZMod m))
      (by omega) (by
        have hm9 : 9 < m := Fact.out
        omega)
  · by_cases hEq : n = a
    · rw [hEq]
      have hiter : ((F^[a]) start) = upperStart := by
        dsimp [F, start, upperStart, a]
        simpa using iterate_returnMap0CaseIIXY_six_column_to_upper_start (m := m) hm
      rw [hiter]
      exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (6 : ZMod m))
        (by
          have hm9 : 9 < m := Fact.out
          omega) (by
          have hm9 : 9 < m := Fact.out
          omega)
    · have hgt : a < n := by
        dsimp [a] at *
        omega
      let s : ℕ := n - a
      have hs_pos : 0 < s := by
        dsimp [s, a]
        omega
      by_cases hsle : s ≤ b
      · have hiter :
          ((F^[n]) start) = ((6 : ZMod m), (((m / 2 + 4 + s : ℕ) : ZMod m))) := by
          have hnEq' : n = s + a := by
            dsimp [s, a] at *
            omega
          calc
            ((F^[n]) start) = ((F^[s]) ((F^[a]) start)) := by
              rw [hnEq', Function.iterate_add_apply]
            _ = ((F^[s]) upperStart) := by
              dsimp [F, start, upperStart, a]
              rw [iterate_returnMap0CaseIIXY_six_column_to_upper_start (m := m) hm]
            _ = ((6 : ZMod m), (((m / 2 + 4 + s : ℕ) : ZMod m))) := by
              dsimp [upperStart]
              rw [iterate_returnMap0CaseIIXY_six_column_upper_partial (m := m) hm (t := s) hsle]
        rw [hiter]
        exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (6 : ZMod m))
          (by
            have hm9 : 9 < m := Fact.out
            omega) (by
            have hm9 : 9 < m := Fact.out
            omega)
      · have hsEq : s = b + 1 := by
          dsimp [b, s, a] at *
          omega
        have hupper :
          ((F^[b]) upperStart) = ((6 : ZMod m), (((m - 2 : ℕ) : ZMod m))) := by
          dsimp [upperStart, b, F]
          rw [iterate_returnMap0CaseIIXY_six_column_upper_partial (m := m) hm
            (t := b) le_rfl]
          have hsum : m / 2 + 4 + b = m - 2 := by omega
          simp [hsum]
        have hiter :
          ((F^[n]) start) = ((6 : ZMod m), (((m - 1 : ℕ) : ZMod m))) := by
          have hnEq' : n = (b + 1) + a := by
            dsimp [b, s, a] at *
            omega
          calc
            ((F^[n]) start) = ((F^[b + 1]) ((F^[a]) start)) := by
              rw [hnEq', Function.iterate_add_apply]
            _ = ((F^[b + 1]) upperStart) := by
              dsimp [F, start, upperStart, a]
              rw [iterate_returnMap0CaseIIXY_six_column_to_upper_start (m := m) hm]
            _ = F ((F^[b]) upperStart) := by
              rw [Function.iterate_succ_apply']
            _ = F ((6 : ZMod m), (((m - 2 : ℕ) : ZMod m))) := by
              rw [hupper]
            _ = ((6 : ZMod m), (((m - 1 : ℕ) : ZMod m))) := by
              dsimp [F]
              simpa using returnMap0CaseIIXY_six_column_m_sub_two (m := m) hm
        rw [hiter]
        exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (6 : ZMod m))
          (by
            have hm9 : 9 < m := Fact.out
            omega) (by
            have hm9 : 9 < m := Fact.out
            omega)

/-!
Planned Case-II mod-10 endgame order:

1. `hfirst` families on the already-closed first-return lanes.
2. Global `hfirst` dispatcher.
3. `m^2` cycle theorem on the return map via `firstReturn_counting`.
4. `m^3` cycle theorem on the full map via the existing semiconjugacy/lift.

These are intentionally left as short draft stubs so the next proof batch can
fill them in without re-deciding theorem order.
-/

theorem hfirst_line_zero_caseII_mod_ten [Fact (9 < m)] :
    ∀ n, 0 < n →
      n < rho0CaseII (m := m) (0 : Fin m) →
        (returnMap0CaseIIXY (m := m)^[n]) (linePoint0 (m := m) (0 : Fin m)) ∉
          Set.range (linePoint0 (m := m)) := by
  intro n hn0 hnlt
  have hrho : rho0CaseII (m := m) (0 : Fin m) = 1 := rho0CaseII_zero (m := m)
  omega

theorem hfirst_line_one_caseII_mod_ten [Fact (9 < m)] (hm : m % 12 = 10) :
    ∀ n, 0 < n →
      n < rho0CaseII (m := m) (⟨1, by omega⟩ : Fin m) →
        (returnMap0CaseIIXY (m := m)^[n])
            (linePoint0 (m := m)
              (⟨1, by omega⟩ : Fin m)) ∉
          Set.range (linePoint0 (m := m)) := by
  let F := returnMap0CaseIIXY (m := m)
  let xFin : Fin m := ⟨1, by omega⟩
  intro n hn0 hnlt
  have hm0 : 0 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (0 < m) := ⟨hm0⟩
  have hrho : rho0CaseII (m := m) xFin = m - 2 := by
    simpa [xFin] using
      rho0CaseII_other (m := m) (x := 1) (by omega)
        (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hnm : n < m - 2 := by
    simpa [xFin, hrho] using hnlt
  have h1 :
      ((F^[1]) (linePoint0 (m := m) xFin)) = ((3 : ZMod m), (2 : ZMod m)) := by
    simpa [Function.iterate_one, linePoint0, xFin] using returnMap0CaseIIXY_one_zero (m := m)
  have h2 :
      ((F^[2]) (linePoint0 (m := m) xFin)) = ((4 : ZMod m), (4 : ZMod m)) := by
    calc
      ((F^[2]) (linePoint0 (m := m) xFin))
          = F (((F^[1]) (linePoint0 (m := m) xFin))) := by
              simp [Function.iterate_succ_apply']
      _ = F ((3 : ZMod m), (2 : ZMod m)) := by rw [h1]
      _ = ((4 : ZMod m), (4 : ZMod m)) := returnMap0CaseIIXY_three_two (m := m)
  by_cases hn1 : n = 1
  · rw [hn1, h1]
    simpa using
      (not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (3 : ZMod m)) (n := 2)
      (by decide) (by
        have hm9 : 9 < m := Fact.out
        omega))
  · by_cases hn2 : n = 2
    · rw [hn2, h2]
      simpa using
        (not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (4 : ZMod m)) (n := 4)
        (by omega) (by
          have hm9 : 9 < m := Fact.out
          omega))
    · have hn3 : 3 ≤ n := by omega
      let t : ℕ := n - 2
      have ht0 : 0 < t := by
        dsimp [t]
        omega
      have ht : t < m - 4 := by
        dsimp [t]
        omega
      have hnEq : n = t + 2 := by
        dsimp [t]
        omega
      have hiter :
          ((F^[n]) (linePoint0 (m := m) xFin)) =
            ((F^[t]) ((4 : ZMod m), (4 : ZMod m))) := by
        rw [hnEq, Function.iterate_add_apply, h2]
      rw [hiter]
      exact hfirst_four_column_to_zero (m := m) hm t ht0 ht

theorem hfirst_line_two_caseII_mod_ten [Fact (9 < m)] (hm : m % 12 = 10) :
    ∀ n, 0 < n →
      n < rho0CaseII (m := m) (⟨2, by omega⟩ : Fin m) →
        (returnMap0CaseIIXY (m := m)^[n])
            (linePoint0 (m := m)
              (⟨2, by omega⟩ : Fin m)) ∉
          Set.range (linePoint0 (m := m)) := by
  let F := returnMap0CaseIIXY (m := m)
  let xFin : Fin m := ⟨2, by omega⟩
  intro n hn0 hnlt
  have hm0 : 0 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (0 < m) := ⟨hm0⟩
  have hrho : rho0CaseII (m := m) xFin = m - 2 := by
    simpa [xFin] using
      rho0CaseII_other (m := m) (x := 2) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hnm : n < m - 2 := by
    simpa [xFin, hrho] using hnlt
  have h1 :
      ((F^[1]) (linePoint0 (m := m) xFin)) = ((3 : ZMod m), (1 : ZMod m)) := by
    simpa [Function.iterate_one, linePoint0, xFin] using
      returnMap0CaseIIXY_line_start_generic (m := m) (x := 2) (by omega) (by omega)
  have h2 :
      ((F^[2]) (linePoint0 (m := m) xFin)) = ((5 : ZMod m), (3 : ZMod m)) := by
    calc
      ((F^[2]) (linePoint0 (m := m) xFin))
          = F (((F^[1]) (linePoint0 (m := m) xFin))) := by
              simp [Function.iterate_succ_apply']
      _ = F ((3 : ZMod m), (1 : ZMod m)) := by rw [h1]
      _ = ((5 : ZMod m), (3 : ZMod m)) := by
            simpa using returnMap0CaseIIXY_R_line (m := m) (y := 1) (by omega)
  have h3 :
      ((F^[3]) (linePoint0 (m := m) xFin)) = ((5 : ZMod m), (4 : ZMod m)) := by
    calc
      ((F^[3]) (linePoint0 (m := m) xFin))
          = F (((F^[2]) (linePoint0 (m := m) xFin))) := by
              simp [Function.iterate_succ_apply']
      _ = F ((5 : ZMod m), (3 : ZMod m)) := by rw [h2]
      _ = ((5 : ZMod m), (4 : ZMod m)) := returnMap0CaseIIXY_five_three (m := m)
  have h4 :
      ((F^[4]) (linePoint0 (m := m) xFin)) = ((6 : ZMod m), (6 : ZMod m)) := by
    calc
      ((F^[4]) (linePoint0 (m := m) xFin))
          = F (((F^[3]) (linePoint0 (m := m) xFin))) := by
              simp [Function.iterate_succ_apply']
      _ = F ((5 : ZMod m), (4 : ZMod m)) := by rw [h3]
      _ = ((6 : ZMod m), (6 : ZMod m)) := returnMap0CaseIIXY_five_four (m := m)
  by_cases hn1 : n = 1
  · rw [hn1, h1]
    simpa using
      (not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (3 : ZMod m)) (n := 1)
      (by decide) (by
        have hm9 : 9 < m := Fact.out
        omega))
  by_cases hn2 : n = 2
  · rw [hn2, h2]
    simpa using
      (not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (5 : ZMod m)) (n := 3)
      (by omega) (by
        have hm9 : 9 < m := Fact.out
        omega))
  by_cases hn3 : n = 3
  · rw [hn3, h3]
    simpa using
      (not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (5 : ZMod m)) (n := 4)
      (by omega) (by
        have hm9 : 9 < m := Fact.out
        omega))
  by_cases hn4 : n = 4
  · rw [hn4, h4]
    simpa using
      (not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (6 : ZMod m)) (n := 6)
      (by omega) (by
        have hm9 : 9 < m := Fact.out
        omega))
  have hn5 : 5 ≤ n := by omega
  let t : ℕ := n - 4
  have ht0 : 0 < t := by
    dsimp [t]
    omega
  have ht : t < m - 6 := by
    dsimp [t]
    omega
  have hnEq : n = t + 4 := by
    dsimp [t]
    omega
  have hiter :
      ((F^[n]) (linePoint0 (m := m) xFin)) =
        ((F^[t]) ((6 : ZMod m), (6 : ZMod m))) := by
    rw [hnEq, Function.iterate_add_apply, h4]
  rw [hiter]
  exact hfirst_six_column_to_zero (m := m) hm t ht0 ht

/-!
Reusable strict-prefix nonreturn layer for Case II mod `10`.

These helpers are the intended abstraction boundary for the remaining `hfirst`
work:

1. repaired warm-up columns (`4` and `6`);
2. generic upper-column runs before the `R` defect;
3. wrapped upper-column runs after `R`;
4. the safe even final-column tail from `A = (x+4,x+4)`.

The goal is to keep the remaining `hfirst` proofs family-based rather than
replaying each lane as a bespoke orbit search.
-/

private theorem hfirst_upper_column_partial [Fact (9 < m)] {c y0 : ℕ}
    (hc4 : 4 ≤ c) (hcle : c ≤ m - 3)
    (hy0l : c ≤ y0) (hy0u : y0 ≤ (m + c - 1) / 2) :
    ∀ n, 0 < n → n ≤ (m + c - 1) / 2 - y0 →
      (returnMap0CaseIIXY (m := m)^[n]) ((((c : ℕ) : ZMod m)), (((y0 : ℕ) : ZMod m))) ∉
        Set.range (linePoint0 (m := m)) := by
  intro n hn0 hnle
  have hm0 : 0 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (0 < m) := ⟨hm0⟩
  have hiter :
      ((returnMap0CaseIIXY (m := m)^[n]) ((((c : ℕ) : ZMod m)), (((y0 : ℕ) : ZMod m)))) =
        ((((c : ℕ) : ZMod m)), (((y0 + n : ℕ) : ZMod m))) := by
    simpa using
      iterate_returnMap0CaseIIXY_upper_column_partial (m := m)
        (c := c) (y0 := y0) (t := n) hc4 hcle hy0l hy0u hnle
  rw [hiter]
  exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (((c : ℕ) : ZMod m)))
    (by omega) (by
      have hm9 : 9 < m := Fact.out
      omega)

private theorem hfirst_wrapped_upper_column_to_zero [Fact (9 < m)] (hm : m % 12 = 10)
    {c y0 : ℕ} (hc1 : 1 ≤ c) (hcle : c ≤ m - 7) (hcodd : Odd c)
    (hy0l : (m + c + 1) / 2 ≤ y0) (hy0u : y0 ≤ m - 2) :
    ∀ n, 0 < n → n < m - y0 →
      (returnMap0CaseIIXY (m := m)^[n]) ((((c : ℕ) : ZMod m)), (((y0 : ℕ) : ZMod m))) ∉
        Set.range (linePoint0 (m := m)) := by
  intro n hn0 hnlt
  have hm0 : 0 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (0 < m) := ⟨hm0⟩
  by_cases hmid : n ≤ m - 2 - y0
  · have hiter :
        ((returnMap0CaseIIXY (m := m)^[n]) ((((c : ℕ) : ZMod m)), (((y0 : ℕ) : ZMod m)))) =
          ((((c : ℕ) : ZMod m)), (((y0 + n : ℕ) : ZMod m))) := by
      simpa using
        iterate_returnMap0CaseIIXY_wrapped_upper_column_partial (m := m) hm
          (c := c) (y0 := y0) (t := n) hc1 hcle hcodd hy0l hy0u hmid
    rw [hiter]
    exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m) (a := (((c : ℕ) : ZMod m)))
      (by omega) (by
        have hm9 : 9 < m := Fact.out
        omega)
  · have hnEq : n = m - 1 - y0 := by omega
    have hiter :
        ((returnMap0CaseIIXY (m := m)^[n]) ((((c : ℕ) : ZMod m)), (((y0 : ℕ) : ZMod m)))) =
          ((((c : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) := by
      rw [hnEq, show m - 1 - y0 = (m - 2 - y0) + 1 by omega, Function.iterate_succ_apply']
      rw [iterate_returnMap0CaseIIXY_wrapped_upper_column_partial (m := m) hm
        (c := c) (y0 := y0) (t := m - 2 - y0) hc1 hcle hcodd hy0l hy0u le_rfl]
      have hsum : y0 + (m - 2 - y0) = m - 2 := by omega
      simp [hsum]
      simpa using
        returnMap0CaseIIXY_wrapped_upper_column_m_sub_two (m := m) (c := c) hc1 (by omega)
    rw [hiter]
    apply not_mem_range_linePoint0_of_snd_ne_zero (m := m)
    rw [cast_sub_one_eq_neg_one (m := m) (by
      have hm9 : 9 < m := Fact.out
      omega)]
    exact neg_ne_zero.mpr (one_ne_zero (m := m))

private theorem hfirst_even_generic_final_column_to_zero_safe [Fact (9 < m)]
    (hm : m % 12 = 10) {x : ℕ}
    (hx4 : 4 ≤ x) (hxle : x ≤ m - 12) (hxeven : Even x) :
    ∀ n, 0 < n → n < m - x - 4 →
      (returnMap0CaseIIXY (m := m)^[n])
          ((((x + 4 : ℕ) : ZMod m)), (((x + 4 : ℕ) : ZMod m))) ∉
        Set.range (linePoint0 (m := m)) := by
  let F := returnMap0CaseIIXY (m := m)
  let start : P0Coord m := ((((x + 4 : ℕ) : ZMod m)), (((x + 4 : ℕ) : ZMod m)))
  let upperStart : P0Coord m :=
    ((((x + 4 : ℕ) : ZMod m)), ((((m / 2 + x / 2 + 3 : ℕ) : ZMod m))))
  let a : ℕ := m / 2 - x / 2 - 1
  let b : ℕ := m / 2 - x / 2 - 5
  intro n hn0 hnlt
  have hm0 : 0 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (0 < m) := ⟨hm0⟩
  have hxle' : x ≤ m - 8 := by omega
  by_cases hlow : n ≤ m / 2 - x / 2 - 2
  · have hiter :
        ((F^[n]) start) =
          ((((x + 4 : ℕ) : ZMod m)), (((x + 4 + n : ℕ) : ZMod m))) := by
      dsimp [F, start]
      simpa using
        iterate_returnMap0CaseIIXY_even_generic_final_column_lower_partial
          (m := m) hm hx4 hxle' hxeven (t := n) hlow
    rw [hiter]
    exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
      (a := (((x + 4 : ℕ) : ZMod m))) (by omega) (by
        have hm9 : 9 < m := Fact.out
        omega)
  · by_cases hEq : n = a
    · rw [hEq]
      have hiter :
          ((F^[a]) start) = upperStart := by
        dsimp [F, start, upperStart, a]
        simpa using
          iterate_returnMap0CaseIIXY_even_generic_final_column_to_upper_start
            (m := m) hm hx4 hxle' hxeven
      rw [hiter]
      exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
        (a := (((x + 4 : ℕ) : ZMod m))) (by
          rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
          rcases hxeven with ⟨r, hr⟩
          rw [hq, hr]
          omega) (by
            have hm9 : 9 < m := Fact.out
            rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
            rcases hxeven with ⟨r, hr⟩
            rw [hq, hr]
            omega)
    · have hgt : a < n := by
        dsimp [a] at *
        omega
      let s : ℕ := n - a
      have hs_pos : 0 < s := by
        dsimp [s, a]
        omega
      have hnEq : n = a + s := by
        dsimp [s, a]
        omega
      by_cases hsle : s ≤ b
      · have hiter :
            ((F^[n]) start) =
              ((((x + 4 : ℕ) : ZMod m)), (((m / 2 + x / 2 + 3 + s : ℕ) : ZMod m))) := by
          have hnEq' : n = s + a := by
            dsimp [s, a] at *
            omega
          calc
            ((F^[n]) start)
                = ((F^[s]) ((F^[a]) start)) := by
                      rw [hnEq', Function.iterate_add_apply]
            _ = ((F^[s]) upperStart) := by
                  dsimp [upperStart, a, F, start]
                  rw [iterate_returnMap0CaseIIXY_even_generic_final_column_to_upper_start
                    (m := m) hm hx4 hxle' hxeven]
            _ = ((((x + 4 : ℕ) : ZMod m)), (((m / 2 + x / 2 + 3 + s : ℕ) : ZMod m))) := by
                  dsimp [upperStart]
                  rw [iterate_returnMap0CaseIIXY_even_generic_final_column_upper_partial
                    (m := m) hm hx4 hxle hxeven (t := s) hsle]
        have hiter' :
            ((returnMap0CaseIIXY (m := m)^[n])
                ((((x + 4 : ℕ) : ZMod m)), (((x + 4 : ℕ) : ZMod m)))) =
              ((((x + 4 : ℕ) : ZMod m)), (((m / 2 + x / 2 + 3 + s : ℕ) : ZMod m))) := by
          simpa [F, start] using hiter
        rw [hiter']
        exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
          (a := (((x + 4 : ℕ) : ZMod m))) (by
            rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
            rcases hxeven with ⟨r, hr⟩
            rw [hq, hr]
            omega) (by
              have hm9 : 9 < m := Fact.out
              rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
              rcases hxeven with ⟨r, hr⟩
              rw [hq, hr]
              omega)
      · have hsEq : s = b + 1 := by
          dsimp [b, s, a] at *
          omega
        have hupper :
            ((F^[b]) upperStart) =
              ((((x + 4 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) := by
          dsimp [upperStart, b, F]
          rw [iterate_returnMap0CaseIIXY_even_generic_final_column_upper_partial
            (m := m) hm hx4 hxle hxeven (t := b) le_rfl]
          have hsum : m / 2 + x / 2 + 3 + b = m - 2 := by
            rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
            rcases hxeven with ⟨r, hr⟩
            rw [hq, hr]
            omega
          simp [hsum]
        have hiter :
            ((F^[n]) start) =
              ((((x + 4 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) := by
          have hnEq' : n = (b + 1) + a := by
            dsimp [b, s, a] at *
            omega
          calc
            ((F^[n]) start)
                = ((F^[b + 1]) ((F^[a]) start)) := by
                      rw [hnEq', Function.iterate_add_apply]
            _ = ((F^[b + 1]) upperStart) := by
                  dsimp [upperStart, a, F, start]
                  rw [iterate_returnMap0CaseIIXY_even_generic_final_column_to_upper_start
                    (m := m) hm hx4 hxle' hxeven]
            _ = F (((F^[b]) upperStart)) := by
                  rw [Function.iterate_succ_apply']
            _ = F ((((x + 4 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) := by
                  rw [hupper]
            _ = ((((x + 4 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) := by
                  dsimp [F]
                  simpa using
                    returnMap0CaseIIXY_wrapped_upper_column_m_sub_two (m := m)
                      (c := x + 4) (by omega) (by omega)
        have hiter' :
            ((returnMap0CaseIIXY (m := m)^[n])
                ((((x + 4 : ℕ) : ZMod m)), (((x + 4 : ℕ) : ZMod m)))) =
              ((((x + 4 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) := by
          simpa [F, start] using hiter
        rw [hiter']
        exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
          (a := (((x + 4 : ℕ) : ZMod m))) (by
            have hm9 : 9 < m := Fact.out
            omega) (by
              have hm9 : 9 < m := Fact.out
              omega)

private theorem hfirst_line_even_generic_caseII_mod_ten_safe [Fact (9 < m)] (hm : m % 12 = 10)
    {x : ℕ} (hx4 : 4 ≤ x) (hxle : x ≤ m - 12) (hxeven : Even x) :
    ∀ n, 0 < n →
      n < rho0CaseII (m := m) (⟨x, by omega⟩ : Fin m) →
        (returnMap0CaseIIXY (m := m)^[n])
            (linePoint0 (m := m) (⟨x, by omega⟩ : Fin m)) ∉
          Set.range (linePoint0 (m := m)) := by
  let F := returnMap0CaseIIXY (m := m)
  let xFin : Fin m := ⟨x, by omega⟩
  intro n hn0 hnlt
  have hm0 : 0 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (0 < m) := ⟨hm0⟩
  have hrho : rho0CaseII (m := m) xFin = m - 2 := by
    simpa [xFin] using
      rho0CaseII_other (m := m) (x := x) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)
  have hnm : n < m - 2 := by
    simpa [xFin, hrho] using hnlt
  have h1 :
      ((F^[1]) (linePoint0 (m := m) xFin)) =
        ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m)) := by
    simpa [Function.iterate_one, linePoint0, xFin] using
      returnMap0CaseIIXY_line_start_generic (m := m) (x := x) (by omega) (by omega)
  have h2 :
      ((F^[2]) (linePoint0 (m := m) xFin)) =
        ((((x + 1 : ℕ) : ZMod m)), (2 : ZMod m)) := by
    calc
      ((F^[2]) (linePoint0 (m := m) xFin))
          = F (((F^[1]) (linePoint0 (m := m) xFin))) := by
              simp [Function.iterate_succ_apply']
      _ = F ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m)) := by rw [h1]
      _ = ((((x + 1 : ℕ) : ZMod m)), (2 : ZMod m)) := by
            exact returnMap0CaseIIXY_even_generic_odd_column_one_step (m := m) hx4 (by omega)
  by_cases hn1 : n = 1
  · rw [hn1, h1]
    simpa using
      (not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
        (a := (((x + 1 : ℕ) : ZMod m))) (n := 1)
        (by decide) (by
          have hm9 : 9 < m := Fact.out
          omega))
  · by_cases hprefix : n ≤ x / 2
    · have hn2 : 2 ≤ n := by omega
      let t : ℕ := n - 2
      have htle : t ≤ x / 2 - 2 := by
        dsimp [t]
        omega
      have hnEq : n = t + 2 := by
        dsimp [t]
        omega
      have hiter :
          ((F^[n]) (linePoint0 (m := m) xFin)) =
            ((((x + 1 : ℕ) : ZMod m)), (((2 + t : ℕ) : ZMod m))) := by
        calc
          ((F^[n]) (linePoint0 (m := m) xFin))
              = ((F^[t]) ((F^[2]) (linePoint0 (m := m) xFin))) := by
                  rw [hnEq, Function.iterate_add_apply]
          _ = ((F^[t]) ((((x + 1 : ℕ) : ZMod m)), (2 : ZMod m))) := by rw [h2]
          _ = ((((x + 1 : ℕ) : ZMod m)), (((2 + t : ℕ) : ZMod m))) := by
                simpa using
                  iterate_returnMap0CaseIIXY_even_generic_odd_column_lower_partial
                    (m := m) (x := x) (t := t) hx4 (by omega) htle
      rw [hiter]
      exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
        (a := (((x + 1 : ℕ) : ZMod m))) (by
          dsimp [t]
          omega) (by
          have hm9 : 9 < m := Fact.out
          dsimp [t]
          omega)
    · by_cases hR : n = x / 2 + 1
      · rw [hR]
        have hiter :
            ((F^[x / 2 + 1]) (linePoint0 (m := m) xFin)) =
              ((((x + 3 : ℕ) : ZMod m)), (((x / 2 + 2 : ℕ) : ZMod m))) := by
          simpa [xFin] using
            iterate_returnMap0CaseIIXY_even_generic_to_R (m := m) (x := x) hx4 (by omega) hxeven
        rw [hiter]
        exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
          (a := (((x + 3 : ℕ) : ZMod m))) (by
            have hm9 : 9 < m := Fact.out
            omega) (by
            have hm9 : 9 < m := Fact.out
            omega)
      · by_cases hmid : n ≤ x + 1
        · let t : ℕ := n - (x / 2 + 1)
          have ht0 : 0 < t := by
            dsimp [t]
            omega
          have htle : t ≤ x / 2 := by
            rcases hxeven with ⟨r, hr⟩
            dsimp [t]
            rw [hr]
            omega
          have hnEq : n = t + (x / 2 + 1) := by
            dsimp [t]
            omega
          have hRstart :
              ((F^[x / 2 + 1]) (linePoint0 (m := m) xFin)) =
                ((((x + 3 : ℕ) : ZMod m)), (((x / 2 + 2 : ℕ) : ZMod m))) := by
            simpa [xFin] using
              iterate_returnMap0CaseIIXY_even_generic_to_R (m := m) (x := x) hx4 (by omega) hxeven
          have hiter :
              ((F^[n]) (linePoint0 (m := m) xFin)) =
                ((((x + 3 : ℕ) : ZMod m)), (((x / 2 + 2 + t : ℕ) : ZMod m))) := by
            calc
              ((F^[n]) (linePoint0 (m := m) xFin))
                  = ((F^[t]) ((F^[x / 2 + 1]) (linePoint0 (m := m) xFin))) := by
                      rw [hnEq, Function.iterate_add_apply]
              _ = ((F^[t]) ((((x + 3 : ℕ) : ZMod m)), (((x / 2 + 2 : ℕ) : ZMod m)))) := by
                    rw [hRstart]
              _ = ((((x + 3 : ℕ) : ZMod m)), (((x / 2 + 2 + t : ℕ) : ZMod m))) := by
                    simpa using
                      iterate_returnMap0CaseIIXY_even_generic_after_R_partial
                        (m := m) (x := x) (t := t) hx4 (by omega) hxeven htle
          rw [hiter]
          exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
            (a := (((x + 3 : ℕ) : ZMod m))) (by
              dsimp [t]
              omega) (by
              have hm9 : 9 < m := Fact.out
              dsimp [t]
              omega)
        · by_cases hA : n = x + 2
          · rw [hA]
            have hiter :
                ((F^[x + 2]) (linePoint0 (m := m) xFin)) =
                  ((((x + 4 : ℕ) : ZMod m)), (((x + 4 : ℕ) : ZMod m))) := by
              simpa [xFin] using
                iterate_returnMap0CaseIIXY_even_generic_to_A (m := m) (x := x) hx4 (by omega) hxeven
            rw [hiter]
            exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
              (a := (((x + 4 : ℕ) : ZMod m))) (by
                have hm9 : 9 < m := Fact.out
                omega) (by
                have hm9 : 9 < m := Fact.out
                omega)
          · let t : ℕ := n - (x + 2)
            have ht0 : 0 < t := by
              dsimp [t]
              omega
            have ht : t < m - x - 4 := by
              dsimp [t]
              omega
            have hnEq : n = t + (x + 2) := by
              dsimp [t]
              omega
            have hAstart :
                ((F^[x + 2]) (linePoint0 (m := m) xFin)) =
                  ((((x + 4 : ℕ) : ZMod m)), (((x + 4 : ℕ) : ZMod m))) := by
              simpa [xFin] using
                iterate_returnMap0CaseIIXY_even_generic_to_A (m := m) (x := x) hx4 (by omega) hxeven
            have hiter :
                ((F^[n]) (linePoint0 (m := m) xFin)) =
                  ((F^[t]) ((((x + 4 : ℕ) : ZMod m)), (((x + 4 : ℕ) : ZMod m)))) := by
              calc
                ((F^[n]) (linePoint0 (m := m) xFin))
                    = ((F^[t]) ((F^[x + 2]) (linePoint0 (m := m) xFin))) := by
                        rw [hnEq, Function.iterate_add_apply]
                _ = ((F^[t]) ((((x + 4 : ℕ) : ZMod m)), (((x + 4 : ℕ) : ZMod m)))) := by
                      rw [hAstart]
            rw [hiter]
            exact hfirst_even_generic_final_column_to_zero_safe
              (m := m) hm hx4 hxle hxeven t ht0 ht

private theorem hfirst_even_generic_final_column_to_zero [Fact (9 < m)]
    (hm : m % 12 = 10) {x : ℕ}
    (hx4 : 4 ≤ x) (hxle : x ≤ m - 8) (hxeven : Even x) :
    ∀ n, 0 < n → n < m - x - 4 →
      (returnMap0CaseIIXY (m := m)^[n])
          ((((x + 4 : ℕ) : ZMod m)), (((x + 4 : ℕ) : ZMod m))) ∉
        Set.range (linePoint0 (m := m)) := by
  by_cases hsafe : x ≤ m - 12
  · exact hfirst_even_generic_final_column_to_zero_safe
      (m := m) hm hx4 hsafe hxeven
  · have hcases : x = m - 10 ∨ x = m - 8 := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rcases hxeven with ⟨r, hr⟩
      rw [hq] at hxle hsafe ⊢
      rw [hr] at hxle hsafe ⊢
      omega
    rcases hcases with hxm10 | hxm8
    · subst hxm10
      intro n hn0 hnlt
      by_cases hlow : n ≤ 3
      · have hiter :
          ((returnMap0CaseIIXY (m := m)^[n])
              ((((m - 6 : ℕ) : ZMod m)), (((m - 6 : ℕ) : ZMod m)))) =
            ((((m - 6 : ℕ) : ZMod m)), (((m - 6 + n : ℕ) : ZMod m))) := by
          have hxeven10 : Even (m - 10) := by
            rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
            rw [hq]
            refine ⟨6 * q, ?_⟩
            omega
          simpa [show m - 10 + 4 = m - 6 by omega] using
            iterate_returnMap0CaseIIXY_even_generic_final_column_lower_partial
              (m := m) hm (x := m - 10) (t := n) (by omega) (by omega) hxeven10 (by omega)
        have hnot :
            (returnMap0CaseIIXY (m := m)^[n])
                ((((m - 6 : ℕ) : ZMod m)), (((m - 6 : ℕ) : ZMod m))) ∉
              Set.range (linePoint0 (m := m)) := by
          rw [hiter]
          exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
            (a := (((m - 6 : ℕ) : ZMod m))) (n := m - 6 + n) (by omega) (by omega)
        simpa [show m - 10 + 4 = m - 6 by omega] using hnot
      · by_cases hupper : n = 4
        · rw [hupper]
          have hupper4 :
              ((returnMap0CaseIIXY (m := m)^[4])
                  ((((m - 6 : ℕ) : ZMod m)), (((m - 6 : ℕ) : ZMod m)))) =
                ((((m - 6 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) := by
            have hxeven10 : Even (m - 10) := by
              rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
              rw [hq]
              refine ⟨6 * q, ?_⟩
              omega
            have hmain := iterate_returnMap0CaseIIXY_even_generic_final_column_to_upper_start
              (m := m) hm (x := m - 10) (by omega) (by omega) hxeven10
            have hsteps : m / 2 - (m - 10) / 2 - 1 = 4 := by
              rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
              rw [hq]
              omega
            have hfst : m - 10 + 4 = m - 6 := by omega
            have hsnd : m / 2 + (m - 10) / 2 + 3 = m - 2 := by
              rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
              rw [hq]
              omega
            simpa [hsteps, hfst, hsnd] using hmain
          have hnot :
              (returnMap0CaseIIXY (m := m)^[4])
                  ((((m - 6 : ℕ) : ZMod m)), (((m - 6 : ℕ) : ZMod m))) ∉
                Set.range (linePoint0 (m := m)) := by
            rw [hupper4]
            exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
              (a := (((m - 6 : ℕ) : ZMod m))) (n := m - 2) (by omega) (by omega)
          simpa [show m - 10 + 4 = m - 6 by omega] using hnot
        · have hnEq : n = 5 := by
            have hnlt6 : n < 6 := by omega
            omega
          have hiter :
              ((returnMap0CaseIIXY (m := m)^[5])
                  ((((m - 6 : ℕ) : ZMod m)), (((m - 6 : ℕ) : ZMod m)))) =
                ((((m - 6 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) := by
            have hupper4 :
                ((returnMap0CaseIIXY (m := m)^[4])
                    ((((m - 6 : ℕ) : ZMod m)), (((m - 6 : ℕ) : ZMod m)))) =
                  ((((m - 6 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) := by
              have hxeven10 : Even (m - 10) := by
                rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
                rw [hq]
                refine ⟨6 * q, ?_⟩
                omega
              have hmain := iterate_returnMap0CaseIIXY_even_generic_final_column_to_upper_start
                (m := m) hm (x := m - 10) (by omega) (by omega) hxeven10
              have hsteps : m / 2 - (m - 10) / 2 - 1 = 4 := by
                rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
                rw [hq]
                omega
              have hfst : m - 10 + 4 = m - 6 := by omega
              have hsnd : m / 2 + (m - 10) / 2 + 3 = m - 2 := by
                rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
                rw [hq]
                omega
              simpa [hsteps, hfst, hsnd] using hmain
            calc
              ((returnMap0CaseIIXY (m := m)^[5])
                  ((((m - 6 : ℕ) : ZMod m)), (((m - 6 : ℕ) : ZMod m))))
                  = returnMap0CaseIIXY (m := m)
                      (((returnMap0CaseIIXY (m := m)^[4])
                        ((((m - 6 : ℕ) : ZMod m)), (((m - 6 : ℕ) : ZMod m))))) := by
                          rw [show 5 = 1 + 4 by omega, Function.iterate_add_apply]
                          simp
              _ = returnMap0CaseIIXY (m := m)
                    ((((m - 6 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) := by
                      rw [hupper4]
              _ = ((((m - 6 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) := by
                    simpa using returnMap0CaseIIXY_wrapped_upper_column_m_sub_two
                      (m := m) (c := m - 6) (by omega) (by omega)
          rw [hnEq]
          have hnot :
              (returnMap0CaseIIXY (m := m)^[5])
                  ((((m - 6 : ℕ) : ZMod m)), (((m - 6 : ℕ) : ZMod m))) ∉
                Set.range (linePoint0 (m := m)) := by
            rw [hiter]
            exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
              (a := (((m - 6 : ℕ) : ZMod m))) (n := m - 1) (by omega) (by omega)
          simpa [show m - 10 + 4 = m - 6 by omega] using hnot
    · subst hxm8
      intro n hn0 hnlt
      by_cases hlow : n ≤ 2
      · have hiter :
            ((returnMap0CaseIIXY (m := m)^[n])
                ((((m - 4 : ℕ) : ZMod m)), (((m - 4 : ℕ) : ZMod m)))) =
              ((((m - 4 : ℕ) : ZMod m)), (((m - 4 + n : ℕ) : ZMod m))) := by
          have hxeven8 : Even (m - 8) := by
            rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
            rw [hq]
            refine ⟨6 * q + 1, ?_⟩
            omega
          simpa [show m - 8 + 4 = m - 4 by omega] using
            iterate_returnMap0CaseIIXY_even_generic_final_column_lower_partial
              (m := m) hm (x := m - 8) (t := n) (by omega) (by omega) hxeven8 (by omega)
        have hnot :
            (returnMap0CaseIIXY (m := m)^[n])
                ((((m - 4 : ℕ) : ZMod m)), (((m - 4 : ℕ) : ZMod m))) ∉
              Set.range (linePoint0 (m := m)) := by
          rw [hiter]
          exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
            (a := (((m - 4 : ℕ) : ZMod m))) (n := m - 4 + n) (by omega) (by omega)
        simpa [show m - 8 + 4 = m - 4 by omega] using hnot
      · have hnEq : n = 3 := by
          have hnlt4 : n < 4 := by omega
          omega
        rw [hnEq]
        have hiter :
            ((returnMap0CaseIIXY (m := m)^[3])
                ((((m - 4 : ℕ) : ZMod m)), (((m - 4 : ℕ) : ZMod m)))) =
              ((((m - 4 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) := by
          have hxeven8 : Even (m - 8) := by
            rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
            rw [hq]
            refine ⟨6 * q + 1, ?_⟩
            omega
          have hmain := iterate_returnMap0CaseIIXY_even_generic_final_column_to_upper_start
            (m := m) hm (x := m - 8) (by omega) (by omega) hxeven8
          have hsteps : m / 2 - (m - 8) / 2 - 1 = 3 := by
            rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
            rw [hq]
            omega
          have hfst : m - 8 + 4 = m - 4 := by omega
          have hsnd : m / 2 + (m - 8) / 2 + 3 = m - 1 := by
            rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
            rw [hq]
            omega
          simpa [hsteps, hfst, hsnd] using hmain
        have hnot :
            (returnMap0CaseIIXY (m := m)^[3])
                ((((m - 4 : ℕ) : ZMod m)), (((m - 4 : ℕ) : ZMod m))) ∉
              Set.range (linePoint0 (m := m)) := by
          rw [hiter]
          exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
            (a := (((m - 4 : ℕ) : ZMod m))) (n := m - 1) (by omega) (by omega)
        simpa [show m - 8 + 4 = m - 4 by omega] using hnot

private theorem hfirst_line_odd_generic_caseII_mod_ten_safe [Fact (9 < m)] (hm : m % 12 = 10)
    {x : ℕ} (hx3 : 3 ≤ x) (hxle : x ≤ m - 11) (hxodd : Odd x) :
    ∀ n, 0 < n →
      n < rho0CaseII (m := m) (⟨x, by omega⟩ : Fin m) →
        (returnMap0CaseIIXY (m := m)^[n])
            (linePoint0 (m := m) (⟨x, by omega⟩ : Fin m)) ∉
          Set.range (linePoint0 (m := m)) := by
  let F := returnMap0CaseIIXY (m := m)
  let xFin : Fin m := ⟨x, by omega⟩
  let b : ℕ := (x - 1) / 2
  intro n hn0 hnlt
  have hm0 : 0 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (0 < m) := ⟨hm0⟩
  have hrho : rho0CaseII (m := m) xFin = m - 2 := by
    simpa [xFin] using
      rho0CaseII_other (m := m) (x := x) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)
  have hnm : n < m - 2 := by
    simpa [xFin, hrho] using hnlt
  have hb1 : 1 ≤ b := by
    dsimp [b]
    rcases hxodd with ⟨r, hr⟩
    rw [hr]
    omega
  have h1 :
      ((F^[1]) (linePoint0 (m := m) xFin)) =
        ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m)) := by
    simpa [Function.iterate_one, linePoint0, xFin] using
      returnMap0CaseIIXY_line_start_generic (m := m) (x := x) (by omega) (by omega)
  have h2 :
      ((F^[2]) (linePoint0 (m := m) xFin)) =
        ((((x + 1 : ℕ) : ZMod m)), (2 : ZMod m)) := by
    calc
      ((F^[2]) (linePoint0 (m := m) xFin))
          = F (((F^[1]) (linePoint0 (m := m) xFin))) := by
              simp [Function.iterate_succ_apply']
      _ = F ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m)) := by rw [h1]
      _ = ((((x + 1 : ℕ) : ZMod m)), (2 : ZMod m)) := by
            exact returnMap0CaseIIXY_odd_generic_even_column_one_step (m := m) hx3 (by omega) hxodd
  have hmidPoint :
      ((F^[b + 2]) (linePoint0 (m := m) xFin)) =
        ((((x + 1 : ℕ) : ZMod m)), ((((x - 1) / 2 + 2 : ℕ) : ZMod m))) := by
    have hbase :
        ((F^[b + 1]) (linePoint0 (m := m) xFin)) =
          ((((x + 1 : ℕ) : ZMod m)), ((((x - 1) / 2 + 1 : ℕ) : ZMod m))) := by
      calc
        ((F^[b + 1]) (linePoint0 (m := m) xFin))
            = ((F^[b - 1]) ((F^[2]) (linePoint0 (m := m) xFin))) := by
                rw [show b + 1 = (b - 1) + 2 by omega, Function.iterate_add_apply]
        _ = ((F^[b - 1]) ((((x + 1 : ℕ) : ZMod m)), (2 : ZMod m))) := by rw [h2]
        _ = ((((x + 1 : ℕ) : ZMod m)), (((2 + (b - 1) : ℕ) : ZMod m))) := by
              simpa using
                iterate_returnMap0CaseIIXY_odd_generic_even_column_lower_partial
                  (m := m) (x := x) (t := b - 1) hx3 (by omega) hxodd le_rfl
        _ = ((((x + 1 : ℕ) : ZMod m)), ((((x - 1) / 2 + 1 : ℕ) : ZMod m))) := by
              dsimp [b]
              have hsum : 2 + ((x - 1) / 2 - 1) = (x - 1) / 2 + 1 := by omega
              simp [hsum]
    calc
      ((F^[b + 2]) (linePoint0 (m := m) xFin))
          = F (((F^[b + 1]) (linePoint0 (m := m) xFin))) := by
              rw [show b + 2 = 1 + (b + 1) by omega, Function.iterate_add_apply]
              simp
      _ = F ((((x + 1 : ℕ) : ZMod m)), ((((x - 1) / 2 + 1 : ℕ) : ZMod m))) := by rw [hbase]
      _ = ((((x + 1 : ℕ) : ZMod m)), ((((x - 1) / 2 + 2 : ℕ) : ZMod m))) := by
            simpa using
              returnMap0CaseIIXY_odd_generic_even_column_mid_step (m := m) hx3 (by omega) hxodd
  have hprefix :
      ((F^[x]) (linePoint0 (m := m) xFin)) =
        ((((x + 1 : ℕ) : ZMod m)), (((x : ℕ) : ZMod m))) := by
    have hsplit :
        ((F^[x]) (linePoint0 (m := m) xFin)) =
          ((F^[x - 1]) ((F^[1]) (linePoint0 (m := m) xFin))) := by
      simpa [show x - 1 + 1 = x by omega] using
        (Function.iterate_add_apply F (x - 1) 1 (linePoint0 (m := m) xFin))
    calc
      ((F^[x]) (linePoint0 (m := m) xFin))
          = ((F^[x - 1]) ((F^[1]) (linePoint0 (m := m) xFin))) := hsplit
      _ = ((F^[x - 1]) ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m))) := by rw [h1]
      _ = ((((x + 1 : ℕ) : ZMod m)), (((x : ℕ) : ZMod m))) := by
            simpa using iterate_returnMap0CaseIIXY_odd_generic_to_A
              (m := m) (x := x) hx3 (by omega) hxodd
  have hA :
      ((F^[x + 1]) (linePoint0 (m := m) xFin)) =
        ((((x + 2 : ℕ) : ZMod m)), (((x + 2 : ℕ) : ZMod m))) := by
    calc
      ((F^[x + 1]) (linePoint0 (m := m) xFin))
          = F (((F^[x]) (linePoint0 (m := m) xFin))) := by
              rw [show x + 1 = 1 + x by omega, Function.iterate_add_apply]
              simp
      _ = F ((((x + 1 : ℕ) : ZMod m)), (((x : ℕ) : ZMod m))) := by rw [hprefix]
      _ = ((((x + 2 : ℕ) : ZMod m)), (((x + 2 : ℕ) : ZMod m))) := by
            simpa using returnMap0CaseIIXY_A_line (m := m) (y := x) (by omega) (by omega)
  by_cases hn1 : n = 1
  · rw [hn1, h1]
    simpa using
      (not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
        (a := (((x + 1 : ℕ) : ZMod m))) (n := 1)
        (by decide) (by
          have hm9 : 9 < m := Fact.out
          omega))
  · by_cases hlow : n ≤ b + 1
    · have hn2 : 2 ≤ n := by omega
      let t : ℕ := n - 2
      have htle : t ≤ b - 1 := by
        dsimp [t]
        omega
      have hnEq : n = t + 2 := by
        dsimp [t]
        omega
      have hiter :
          ((F^[n]) (linePoint0 (m := m) xFin)) =
            ((((x + 1 : ℕ) : ZMod m)), (((2 + t : ℕ) : ZMod m))) := by
        calc
          ((F^[n]) (linePoint0 (m := m) xFin))
              = ((F^[t]) ((F^[2]) (linePoint0 (m := m) xFin))) := by
                  rw [hnEq, Function.iterate_add_apply]
          _ = ((F^[t]) ((((x + 1 : ℕ) : ZMod m)), (2 : ZMod m))) := by rw [h2]
          _ = ((((x + 1 : ℕ) : ZMod m)), (((2 + t : ℕ) : ZMod m))) := by
                dsimp [b] at htle
                simpa using
                  iterate_returnMap0CaseIIXY_odd_generic_even_column_lower_partial
                    (m := m) (x := x) (t := t) hx3 (by omega) hxodd htle
      rw [hiter]
      exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
        (a := (((x + 1 : ℕ) : ZMod m))) (by
          dsimp [t]
          omega) (by
          have hm9 : 9 < m := Fact.out
          dsimp [t]
          omega)
    · by_cases hmid : n = b + 2
      · rw [hmid, hmidPoint]
        exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
          (a := (((x + 1 : ℕ) : ZMod m))) (by
            omega) (by
            have hm9 : 9 < m := Fact.out
            omega)
      · by_cases hupper : n ≤ x
        · let t : ℕ := n - (b + 2)
          have ht0 : 0 < t := by
            dsimp [t]
            omega
          have htle : t ≤ b - 1 := by
            dsimp [t, b]
            rcases hxodd with ⟨r, hr⟩
            rw [hr] at hupper ⊢
            omega
          have hnEq : n = t + (b + 2) := by
            dsimp [t]
            omega
          have hiter :
              ((F^[n]) (linePoint0 (m := m) xFin)) =
                ((((x + 1 : ℕ) : ZMod m)), (((((x - 1) / 2 + 2) + t : ℕ) : ZMod m))) := by
            calc
              ((F^[n]) (linePoint0 (m := m) xFin))
                  = ((F^[t]) ((F^[b + 2]) (linePoint0 (m := m) xFin))) := by
                      rw [hnEq, Function.iterate_add_apply]
              _ = ((F^[t]) ((((x + 1 : ℕ) : ZMod m)), ((((x - 1) / 2 + 2 : ℕ) : ZMod m)))) := by
                    rw [hmidPoint]
              _ = ((((x + 1 : ℕ) : ZMod m)), (((((x - 1) / 2 + 2) + t : ℕ) : ZMod m))) := by
                    dsimp [b] at htle
                    simpa using
                      iterate_returnMap0CaseIIXY_odd_generic_even_column_upper_partial
                        (m := m) (x := x) (t := t) hx3 (by omega) hxodd htle
          rw [hiter]
          exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
            (a := (((x + 1 : ℕ) : ZMod m))) (by
              dsimp [b, t]
              omega) (by
              have hm9 : 9 < m := Fact.out
              dsimp [b, t]
              omega)
        · by_cases hAeq : n = x + 1
          · rw [hAeq, hA]
            exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
              (a := (((x + 2 : ℕ) : ZMod m))) (by
                have hm9 : 9 < m := Fact.out
                omega) (by
                have hm9 : 9 < m := Fact.out
                omega)
          · by_cases hpreR : n ≤ x + 1 + (m - x - 3) / 2
            · let t : ℕ := n - (x + 1)
              have ht0 : 0 < t := by
                dsimp [t]
                omega
              have htle : t ≤ (m - x - 3) / 2 := by
                dsimp [t]
                omega
              have hnEq : n = t + (x + 1) := by
                dsimp [t]
                omega
              have hiter :
                  ((F^[n]) (linePoint0 (m := m) xFin)) =
                    ((F^[t]) ((((x + 2 : ℕ) : ZMod m)), (((x + 2 : ℕ) : ZMod m)))) := by
                calc
                  ((F^[n]) (linePoint0 (m := m) xFin))
                      = ((F^[t]) ((F^[x + 1]) (linePoint0 (m := m) xFin))) := by
                          rw [hnEq, Function.iterate_add_apply]
                  _ = ((F^[t]) ((((x + 2 : ℕ) : ZMod m)), (((x + 2 : ℕ) : ZMod m)))) := by
                        rw [hA]
              rw [hiter]
              exact hfirst_upper_column_partial (m := m)
                (c := x + 2) (y0 := x + 2) (by omega) (by omega) (by omega) (by omega)
                t ht0 (by
                  dsimp [t]
                  rcases hxodd with ⟨r, hr⟩
                  rw [hr] at hpreR ⊢
                  omega)
            · by_cases hReq : n = x + 2 + (m - x - 3) / 2
              · rw [hReq]
                have hiter :
                    ((F^[x + 2 + (m - x - 3) / 2]) (linePoint0 (m := m) xFin)) =
                      ((((x + 4 : ℕ) : ZMod m)), ((((m + x + 5) / 2 : ℕ) : ZMod m))) := by
                  simpa [xFin] using
                    iterate_returnMap0CaseIIXY_odd_generic_to_R (m := m) hm hx3 (by omega) hxodd
                rw [hiter]
                exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
                  (a := (((x + 4 : ℕ) : ZMod m))) (by
                    rcases hxodd with ⟨r, hr⟩
                    rw [hr]
                    omega) (by
                    have hm9 : 9 < m := Fact.out
                    rcases hxodd with ⟨r, hr⟩
                    rw [hr]
                    omega)
              · let t : ℕ := n - (x + 2 + (m - x - 3) / 2)
                have ht0 : 0 < t := by
                  dsimp [t]
                  omega
                have ht : t < (m - x - 5) / 2 := by
                  dsimp [t]
                  rcases hxodd with ⟨r, hr⟩
                  rw [hr] at ⊢
                  omega
                have hnEq : n = t + (x + 2 + (m - x - 3) / 2) := by
                  dsimp [t]
                  omega
                have hR :
                    ((F^[x + 2 + (m - x - 3) / 2]) (linePoint0 (m := m) xFin)) =
                      ((((x + 4 : ℕ) : ZMod m)), ((((m + x + 5) / 2 : ℕ) : ZMod m))) := by
                  simpa [xFin] using
                    iterate_returnMap0CaseIIXY_odd_generic_to_R (m := m) hm hx3 (by omega) hxodd
                have hiter :
                    ((F^[n]) (linePoint0 (m := m) xFin)) =
                      ((F^[t]) ((((x + 4 : ℕ) : ZMod m)), ((((m + x + 5) / 2 : ℕ) : ZMod m)))) := by
                  calc
                    ((F^[n]) (linePoint0 (m := m) xFin))
                        = ((F^[t]) ((F^[x + 2 + (m - x - 3) / 2]) (linePoint0 (m := m) xFin))) := by
                            rw [hnEq, Function.iterate_add_apply]
                    _ = ((F^[t]) ((((x + 4 : ℕ) : ZMod m)), ((((m + x + 5) / 2 : ℕ) : ZMod m)))) := by
                          rw [hR]
                rw [hiter]
                exact hfirst_wrapped_upper_column_to_zero (m := m) hm
                  (c := x + 4) (y0 := (m + x + 5) / 2) (by omega) (by omega)
                  (by
                    rcases hxodd with ⟨r, hr⟩
                    refine ⟨r + 2, ?_⟩
                    omega)
                  (by omega) (by omega) t ht0 (by
                    rcases hxodd with ⟨r, hr⟩
                    rw [hr]
                    omega)

private theorem hfirst_line_odd_generic_caseII_mod_ten_to_R [Fact (9 < m)] (hm : m % 12 = 10)
    {x : ℕ} (hx3 : 3 ≤ x) (hxle : x ≤ m - 7) (hxodd : Odd x) :
    ∀ n, 0 < n →
      n ≤ x + 2 + (m - x - 3) / 2 →
        (returnMap0CaseIIXY (m := m)^[n])
            (linePoint0 (m := m) (⟨x, by omega⟩ : Fin m)) ∉
          Set.range (linePoint0 (m := m)) := by
  let F := returnMap0CaseIIXY (m := m)
  let xFin : Fin m := ⟨x, by omega⟩
  let b : ℕ := (x - 1) / 2
  intro n hn0 hnle
  have hm0 : 0 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (0 < m) := ⟨hm0⟩
  have hb1 : 1 ≤ b := by
    dsimp [b]
    rcases hxodd with ⟨r, hr⟩
    rw [hr]
    omega
  have h1 :
      ((F^[1]) (linePoint0 (m := m) xFin)) =
        ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m)) := by
    simpa [Function.iterate_one, linePoint0, xFin] using
      returnMap0CaseIIXY_line_start_generic (m := m) (x := x) (by omega) (by omega)
  have h2 :
      ((F^[2]) (linePoint0 (m := m) xFin)) =
        ((((x + 1 : ℕ) : ZMod m)), (2 : ZMod m)) := by
    calc
      ((F^[2]) (linePoint0 (m := m) xFin))
          = F (((F^[1]) (linePoint0 (m := m) xFin))) := by
              simp [Function.iterate_succ_apply']
      _ = F ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m)) := by rw [h1]
      _ = ((((x + 1 : ℕ) : ZMod m)), (2 : ZMod m)) := by
            exact returnMap0CaseIIXY_odd_generic_even_column_one_step (m := m) hx3 (by omega) hxodd
  have hmidPoint :
      ((F^[b + 2]) (linePoint0 (m := m) xFin)) =
        ((((x + 1 : ℕ) : ZMod m)), ((((x - 1) / 2 + 2 : ℕ) : ZMod m))) := by
    have hbase :
        ((F^[b + 1]) (linePoint0 (m := m) xFin)) =
          ((((x + 1 : ℕ) : ZMod m)), ((((x - 1) / 2 + 1 : ℕ) : ZMod m))) := by
      calc
        ((F^[b + 1]) (linePoint0 (m := m) xFin))
            = ((F^[b - 1]) ((F^[2]) (linePoint0 (m := m) xFin))) := by
                rw [show b + 1 = (b - 1) + 2 by omega, Function.iterate_add_apply]
        _ = ((F^[b - 1]) ((((x + 1 : ℕ) : ZMod m)), (2 : ZMod m))) := by rw [h2]
        _ = ((((x + 1 : ℕ) : ZMod m)), (((2 + (b - 1) : ℕ) : ZMod m))) := by
              simpa using
                iterate_returnMap0CaseIIXY_odd_generic_even_column_lower_partial
                  (m := m) (x := x) (t := b - 1) hx3 (by omega) hxodd le_rfl
        _ = ((((x + 1 : ℕ) : ZMod m)), ((((x - 1) / 2 + 1 : ℕ) : ZMod m))) := by
              dsimp [b]
              have hsum : 2 + ((x - 1) / 2 - 1) = (x - 1) / 2 + 1 := by omega
              simp [hsum]
    calc
      ((F^[b + 2]) (linePoint0 (m := m) xFin))
          = F (((F^[b + 1]) (linePoint0 (m := m) xFin))) := by
              rw [show b + 2 = 1 + (b + 1) by omega, Function.iterate_add_apply]
              simp
      _ = F ((((x + 1 : ℕ) : ZMod m)), ((((x - 1) / 2 + 1 : ℕ) : ZMod m))) := by rw [hbase]
      _ = ((((x + 1 : ℕ) : ZMod m)), ((((x - 1) / 2 + 2 : ℕ) : ZMod m))) := by
            simpa using
              returnMap0CaseIIXY_odd_generic_even_column_mid_step (m := m) hx3 (by omega) hxodd
  have hprefix :
      ((F^[x]) (linePoint0 (m := m) xFin)) =
        ((((x + 1 : ℕ) : ZMod m)), (((x : ℕ) : ZMod m))) := by
    have hsplit :
        ((F^[x]) (linePoint0 (m := m) xFin)) =
          ((F^[x - 1]) ((F^[1]) (linePoint0 (m := m) xFin))) := by
      simpa [show x - 1 + 1 = x by omega] using
        (Function.iterate_add_apply F (x - 1) 1 (linePoint0 (m := m) xFin))
    calc
      ((F^[x]) (linePoint0 (m := m) xFin))
          = ((F^[x - 1]) ((F^[1]) (linePoint0 (m := m) xFin))) := hsplit
      _ = ((F^[x - 1]) ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m))) := by rw [h1]
      _ = ((((x + 1 : ℕ) : ZMod m)), (((x : ℕ) : ZMod m))) := by
            simpa using iterate_returnMap0CaseIIXY_odd_generic_to_A
              (m := m) (x := x) hx3 (by omega) hxodd
  have hA :
      ((F^[x + 1]) (linePoint0 (m := m) xFin)) =
        ((((x + 2 : ℕ) : ZMod m)), (((x + 2 : ℕ) : ZMod m))) := by
    calc
      ((F^[x + 1]) (linePoint0 (m := m) xFin))
          = F (((F^[x]) (linePoint0 (m := m) xFin))) := by
              rw [show x + 1 = 1 + x by omega, Function.iterate_add_apply]
              simp
      _ = F ((((x + 1 : ℕ) : ZMod m)), (((x : ℕ) : ZMod m))) := by rw [hprefix]
      _ = ((((x + 2 : ℕ) : ZMod m)), (((x + 2 : ℕ) : ZMod m))) := by
            simpa using returnMap0CaseIIXY_A_line (m := m) (y := x) (by omega) (by omega)
  by_cases hn1 : n = 1
  · rw [hn1, h1]
    simpa using
      (not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
        (a := (((x + 1 : ℕ) : ZMod m))) (n := 1)
        (by decide) (by
          have hm9 : 9 < m := Fact.out
          omega))
  · by_cases hlow : n ≤ b + 1
    · have hn2 : 2 ≤ n := by omega
      let t : ℕ := n - 2
      have htle : t ≤ b - 1 := by
        dsimp [t]
        omega
      have hnEq : n = t + 2 := by
        dsimp [t]
        omega
      have hiter :
          ((F^[n]) (linePoint0 (m := m) xFin)) =
            ((((x + 1 : ℕ) : ZMod m)), (((2 + t : ℕ) : ZMod m))) := by
        calc
          ((F^[n]) (linePoint0 (m := m) xFin))
              = ((F^[t]) ((F^[2]) (linePoint0 (m := m) xFin))) := by
                  rw [hnEq, Function.iterate_add_apply]
          _ = ((F^[t]) ((((x + 1 : ℕ) : ZMod m)), (2 : ZMod m))) := by rw [h2]
          _ = ((((x + 1 : ℕ) : ZMod m)), (((2 + t : ℕ) : ZMod m))) := by
                dsimp [b] at htle
                simpa using
                  iterate_returnMap0CaseIIXY_odd_generic_even_column_lower_partial
                    (m := m) (x := x) (t := t) hx3 (by omega) hxodd htle
      rw [hiter]
      exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
        (a := (((x + 1 : ℕ) : ZMod m))) (by
          dsimp [t]
          omega) (by
          have hm9 : 9 < m := Fact.out
          dsimp [t]
          omega)
    · by_cases hmid : n = b + 2
      · rw [hmid, hmidPoint]
        exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
          (a := (((x + 1 : ℕ) : ZMod m))) (by
            omega) (by
            have hm9 : 9 < m := Fact.out
            omega)
      · by_cases hupper : n ≤ x
        · let t : ℕ := n - (b + 2)
          have ht0 : 0 < t := by
            dsimp [t]
            omega
          have htle : t ≤ b - 1 := by
            dsimp [t, b]
            rcases hxodd with ⟨r, hr⟩
            rw [hr] at hupper ⊢
            omega
          have hnEq : n = t + (b + 2) := by
            dsimp [t]
            omega
          have hiter :
              ((F^[n]) (linePoint0 (m := m) xFin)) =
                ((((x + 1 : ℕ) : ZMod m)), (((((x - 1) / 2 + 2) + t : ℕ) : ZMod m))) := by
            calc
              ((F^[n]) (linePoint0 (m := m) xFin))
                  = ((F^[t]) ((F^[b + 2]) (linePoint0 (m := m) xFin))) := by
                      rw [hnEq, Function.iterate_add_apply]
              _ = ((F^[t]) ((((x + 1 : ℕ) : ZMod m)), ((((x - 1) / 2 + 2 : ℕ) : ZMod m)))) := by
                    rw [hmidPoint]
              _ = ((((x + 1 : ℕ) : ZMod m)), (((((x - 1) / 2 + 2) + t : ℕ) : ZMod m))) := by
                    dsimp [b] at htle
                    simpa using
                      iterate_returnMap0CaseIIXY_odd_generic_even_column_upper_partial
                        (m := m) (x := x) (t := t) hx3 (by omega) hxodd htle
          rw [hiter]
          exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
            (a := (((x + 1 : ℕ) : ZMod m))) (by
              dsimp [b, t]
              omega) (by
              have hm9 : 9 < m := Fact.out
              dsimp [b, t]
              omega)
        · by_cases hAeq : n = x + 1
          · rw [hAeq, hA]
            exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
              (a := (((x + 2 : ℕ) : ZMod m))) (by
                have hm9 : 9 < m := Fact.out
                omega) (by
                have hm9 : 9 < m := Fact.out
                omega)
          · by_cases hpreR : n ≤ x + 1 + (m - x - 3) / 2
            · let t : ℕ := n - (x + 1)
              have ht0 : 0 < t := by
                dsimp [t]
                omega
              have hnEq : n = t + (x + 1) := by
                dsimp [t]
                omega
              have hiter :
                  ((F^[n]) (linePoint0 (m := m) xFin)) =
                    ((F^[t]) ((((x + 2 : ℕ) : ZMod m)), (((x + 2 : ℕ) : ZMod m)))) := by
                calc
                  ((F^[n]) (linePoint0 (m := m) xFin))
                      = ((F^[t]) ((F^[x + 1]) (linePoint0 (m := m) xFin))) := by
                          rw [hnEq, Function.iterate_add_apply]
                  _ = ((F^[t]) ((((x + 2 : ℕ) : ZMod m)), (((x + 2 : ℕ) : ZMod m)))) := by
                        rw [hA]
              rw [hiter]
              exact hfirst_upper_column_partial (m := m)
                (c := x + 2) (y0 := x + 2) (by omega) (by omega) (by omega) (by omega)
                t ht0 (by
                  dsimp [t]
                  rcases hxodd with ⟨r, hr⟩
                  rw [hr] at hpreR ⊢
                  omega)
            · by_cases hReq : n = x + 2 + (m - x - 3) / 2
              · rw [hReq]
                have hiter :
                    ((F^[x + 2 + (m - x - 3) / 2]) (linePoint0 (m := m) xFin)) =
                      ((((x + 4 : ℕ) : ZMod m)), ((((m + x + 5) / 2 : ℕ) : ZMod m))) := by
                  simpa [xFin] using
                    iterate_returnMap0CaseIIXY_odd_generic_to_R (m := m) hm hx3 (by omega) hxodd
                rw [hiter]
                exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
                  (a := (((x + 4 : ℕ) : ZMod m))) (by
                    rcases hxodd with ⟨r, hr⟩
                    rw [hr]
                    omega) (by
                    have hm9 : 9 < m := Fact.out
                    rcases hxodd with ⟨r, hr⟩
                    rw [hr]
                    omega)
              · exfalso
                omega

theorem hfirst_line_odd_generic_caseII_mod_ten [Fact (9 < m)] (hm : m % 12 = 10)
    {x : ℕ} (hx3 : 3 ≤ x) (hxle : x ≤ m - 7) (hxodd : Odd x) :
    ∀ n, 0 < n →
      n < rho0CaseII (m := m) (⟨x, by omega⟩ : Fin m) →
        (returnMap0CaseIIXY (m := m)^[n])
            (linePoint0 (m := m) (⟨x, by omega⟩ : Fin m)) ∉
          Set.range (linePoint0 (m := m)) := by
  intro n hn0 hnlt
  by_cases hsafe : x ≤ m - 11
  · exact hfirst_line_odd_generic_caseII_mod_ten_safe
      (m := m) hm hx3 hsafe hxodd n hn0 hnlt
  · have hcases : x = m - 9 ∨ x = m - 7 := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rcases hxodd with ⟨r, hr⟩
      rw [hq] at hxle hsafe ⊢
      rw [hr] at hxle hsafe ⊢
      omega
    rcases hcases with hxm9 | hxm7
    · subst hxm9
      have hrho : rho0CaseII (m := m) (⟨m - 9, by omega⟩ : Fin m) = m - 2 := by
        simpa using
          rho0CaseII_other (m := m) (x := m - 9) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) (by omega)
      have hnm : n < m - 2 := by
        simpa [hrho] using hnlt
      by_cases hRle : n ≤ m - 4
      · have hbound : n ≤ (m - 9) + 2 + (m - (m - 9) - 3) / 2 := by omega
        simpa using hfirst_line_odd_generic_caseII_mod_ten_to_R
          (m := m) hm (x := m - 9) (by omega) (by omega) hxodd n hn0 hbound
      · have hnEq : n = m - 3 := by
          omega
        rw [hnEq]
        have hR :
            ((returnMap0CaseIIXY (m := m)^[m - 4])
                (linePoint0 (m := m) (⟨m - 9, by omega⟩ : Fin m))) =
              ((((m - 5 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) := by
          have hmain := iterate_returnMap0CaseIIXY_odd_generic_to_R (m := m) hm
            (x := m - 9) (by omega) (by omega) hxodd
          have hsteps : m - 9 + 2 + (m - (m - 9) - 3) / 2 = m - 4 := by omega
          have hfst : m - 9 + 4 = m - 5 := by omega
          have hsnd : (m + (m - 9) + 5) / 2 = m - 2 := by omega
          simpa [hsteps, hfst, hsnd] using hmain
        have hiter :
            ((returnMap0CaseIIXY (m := m)^[m - 3])
                (linePoint0 (m := m) (⟨m - 9, by omega⟩ : Fin m))) =
              ((((m - 5 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) := by
          calc
            ((returnMap0CaseIIXY (m := m)^[m - 3])
                (linePoint0 (m := m) (⟨m - 9, by omega⟩ : Fin m)))
                = returnMap0CaseIIXY (m := m)
                    (((returnMap0CaseIIXY (m := m)^[m - 4])
                      (linePoint0 (m := m) (⟨m - 9, by omega⟩ : Fin m)))) := by
                        rw [show m - 3 = 1 + (m - 4) by omega, Function.iterate_add_apply]
                        simp
            _ = returnMap0CaseIIXY (m := m)
                  ((((m - 5 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) := by
                    rw [hR]
            _ = ((((m - 5 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) := by
                  simpa using returnMap0CaseIIXY_wrapped_upper_column_m_sub_two
                    (m := m) (c := m - 5) (by omega) (by omega)
        rw [hiter]
        exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
          (a := (((m - 5 : ℕ) : ZMod m))) (by omega) (by omega)
    · subst hxm7
      have hrho : rho0CaseII (m := m) (⟨m - 7, by omega⟩ : Fin m) = m - 2 := by
        simpa using
          rho0CaseII_other (m := m) (x := m - 7) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) (by omega)
      have hnm : n < m - 2 := by
        simpa [hrho] using hnlt
      have hbound : n ≤ (m - 7) + 2 + (m - (m - 7) - 3) / 2 := by
        omega
      simpa using hfirst_line_odd_generic_caseII_mod_ten_to_R
        (m := m) hm (x := m - 7) (by omega) (by omega) hxodd n hn0 hbound

theorem hfirst_line_even_generic_caseII_mod_ten [Fact (9 < m)] (hm : m % 12 = 10)
    {x : ℕ} (hx4 : 4 ≤ x) (hxle : x ≤ m - 8) (hxeven : Even x) :
    ∀ n, 0 < n →
      n < rho0CaseII (m := m) (⟨x, by omega⟩ : Fin m) →
        (returnMap0CaseIIXY (m := m)^[n])
            (linePoint0 (m := m) (⟨x, by omega⟩ : Fin m)) ∉
          Set.range (linePoint0 (m := m)) := by
  let F := returnMap0CaseIIXY (m := m)
  let xFin : Fin m := ⟨x, by omega⟩
  intro n hn0 hnlt
  have hm0 : 0 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (0 < m) := ⟨hm0⟩
  have hrho : rho0CaseII (m := m) xFin = m - 2 := by
    simpa [xFin] using
      rho0CaseII_other (m := m) (x := x) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)
  have hnm : n < m - 2 := by
    simpa [xFin, hrho] using hnlt
  have h1 :
      ((F^[1]) (linePoint0 (m := m) xFin)) =
        ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m)) := by
    simpa [Function.iterate_one, linePoint0, xFin] using
      returnMap0CaseIIXY_line_start_generic (m := m) (x := x) (by omega) (by omega)
  have h2 :
      ((F^[2]) (linePoint0 (m := m) xFin)) =
        ((((x + 1 : ℕ) : ZMod m)), (2 : ZMod m)) := by
    calc
      ((F^[2]) (linePoint0 (m := m) xFin))
          = F (((F^[1]) (linePoint0 (m := m) xFin))) := by
              simp [Function.iterate_succ_apply']
      _ = F ((((x + 1 : ℕ) : ZMod m)), (1 : ZMod m)) := by rw [h1]
      _ = ((((x + 1 : ℕ) : ZMod m)), (2 : ZMod m)) := by
            exact returnMap0CaseIIXY_even_generic_odd_column_one_step (m := m) hx4 (by omega)
  by_cases hn1 : n = 1
  · rw [hn1, h1]
    simpa using
      (not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
        (a := (((x + 1 : ℕ) : ZMod m))) (n := 1)
        (by decide) (by
          have hm9 : 9 < m := Fact.out
          omega))
  · by_cases hprefix : n ≤ x / 2
    · have hn2 : 2 ≤ n := by omega
      let t : ℕ := n - 2
      have htle : t ≤ x / 2 - 2 := by
        dsimp [t]
        omega
      have hnEq : n = t + 2 := by
        dsimp [t]
        omega
      have hiter :
          ((F^[n]) (linePoint0 (m := m) xFin)) =
            ((((x + 1 : ℕ) : ZMod m)), (((2 + t : ℕ) : ZMod m))) := by
        calc
          ((F^[n]) (linePoint0 (m := m) xFin))
              = ((F^[t]) ((F^[2]) (linePoint0 (m := m) xFin))) := by
                  rw [hnEq, Function.iterate_add_apply]
          _ = ((F^[t]) ((((x + 1 : ℕ) : ZMod m)), (2 : ZMod m))) := by rw [h2]
          _ = ((((x + 1 : ℕ) : ZMod m)), (((2 + t : ℕ) : ZMod m))) := by
                simpa using
                  iterate_returnMap0CaseIIXY_even_generic_odd_column_lower_partial
                    (m := m) (x := x) (t := t) hx4 (by omega) htle
      rw [hiter]
      exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
        (a := (((x + 1 : ℕ) : ZMod m))) (by
          dsimp [t]
          omega) (by
          have hm9 : 9 < m := Fact.out
          dsimp [t]
          omega)
    · by_cases hR : n = x / 2 + 1
      · rw [hR]
        have hiter :
            ((F^[x / 2 + 1]) (linePoint0 (m := m) xFin)) =
              ((((x + 3 : ℕ) : ZMod m)), (((x / 2 + 2 : ℕ) : ZMod m))) := by
          simpa [xFin] using
            iterate_returnMap0CaseIIXY_even_generic_to_R (m := m) (x := x) hx4 (by omega) hxeven
        rw [hiter]
        exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
          (a := (((x + 3 : ℕ) : ZMod m))) (by
            have hm9 : 9 < m := Fact.out
            omega) (by
            have hm9 : 9 < m := Fact.out
            omega)
      · by_cases hmid : n ≤ x + 1
        · let t : ℕ := n - (x / 2 + 1)
          have ht0 : 0 < t := by
            dsimp [t]
            omega
          have htle : t ≤ x / 2 := by
            rcases hxeven with ⟨r, hr⟩
            dsimp [t]
            rw [hr]
            omega
          have hnEq : n = t + (x / 2 + 1) := by
            dsimp [t]
            omega
          have hRstart :
              ((F^[x / 2 + 1]) (linePoint0 (m := m) xFin)) =
                ((((x + 3 : ℕ) : ZMod m)), (((x / 2 + 2 : ℕ) : ZMod m))) := by
            simpa [xFin] using
              iterate_returnMap0CaseIIXY_even_generic_to_R (m := m) (x := x) hx4 (by omega) hxeven
          have hiter :
              ((F^[n]) (linePoint0 (m := m) xFin)) =
                ((((x + 3 : ℕ) : ZMod m)), (((x / 2 + 2 + t : ℕ) : ZMod m))) := by
            calc
              ((F^[n]) (linePoint0 (m := m) xFin))
                  = ((F^[t]) ((F^[x / 2 + 1]) (linePoint0 (m := m) xFin))) := by
                      rw [hnEq, Function.iterate_add_apply]
              _ = ((F^[t]) ((((x + 3 : ℕ) : ZMod m)), (((x / 2 + 2 : ℕ) : ZMod m)))) := by
                    rw [hRstart]
              _ = ((((x + 3 : ℕ) : ZMod m)), (((x / 2 + 2 + t : ℕ) : ZMod m))) := by
                    simpa using
                      iterate_returnMap0CaseIIXY_even_generic_after_R_partial
                        (m := m) (x := x) (t := t) hx4 (by omega) hxeven htle
          rw [hiter]
          exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
            (a := (((x + 3 : ℕ) : ZMod m))) (by
              dsimp [t]
              omega) (by
              have hm9 : 9 < m := Fact.out
              dsimp [t]
              omega)
        · by_cases hA : n = x + 2
          · rw [hA]
            have hiter :
                ((F^[x + 2]) (linePoint0 (m := m) xFin)) =
                  ((((x + 4 : ℕ) : ZMod m)), (((x + 4 : ℕ) : ZMod m))) := by
              simpa [xFin] using
                iterate_returnMap0CaseIIXY_even_generic_to_A (m := m) (x := x) hx4 (by omega) hxeven
            rw [hiter]
            exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
              (a := (((x + 4 : ℕ) : ZMod m))) (by
                have hm9 : 9 < m := Fact.out
                omega) (by
                have hm9 : 9 < m := Fact.out
                omega)
          · let t : ℕ := n - (x + 2)
            have ht0 : 0 < t := by
              dsimp [t]
              omega
            have ht : t < m - x - 4 := by
              dsimp [t]
              omega
            have hnEq : n = t + (x + 2) := by
              dsimp [t]
              omega
            have hAstart :
                ((F^[x + 2]) (linePoint0 (m := m) xFin)) =
                  ((((x + 4 : ℕ) : ZMod m)), (((x + 4 : ℕ) : ZMod m))) := by
              simpa [xFin] using
                iterate_returnMap0CaseIIXY_even_generic_to_A (m := m) (x := x) hx4 (by omega) hxeven
            have hiter :
                ((F^[n]) (linePoint0 (m := m) xFin)) =
                  ((F^[t]) ((((x + 4 : ℕ) : ZMod m)), (((x + 4 : ℕ) : ZMod m)))) := by
              calc
                ((F^[n]) (linePoint0 (m := m) xFin))
                    = ((F^[t]) ((F^[x + 2]) (linePoint0 (m := m) xFin))) := by
                        rw [hnEq, Function.iterate_add_apply]
                _ = ((F^[t]) ((((x + 4 : ℕ) : ZMod m)), (((x + 4 : ℕ) : ZMod m)))) := by
                      rw [hAstart]
            rw [hiter]
            exact hfirst_even_generic_final_column_to_zero
              (m := m) hm hx4 hxle hxeven t ht0 ht

theorem hfirst_line_m_sub_six_caseII_mod_ten [Fact (9 < m)] (hm : m % 12 = 10) :
    ∀ n, 0 < n →
      n < rho0CaseII (m := m) (⟨m - 6, by omega⟩ : Fin m) →
        (returnMap0CaseIIXY (m := m)^[n])
            (linePoint0 (m := m) (⟨m - 6, by omega⟩ : Fin m)) ∉
          Set.range (linePoint0 (m := m)) := by
  let F := returnMap0CaseIIXY (m := m)
  let xFin : Fin m := ⟨m - 6, by omega⟩
  let start : P0Coord m := linePoint0 (m := m) xFin
  intro n hn0 hnlt
  have hm0 : 0 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (0 < m) := ⟨hm0⟩
  have hrho : rho0CaseII (m := m) xFin = 2 * m - 4 := by
    simpa [xFin] using
      rho0CaseII_eq_two_mul_sub_four_of_val_eq_m_sub_six (m := m) (x := xFin) rfl
  have hnm : n < 2 * m - 4 := by
    simpa [xFin, hrho] using hnlt
  have hx4 : 4 ≤ m - 6 := by
    have hm9 : 9 < m := Fact.out
    omega
  have hxleR : m - 6 ≤ m - 4 := by omega
  have hxeven : Even (m - 6) := by
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rw [hq]
    refine ⟨6 * q + 2, ?_⟩
    omega
  have h1 :
      ((F^[1]) start) = ((((m - 5 : ℕ) : ZMod m)), (1 : ZMod m)) := by
    simpa [F, Function.iterate_one, start, show m - 6 + 1 = m - 5 by omega] using
      returnMap0CaseIIXY_line_start_generic (m := m) (x := m - 6) (by omega) (by omega)
  have hR :
      ((F^[m / 2 - 2]) start) =
        ((((m - 3 : ℕ) : ZMod m)), (((m / 2 - 1 : ℕ) : ZMod m))) := by
    have hmain := iterate_returnMap0CaseIIXY_even_generic_to_R
      (m := m) (x := m - 6) hx4 hxleR hxeven
    have hsteps : (m - 6) / 2 + 1 = m / 2 - 2 := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega
    have hfst : (m - 6) + 3 = m - 3 := by omega
    have hsnd : (m - 6) / 2 + 2 = m / 2 - 1 := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega
    simpa [linePoint0, hsteps, hfst, hsnd] using hmain
  have hApoint :
      ((F^[m - 4]) start) =
        ((((m - 2 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) := by
    have hpreA :
        ((F^[m / 2 - 3]) ((((m - 3 : ℕ) : ZMod m)), (((m / 2 - 1 : ℕ) : ZMod m)))) =
          ((((m - 3 : ℕ) : ZMod m)), (((m - 4 : ℕ) : ZMod m))) := by
      have hmain := iterate_returnMap0CaseIIXY_even_generic_after_R_partial
        (m := m) (x := m - 6) (t := m / 2 - 3) hx4 hxleR hxeven
          (by
            rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
            rw [hq]
            omega)
      have hstart : (m - 6) / 2 + 2 = m / 2 - 1 := by
        rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
        rw [hq]
        omega
      have hend : (m - 6) / 2 + 2 + (m / 2 - 3) = m - 4 := by
        rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
        rw [hq]
        omega
      calc
        ((F^[m / 2 - 3]) ((((m - 3 : ℕ) : ZMod m)), (((m / 2 - 1 : ℕ) : ZMod m))))
            = ((returnMap0CaseIIXY (m := m)^[m / 2 - 3])
                ((((m - 6 + 3 : ℕ) : ZMod m)), ((((m - 6) / 2 + 2 : ℕ) : ZMod m)))) := by
                  simp [F, hstart, show m - 6 + 3 = m - 3 by omega]
        _ = ((((m - 6 + 3 : ℕ) : ZMod m)), ((((m - 6) / 2 + 2 + (m / 2 - 3) : ℕ) : ZMod m))) := hmain
        _ = ((((m - 3 : ℕ) : ZMod m)), (((m - 4 : ℕ) : ZMod m))) := by
              simp [hend, show m - 6 + 3 = m - 3 by omega]
    calc
      ((F^[m - 4]) start) = F (((F^[m - 5]) start)) := by
        simpa [show 1 + (m - 5) = m - 4 by omega] using
          (Function.iterate_add_apply F 1 (m - 5) start)
      _ = F ((((m - 3 : ℕ) : ZMod m)), (((m - 4 : ℕ) : ZMod m))) := by
            have hsplit :
                ((F^[m - 5]) start) =
                  ((F^[m / 2 - 3]) ((F^[m / 2 - 2]) start)) := by
                    simpa [show (m / 2 - 3) + (m / 2 - 2) = m - 5 by
                      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
                      rw [hq]
                      omega] using
                      (Function.iterate_add_apply F (m / 2 - 3) (m / 2 - 2) start)
            rw [hsplit, hR, hpreA]
      _ = ((((m - 2 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) := by
            simpa [F, show (m - 4) + 1 = m - 3 by omega, show (m - 4) + 2 = m - 2 by omega] using
              returnMap0CaseIIXY_A_line (m := m) (y := m - 4) (by omega) (by omega)
  have hafter1 :
      ((F^[m - 3]) start) = ((1 : ZMod m), (1 : ZMod m)) := by
    calc
      ((F^[m - 3]) start) = F (((F^[m - 4]) start)) := by
        simpa [show 1 + (m - 4) = m - 3 by omega] using
          (Function.iterate_add_apply F 1 (m - 4) start)
      _ = F ((((m - 2 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) := by rw [hApoint]
      _ = ((1 : ZMod m), (1 : ZMod m)) := by
            exact returnMap0CaseIIXY_m_sub_two_m_sub_two (m := m)
  have hafter0 :
      ((F^[m - 2]) start) = ((0 : ZMod m), (1 : ZMod m)) := by
    calc
      ((F^[m - 2]) start) = F (((F^[m - 3]) start)) := by
        simpa [show 1 + (m - 3) = m - 2 by omega] using
          (Function.iterate_add_apply F 1 (m - 3) start)
      _ = F ((1 : ZMod m), (1 : ZMod m)) := by rw [hafter1]
      _ = ((0 : ZMod m), (1 : ZMod m)) := by
            exact returnMap0CaseIIXY_one_one (m := m)
  have hafter12 :
      ((F^[m - 1]) start) = ((1 : ZMod m), (2 : ZMod m)) := by
    calc
      ((F^[m - 1]) start) = F (((F^[m - 2]) start)) := by
        simpa [show 1 + (m - 2) = m - 1 by omega] using
          (Function.iterate_add_apply F 1 (m - 2) start)
      _ = F ((0 : ZMod m), (1 : ZMod m)) := by rw [hafter0]
      _ = ((1 : ZMod m), (2 : ZMod m)) := by
            exact returnMap0CaseIIXY_zero_one (m := m)
  have hmid :
      ((F^[m + (m / 2 - 2)]) start) =
        ((3 : ZMod m), (((m / 2 + 2 : ℕ) : ZMod m))) := by
    have hcol1 :
        ((F^[m / 2 - 2]) ((1 : ZMod m), (2 : ZMod m))) =
          ((1 : ZMod m), (((m / 2 : ℕ) : ZMod m))) := by
      have hmain := iterate_returnMap0CaseIIXY_one_column_lower_partial
        (m := m) hm (t := m / 2 - 2) le_rfl
      have hsum : 2 + (m / 2 - 2) = m / 2 := by
        rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
        rw [hq]
        omega
      simpa [hsum] using hmain
    have hmidStep :
        F ((1 : ZMod m), (((m / 2 : ℕ) : ZMod m))) =
          ((3 : ZMod m), (((m / 2 + 2 : ℕ) : ZMod m))) := by
      exact returnMap0CaseIIXY_one_column_mid_step (m := m) hm
    calc
      ((F^[m + (m / 2 - 2)]) start)
          = ((F^[m / 2 - 1]) ((F^[m - 1]) start)) := by
              simpa [show (m / 2 - 1) + (m - 1) = m + (m / 2 - 2) by omega] using
                (Function.iterate_add_apply F (m / 2 - 1) (m - 1) start)
      _ = ((F^[m / 2 - 1]) ((1 : ZMod m), (2 : ZMod m))) := by rw [hafter12]
      _ = F (((F^[m / 2 - 2]) ((1 : ZMod m), (2 : ZMod m)))) := by
            simpa [show 1 + (m / 2 - 2) = m / 2 - 1 by
              rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
              rw [hq]
              omega] using
              (Function.iterate_add_apply F 1 (m / 2 - 2) ((1 : ZMod m), (2 : ZMod m)))
      _ = F ((1 : ZMod m), (((m / 2 : ℕ) : ZMod m))) := by rw [hcol1]
      _ = ((3 : ZMod m), (((m / 2 + 2 : ℕ) : ZMod m))) := by
            exact hmidStep
  by_cases hprefix : n ≤ m / 2 - 3
  · by_cases hn1 : n = 1
    · rw [hn1]
      have hiter :
          ((returnMap0CaseIIXY (m := m)^[1]) (linePoint0 (m := m) xFin)) =
            ((((m - 5 : ℕ) : ZMod m)), (1 : ZMod m)) := by
        simpa [F, start, Function.iterate_one] using h1
      rw [hiter]
      simpa using
        (not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
          (a := (((m - 5 : ℕ) : ZMod m))) (n := 1)
          (by decide) (by
            have hm9 : 9 < m := Fact.out
            omega))
    · have hn2 : 2 ≤ n := by omega
      let t : ℕ := n - 2
      have ht : t ≤ (m - 6) / 2 - 2 := by
        dsimp [t]
        rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
        rw [hq] at hprefix ⊢
        omega
      have hnEq : n = t + 2 := by
        dsimp [t]
        omega
      have h2 :
          ((F^[2]) start) = ((((m - 5 : ℕ) : ZMod m)), (2 : ZMod m)) := by
        calc
          ((F^[2]) start) = F (((F^[1]) start)) := by simp [Function.iterate_succ_apply']
          _ = F ((((m - 5 : ℕ) : ZMod m)), (1 : ZMod m)) := by rw [h1]
          _ = ((((m - 5 : ℕ) : ZMod m)), (2 : ZMod m)) := by
                simpa [show (m - 6) + 1 = m - 5 by omega] using
                  returnMap0CaseIIXY_even_generic_odd_column_one_step
                    (m := m) (x := m - 6) (by omega) (by omega)
      have hiter :
          ((F^[n]) start) =
            ((((m - 5 : ℕ) : ZMod m)), (((2 + t : ℕ) : ZMod m))) := by
        calc
          ((F^[n]) start) = ((F^[t]) ((F^[2]) start)) := by
            rw [hnEq, Function.iterate_add_apply]
          _ = ((F^[t]) ((((m - 5 : ℕ) : ZMod m)), (2 : ZMod m))) := by rw [h2]
          _ = ((((m - 5 : ℕ) : ZMod m)), (((2 + t : ℕ) : ZMod m))) := by
            simpa [F, show (m - 6) + 1 = m - 5 by omega] using
              iterate_returnMap0CaseIIXY_even_generic_odd_column_lower_partial
                (m := m) (x := m - 6) (t := t) (by omega) (by omega) ht
      rw [hiter]
      exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
        (a := (((m - 5 : ℕ) : ZMod m))) (by
          dsimp [t]
          omega) (by
          have hm9 : 9 < m := Fact.out
          dsimp [t]
          omega)
  · by_cases hReq : n = m / 2 - 2
    · rw [hReq, hR]
      exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
        (a := (((m - 3 : ℕ) : ZMod m))) (by
          rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
          rw [hq]
          omega) (by
          have hm9 : 9 < m := Fact.out
          rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
          rw [hq]
          omega)
    · by_cases hupper : n ≤ m - 5
      · let t : ℕ := n - (m / 2 - 2)
        have ht0 : 0 < t := by
          dsimp [t]
          omega
        have ht : t ≤ (m - 6) / 2 := by
          dsimp [t]
          rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
          rw [hq] at hupper ⊢
          omega
        have hnEq : n = t + (m / 2 - 2) := by
          dsimp [t]
          omega
        have hiter :
            ((F^[n]) start) =
              ((((m - 3 : ℕ) : ZMod m)), (((m / 2 - 1 + t : ℕ) : ZMod m))) := by
          calc
            ((F^[n]) start) = ((F^[t]) ((F^[m / 2 - 2]) start)) := by
              rw [hnEq, Function.iterate_add_apply]
            _ = ((F^[t]) ((((m - 3 : ℕ) : ZMod m)), (((m / 2 - 1 : ℕ) : ZMod m)))) := by
              rw [hR]
            _ = ((((m - 3 : ℕ) : ZMod m)), (((m / 2 - 1 + t : ℕ) : ZMod m))) := by
              have hmain := iterate_returnMap0CaseIIXY_even_generic_after_R_partial
                (m := m) (x := m - 6) (t := t) (by omega) (by omega) hxeven ht
              have hstart : (m - 6) / 2 + 2 = m / 2 - 1 := by
                rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
                rw [hq]
                omega
              have hend : (m - 6) / 2 + 2 + t = m / 2 - 1 + t := by
                rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
                rw [hq]
                omega
              calc
                ((F^[t]) ((((m - 3 : ℕ) : ZMod m)), (((m / 2 - 1 : ℕ) : ZMod m))))
                    = ((returnMap0CaseIIXY (m := m)^[t])
                        ((((m - 6 + 3 : ℕ) : ZMod m)), ((((m - 6) / 2 + 2 : ℕ) : ZMod m)))) := by
                          simp [F, hstart, show m - 6 + 3 = m - 3 by omega]
                _ = ((((m - 6 + 3 : ℕ) : ZMod m)), ((((m - 6) / 2 + 2 + t : ℕ) : ZMod m))) := hmain
                _ = ((((m - 3 : ℕ) : ZMod m)), (((m / 2 - 1 + t : ℕ) : ZMod m))) := by
                      simp [hend, show m - 6 + 3 = m - 3 by omega]
        rw [hiter]
        exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
          (a := (((m - 3 : ℕ) : ZMod m))) (by
            rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
            rw [hq]
            dsimp [t]
            omega) (by
            have hm9 : 9 < m := Fact.out
            rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
            rw [hq]
            dsimp [t]
            omega)
      · by_cases hAeq : n = m - 4
        · rw [hAeq, hApoint]
          exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
            (a := (((m - 2 : ℕ) : ZMod m))) (by
              have hm9 : 9 < m := Fact.out
              omega) (by
              have hm9 : 9 < m := Fact.out
              omega)
        · by_cases h1eq : n = m - 3
          · rw [h1eq, hafter1]
            simpa using
              (not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
                (a := (1 : ZMod m)) (n := 1) (by decide) (by omega))
          · by_cases h0eq : n = m - 2
            · rw [h0eq, hafter0]
              simpa using
                (not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
                  (a := (0 : ZMod m)) (n := 1) (by decide) (by omega))
            · by_cases h12eq : n = m - 1
              · rw [h12eq, hafter12]
                simpa using
                  (not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
                    (a := (1 : ZMod m)) (n := 2) (by omega) (by omega))
              · by_cases honecol : n ≤ m + (m / 2 - 3)
                · let t : ℕ := n - (m - 1)
                  have ht : t ≤ m / 2 - 2 := by
                    dsimp [t]
                    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
                    rw [hq] at honecol ⊢
                    omega
                  have hnEq : n = t + (m - 1) := by
                    dsimp [t]
                    omega
                  have hiter :
                      ((F^[n]) start) =
                        ((1 : ZMod m), (((2 + t : ℕ) : ZMod m))) := by
                    calc
                      ((F^[n]) start) = ((F^[t]) ((F^[m - 1]) start)) := by
                        rw [hnEq, Function.iterate_add_apply]
                      _ = ((F^[t]) ((1 : ZMod m), (2 : ZMod m))) := by rw [hafter12]
                      _ = ((1 : ZMod m), (((2 + t : ℕ) : ZMod m))) := by
                            simpa using iterate_returnMap0CaseIIXY_one_column_lower_partial
                              (m := m) hm (t := t) ht
                  rw [hiter]
                  exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
                    (a := (1 : ZMod m)) (by
                      dsimp [t]
                      omega) (by
                      have hm9 : 9 < m := Fact.out
                      dsimp [t]
                      omega)
                · by_cases hmidEq : n = m + (m / 2 - 2)
                  · rw [hmidEq, hmid]
                    exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
                      (a := (3 : ZMod m)) (by
                        rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
                        rw [hq]
                        omega) (by
                        have hm9 : 9 < m := Fact.out
                        rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
                        rw [hq]
                        omega)
                  · let s : ℕ := n - (m + (m / 2 - 2))
                    have hs0 : 0 < s := by
                      dsimp [s]
                      omega
                    have hs : s < m - (m / 2 + 2) := by
                      dsimp [s]
                      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
                      rw [hq] at hnm ⊢
                      omega
                    have hnEq : n = s + (m + (m / 2 - 2)) := by
                      dsimp [s]
                      omega
                    have hiter :
                        ((F^[n]) start) =
                          ((F^[s]) ((3 : ZMod m), (((m / 2 + 2 : ℕ) : ZMod m)))) := by
                      calc
                        ((F^[n]) start) = ((F^[s]) ((F^[m + (m / 2 - 2)]) start)) := by
                          rw [hnEq, Function.iterate_add_apply]
                        _ = ((F^[s]) ((3 : ZMod m), (((m / 2 + 2 : ℕ) : ZMod m)))) := by rw [hmid]
                    rw [hiter]
                    simpa [F] using
                      hfirst_wrapped_upper_column_to_zero (m := m) hm
                        (c := 3) (y0 := m / 2 + 2) (by omega) (by omega) (by exact ⟨1, by omega⟩)
                        (by
                          rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
                          rw [hq]
                          omega)
                        (by
                          rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
                          rw [hq]
                          omega)
                        s hs0 hs

theorem hfirst_line_m_sub_five_caseII_mod_ten [Fact (9 < m)] (hm : m % 12 = 10) :
    ∀ n, 0 < n →
      n < rho0CaseII (m := m) (⟨m - 5, by omega⟩ : Fin m) →
        (returnMap0CaseIIXY (m := m)^[n])
            (linePoint0 (m := m) (⟨m - 5, by omega⟩ : Fin m)) ∉
          Set.range (linePoint0 (m := m)) := by
  let F := returnMap0CaseIIXY (m := m)
  let xFin : Fin m := ⟨m - 5, by omega⟩
  let start : P0Coord m := linePoint0 (m := m) xFin
  let b : ℕ := (m - 6) / 2
  intro n hn0 hnlt
  have hm0 : 0 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (0 < m) := ⟨hm0⟩
  have hrho : rho0CaseII (m := m) xFin = m - 1 := by
    simpa [xFin] using
      rho0CaseII_eq_sub_one_of_val_eq_m_sub_five (m := m) (x := xFin) rfl
  have hnm : n < m - 1 := by
    simpa [xFin, hrho] using hnlt
  have hxodd : Odd (m - 5) := by
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rw [hq]
    refine ⟨6 * q + 2, ?_⟩
    omega
  have hb1 : 1 ≤ b := by
    dsimp [b]
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rw [hq]
    omega
  have h1 :
      ((F^[1]) start) = ((((m - 4 : ℕ) : ZMod m)), (1 : ZMod m)) := by
    simpa [F, Function.iterate_one, start, show m - 5 + 1 = m - 4 by omega] using
      returnMap0CaseIIXY_line_start_generic (m := m) (x := m - 5) (by omega) (by omega)
  have h2 :
      ((F^[2]) start) = ((((m - 4 : ℕ) : ZMod m)), (2 : ZMod m)) := by
    calc
      ((F^[2]) start) = F (((F^[1]) start)) := by simp [Function.iterate_succ_apply']
      _ = F ((((m - 4 : ℕ) : ZMod m)), (1 : ZMod m)) := by rw [h1]
      _ = ((((m - 4 : ℕ) : ZMod m)), (2 : ZMod m)) := by
            simpa [show (m - 5) + 1 = m - 4 by omega] using
              returnMap0CaseIIXY_odd_generic_even_column_one_step
                (m := m) (x := m - 5) (by omega) (by omega) hxodd
  have hmidPoint :
      ((F^[b + 2]) start) =
        ((((m - 4 : ℕ) : ZMod m)), (((b + 2 : ℕ) : ZMod m))) := by
    have hbase :
        ((F^[b + 1]) start) =
          ((((m - 4 : ℕ) : ZMod m)), (((b + 1 : ℕ) : ZMod m))) := by
      calc
        ((F^[b + 1]) start) = ((F^[b - 1]) ((F^[2]) start)) := by
          rw [show b + 1 = (b - 1) + 2 by omega, Function.iterate_add_apply]
        _ = ((F^[b - 1]) ((((m - 4 : ℕ) : ZMod m)), (2 : ZMod m))) := by rw [h2]
        _ = ((((m - 4 : ℕ) : ZMod m)), (((2 + (b - 1) : ℕ) : ZMod m))) := by
              simpa [F, show m - 5 + 1 = m - 4 by omega] using
                iterate_returnMap0CaseIIXY_odd_generic_even_column_lower_partial
                  (m := m) (x := m - 5) (t := b - 1) (by omega) (by omega) hxodd le_rfl
        _ = ((((m - 4 : ℕ) : ZMod m)), (((b + 1 : ℕ) : ZMod m))) := by
              have hsum : 2 + (b - 1) = b + 1 := by omega
              simp [hsum]
    calc
      ((F^[b + 2]) start) = F (((F^[b + 1]) start)) := by
        rw [show b + 2 = 1 + (b + 1) by omega, Function.iterate_add_apply]
        simp
      _ = F ((((m - 4 : ℕ) : ZMod m)), (((b + 1 : ℕ) : ZMod m))) := by rw [hbase]
      _ = ((((m - 4 : ℕ) : ZMod m)), (((b + 2 : ℕ) : ZMod m))) := by
            have hmain := returnMap0CaseIIXY_odd_generic_even_column_mid_step
              (m := m) (x := m - 5) (by omega) (by omega) hxodd
            have hmid : ((m - 5 - 1) / 2 + 1 : ℕ) = b + 1 := by
              dsimp [b]
              omega
            simpa [show m - 5 + 1 = m - 4 by omega, hmid] using hmain
  have hApoint :
      ((F^[m - 4]) start) = ((((m - 3 : ℕ) : ZMod m)), (((m - 3 : ℕ) : ZMod m))) := by
    have hsplit :
        ((F^[m - 5]) start) =
          ((((m - 4 : ℕ) : ZMod m)), (((m - 5 : ℕ) : ZMod m))) := by
      have hstep :
          ((F^[m - 5]) start) = ((F^[m - 6]) ((F^[1]) start)) := by
        simpa [show (m - 6) + 1 = m - 5 by omega] using
          (Function.iterate_add_apply F (m - 6) 1 start)
      calc
        ((F^[m - 5]) start) = ((F^[m - 6]) ((F^[1]) start)) := hstep
        _ = ((F^[m - 6]) ((((m - 4 : ℕ) : ZMod m)), (1 : ZMod m))) := by rw [h1]
        _ = ((((m - 4 : ℕ) : ZMod m)), (((m - 5 : ℕ) : ZMod m))) := by
              simpa [F, show (m - 5) - 1 = m - 6 by omega, show m - 5 + 1 = m - 4 by omega] using
                iterate_returnMap0CaseIIXY_odd_generic_to_A
                  (m := m) (x := m - 5) (by omega) (by omega) hxodd
    calc
      ((F^[m - 4]) start) = F (((F^[m - 5]) start)) := by
        simpa [show 1 + (m - 5) = m - 4 by omega] using
          (Function.iterate_add_apply F 1 (m - 5) start)
      _ = F ((((m - 4 : ℕ) : ZMod m)), (((m - 5 : ℕ) : ZMod m))) := by rw [hsplit]
      _ = ((((m - 3 : ℕ) : ZMod m)), (((m - 3 : ℕ) : ZMod m))) := by
            simpa [F, show m - 5 + 1 = m - 4 by omega, show m - 5 + 2 = m - 3 by omega] using
              returnMap0CaseIIXY_A_line (m := m) (y := m - 5) (by omega) (by omega)
  have hupPoint :
      ((F^[m - 3]) start) = ((((m - 3 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) := by
    calc
      ((F^[m - 3]) start) = F (((F^[m - 4]) start)) := by
        simpa [show 1 + (m - 4) = m - 3 by omega] using
          (Function.iterate_add_apply F 1 (m - 4) start)
      _ = F ((((m - 3 : ℕ) : ZMod m)), (((m - 3 : ℕ) : ZMod m))) := by rw [hApoint]
      _ = ((((m - 3 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) := by
            simpa [F, show m - 3 + 1 = m - 2 by omega] using
              returnMap0CaseIIXY_upper_column_step (m := m)
                (c := m - 3) (y := m - 3) (by omega) (by omega) (by omega) (by omega)
  have hlast :
      ((F^[m - 2]) start) = ((((m - 2 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) := by
    calc
      ((F^[m - 2]) start) = F (((F^[m - 3]) start)) := by
        simpa [show 1 + (m - 3) = m - 2 by omega] using
          (Function.iterate_add_apply F 1 (m - 3) start)
      _ = F ((((m - 3 : ℕ) : ZMod m)), (((m - 2 : ℕ) : ZMod m))) := by rw [hupPoint]
      _ = ((((m - 2 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) := by
            simpa [F] using returnMap0CaseIIXY_m_sub_three_m_sub_two (m := m)
  by_cases hn1 : n = 1
  · rw [hn1, h1]
    simpa using
      (not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
        (a := (((m - 4 : ℕ) : ZMod m))) (n := 1)
        (by decide) (by
          have hm9 : 9 < m := Fact.out
          omega))
  · by_cases hlow : n ≤ b + 1
    · have hn2 : 2 ≤ n := by omega
      let t : ℕ := n - 2
      have ht : t ≤ b - 1 := by
        dsimp [t]
        omega
      have hnEq : n = t + 2 := by
        dsimp [t]
        omega
      have hiter :
          ((F^[n]) start) =
            ((((m - 4 : ℕ) : ZMod m)), (((2 + t : ℕ) : ZMod m))) := by
        calc
          ((F^[n]) start) = ((F^[t]) ((F^[2]) start)) := by
            rw [hnEq, Function.iterate_add_apply]
          _ = ((F^[t]) ((((m - 4 : ℕ) : ZMod m)), (2 : ZMod m))) := by rw [h2]
          _ = ((((m - 4 : ℕ) : ZMod m)), (((2 + t : ℕ) : ZMod m))) := by
            simpa [F, show m - 5 + 1 = m - 4 by omega] using
              iterate_returnMap0CaseIIXY_odd_generic_even_column_lower_partial
                (m := m) (x := m - 5) (t := t) (by omega) (by omega) hxodd ht
      rw [hiter]
      exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
        (a := (((m - 4 : ℕ) : ZMod m))) (by
          dsimp [t]
          omega) (by
          have hm9 : 9 < m := Fact.out
          dsimp [t]
          omega)
    · by_cases hmid : n = b + 2
      · rw [hmid, hmidPoint]
        exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
          (a := (((m - 4 : ℕ) : ZMod m))) (by
            dsimp [b]
            rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
            rw [hq]
            omega) (by
            have hm9 : 9 < m := Fact.out
            dsimp [b]
            rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
            rw [hq]
            omega)
      · by_cases hupper : n ≤ m - 5
        · let t : ℕ := n - (b + 2)
          have ht0 : 0 < t := by
            dsimp [t]
            omega
          have ht : t ≤ b - 1 := by
            dsimp [t, b]
            rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
            rw [hq] at hupper ⊢
            omega
          have hnEq : n = t + (b + 2) := by
            dsimp [t]
            omega
          have hiter :
              ((F^[n]) start) =
                ((((m - 4 : ℕ) : ZMod m)), (((b + 2 + t : ℕ) : ZMod m))) := by
            calc
              ((F^[n]) start) = ((F^[t]) ((F^[b + 2]) start)) := by
                rw [hnEq, Function.iterate_add_apply]
              _ = ((F^[t]) ((((m - 4 : ℕ) : ZMod m)), (((b + 2 : ℕ) : ZMod m)))) := by
                rw [hmidPoint]
              _ = ((((m - 4 : ℕ) : ZMod m)), (((b + 2 + t : ℕ) : ZMod m))) := by
                simpa [F, show m - 5 + 1 = m - 4 by omega] using
                  iterate_returnMap0CaseIIXY_odd_generic_even_column_upper_partial
                    (m := m) (x := m - 5) (t := t) (by omega) (by omega) hxodd ht
          rw [hiter]
          exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
            (a := (((m - 4 : ℕ) : ZMod m))) (by
              dsimp [b, t]
              omega) (by
              have hm9 : 9 < m := Fact.out
              dsimp [b, t]
              omega)
        · by_cases hAeq : n = m - 4
          · rw [hAeq, hApoint]
            exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
              (a := (((m - 3 : ℕ) : ZMod m))) (by
                have hm9 : 9 < m := Fact.out
                omega) (by
                have hm9 : 9 < m := Fact.out
                omega)
          · by_cases hupEq : n = m - 3
            · rw [hupEq, hupPoint]
              exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
                (a := (((m - 3 : ℕ) : ZMod m))) (by
                  have hm9 : 9 < m := Fact.out
                  omega) (by
                  have hm9 : 9 < m := Fact.out
                  omega)
            · have hlastEq : n = m - 2 := by omega
              rw [hlastEq, hlast]
              exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
                (a := (((m - 2 : ℕ) : ZMod m))) (by
                  have hm9 : 9 < m := Fact.out
                  omega) (by
                  have hm9 : 9 < m := Fact.out
                  omega)

theorem hfirst_line_m_sub_four_caseII_mod_ten [Fact (9 < m)] (hm : m % 12 = 10) :
    ∀ n, 0 < n →
      n < rho0CaseII (m := m) (⟨m - 4, by omega⟩ : Fin m) →
        (returnMap0CaseIIXY (m := m)^[n])
            (linePoint0 (m := m) (⟨m - 4, by omega⟩ : Fin m)) ∉
          Set.range (linePoint0 (m := m)) := by
  let F := returnMap0CaseIIXY (m := m)
  let xFin : Fin m := ⟨m - 4, by omega⟩
  let start : P0Coord m := linePoint0 (m := m) xFin
  intro n hn0 hnlt
  have hm0 : 0 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (0 < m) := ⟨hm0⟩
  have hrho : rho0CaseII (m := m) xFin = m - 2 := by
    simpa [xFin] using
      rho0CaseII_other (m := m) (x := m - 4) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)
  have hnm : n < m - 2 := by
    simpa [xFin, hrho] using hnlt
  have hx4 : 4 ≤ m - 4 := by
    have hm9 : 9 < m := Fact.out
    omega
  have hxle : m - 4 ≤ m - 4 := le_rfl
  have hxeven : Even (m - 4) := by
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rw [hq]
    refine ⟨6 * q + 3, ?_⟩
    omega
  have h1 :
      F start = ((((m - 3 : ℕ) : ZMod m)), (1 : ZMod m)) := by
    simpa [F, start, show (m - 4) + 1 = m - 3 by omega] using
      returnMap0CaseIIXY_line_start_generic (m := m) (x := m - 4) (by omega) (by omega)
  have hR :
      ((F^[m / 2 - 1]) start) =
        ((((m - 1 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m))) := by
    have hmain := iterate_returnMap0CaseIIXY_even_generic_to_R
      (m := m) (x := m - 4) hx4 hxle hxeven
    have hsteps : (m - 4) / 2 + 1 = m / 2 - 1 := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega
    have hfst : (m - 4) + 3 = m - 1 := by omega
    have hsnd : (m - 4) / 2 + 2 = m / 2 := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega
    simpa [hsteps, hfst, hsnd] using hmain
  by_cases hn1 : n = 1
  · rw [hn1]
    have hiter :
        ((returnMap0CaseIIXY (m := m)^[1]) (linePoint0 (m := m) xFin)) =
          ((((m - 3 : ℕ) : ZMod m)), (1 : ZMod m)) := by
      simpa [F, start, Function.iterate_one] using h1
    rw [hiter]
    simpa using
      (not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
        (a := (((m - 3 : ℕ) : ZMod m))) (n := 1)
        (by decide) (by
          have hm9 : 9 < m := Fact.out
          omega))
  · by_cases hlow : n ≤ m / 2 - 2
    · have hn2 : 2 ≤ n := by omega
      let t : ℕ := n - 2
      have ht : t ≤ (m - 4) / 2 - 2 := by
        dsimp [t]
        rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
        rw [hq] at hlow ⊢
        omega
      have hnEq : n = t + 2 := by
        dsimp [t]
        omega
      have h2 :
          ((F^[2]) start) = ((((m - 3 : ℕ) : ZMod m)), (2 : ZMod m)) := by
        calc
          ((F^[2]) start) = F (F start) := by simp [Function.iterate_succ_apply']
          _ = F ((((m - 3 : ℕ) : ZMod m)), (1 : ZMod m)) := by rw [h1]
          _ = ((((m - 3 : ℕ) : ZMod m)), (2 : ZMod m)) := by
                simpa [show (m - 4) + 1 = m - 3 by omega] using
                  returnMap0CaseIIXY_even_generic_odd_column_one_step (m := m)
                    (x := m - 4) (by omega) (by omega)
      have hiter :
          ((F^[n]) start) =
            ((((m - 3 : ℕ) : ZMod m)), (((2 + t : ℕ) : ZMod m))) := by
        calc
          ((F^[n]) start) = ((F^[t]) ((F^[2]) start)) := by
            rw [hnEq, Function.iterate_add_apply]
          _ = ((F^[t]) ((((m - 3 : ℕ) : ZMod m)), (2 : ZMod m))) := by rw [h2]
          _ = ((((m - 3 : ℕ) : ZMod m)), (((2 + t : ℕ) : ZMod m))) := by
            simpa [F, show (m - 4) + 1 = m - 3 by omega] using
              iterate_returnMap0CaseIIXY_even_generic_odd_column_lower_partial
                (m := m) (x := m - 4) (t := t) (by omega) (by omega) ht
      rw [hiter]
      exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
        (a := (((m - 3 : ℕ) : ZMod m))) (by
          dsimp [t]
          omega) (by
          have hm9 : 9 < m := Fact.out
          dsimp [t]
          omega)
    · by_cases hEq : n = m / 2 - 1
      · rw [hEq, hR]
        simpa using
          (not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
            (a := (((m - 1 : ℕ) : ZMod m))) (n := m / 2)
            (by
              rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
              rw [hq]
              omega) (by
                have hm9 : 9 < m := Fact.out
                rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
                rw [hq]
                omega))
      · let t : ℕ := n - (m / 2 - 1)
        have ht0 : 0 < t := by
          dsimp [t]
          omega
        have ht : t ≤ (m - 4) / 2 := by
          dsimp [t]
          rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
          rw [hq] at hnm ⊢
          omega
        have hnEq : n = t + (m / 2 - 1) := by
          dsimp [t]
          omega
        have hiter :
            ((F^[n]) start) =
              ((((m - 1 : ℕ) : ZMod m)), (((m / 2 + t : ℕ) : ZMod m))) := by
          calc
            ((F^[n]) start) = ((F^[t]) ((F^[m / 2 - 1]) start)) := by
              rw [hnEq, Function.iterate_add_apply]
            _ = ((F^[t]) ((((m - 1 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m)))) := by
              rw [hR]
            _ = ((((m - 1 : ℕ) : ZMod m)), (((m / 2 + t : ℕ) : ZMod m))) := by
              have hmain := iterate_returnMap0CaseIIXY_even_generic_after_R_partial
                (m := m) (x := m - 4) (t := t) (by omega) (by omega) hxeven ht
              have hstart : (m - 4) / 2 + 2 = m / 2 := by
                rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
                rw [hq]
                omega
              have hend : (m - 4) / 2 + 2 + t = m / 2 + t := by
                rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
                rw [hq]
                omega
              calc
                ((F^[t]) ((((m - 1 : ℕ) : ZMod m)), (((m / 2 : ℕ) : ZMod m))))
                    = ((returnMap0CaseIIXY (m := m)^[t])
                        ((((m - 4 + 3 : ℕ) : ZMod m)), ((((m - 4) / 2 + 2 : ℕ) : ZMod m)))) := by
                          simp [F, hstart, show m - 4 + 3 = m - 1 by omega]
                _ = ((((m - 4 + 3 : ℕ) : ZMod m)), ((((m - 4) / 2 + 2 + t : ℕ) : ZMod m))) := hmain
                _ = ((((m - 1 : ℕ) : ZMod m)), (((m / 2 + t : ℕ) : ZMod m))) := by
                      simp [hend, show m - 4 + 3 = m - 1 by omega]
        rw [hiter]
        exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
          (a := (((m - 1 : ℕ) : ZMod m))) (by
            rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
            rw [hq]
            dsimp [t]
            omega) (by
              have hm9 : 9 < m := Fact.out
              rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
              rw [hq]
              dsimp [t]
              omega)

theorem hfirst_line_m_sub_three_caseII_mod_ten [Fact (9 < m)] (hm : m % 12 = 10) :
    ∀ n, 0 < n →
      n < rho0CaseII (m := m) (⟨m - 3, by omega⟩ : Fin m) →
        (returnMap0CaseIIXY (m := m)^[n])
            (linePoint0 (m := m) (⟨m - 3, by omega⟩ : Fin m)) ∉
          Set.range (linePoint0 (m := m)) := by
  let F := returnMap0CaseIIXY (m := m)
  let xFin : Fin m := ⟨m - 3, by omega⟩
  let start : P0Coord m := linePoint0 (m := m) xFin
  let b : ℕ := (m - 4) / 2
  intro n hn0 hnlt
  have hm0 : 0 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (0 < m) := ⟨hm0⟩
  have hrho : rho0CaseII (m := m) xFin = 2 * m - 3 := by
    simpa [xFin] using
      rho0CaseII_eq_two_mul_sub_three_of_val_eq_m_sub_three (m := m) (x := xFin) rfl
  have hnm : n < 2 * m - 3 := by
    simpa [xFin, hrho] using hnlt
  have hxodd : Odd (m - 3) := by
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rw [hq]
    refine ⟨6 * q + 3, ?_⟩
    omega
  have hb1 : 1 ≤ b := by
    dsimp [b]
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rw [hq]
    omega
  have h1 :
      ((F^[1]) start) = ((((m - 2 : ℕ) : ZMod m)), (1 : ZMod m)) := by
    simpa [Function.iterate_one, F, start, xFin, linePoint0, show (m - 3) + 1 = m - 2 by omega] using
      returnMap0CaseIIXY_line_start_generic (m := m) (x := m - 3) (by omega) (by omega)
  have h2 :
      ((F^[2]) start) = ((((m - 2 : ℕ) : ZMod m)), (2 : ZMod m)) := by
    calc
      ((F^[2]) start) = F (((F^[1]) start)) := by simp [Function.iterate_succ_apply']
      _ = F ((((m - 2 : ℕ) : ZMod m)), (1 : ZMod m)) := by rw [h1]
      _ = ((((m - 2 : ℕ) : ZMod m)), (2 : ZMod m)) := by
            simpa [show (m - 3) + 1 = m - 2 by omega] using
              returnMap0CaseIIXY_odd_generic_even_column_one_step
                (m := m) (hx3 := by omega) (hxle := by omega) (hxodd := hxodd)
  have hmidPoint :
      ((F^[b + 2]) start) =
        ((((m - 2 : ℕ) : ZMod m)), (((b + 2 : ℕ) : ZMod m))) := by
    have hbase :
        ((F^[b + 1]) start) =
          ((((m - 2 : ℕ) : ZMod m)), (((b + 1 : ℕ) : ZMod m))) := by
      calc
        ((F^[b + 1]) start) = ((F^[b - 1]) ((F^[2]) start)) := by
          rw [show b + 1 = (b - 1) + 2 by omega, Function.iterate_add_apply]
        _ = ((F^[b - 1]) ((((m - 2 : ℕ) : ZMod m)), (2 : ZMod m))) := by rw [h2]
        _ = ((((m - 2 : ℕ) : ZMod m)), (((2 + (b - 1) : ℕ) : ZMod m))) := by
              simpa [show m - 3 + 1 = m - 2 by omega] using
                iterate_returnMap0CaseIIXY_odd_generic_even_column_lower_partial
                  (m := m) (x := m - 3) (t := b - 1) (by omega) (by omega) hxodd le_rfl
        _ = ((((m - 2 : ℕ) : ZMod m)), (((b + 1 : ℕ) : ZMod m))) := by
              have hsum : 2 + (b - 1) = b + 1 := by omega
              simp [hsum]
    calc
      ((F^[b + 2]) start) = F (((F^[b + 1]) start)) := by
        rw [show b + 2 = 1 + (b + 1) by omega, Function.iterate_add_apply]
        simp
      _ = F ((((m - 2 : ℕ) : ZMod m)), (((b + 1 : ℕ) : ZMod m))) := by rw [hbase]
      _ = ((((m - 2 : ℕ) : ZMod m)), (((b + 2 : ℕ) : ZMod m))) := by
            dsimp [b]
            simpa [show m - 3 + 1 = m - 2 by omega] using
              returnMap0CaseIIXY_odd_generic_even_column_mid_step
                (m := m) (hx3 := by omega) (hxle := by omega) (hxodd := hxodd)
  have hApoint :
      ((F^[m - 3]) start) =
        ((((m - 2 : ℕ) : ZMod m)), (((m - 3 : ℕ) : ZMod m))) := by
    calc
      ((F^[m - 3]) start) = ((F^[m - 4]) ((F^[1]) start)) := by
        simpa [show (m - 4) + 1 = m - 3 by omega] using
          (Function.iterate_add_apply F (m - 4) 1 start)
      _ = ((F^[m - 4]) ((((m - 2 : ℕ) : ZMod m)), (1 : ZMod m))) := by rw [h1]
      _ = ((((m - 2 : ℕ) : ZMod m)), (((m - 3 : ℕ) : ZMod m))) := by
            simpa [show m - 3 + 1 = m - 2 by omega] using
              iterate_returnMap0CaseIIXY_odd_generic_to_A
                (m := m) (x := m - 3) (by omega) (by omega) hxodd
  have hafterA :
      ((F^[m - 2]) start) =
        ((((m - 1 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) := by
    calc
      ((F^[m - 2]) start) = F (((F^[m - 3]) start)) := by
        simpa [show 1 + (m - 3) = m - 2 by omega] using
          (Function.iterate_add_apply F 1 (m - 3) start)
      _ = F ((((m - 2 : ℕ) : ZMod m)), (((m - 3 : ℕ) : ZMod m))) := by rw [hApoint]
      _ = ((((m - 1 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) := by
            simpa [show (m - 3) + 1 = m - 2 by omega, show (m - 3) + 2 = m - 1 by omega] using
              returnMap0CaseIIXY_A_line (m := m) (y := m - 3) (by omega) (by omega)
  have hafterQ :
      ((F^[m - 1]) start) = ((2 : ZMod m), (2 : ZMod m)) := by
    calc
      ((F^[m - 1]) start) = F (((F^[m - 2]) start)) := by
        simpa [show 1 + (m - 2) = m - 1 by omega] using
          (Function.iterate_add_apply F 1 (m - 2) start)
      _ = F ((((m - 1 : ℕ) : ZMod m)), (((m - 1 : ℕ) : ZMod m))) := by rw [hafterA]
      _ = ((2 : ZMod m), (2 : ZMod m)) := by
            exact returnMap0CaseIIXY_m_sub_one_m_sub_one (m := m)
  by_cases hn1 : n = 1
  · rw [hn1, h1]
    simpa using
      (not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
        (a := (((m - 2 : ℕ) : ZMod m))) (n := 1)
        (by decide) (by
          have hm9 : 9 < m := Fact.out
          omega))
  · by_cases hlow : n ≤ b + 1
    · have hn2 : 2 ≤ n := by omega
      let t : ℕ := n - 2
      have ht : t ≤ b - 1 := by
        dsimp [t]
        omega
      have hnEq : n = t + 2 := by
        dsimp [t]
        omega
      have hiter :
          ((F^[n]) start) =
            ((((m - 2 : ℕ) : ZMod m)), (((2 + t : ℕ) : ZMod m))) := by
        calc
          ((F^[n]) start) = ((F^[t]) ((F^[2]) start)) := by
            rw [hnEq, Function.iterate_add_apply]
          _ = ((F^[t]) ((((m - 2 : ℕ) : ZMod m)), (2 : ZMod m))) := by rw [h2]
          _ = ((((m - 2 : ℕ) : ZMod m)), (((2 + t : ℕ) : ZMod m))) := by
                simpa [show m - 3 + 1 = m - 2 by omega] using
                  iterate_returnMap0CaseIIXY_odd_generic_even_column_lower_partial
                    (m := m) (x := m - 3) (t := t) (by omega) (by omega) hxodd ht
      rw [hiter]
      exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
        (a := (((m - 2 : ℕ) : ZMod m))) (by
          dsimp [t]
          omega) (by
          have hm9 : 9 < m := Fact.out
          dsimp [t]
          omega)
    · by_cases hmid : n = b + 2
      · rw [hmid, hmidPoint]
        exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
          (a := (((m - 2 : ℕ) : ZMod m))) (by
            dsimp [b]
            rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
            rw [hq]
            omega) (by
            have hm9 : 9 < m := Fact.out
            dsimp [b]
            rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
            rw [hq]
            omega)
      · by_cases hupper : n ≤ m - 3
        · let t : ℕ := n - (b + 2)
          have ht0 : 0 < t := by
            dsimp [t]
            omega
          have ht : t ≤ b - 1 := by
            dsimp [t, b]
            rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
            rw [hq] at hupper ⊢
            omega
          have hnEq : n = t + (b + 2) := by
            dsimp [t]
            omega
          have hiter :
              ((F^[n]) start) =
                ((((m - 2 : ℕ) : ZMod m)), (((b + 2 + t : ℕ) : ZMod m))) := by
            calc
              ((F^[n]) start) = ((F^[t]) ((F^[b + 2]) start)) := by
                rw [hnEq, Function.iterate_add_apply]
              _ = ((F^[t]) ((((m - 2 : ℕ) : ZMod m)), (((b + 2 : ℕ) : ZMod m)))) := by
                rw [hmidPoint]
              _ = ((((m - 2 : ℕ) : ZMod m)), (((b + 2 + t : ℕ) : ZMod m))) := by
                simpa [show m - 3 + 1 = m - 2 by omega] using
                  iterate_returnMap0CaseIIXY_odd_generic_even_column_upper_partial
                    (m := m) (x := m - 3) (t := t) (by omega) (by omega) hxodd ht
          rw [hiter]
          exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
            (a := (((m - 2 : ℕ) : ZMod m))) (by
              dsimp [b, t]
              omega) (by
              have hm9 : 9 < m := Fact.out
              dsimp [b, t]
              omega)
        · by_cases hAeq : n = m - 2
          · rw [hAeq, hafterA]
            exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
              (a := (((m - 1 : ℕ) : ZMod m))) (by
                have hm9 : 9 < m := Fact.out
                omega) (by
                have hm9 : 9 < m := Fact.out
                omega)
          · by_cases hQeq : n = m - 1
            · rw [hQeq, hafterQ]
              simpa using
                (not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
                  (a := (2 : ZMod m)) (n := 2) (by omega) (by omega))
            · let t : ℕ := n - (m - 1)
              have ht0 : 0 < t := by
                dsimp [t]
                omega
              have ht : t < m - 2 := by
                dsimp [t]
                omega
              have hnEq : n = t + (m - 1) := by
                dsimp [t]
                omega
              have hiter :
                  ((F^[n]) start) = ((F^[t]) ((2 : ZMod m), (2 : ZMod m))) := by
                calc
                  ((F^[n]) start) = ((F^[t]) ((F^[m - 1]) start)) := by
                    rw [hnEq, Function.iterate_add_apply]
                  _ = ((F^[t]) ((2 : ZMod m), (2 : ZMod m))) := by rw [hafterQ]
              rw [hiter]
              exact hfirst_two_column_to_zero (m := m) hm t ht0 ht

theorem hfirst_line_m_sub_two_caseII_mod_ten [Fact (9 < m)] (hm : m % 12 = 10) :
    ∀ n, 0 < n →
      n < rho0CaseII (m := m) (⟨m - 2, by omega⟩ : Fin m) →
        (returnMap0CaseIIXY (m := m)^[n])
            (linePoint0 (m := m) (⟨m - 2, by omega⟩ : Fin m)) ∉
          Set.range (linePoint0 (m := m)) := by
  let F := returnMap0CaseIIXY (m := m)
  let xFin : Fin m := ⟨m - 2, by omega⟩
  let start : P0Coord m := linePoint0 (m := m) xFin
  intro n hn0 hnlt
  have hm0 : 0 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (0 < m) := ⟨hm0⟩
  have hrho : rho0CaseII (m := m) xFin = 2 * m - 4 := by
    simpa [xFin] using
      rho0CaseII_eq_two_mul_sub_four_of_val_eq_m_sub_two (m := m) (x := xFin) rfl
  have hnm : n < 2 * m - 4 := by
    simpa [xFin, hrho] using hnlt
  have h1 :
      ((F^[1]) start) = ((0 : ZMod m), (2 : ZMod m)) := by
    simpa [Function.iterate_one, F, start, xFin, linePoint0] using
      returnMap0CaseIIXY_m_sub_two_zero (m := m)
  have hafterZero :
      ((F^[m - 2]) start) = ((0 : ZMod m), (((m - 1 : ℕ) : ZMod m))) := by
    calc
      ((F^[m - 2]) start) = ((F^[m - 3]) ((F^[1]) start)) := by
        simpa [show (m - 3) + 1 = m - 2 by omega] using
          (Function.iterate_add_apply F (m - 3) 1 start)
      _ = ((F^[m - 3]) ((0 : ZMod m), (2 : ZMod m))) := by rw [h1]
      _ = ((0 : ZMod m), (((m - 1 : ℕ) : ZMod m))) := by
            exact iterate_returnMap0CaseIIXY_zero_column_to_top (m := m) hm
  have hafterCorner :
      ((F^[m - 1]) start) = ((2 : ZMod m), (1 : ZMod m)) := by
    calc
      ((F^[m - 1]) start) = F (((F^[m - 2]) start)) := by
        simpa [show 1 + (m - 2) = m - 1 by omega] using
          (Function.iterate_add_apply F 1 (m - 2) start)
      _ = F ((0 : ZMod m), (((m - 1 : ℕ) : ZMod m))) := by rw [hafterZero]
      _ = ((2 : ZMod m), (1 : ZMod m)) := by
            exact returnMap0CaseIIXY_zero_m_sub_one (m := m)
  have hafterThree :
      ((F^[m]) start) = ((3 : ZMod m), (3 : ZMod m)) := by
    calc
      ((F^[m]) start) = F (((F^[m - 1]) start)) := by
        simpa [show 1 + (m - 1) = m by omega] using
          (Function.iterate_add_apply F 1 (m - 1) start)
      _ = F ((2 : ZMod m), (1 : ZMod m)) := by rw [hafterCorner]
      _ = ((3 : ZMod m), (3 : ZMod m)) := by
            exact returnMap0CaseIIXY_two_one (m := m)
  have hafterCol3 :
      ((F^[m + (m / 2 - 2)]) start) =
        ((3 : ZMod m), (((m / 2 + 1 : ℕ) : ZMod m))) := by
    calc
      ((F^[m + (m / 2 - 2)]) start)
          = ((F^[m / 2 - 2]) ((F^[m]) start)) := by
              simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
                Function.iterate_add_apply F (m / 2 - 2) m start
      _ = ((F^[m / 2 - 2]) ((3 : ZMod m), (3 : ZMod m))) := by rw [hafterThree]
      _ = ((3 : ZMod m), (((3 + (m / 2 - 2) : ℕ) : ZMod m))) := by
            rw [iterate_returnMap0CaseIIXY_three_column_lower_partial (m := m)
              (t := m / 2 - 2) le_rfl]
      _ = ((3 : ZMod m), (((m / 2 + 1 : ℕ) : ZMod m))) := by
            have hsum : 3 + (m / 2 - 2) = m / 2 + 1 := by omega
            simp [hsum]
  have hafterR :
      ((F^[m + (m / 2 - 1)]) start) =
        ((5 : ZMod m), (((m / 2 + 3 : ℕ) : ZMod m))) := by
    calc
      ((F^[m + (m / 2 - 1)]) start) = F (((F^[m + (m / 2 - 2)]) start)) := by
        have hsum : 1 + (m + (m / 2 - 2)) = m + (m / 2 - 1) := by omega
        simpa [hsum] using
          (Function.iterate_add_apply F 1 (m + (m / 2 - 2)) start)
      _ = F ((3 : ZMod m), (((m / 2 + 1 : ℕ) : ZMod m))) := by rw [hafterCol3]
      _ = ((5 : ZMod m), (((m / 2 + 3 : ℕ) : ZMod m))) := by
            have hR := returnMap0CaseIIXY_R_line (m := m) (y := m / 2 + 1) (by omega)
            simpa [show 1 + 2 * (m / 2 + 1) = m + 3 by omega,
              show 3 + 2 * (m / 2 + 1) = m + 5 by omega,
              show (m / 2 + 1) + 2 = m / 2 + 3 by omega,
              Nat.cast_add] using hR
  by_cases hn1 : n = 1
  · rw [hn1, h1]
    simpa using
      (not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
        (a := (0 : ZMod m)) (n := 2) (by omega) (by omega))
  · by_cases hzero : n ≤ m - 2
    · let t : ℕ := n - 1
      have ht0 : 0 < t := by
        dsimp [t]
        omega
      have ht : t < m - 2 := by
        dsimp [t]
        omega
      have hnEq : n = t + 1 := by
        dsimp [t]
        omega
      have hiter :
          ((F^[n]) start) = ((F^[t]) ((0 : ZMod m), (2 : ZMod m))) := by
        calc
          ((F^[n]) start) = ((F^[t]) ((F^[1]) start)) := by
            rw [hnEq, Function.iterate_add_apply]
          _ = ((F^[t]) ((0 : ZMod m), (2 : ZMod m))) := by rw [h1]
      rw [hiter]
      exact hfirst_zero_column_to_top (m := m) hm t ht0 ht
    · by_cases hcorner : n = m - 1
      · rw [hcorner, hafterCorner]
        simpa using
          (not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
            (a := (2 : ZMod m)) (n := 1) (by decide) (by omega))
      · by_cases hthree : n = m
        · rw [hthree, hafterThree]
          simpa using
            (not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
              (a := (3 : ZMod m)) (n := 3) (by omega) (by omega))
        · by_cases hcol3 : n ≤ m + (m / 2 - 2)
          · let t : ℕ := n - m
            have ht0 : 0 < t := by
              dsimp [t]
              omega
            have ht : t ≤ m / 2 - 2 := by
              dsimp [t]
              omega
            have hnEq : n = t + m := by
              dsimp [t]
              omega
            have hiter :
                ((F^[n]) start) = ((3 : ZMod m), (((3 + t : ℕ) : ZMod m))) := by
              calc
                ((F^[n]) start) = ((F^[t]) ((F^[m]) start)) := by
                  rw [hnEq, Function.iterate_add_apply]
                _ = ((F^[t]) ((3 : ZMod m), (3 : ZMod m))) := by rw [hafterThree]
                _ = ((3 : ZMod m), (((3 + t : ℕ) : ZMod m))) := by
                      rw [iterate_returnMap0CaseIIXY_three_column_lower_partial (m := m)
                        (t := t) ht]
            rw [hiter]
            exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
              (a := (3 : ZMod m)) (by
                dsimp [t]
                omega) (by
                have hm9 : 9 < m := Fact.out
                dsimp [t]
                omega)
          · by_cases hReq : n = m + (m / 2 - 1)
            · rw [hReq, hafterR]
              exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
                (a := (5 : ZMod m)) (by
                  rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
                  rw [hq]
                  omega) (by
                  have hm9 : 9 < m := Fact.out
                  rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
                  rw [hq]
                  omega)
            · let s : ℕ := n - (m + (m / 2 - 1))
              have hs0 : 0 < s := by
                dsimp [s]
                omega
              have hs : s < m - (m / 2 + 3) := by
                dsimp [s]
                omega
              have hnEq : n = s + (m + (m / 2 - 1)) := by
                dsimp [s]
                omega
              have hiter :
                  ((F^[n]) start) =
                    ((F^[s]) ((5 : ZMod m), (((m / 2 + 3 : ℕ) : ZMod m)))) := by
                calc
                  ((F^[n]) start) = ((F^[s]) ((F^[m + (m / 2 - 1)]) start)) := by
                    rw [hnEq, Function.iterate_add_apply]
                  _ = ((F^[s]) ((5 : ZMod m), (((m / 2 + 3 : ℕ) : ZMod m)))) := by rw [hafterR]
              rw [hiter]
              by_cases hm10 : m = 10
              · subst hm10
                have hs1 : s = 1 := by
                  omega
                rw [hs1]
                have hstep :
                    ((returnMap0CaseIIXY (m := 10)^[1]) ((5 : ZMod 10), (((10 / 2 + 3 : ℕ) : ZMod 10)))) =
                      ((5 : ZMod 10), (((10 - 1 : ℕ) : ZMod 10))) := by
                  calc
                    ((returnMap0CaseIIXY (m := 10)^[1]) ((5 : ZMod 10), (((10 / 2 + 3 : ℕ) : ZMod 10))))
                        = returnMap0CaseIIXY (m := 10) ((5 : ZMod 10), (((10 - 2 : ℕ) : ZMod 10))) := by
                            decide
                    _ = ((5 : ZMod 10), (((10 - 1 : ℕ) : ZMod 10))) := by
                          simpa using
                            returnMap0CaseIIXY_wrapped_upper_column_m_sub_two
                              (m := 10) (c := 5) (by omega) (by omega)
                rw [hstep]
                exact not_mem_range_linePoint0_of_nat_snd_pos_lt
                  (m := 10) (a := (5 : ZMod 10)) (n := 9) (by omega) (by omega)
              · simpa [F] using
                  hfirst_wrapped_upper_column_to_zero (m := m) hm
                    (c := 5) (y0 := m / 2 + 3) (by omega)
                    (by
                      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
                      rw [hq] at hm10 ⊢
                      omega)
                    (by exact ⟨2, by omega⟩)
                    (by
                      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
                      rw [hq]
                      omega)
                    (by
                      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
                      rw [hq]
                      omega)
                    s hs0 hs

theorem hfirst_line_m_sub_one_caseII_mod_ten [Fact (9 < m)] (hm : m % 12 = 10) :
    ∀ n, 0 < n →
      n < rho0CaseII (m := m) (⟨m - 1, by omega⟩ : Fin m) →
        (returnMap0CaseIIXY (m := m)^[n])
            (linePoint0 (m := m) (⟨m - 1, by omega⟩ : Fin m)) ∉
          Set.range (linePoint0 (m := m)) := by
  let F := returnMap0CaseIIXY (m := m)
  let xFin : Fin m := ⟨m - 1, by omega⟩
  let start : P0Coord m := linePoint0 (m := m) xFin
  intro n hn0 hnlt
  have hm0 : 0 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (0 < m) := ⟨hm0⟩
  have hrho : rho0CaseII (m := m) xFin = m - 1 := by
    simpa [xFin] using
      rho0CaseII_eq_sub_one_of_val_eq_m_sub_one (m := m) (x := xFin) rfl
  have hnm : n < m - 1 := by
    simpa [xFin, hrho] using hnlt
  have h1 :
      F start = ((((m - 1 : ℕ) : ZMod m)), (1 : ZMod m)) := by
    simpa [F, start] using returnMap0CaseIIXY_m_sub_one_zero_one (m := m)
  have h2 :
      ((F^[2]) start) = ((((m - 1 : ℕ) : ZMod m)), (2 : ZMod m)) := by
    calc
      ((F^[2]) start) = F (F start) := by simp [Function.iterate_succ_apply']
      _ = F ((((m - 1 : ℕ) : ZMod m)), (1 : ZMod m)) := by rw [h1]
      _ = ((((m - 1 : ℕ) : ZMod m)), (2 : ZMod m)) := by
            simpa [show (m - 2) + 1 = m - 1 by omega] using
              returnMap0CaseIIXY_even_generic_odd_column_one_step (m := m)
                (x := m - 2) (by omega) (by omega)
  have hprefix :
      ((F^[m / 2 - 1]) start) =
        ((((m - 1 : ℕ) : ZMod m)), (((m / 2 - 1 : ℕ) : ZMod m))) := by
    have htail :
        ((F^[m / 2 - 3]) ((((m - 1 : ℕ) : ZMod m)), (2 : ZMod m))) =
          ((((m - 1 : ℕ) : ZMod m)), (((m / 2 - 1 : ℕ) : ZMod m))) := by
      have ht : m / 2 - 3 ≤ (m - 2) / 2 - 2 := by
        rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
        rw [hq]
        omega
      have hmain := iterate_returnMap0CaseIIXY_even_generic_odd_column_lower_partial
        (m := m) (x := m - 2) (t := m / 2 - 3) (by omega) (by omega) ht
      have hsum : 2 + (m / 2 - 3) = m / 2 - 1 := by
        rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
        rw [hq]
        omega
      simpa [F, show (m - 2) + 1 = m - 1 by omega, hsum] using hmain
    calc
      ((F^[m / 2 - 1]) start) = ((F^[m / 2 - 3]) ((F^[2]) start)) := by
        rw [show m / 2 - 1 = (m / 2 - 3) + 2 by
          rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
          rw [hq]
          omega,
          Function.iterate_add_apply]
      _ = ((F^[m / 2 - 3]) ((((m - 1 : ℕ) : ZMod m)), (2 : ZMod m))) := by rw [h2]
      _ = ((((m - 1 : ℕ) : ZMod m)), (((m / 2 - 1 : ℕ) : ZMod m))) := htail
  have hR :
      F ((((m - 1 : ℕ) : ZMod m)), (((m / 2 - 1 : ℕ) : ZMod m))) =
        ((1 : ZMod m), (((m / 2 + 1 : ℕ) : ZMod m))) := by
    have hy : m / 2 - 1 ≤ m - 3 := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega
    have hmain := returnMap0CaseIIXY_R_line (m := m) (y := m / 2 - 1) hy
    have hxnat : 1 + 2 * (m / 2 - 1) = m - 1 := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega
    have hxdst : 3 + 2 * (m / 2 - 1) = m + 1 := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega
    have hynat : (m / 2 - 1) + 2 = m / 2 + 1 := by
      rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
      rw [hq]
      omega
    calc
      F ((((m - 1 : ℕ) : ZMod m)), (((m / 2 - 1 : ℕ) : ZMod m)))
          = ((((m + 1 : ℕ) : ZMod m)), (((m / 2 + 1 : ℕ) : ZMod m))) := by
              simpa [F, hxnat, hxdst, hynat, Nat.cast_add] using hmain
      _ = ((1 : ZMod m), (((m / 2 + 1 : ℕ) : ZMod m))) := by
            simp [Nat.cast_add]
  have hafterR :
      ((F^[m / 2]) start) = ((1 : ZMod m), (((m / 2 + 1 : ℕ) : ZMod m))) := by
    calc
      ((F^[m / 2]) start) = F (((F^[m / 2 - 1]) start)) := by
        simpa [show 1 + (m / 2 - 1) = m / 2 by
          rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
          rw [hq]
          omega] using
          (Function.iterate_add_apply F 1 (m / 2 - 1) start)
      _ = F ((((m - 1 : ℕ) : ZMod m)), (((m / 2 - 1 : ℕ) : ZMod m))) := by rw [hprefix]
      _ = ((1 : ZMod m), (((m / 2 + 1 : ℕ) : ZMod m))) := hR
  by_cases hn1 : n = 1
  · rw [hn1]
    have hiter :
        ((returnMap0CaseIIXY (m := m)^[1]) (linePoint0 (m := m) xFin)) =
          ((((m - 1 : ℕ) : ZMod m)), (1 : ZMod m)) := by
      simpa [F, start, Function.iterate_one] using h1
    rw [hiter]
    simpa using
      (not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
        (a := (((m - 1 : ℕ) : ZMod m))) (n := 1)
        (by decide) (by
          have hm9 : 9 < m := Fact.out
          omega))
  · by_cases hprefixCase : n ≤ m / 2 - 1
    · have hn2 : 2 ≤ n := by omega
      let t : ℕ := n - 2
      have ht : t ≤ m / 2 - 3 := by
        dsimp [t]
        omega
      have hnEq : n = t + 2 := by
        dsimp [t]
        omega
      have hiter :
          ((F^[n]) start) =
            ((((m - 1 : ℕ) : ZMod m)), (((2 + t : ℕ) : ZMod m))) := by
        have ht' : t ≤ (m - 2) / 2 - 2 := by
          rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
          rw [hq] at ht ⊢
          omega
        calc
          ((F^[n]) start) = ((F^[t]) ((F^[2]) start)) := by
            rw [hnEq, Function.iterate_add_apply]
          _ = ((F^[t]) ((((m - 1 : ℕ) : ZMod m)), (2 : ZMod m))) := by rw [h2]
          _ = ((((m - 1 : ℕ) : ZMod m)), (((2 + t : ℕ) : ZMod m))) := by
            simpa [F, show (m - 2) + 1 = m - 1 by omega] using
              iterate_returnMap0CaseIIXY_even_generic_odd_column_lower_partial
                (m := m) (x := m - 2) (t := t) (by omega) (by omega) ht'
      rw [hiter]
      exact not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
        (a := (((m - 1 : ℕ) : ZMod m))) (by
          dsimp [t]
          omega) (by
          have hm9 : 9 < m := Fact.out
          dsimp [t]
          omega)
    · by_cases hEq : n = m / 2
      · rw [hEq, hafterR]
        simpa using
          (not_mem_range_linePoint0_of_nat_snd_pos_lt (m := m)
            (a := (1 : ZMod m)) (n := m / 2 + 1)
            (by
              rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
              rw [hq]
              omega) (by
                have hm9 : 9 < m := Fact.out
                rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
                rw [hq]
                omega))
      · let t : ℕ := n - (m / 2)
        have ht0 : 0 < t := by
          dsimp [t]
          omega
        have ht : t < m - (m / 2 + 1) := by
          dsimp [t]
          omega
        have hnEq : n = t + m / 2 := by
          dsimp [t]
          omega
        have hiter :
            ((F^[n]) start) =
              ((F^[t]) ((1 : ZMod m), (((m / 2 + 1 : ℕ) : ZMod m)))) := by
          calc
            ((F^[n]) start) = ((F^[t]) ((F^[m / 2]) start)) := by
              rw [hnEq, Function.iterate_add_apply]
            _ = ((F^[t]) ((1 : ZMod m), (((m / 2 + 1 : ℕ) : ZMod m)))) := by
              rw [hafterR]
        rw [hiter]
        simpa [F] using
          hfirst_wrapped_upper_column_to_zero (m := m) hm
            (c := 1) (y0 := m / 2 + 1) (by omega) (by omega) (by exact ⟨0, by omega⟩)
            (by
              rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
              rw [hq]
              omega)
            (by
              rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
              rw [hq]
              omega)
            t ht0 ht

theorem hfirst_line_case0_caseII_mod_ten [Fact (9 < m)] (hm : m % 12 = 10) (x : Fin m) :
    ∀ n, 0 < n →
      n < rho0CaseII (m := m) x →
        (returnMap0CaseIIXY (m := m)^[n]) (linePoint0 (m := m) x) ∉
          Set.range (linePoint0 (m := m)) := by
  by_cases hx0 : x.1 = 0
  · have hx' : x = (0 : Fin m) := Fin.ext hx0
    simpa [hx'] using hfirst_line_zero_caseII_mod_ten (m := m)
  by_cases hx1 : x.1 = 1
  · let x0 : Fin m := ⟨1, by
        have hm9 : 9 < m := Fact.out
        omega⟩
    have hx' : x = x0 := by
      apply Fin.ext
      simpa [x0] using hx1
    simpa [hx'] using hfirst_line_one_caseII_mod_ten (m := m) hm
  by_cases hx2 : x.1 = 2
  · let x0 : Fin m := ⟨2, by
        have hm9 : 9 < m := Fact.out
        omega⟩
    have hx' : x = x0 := by
      apply Fin.ext
      simpa [x0] using hx2
    simpa [hx'] using hfirst_line_two_caseII_mod_ten (m := m) hm
  by_cases hxm6 : x.1 = m - 6
  · let x0 : Fin m := ⟨m - 6, by omega⟩
    have hx' : x = x0 := Fin.ext hxm6
    simpa [hx'] using hfirst_line_m_sub_six_caseII_mod_ten (m := m) hm
  by_cases hxm5 : x.1 = m - 5
  · let x0 : Fin m := ⟨m - 5, by omega⟩
    have hx' : x = x0 := Fin.ext hxm5
    simpa [hx'] using hfirst_line_m_sub_five_caseII_mod_ten (m := m) hm
  by_cases hxm4 : x.1 = m - 4
  · let x0 : Fin m := ⟨m - 4, by omega⟩
    have hx' : x = x0 := Fin.ext hxm4
    simpa [hx'] using hfirst_line_m_sub_four_caseII_mod_ten (m := m) hm
  by_cases hxm3 : x.1 = m - 3
  · let x0 : Fin m := ⟨m - 3, by omega⟩
    have hx' : x = x0 := Fin.ext hxm3
    simpa [hx'] using hfirst_line_m_sub_three_caseII_mod_ten (m := m) hm
  by_cases hxm2 : x.1 = m - 2
  · let x0 : Fin m := ⟨m - 2, by omega⟩
    have hx' : x = x0 := Fin.ext hxm2
    simpa [hx'] using hfirst_line_m_sub_two_caseII_mod_ten (m := m) hm
  by_cases hxm1 : x.1 = m - 1
  · let x0 : Fin m := ⟨m - 1, by omega⟩
    have hx' : x = x0 := Fin.ext hxm1
    simpa [hx'] using hfirst_line_m_sub_one_caseII_mod_ten (m := m) hm
  have hmEven : Even m := by
    rcases eq_twelve_mul_add_ten_of_mod_twelve_eq_ten (m := m) hm with ⟨q, hq⟩
    rw [hq]
    exact ⟨6 * q + 5, by omega⟩
  rcases Nat.even_or_odd x.1 with hxeven | hxodd
  · have hx4 : 4 ≤ x.1 := by
      rcases hxeven with ⟨k, hk⟩
      omega
    have hxle : x.1 ≤ m - 8 := by
      rcases hxeven with ⟨k, hk⟩
      rcases hmEven with ⟨r, hr⟩
      omega
    simpa using hfirst_line_even_generic_caseII_mod_ten (m := m) hm
      (x := x.1) hx4 hxle hxeven
  · have hx3 : 3 ≤ x.1 := by
      rcases hxodd with ⟨k, hk⟩
      omega
    have hxle : x.1 ≤ m - 7 := by
      rcases hxodd with ⟨k, hk⟩
      rcases hmEven with ⟨r, hr⟩
      omega
    simpa using hfirst_line_odd_generic_caseII_mod_ten (m := m) hm
      (x := x.1) hx3 hxle hxodd

theorem cycleOn_returnMap0CaseII_caseII_mod_ten [Fact (9 < m)] (hm : m % 12 = 10) :
    TorusD4.CycleOn (m ^ 2) (returnMap0CaseIIXY (m := m))
      (linePoint0 (m := m) (0 : Fin m)) := by
  have hm0 : 0 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : NeZero m := ⟨Nat.ne_of_gt hm0⟩
  letI : Fact (0 < m) := ⟨hm0⟩
  have hm6 : m % 6 = 4 := mod_six_eq_four_of_mod_twelve_eq_ten (m := m) hm
  have hsumCard :
      TorusD3Even.blockTime
          (TorusD3Even.T0CaseII (m := m) hm6)
          (rho0CaseII (m := m))
          ⟨0, hm0⟩
          m = Fintype.card (P0Coord m) := by
    simpa [P0Coord, ZMod.card, pow_two] using hsum_case0_caseII_mod_ten (m := m) hm
  simpa [P0Coord, ZMod.card, pow_two] using
    (TorusD3Even.firstReturn_counting
      (α := P0Coord m) (β := Fin m)
      (F := returnMap0CaseIIXY (m := m)) (embed := linePoint0 (m := m))
      (T := TorusD3Even.T0CaseII (m := m) hm6) (rho := rho0CaseII (m := m))
      (M := m) (x0 := (0 : Fin m))
      linePoint0_injective
      (cycleOn_laneMap0_caseII_mod_ten (m := m) hm)
      (hreturn_line_case0_caseII_mod_ten (m := m) hm)
      (hfirst_line_case0_caseII_mod_ten (m := m) hm)
      hsumCard)

theorem cycleOn_fullMap0CaseII_caseII_mod_ten [Fact (9 < m)] (hm : m % 12 = 10) :
    TorusD4.CycleOn (m ^ 3) (fullMap0CaseII (m := m))
      (slicePoint (0 : ZMod m) (linePoint0 (m := m) (0 : Fin m))) := by
  have hm0 : 0 < m := by
    have hm9 : 9 < m := Fact.out
    omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : NeZero m := ⟨Nat.ne_of_gt hm0⟩
  have hretOrig :
      TorusD4.CycleOn (m ^ 2) (returnMap0CaseII (m := m))
        ((xyEquiv (m := m)).symm (linePoint0 (m := m) (0 : Fin m))) := by
    exact TorusD4.cycleOn_conj (xyEquiv (m := m)).symm
      (f := returnMap0CaseIIXY (m := m)) (g := returnMap0CaseII (m := m))
      (returnMap0CaseII_semiconj_xy_symm (m := m))
      (cycleOn_returnMap0CaseII_caseII_mod_ten (m := m) hm)
  simpa [xyEquiv, linePoint0, fromXY] using
    (cycleOn_full_of_cycleOn_p0 (m := m)
      (F := fullMap0CaseII (m := m)) (T := returnMap0CaseII (m := m))
      (hstep := fullMap0CaseII_snd (m := m))
      (hreturn := iterate_m_fullMap0CaseII_slicePoint_zero (m := m))
      (u := (xyEquiv (m := m)).symm (linePoint0 (m := m) (0 : Fin m)))
      hretOrig)

end TorusD3Odometer
