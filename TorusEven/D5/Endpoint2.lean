-- STATUS: main-path (terminal plane, colour i = 2: support B_2, partner, the 2m-cycle)
import TorusEven.D5.Endpoint1

/-!
# Colour `i = 2` (physical colour `4`, direction `1`, functional `ℓ_2 = a + b`)

`B_2 = {A, B, C, Y_t (t ≠ 2), X_t (t ∉ {0,1})}`,
`j_2 = (A, B, Y_3, Y_4, …, Y_{m-1}, Y_0, Y_1, C, X_2, X_3, …, X_{m-1})`,
fibre pairs `(Y_0 X_{m-1})(A Y_1)(B C)(X_{s-2} Y_{s-1})`.
-/

namespace TorusEven
namespace D5

variable {m : ℕ} [NeZero m]

/-- The support `B_2` as a union of families. -/
def fam2 (q : Pt m) : Prop :=
  q = ptA ∨ q = ptB ∨ q = ptC ∨ (q.1 = 1 ∧ q.2 ≠ 2) ∨ (q.2 = 2 ∧ q.1 ≠ 0 ∧ q.1 ≠ 1)

/-- The fibre partner for `ℓ_2 = a + b`. -/
def partner2 (q : Pt m) : Pt m :=
  if q = ptB then ptC else if q = ptC then ptB
  else if q.2 = 2 then (1, q.1 + 1) else (q.1 + q.2 - 2, 2)

theorem partner2_sum (q : Pt m) : (partner2 q).1 + (partner2 q).2 = q.1 + q.2 := by
  unfold partner2
  split_ifs with hB hC h2
  · subst hB; simp [ptB, ptC]
  · subst hC; simp [ptB, ptC]
  · simp [h2]; ring
  · simp

/-- The composite `N_2 ∘ j_2`. -/
def NJ2 (q : Pt m) : Pt m := partner2 (jmap 2 q)

section colour2

variable (h6 : 6 ≤ m)
include h6

theorem fam2_of_inB {q : Pt m} (h : inB 2 q) : fam2 q := by
  have hc := consts h6
  rcases q with ⟨a, b⟩
  rcases omega_cases (m := m) (a, b) with
    ⟨ha, hb, hw⟩ | ⟨ha, hb, hw⟩ | ⟨ha, hb, hw⟩ | ⟨ha, hb, hw⟩ | ⟨ha, hb, hw⟩ | ⟨ha, hb, hw⟩ |
    ⟨ha, hb, hw⟩ | ⟨ha, hb, hw⟩ | ⟨hb, ha0, ha1, ha2, hw⟩ | ⟨ha, hb0, hb1, hb2, hb3, hw⟩ |
    ⟨hab, hb0, hb1, hb2, hb3, hw⟩ | hw <;>
    simp only [inB, hw] at h
  · simp only at ha hb; subst ha; subst hb; simp [fam2, hc]
  · exact absurd (by decide) h
  · simp only at ha hb; subst ha; subst hb; simp [fam2, hc]
  · simp only at ha hb; subst ha; subst hb; simp [fam2, ptC]
  · simp only at ha hb; subst ha; subst hb; simp [fam2, ptA]
  · simp only at ha hb; subst ha; subst hb; simp [fam2, hc]
  · simp only at ha hb; subst ha; subst hb; simp [fam2, ptB]
  · simp only at ha hb; subst ha; subst hb; simp [fam2, hc]
  · simp only at hb ha0 ha1 ha2; subst hb
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, ha0, ha1⟩)))
  · simp only at ha hb0 hb1 hb2 hb3; subst ha
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hb2⟩)))
  · exact absurd (by decide) h
  · exact absurd (by decide) h

theorem inB_of_fam2 {q : Pt m} (h : fam2 q) : inB 2 q := by
  have hc := consts h6
  unfold inB
  rcases h with rfl | rfl | rfl | ⟨ha, hb2⟩ | ⟨hb, ha0, ha1⟩
  · rw [omega_A h6]; decide
  · rw [omega_B h6]; decide
  · rw [omega_C h6]; decide
  · rcases q with ⟨a, b⟩
    simp only at ha hb2
    subst ha
    by_cases hb0 : b = 0
    · subst hb0; rw [show ((1 : ZMod m), (0 : ZMod m)) = ptY 0 from rfl, omega_Y0 h6]; decide
    by_cases hb1 : b = 1
    · subst hb1; rw [show ((1 : ZMod m), (1 : ZMod m)) = ptY 1 from rfl, omega_Y1 h6]; decide
    by_cases hb3 : b = 3
    · subst hb3; rw [show ((1 : ZMod m), (3 : ZMod m)) = ptY 3 from rfl, omega_Y3 h6]; decide
    · rw [show (((1 : ZMod m), b) : Pt m) = ptY b from rfl, omega_Y h6 b hb0 hb1 hb2 hb3]; decide
  · rcases q with ⟨a, b⟩
    simp only at hb ha0 ha1
    subst hb
    by_cases ha2 : a = 2
    · subst ha2; rw [show ((2 : ZMod m), (2 : ZMod m)) = ptX 2 from rfl, omega_X2 h6]; decide
    · rw [show ((a, (2 : ZMod m)) : Pt m) = ptX a from rfl, omega_X h6 a ha0 ha1 ha2]; decide

/-! The local map `j_2` on the families. -/

theorem j2_A : jmap 2 (ptA : Pt m) = ptB := by
  rw [jmap, omega_A h6]; ext <;> simp [ptA, ptB, avec, p201] <;> ring

theorem j2_B : jmap 2 (ptB : Pt m) = ptY 3 := by
  rw [jmap, omega_B h6]; ext <;> simp [ptB, ptY, avec, p120] <;> ring

theorem j2_C : jmap 2 (ptC : Pt m) = ptX 2 := by
  rw [jmap, omega_C h6]; ext <;> simp [ptC, ptX, avec, p201] <;> ring

theorem j2_Y0 : jmap 2 (ptY 0 : Pt m) = ptY 1 := by
  rw [jmap, omega_Y0 h6]; ext <;> simp [ptY, avec, p021] <;> ring

theorem j2_Y1 : jmap 2 (ptY 1 : Pt m) = ptC := by
  rw [jmap, omega_Y1 h6]; ext <;> simp [ptY, ptC, avec, p120] <;> ring

theorem j2_Y3 : jmap 2 (ptY 3 : Pt m) = ptY 4 := by
  rw [jmap, omega_Y3 h6]; ext <;> simp [ptY, avec, p201] <;> ring

theorem j2_X2 : jmap 2 (ptX 2 : Pt m) = ptX 3 := by
  rw [jmap, omega_X2 h6]; ext <;> simp [ptX, avec, p120] <;> ring

theorem j2_X (t : ZMod m) (h0 : t ≠ 0) (h1 : t ≠ 1) (h2 : t ≠ 2) :
    jmap 2 (ptX t) = ptX (t + 1) := by
  rw [jmap, omega_X h6 t h0 h1 h2]; ext <;> simp [ptX, avec, p210] <;> ring

theorem j2_Y (t : ZMod m) (h0 : t ≠ 0) (h1 : t ≠ 1) (h2 : t ≠ 2) (h3 : t ≠ 3) :
    jmap 2 (ptY t) = ptY (t + 1) := by
  rw [jmap, omega_Y h6 t h0 h1 h2 h3]; ext <;> simp [ptY, avec, p021] <;> ring

/-! The partner on the families. -/

theorem partner2_B : partner2 (ptB : Pt m) = ptC := by simp [partner2]

theorem partner2_C : partner2 (ptC : Pt m) = ptB := by
  have hc := consts h6
  simp [partner2, ptB, ptC, hc]

theorem partner2_X (t : ZMod m) : partner2 (ptX t) = ptY (t + 1) := by
  have hc := consts h6
  have hB : (ptX t : Pt m) ≠ ptB := by simp [ptX, ptB, hc]
  have hC : (ptX t : Pt m) ≠ ptC := by simp [ptX, ptC, hc]
  unfold partner2
  rw [if_neg hB, if_neg hC]
  simp [ptX, ptY]

theorem partner2_Y (t : ZMod m) (h1 : t ≠ 1) (h2 : t ≠ 2) : partner2 (ptY t) = ptX (t - 1) := by
  have hc := consts h6
  have hB : (ptY t : Pt m) ≠ ptB := by simp [ptY, ptB, hc]
  have hC : (ptY t : Pt m) ≠ ptC := by simp [ptY, ptC, hc]
  unfold partner2
  rw [if_neg hB, if_neg hC]
  refine Prod.ext ?_ ?_ <;> simp [ptX, ptY, h2] <;> ring

theorem partner2_A : partner2 (ptA : Pt m) = ptY 1 := by
  rw [show (ptA : Pt m) = ptX 0 by simp [ptA, ptX], partner2_X h6]; simp

theorem partner2_Y0 : partner2 (ptY 0 : Pt m) = ptX (-1) := by
  have hc := consts h6
  rw [partner2_Y h6 0 hc.1 hc.2.2.1]; simp

theorem partner2_Y3 : partner2 (ptY 3 : Pt m) = ptX 2 := by
  have hc := consts h6
  rw [partner2_Y h6 3 hc.2.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.2.1]; norm_num

theorem partner2_X2 : partner2 (ptX 2 : Pt m) = ptY 3 := by
  rw [partner2_X h6]; norm_num

theorem partner2_Y1 : partner2 (ptY 1 : Pt m) = ptA := by
  have hc := consts h6
  have hB : (ptY 1 : Pt m) ≠ ptB := by simp [ptY, ptB, hc]
  have hC : (ptY 1 : Pt m) ≠ ptC := by simp [ptY, ptC, hc]
  unfold partner2
  rw [if_neg hB, if_neg hC]
  refine Prod.ext ?_ ?_ <;> simp [ptY, ptA, hc] <;> ring

/-! The composite. -/

theorem NJ2_A : NJ2 (ptA : Pt m) = ptC := by rw [NJ2, j2_A h6, partner2_B h6]
theorem NJ2_C : NJ2 (ptC : Pt m) = ptY 3 := by rw [NJ2, j2_C h6, partner2_X2 h6]
theorem NJ2_Y1 : NJ2 (ptY 1 : Pt m) = ptB := by rw [NJ2, j2_Y1 h6, partner2_C h6]
theorem NJ2_B : NJ2 (ptB : Pt m) = ptX 2 := by rw [NJ2, j2_B h6, partner2_Y3 h6]
theorem NJ2_Y0 : NJ2 (ptY 0 : Pt m) = ptA := by rw [NJ2, j2_Y0 h6, partner2_Y1 h6]

theorem NJ2_X2 : NJ2 (ptX 2 : Pt m) = ptY 4 := by
  rw [NJ2, j2_X2 h6, partner2_X h6]; norm_num

theorem NJ2_Y3 : NJ2 (ptY 3 : Pt m) = ptX 3 := by
  have hc := consts h6
  rw [NJ2, j2_Y3 h6, partner2_Y h6 4 hc.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  norm_num

theorem NJ2_X (t : ZMod m) (h0 : t ≠ 0) (h1 : t ≠ 1) (h2 : t ≠ 2) :
    NJ2 (ptX t) = ptY (t + 2) := by
  rw [NJ2, j2_X h6 t h0 h1 h2, partner2_X h6]
  congr 1; ring

theorem NJ2_Y (t : ZMod m) (h0 : t ≠ 0) (h1 : t ≠ 1) (h2 : t ≠ 2) (h3 : t ≠ 3) :
    NJ2 (ptY t) = ptX t := by
  rw [NJ2, j2_Y h6 t h0 h1 h2 h3, partner2_Y h6 (t + 1)
    (fun h => h0 (by linear_combination h)) (fun h => h1 (by linear_combination h))]
  congr 1; ring

end colour2

/-- The `2m`-cycle of `N_2 ∘ j_2` through `B_2`, indexed by position. -/
def pos2 (m : ℕ) (k : ℕ) : Pt m :=
  if k = 0 then ptA
  else if k = 1 then ptC
  else if k ≤ m - 1 then (if k % 2 = 0 then ptY ((k + 1 : ℕ) : ZMod m) else ptX (k : ZMod m))
  else if k = m then ptY 1
  else if k = m + 1 then ptB
  else if k = m + 2 then ptX 2
  else (if k % 2 = 1 then ptY ((k + 1 : ℕ) : ZMod m) else ptX (k : ZMod m))

theorem cast_not_small {k : ℕ} (hk : 2 ≤ k) (h0 : ¬ m ∣ k) (h1 : ¬ m ∣ k - 1)
    (h2 : ¬ m ∣ k - 2) :
    (k : ZMod m) ≠ 0 ∧ (k : ZMod m) ≠ 1 ∧ (k : ZMod m) ≠ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using natCast_ne_natCast_of_not_dvd (m := m) (a := k) (b := 0) (by omega)
      (by simpa using h0)
  · simpa using natCast_ne_natCast_of_not_dvd (m := m) (a := k) (b := 1) (by omega) h1
  · simpa using natCast_ne_natCast_of_not_dvd (m := m) (a := k) (b := 2) hk h2

section cycle2

variable (h6 : 6 ≤ m) (hm : Even m)
include h6 hm

theorem pos2_zero : pos2 m 0 = ptA := by simp [pos2]
theorem pos2_one : pos2 m 1 = ptC := by simp [pos2]

theorem pos2_low_even {k : ℕ} (h1 : 2 ≤ k) (h2 : k ≤ m - 1) (heven : k % 2 = 0) :
    pos2 m k = ptY ((k + 1 : ℕ) : ZMod m) := by
  have hk0 : k ≠ 0 := by omega
  have hk1 : k ≠ 1 := by omega
  simp [pos2, hk0, hk1, h2, heven]

theorem pos2_low_odd {k : ℕ} (h1 : 3 ≤ k) (h2 : k ≤ m - 1) (hodd : k % 2 = 1) :
    pos2 m k = ptX (k : ZMod m) := by
  have hk0 : k ≠ 0 := by omega
  have hk1 : k ≠ 1 := by omega
  simp [pos2, hk0, hk1, h2, hodd]

theorem pos2_m : pos2 m m = ptY 1 := by
  have h0 : m ≠ 0 := by omega
  have h1 : m ≠ 1 := by omega
  have h2 : ¬ (m ≤ m - 1) := by omega
  simp [pos2, h0, h1, h2]

theorem pos2_m_add_one : pos2 m (m + 1) = ptB := by
  have h0 : m + 1 ≠ 0 := by omega
  have h1 : m + 1 ≠ 1 := by omega
  have h2 : ¬ (m + 1 ≤ m - 1) := by omega
  have h3 : m + 1 ≠ m := by omega
  have hm0 : m ≠ 0 := by omega
  simp [pos2, h0, h1, h2, h3, hm0]

theorem pos2_m_add_two : pos2 m (m + 2) = ptX 2 := by
  have h0 : m + 2 ≠ 0 := by omega
  have h1 : m + 2 ≠ 1 := by omega
  have h2 : ¬ (m + 2 ≤ m - 1) := by omega
  have h3 : m + 2 ≠ m := by omega
  have h4 : m + 2 ≠ m + 1 := by omega
  have hm0 : m ≠ 0 := by omega
  simp [pos2, h0, h1, h2, h3, h4, hm0]

theorem pos2_high_odd {k : ℕ} (h1 : m + 3 ≤ k) (hodd : k % 2 = 1) :
    pos2 m k = ptY ((k + 1 : ℕ) : ZMod m) := by
  have hk0 : k ≠ 0 := by omega
  have hk1 : k ≠ 1 := by omega
  have hk2 : ¬ (k ≤ m - 1) := by omega
  have hk3 : k ≠ m := by omega
  have hk4 : k ≠ m + 1 := by omega
  have hk5 : k ≠ m + 2 := by omega
  simp [pos2, hk0, hk1, hk2, hk3, hk4, hk5, hodd]

theorem pos2_high_even {k : ℕ} (h1 : m + 3 ≤ k) (heven : k % 2 = 0) :
    pos2 m k = ptX (k : ZMod m) := by
  have hk0 : k ≠ 0 := by omega
  have hk1 : k ≠ 1 := by omega
  have hk2 : ¬ (k ≤ m - 1) := by omega
  have hk3 : k ≠ m := by omega
  have hk4 : k ≠ m + 1 := by omega
  have hk5 : k ≠ m + 2 := by omega
  simp [pos2, hk0, hk1, hk2, hk3, hk4, hk5, heven]

theorem NJ2_pos2_succ {k : ℕ} (hk : k < 2 * m - 1) : NJ2 (pos2 m k) = pos2 m (k + 1) := by
  have hm' := hm
  obtain ⟨r, hr⟩ := hm'
  rcases Nat.lt_or_ge k 3 with hk2 | hk2
  · interval_cases k
    · rw [pos2_zero h6 hm, NJ2_A h6, pos2_one h6 hm]
    · rw [pos2_one h6 hm, NJ2_C h6, pos2_low_even h6 hm (by omega) (by omega) (by omega)]
      norm_num
    · rw [pos2_low_even h6 hm (by omega) (by omega) (by omega),
        show ((2 + 1 : ℕ) : ZMod m) = 3 by norm_num, NJ2_Y3 h6,
        pos2_low_odd h6 hm (by omega) (by omega) (by omega)]
      norm_num
  by_cases hlow : k ≤ m - 2
  · rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · have hns := cast_succ_not_small (m := m) (k := k) (by omega)
        (not_dvd_of_lt_of_lt (by omega) (by omega)) (not_dvd_of_lt_of_lt (by omega) (by omega))
        (not_dvd_of_lt_of_lt (by omega) (by omega))
      rw [pos2_low_even h6 hm (by omega) (by omega) (by omega), NJ2_Y h6 _ hns.1 hns.2.1 hns.2.2
        (fun h => ?_), pos2_low_odd h6 hm (by omega) (by omega) (by omega)]
      exact natCast_ne_natCast_of_not_dvd (m := m) (a := k + 1) (b := 3) (by omega)
        (not_dvd_of_lt_of_lt (by omega) (by omega)) (by simpa using h)
    · have hns := cast_not_small (m := m) (k := k) (by omega)
        (not_dvd_of_lt_of_lt (by omega) (by omega)) (not_dvd_of_lt_of_lt (by omega) (by omega))
        (not_dvd_of_lt_of_lt (by omega) (by omega))
      rw [pos2_low_odd h6 hm (by omega) (by omega) (by omega), NJ2_X h6 _ hns.1 hns.2.1 hns.2.2,
        pos2_low_even h6 hm (by omega) (by omega) (by omega)]
      congr 1; push_cast; ring
  by_cases hk1 : k = m - 1
  · subst hk1
    rw [pos2_low_odd h6 hm (by omega) (by omega) (by omega), cast_sub_self (by omega)]
    have hns := neg_cast_not_small (m := m) (k := 1) (not_dvd_of_lt_of_lt (by omega) (by omega))
      (not_dvd_of_lt_of_lt (by omega) (by omega)) (not_dvd_of_lt_of_lt (by omega) (by omega))
    rw [NJ2_X h6 _ hns.1 hns.2.1 hns.2.2, show m - 1 + 1 = m by omega, pos2_m h6 hm]
    congr 1; push_cast; ring
  by_cases hkm : k = m
  · subst hkm
    rw [pos2_m h6 hm, NJ2_Y1 h6, pos2_m_add_one h6 hm]
  by_cases hkm1 : k = m + 1
  · subst hkm1
    rw [pos2_m_add_one h6 hm, NJ2_B h6, pos2_m_add_two h6 hm]
  by_cases hkm2 : k = m + 2
  · subst hkm2
    rw [pos2_m_add_two h6 hm, NJ2_X2 h6, pos2_high_odd h6 hm (by omega) (by omega)]
    congr 1; push_cast; rw [ZMod.natCast_self]; ring
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hns := cast_not_small (m := m) (k := k) (by omega)
      (not_dvd_of_between (by omega) (by omega)) (not_dvd_of_between (by omega) (by omega))
      (not_dvd_of_between (by omega) (by omega))
    rw [pos2_high_even h6 hm (by omega) (by omega), NJ2_X h6 _ hns.1 hns.2.1 hns.2.2,
      pos2_high_odd h6 hm (by omega) (by omega)]
    congr 1; push_cast; ring
  · have hns := cast_succ_not_small (m := m) (k := k) (by omega)
      (not_dvd_of_between (by omega) (by omega)) (not_dvd_of_between (by omega) (by omega))
      (not_dvd_of_between (by omega) (by omega))
    rw [pos2_high_odd h6 hm (by omega) (by omega), NJ2_Y h6 _ hns.1 hns.2.1 hns.2.2
      (fun h => ?_), pos2_high_even h6 hm (by omega) (by omega)]
    exact natCast_ne_natCast_of_not_dvd (m := m) (a := k + 1) (b := 3) (by omega)
      (not_dvd_of_between (by omega) (by omega)) (by simpa using h)

theorem NJ2_pos2_wrap : NJ2 (pos2 m (2 * m - 1)) = pos2 m 0 := by
  have hm' := hm
  obtain ⟨r, hr⟩ := hm'
  rw [pos2_high_odd h6 hm (by omega) (by omega), show 2 * m - 1 + 1 = 2 * m by omega,
    Nat.cast_mul, ZMod.natCast_self, mul_zero, NJ2_Y0 h6, pos2_zero h6 hm]

theorem NJ2_iterate {k : ℕ} (hk : k ≤ 2 * m - 1) : NJ2^[k] (ptA : Pt m) = pos2 m k := by
  induction k with
  | zero => simp [pos2_zero h6 hm]
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega), NJ2_pos2_succ h6 hm (by omega)]

/-- Every point of `B_2` is on the cycle. -/
theorem exists_pos2 {q : Pt m} (hq : fam2 q) : ∃ k, k ≤ 2 * m - 1 ∧ pos2 m k = q := by
  have hm' := hm
  obtain ⟨r, hr⟩ := hm'
  rcases hq with rfl | rfl | rfl | ⟨ha, hb2⟩ | ⟨hb, ha0, ha1⟩
  · exact ⟨0, by omega, pos2_zero h6 hm⟩
  · exact ⟨m + 1, by omega, pos2_m_add_one h6 hm⟩
  · exact ⟨1, by omega, pos2_one h6 hm⟩
  · rcases q with ⟨a, b⟩
    simp only at ha hb2
    subst ha
    have hv : ((b.val : ℕ) : ZMod m) = b := ZMod.natCast_zmod_val b
    have hvlt : b.val < m := ZMod.val_lt b
    have hv2 : b.val ≠ 2 := fun h => hb2 (by rw [← hv, h]; simp)
    by_cases hv0 : b.val = 0
    · refine ⟨2 * m - 1, le_rfl, ?_⟩
      rw [pos2_high_odd h6 hm (by omega) (by omega), show 2 * m - 1 + 1 = 2 * m by omega,
        Nat.cast_mul, ZMod.natCast_self, mul_zero, ← hv, hv0]
      simp [ptY]
    by_cases hv1 : b.val = 1
    · refine ⟨m, by omega, ?_⟩
      rw [pos2_m h6 hm, ← hv, hv1]
      simp [ptY]
    rcases Nat.even_or_odd b.val with ⟨j, hj⟩ | ⟨j, hj⟩
    · refine ⟨m + b.val - 1, by omega, ?_⟩
      rw [pos2_high_odd h6 hm (by omega) (by omega), Nat.sub_add_cancel (by omega),
        Nat.cast_add, ZMod.natCast_self, zero_add, hv]
      rfl
    · refine ⟨b.val - 1, by omega, ?_⟩
      rw [pos2_low_even h6 hm (by omega) (by omega) (by omega), Nat.sub_add_cancel (by omega), hv]
      rfl
  · rcases q with ⟨a, b⟩
    simp only at hb ha0 ha1
    subst hb
    have hv : ((a.val : ℕ) : ZMod m) = a := ZMod.natCast_zmod_val a
    have hvlt : a.val < m := ZMod.val_lt a
    have hv0 : a.val ≠ 0 := fun h => ha0 (by rw [← hv, h]; simp)
    have hv1 : a.val ≠ 1 := fun h => ha1 (by rw [← hv, h]; simp)
    by_cases hv2 : a.val = 2
    · refine ⟨m + 2, by omega, ?_⟩
      rw [pos2_m_add_two h6 hm, ← hv, hv2]
      simp [ptX]
    rcases Nat.even_or_odd a.val with ⟨j, hj⟩ | ⟨j, hj⟩
    · refine ⟨m + a.val, by omega, ?_⟩
      rw [pos2_high_even h6 hm (by omega) (by omega), Nat.cast_add, ZMod.natCast_self, zero_add,
        hv]
      rfl
    · refine ⟨a.val, by omega, ?_⟩
      rw [pos2_low_odd h6 hm (by omega) (by omega) (by omega), hv]
      rfl

/-- The orbit of `A` under `N_2 ∘ j_2` is all of `B_2`. -/
theorem NJ2_orbit_covers {q : Pt m} (hq : inB 2 q) : ∃ k, NJ2^[k] (ptA : Pt m) = q := by
  obtain ⟨k, hk, hpos⟩ := exists_pos2 h6 hm (fam2_of_inB h6 hq)
  exact ⟨k, by rw [NJ2_iterate h6 hm hk, hpos]⟩

/-! ### Fibres of `ℓ_2 = a + b` -/

theorem partner2_inB {q : Pt m} (hq : inB 2 q) : inB 2 (partner2 q) := by
  have hc := consts h6
  apply inB_of_fam2 h6
  rcases fam2_of_inB h6 hq with rfl | rfl | rfl | ⟨ha, hb2⟩ | ⟨hb, ha0, ha1⟩
  · rw [partner2_A h6]; simp [fam2, ptY, hc]
  · rw [partner2_B h6]; simp [fam2]
  · rw [partner2_C h6]; simp [fam2]
  · rcases q with ⟨a, b⟩
    simp only at ha hb2
    subst ha
    by_cases hb1 : b = 1
    · subst hb1
      rw [show ((1 : ZMod m), (1 : ZMod m)) = ptY 1 from rfl, partner2_Y1 h6]; simp [fam2]
    · rw [show ((1 : ZMod m), b) = ptY b from rfl, partner2_Y h6 b hb1 hb2]
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,
        fun h => hb1 (by have h' : b - 1 = 0 := h; linear_combination h'),
        fun h => hb2 (by have h' : b - 1 = 1 := h; linear_combination h')⟩)))
  · rcases q with ⟨a, b⟩
    simp only at hb ha0 ha1
    subst hb
    rw [show ((a, (2 : ZMod m)) : Pt m) = ptX a from rfl, partner2_X h6]
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,
      fun h => ha1 (by have h' : a + 1 = 2 := h; linear_combination h')⟩)))

theorem partner2_ne {q : Pt m} (hq : inB 2 q) : partner2 q ≠ q := by
  have hc := consts h6
  rcases fam2_of_inB h6 hq with rfl | rfl | rfl | ⟨ha, hb2⟩ | ⟨hb, ha0, ha1⟩
  · rw [partner2_A h6]; simp [ptA, ptY, hc]
  · rw [partner2_B h6]; simp [ptB, ptC, hc]
  · rw [partner2_C h6]; simp [ptB, ptC, hc]
  · rcases q with ⟨a, b⟩
    simp only at ha hb2
    subst ha
    by_cases hb1 : b = 1
    · subst hb1
      rw [show ((1 : ZMod m), (1 : ZMod m)) = ptY 1 from rfl, partner2_Y1 h6]; simp [ptA, ptY, hc]
    · rw [show ((1 : ZMod m), b) = ptY b from rfl, partner2_Y h6 b hb1 hb2]
      intro h
      have := congrArg Prod.snd h
      simp [ptX, ptY] at this
      exact hb2 this.symm
  · rcases q with ⟨a, b⟩
    simp only at hb ha0 ha1
    subst hb
    rw [show ((a, (2 : ZMod m)) : Pt m) = ptX a from rfl, partner2_X h6]
    intro h
    have := congrArg Prod.fst h
    simp [ptX, ptY] at this
    exact ha1 this.symm

theorem fibre2_exists (v : ZMod m) : ∃ q : Pt m, inB 2 q ∧ q.1 + q.2 = v := by
  have hc := consts h6
  by_cases h3 : v = 3
  · exact ⟨ptB, inB_of_fam2 h6 (Or.inr (Or.inl rfl)), by simp [ptB, h3]⟩
  · refine ⟨ptY (v - 1), inB_of_fam2 h6 (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩)))), ?_⟩
    · exact fun h => h3 (by have h' : v - 1 = 2 := h; linear_combination h')
    · simp [ptY]

/-- The families grouped by the sum of coordinates. -/
theorem fam2_classes {q : Pt m} (hq : fam2 q) :
    (q.1 + q.2 = 1 ∧ (q = ptY 0 ∨ q = ptX (-1))) ∨ (q.1 + q.2 = 2 ∧ (q = ptA ∨ q = ptY 1)) ∨
    (q.1 + q.2 = 3 ∧ (q = ptB ∨ q = ptC)) ∨
    (q.1 + q.2 ≠ 1 ∧ q.1 + q.2 ≠ 2 ∧ q.1 + q.2 ≠ 3 ∧
      (q = ptX (q.1 + q.2 - 2) ∨ q = ptY (q.1 + q.2 - 1))) := by
  have hc := consts h6
  rcases hq with rfl | rfl | rfl | ⟨ha, hb2⟩ | ⟨hb, ha0, ha1⟩
  · exact Or.inr (Or.inl ⟨by simp [ptA], Or.inl rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨by simp [ptB], Or.inl rfl⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨by simp [ptC], Or.inr rfl⟩))
  · rcases q with ⟨a, b⟩
    simp only at ha hb2
    subst ha
    by_cases hb0 : b = 0
    · subst hb0; exact Or.inl ⟨by simp, Or.inl rfl⟩
    by_cases hb1 : b = 1
    · subst hb1; exact Or.inr (Or.inl ⟨by norm_num, Or.inr rfl⟩)
    · refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, Or.inr (by simp [ptY])⟩))
      · exact fun h => hb0 (by linear_combination h)
      · exact fun h => hb1 (by linear_combination h)
      · exact fun h => hb2 (by linear_combination h)
  · rcases q with ⟨a, b⟩
    simp only at hb ha0 ha1
    subst hb
    by_cases ham : a = -1
    · subst ham; exact Or.inl ⟨by ring, Or.inr rfl⟩
    · refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, Or.inl (by simp [ptX])⟩))
      · exact fun h => ham (by linear_combination h)
      · exact fun h => ha0 (by linear_combination h)
      · exact fun h => ha1 (by linear_combination h)

theorem fam2_sum_one {q : Pt m} (hq : fam2 q) (h : q.1 + q.2 = 1) : q = ptY 0 ∨ q = ptX (-1) := by
  have hc := consts h6
  rcases fam2_classes h6 hm hq with ⟨ha, hq1⟩ | ⟨ha, hq1⟩ | ⟨ha, hq1⟩ | ⟨ha1, ha2, ha3, hq1⟩
  · exact hq1
  · exact absurd (ha.symm.trans h) hc.2.2.2.2.2.2.2.1
  · exact absurd (ha.symm.trans h) hc.2.2.2.2.2.2.2.2.2.1
  · exact absurd h ha1

theorem fam2_sum_two {q : Pt m} (hq : fam2 q) (h : q.1 + q.2 = 2) : q = ptA ∨ q = ptY 1 := by
  have hc := consts h6
  rcases fam2_classes h6 hm hq with ⟨ha, hq1⟩ | ⟨ha, hq1⟩ | ⟨ha, hq1⟩ | ⟨ha1, ha2, ha3, hq1⟩
  · exact absurd (ha.symm.trans h) hc.2.2.2.2.2.2.1
  · exact hq1
  · exact absurd (ha.symm.trans h) hc.2.2.2.2.2.2.2.2.2.2.2.1
  · exact absurd h ha2

theorem fam2_sum_three {q : Pt m} (hq : fam2 q) (h : q.1 + q.2 = 3) : q = ptB ∨ q = ptC := by
  have hc := consts h6
  rcases fam2_classes h6 hm hq with ⟨ha, hq1⟩ | ⟨ha, hq1⟩ | ⟨ha, hq1⟩ | ⟨ha1, ha2, ha3, hq1⟩
  · exact absurd (ha.symm.trans h) hc.2.2.2.2.2.2.2.2.1
  · exact absurd (ha.symm.trans h) hc.2.2.2.2.2.2.2.2.2.2.1
  · exact hq1
  · exact absurd h ha3

theorem fam2_sum_other {q : Pt m} (hq : fam2 q) (h1 : q.1 + q.2 ≠ 1) (h2 : q.1 + q.2 ≠ 2)
    (h3 : q.1 + q.2 ≠ 3) : q = ptX (q.1 + q.2 - 2) ∨ q = ptY (q.1 + q.2 - 1) := by
  rcases fam2_classes h6 hm hq with ⟨ha, hq1⟩ | ⟨ha, hq1⟩ | ⟨ha, hq1⟩ | ⟨ha1, ha2, ha3, hq1⟩
  · exact absurd ha h1
  · exact absurd ha h2
  · exact absurd ha h3
  · exact hq1

theorem fibre2_unique {q q' : Pt m} (hq : inB 2 q) (hq' : inB 2 q') (h : q'.1 + q'.2 = q.1 + q.2) :
    q' = q ∨ q' = partner2 q := by
  have hc := consts h6
  have hf := fam2_of_inB h6 hq
  have hf' := fam2_of_inB h6 hq'
  rcases fam2_classes h6 hm hf with ⟨ha, hq1⟩ | ⟨ha, hq1⟩ | ⟨ha, hq1⟩ | ⟨ha1, ha2, ha3, hq1⟩
  · rcases fam2_sum_one h6 hm hf' (h.trans ha) with rfl | rfl <;> rcases hq1 with rfl | rfl <;>
      simp [partner2_Y0 h6, partner2_X h6]
  · rcases fam2_sum_two h6 hm hf' (h.trans ha) with rfl | rfl <;> rcases hq1 with rfl | rfl <;>
      simp [partner2_A h6, partner2_Y1 h6]
  · rcases fam2_sum_three h6 hm hf' (h.trans ha) with rfl | rfl <;> rcases hq1 with rfl | rfl <;>
      simp [partner2_B h6, partner2_C h6]
  · have h1' : q'.1 + q'.2 ≠ 1 := by rw [h]; exact ha1
    have h2' : q'.1 + q'.2 ≠ 2 := by rw [h]; exact ha2
    have h3' : q'.1 + q'.2 ≠ 3 := by rw [h]; exact ha3
    have hy1 : q.1 + q.2 - 1 ≠ 1 := fun h' => ha2 (by linear_combination h')
    have hy2 : q.1 + q.2 - 1 ≠ 2 := fun h' => ha3 (by linear_combination h')
    rcases fam2_sum_other h6 hm hf' h1' h2' h3' with hq2 | hq2 <;>
      rcases hq1 with hq1 | hq1 <;> rw [h] at hq2
    · left; rw [hq2, ← hq1]
    · right
      rw [hq2]
      conv_rhs => rw [hq1]
      rw [partner2_Y h6 _ hy1 hy2]
      congr 1; ring
    · right
      rw [hq2]
      conv_rhs => rw [hq1]
      rw [partner2_X h6]
      congr 1; ring
    · left; rw [hq2, ← hq1]

/-- `j_2` maps `B_2` into itself. -/
theorem jmap2_inB {q : Pt m} (hq : inB 2 q) : inB 2 (jmap 2 q) := by
  have hc := consts h6
  apply inB_of_fam2 h6
  rcases fam2_of_inB h6 hq with rfl | rfl | rfl | ⟨ha, hb2⟩ | ⟨hb, ha0, ha1⟩
  · rw [j2_A h6]; simp [fam2]
  · rw [j2_B h6]; simp [fam2, ptY, hc]
  · rw [j2_C h6]; simp [fam2, ptX, hc]
  · rcases q with ⟨a, b⟩
    simp only at ha hb2
    subst ha
    by_cases hb0 : b = 0
    · subst hb0
      rw [show ((1 : ZMod m), (0 : ZMod m)) = ptY 0 from rfl, j2_Y0 h6]; simp [fam2, ptY, hc]
    by_cases hb1 : b = 1
    · subst hb1
      rw [show ((1 : ZMod m), (1 : ZMod m)) = ptY 1 from rfl, j2_Y1 h6]; simp [fam2]
    by_cases hb3 : b = 3
    · subst hb3
      rw [show ((1 : ZMod m), (3 : ZMod m)) = ptY 3 from rfl, j2_Y3 h6]; simp [fam2, ptY, hc]
    · rw [show ((1 : ZMod m), b) = ptY b from rfl, j2_Y h6 b hb0 hb1 hb2 hb3]
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,
        fun h => hb1 (by have h' : b + 1 = 2 := h; linear_combination h')⟩)))
  · rcases q with ⟨a, b⟩
    simp only at hb ha0 ha1
    subst hb
    by_cases ha2 : a = 2
    · subst ha2
      rw [show ((2 : ZMod m), (2 : ZMod m)) = ptX 2 from rfl, j2_X2 h6]; simp [fam2, ptX, hc]
    · rw [show ((a, (2 : ZMod m)) : Pt m) = ptX a from rfl, j2_X h6 a ha0 ha1 ha2]
      by_cases ham : a = -1
      · subst ham
        rw [show (-1 : ZMod m) + 1 = 0 by ring]; simp [fam2, ptX, ptA]
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,
          fun h => ham (by have h' : a + 1 = 0 := h; linear_combination h'),
          fun h => ha0 (by have h' : a + 1 = 1 := h; linear_combination h')⟩)))

theorem NJ2_inB {q : Pt m} (hq : inB 2 q) : inB 2 (NJ2 q) :=
  partner2_inB h6 hm (jmap2_inB h6 hm hq)

end cycle2

end D5
end TorusEven
