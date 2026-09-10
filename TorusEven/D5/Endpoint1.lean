-- STATUS: main-path (terminal plane, colour i = 1: support B_1, partner, the 2m-cycle)
import TorusEven.D5.Endpoint

/-!
# Colour `i = 1` (physical colour `3`, direction `0`, functional `ℓ_1 = b`)

`B_1 = {A, B, C, X_2, Y_0, Y_1, Y_t (t ∉ {0,1,2}), Z_t (t ∉ {0,1,2})}`,
`j_1 = (A, Y_1, Y_0, Y_{m-1}, …, Y_3, X_2, C, Z_3, …, Z_{m-1}, B)`,
fibre pairs `(Y_0 Z_3)(Y_1 C)(A X_2)(Y_3 B)(Y_t Z_{3-t})`.
-/

namespace TorusEven
namespace D5

variable {m : ℕ} [NeZero m]

/-- The support `B_1` as a union of families. -/
def fam1 (q : Pt m) : Prop :=
  q = ptA ∨ q = ptB ∨ q = ptC ∨ q = ptX 2 ∨ q = ptY 0 ∨ q = ptY 1 ∨
    (q.1 = 1 ∧ q.2 ≠ 0 ∧ q.2 ≠ 1 ∧ q.2 ≠ 2) ∨ (q.1 + q.2 = 3 ∧ q.1 ≠ 0 ∧ q.1 ≠ 1 ∧ q.1 ≠ 2)

/-- The fibre partner for `ℓ_1 = b`. -/
def partner1 (q : Pt m) : Pt m :=
  if q.2 = 2 then (2 - q.1, 2) else (4 - q.2 - q.1, q.2)

theorem partner1_snd (q : Pt m) : (partner1 q).2 = q.2 := by
  unfold partner1
  split_ifs <;> simp [*]

/-- The composite `N_1 ∘ j_1`. -/
def NJ1 (q : Pt m) : Pt m := partner1 (jmap 1 q)

theorem ptZ_three : (ptZ (3 : ZMod m) : Pt m) = (3, 0) := by simp [ptZ]

section colour1

variable (h6 : 6 ≤ m)
include h6

theorem fam1_of_inB {q : Pt m} (h : inB 1 q) : fam1 q := by
  have hc := consts h6
  rcases q with ⟨a, b⟩
  rcases omega_cases (m := m) (a, b) with
    ⟨ha, hb, hw⟩ | ⟨ha, hb, hw⟩ | ⟨ha, hb, hw⟩ | ⟨ha, hb, hw⟩ | ⟨ha, hb, hw⟩ | ⟨ha, hb, hw⟩ |
    ⟨ha, hb, hw⟩ | ⟨ha, hb, hw⟩ | ⟨hb, ha0, ha1, ha2, hw⟩ | ⟨ha, hb0, hb1, hb2, hb3, hw⟩ |
    ⟨hab, hb0, hb1, hb2, hb3, hw⟩ | hw <;>
    simp only [inB, hw] at h
  · simp only at ha hb; subst ha; subst hb; simp [fam1, ptY]
  · simp only at ha hb; subst ha; subst hb; simp [fam1, ptA, ptB, ptC, ptX, ptY, hc]
  · simp only at ha hb; subst ha; subst hb; simp [fam1, ptY]
  · simp only at ha hb; subst ha; subst hb; simp [fam1, ptC]
  · simp only at ha hb; subst ha; subst hb; simp [fam1, ptA]
  · simp only at ha hb; subst ha; subst hb; simp [fam1, ptX]
  · simp only at ha hb; subst ha; subst hb; simp [fam1, ptB]
  · simp only at ha hb; subst ha; subst hb; simp [fam1, ptA, ptB, ptC, ptX, ptY, hc]
  · exact absurd (by decide) h
  · simp only at ha hb0 hb1 hb2 hb3; subst ha
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hb0, hb1, hb2⟩))))))
  · simp only at hab hb0 hb1 hb2 hb3
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hab, ?_, ?_, ?_⟩))))))
    · exact fun h => hb3 (by linear_combination hab - h)
    · exact fun h => hb2 (by linear_combination hab - h)
    · exact fun h => hb1 (by linear_combination hab - h)
  · exact absurd (by decide) h

theorem inB_of_fam1 {q : Pt m} (h : fam1 q) : inB 1 q := by
  have hc := consts h6
  unfold inB
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | ⟨ha, hb0, hb1, hb2⟩ | ⟨hab, ha0, ha1, ha2⟩
  · rw [omega_A h6]; decide
  · rw [omega_B h6]; decide
  · rw [omega_C h6]; decide
  · rw [omega_X2 h6]; decide
  · rw [omega_Y0 h6]; decide
  · rw [omega_Y1 h6]; decide
  · rcases q with ⟨a, b⟩
    simp only at ha hb0 hb1 hb2
    subst ha
    by_cases hb3 : b = 3
    · subst hb3
      rw [show ((1 : ZMod m), (3 : ZMod m)) = ptY 3 from rfl, omega_Y3 h6]; decide
    · rw [show (((1 : ZMod m), b) : Pt m) = ptY b from rfl, omega_Y h6 b hb0 hb1 hb2 hb3]; decide
  · rcases q with ⟨a, b⟩
    simp only at hab ha0 ha1 ha2
    have hb : b = 3 - a := by linear_combination hab
    subst hb
    rw [show ((a, (3 : ZMod m) - a) : Pt m) = ptZ a from rfl, omega_Z h6 a ha0 ha1 ha2]; decide

/-! The local map `j_1` on the families. -/

theorem j1_A : jmap 1 (ptA : Pt m) = ptY 1 := by
  rw [jmap, omega_A h6]; ext <;> simp [ptA, ptY, avec, p201] <;> ring

theorem j1_B : jmap 1 (ptB : Pt m) = ptA := by
  rw [jmap, omega_B h6]; ext <;> simp [ptB, ptA, avec, p120] <;> ring

theorem j1_C : jmap 1 (ptC : Pt m) = ptZ 3 := by
  rw [jmap, omega_C h6]; ext <;> simp [ptC, ptZ, avec, p201] <;> ring

theorem j1_X2 : jmap 1 (ptX 2 : Pt m) = ptC := by
  rw [jmap, omega_X2 h6]; ext <;> simp [ptX, ptC, avec, p120] <;> ring

theorem j1_Y0 : jmap 1 (ptY 0 : Pt m) = ptY (-1) := by
  rw [jmap, omega_Y0 h6]; ext <;> simp [ptY, avec, p021] <;> ring

theorem j1_Y1 : jmap 1 (ptY 1 : Pt m) = ptY 0 := by
  rw [jmap, omega_Y1 h6]; ext <;> simp [ptY, avec, p120] <;> ring

theorem j1_Y3 : jmap 1 (ptY 3 : Pt m) = ptX 2 := by
  rw [jmap, omega_Y3 h6]; ext <;> simp [ptY, ptX, avec, p201] <;> ring

theorem j1_Y (t : ZMod m) (h0 : t ≠ 0) (h1 : t ≠ 1) (h2 : t ≠ 2) (h3 : t ≠ 3) :
    jmap 1 (ptY t) = ptY (t - 1) := by
  rw [jmap, omega_Y h6 t h0 h1 h2 h3]; ext <;> simp [ptY, avec, p021] <;> ring

theorem j1_Z (t : ZMod m) (h0 : t ≠ 0) (h1 : t ≠ 1) (h2 : t ≠ 2) :
    jmap 1 (ptZ t) = ptZ (t + 1) := by
  rw [jmap, omega_Z h6 t h0 h1 h2]; ext <;> simp [ptZ, avec, p102] <;> ring

/-! The partner on the families. -/

theorem partner1_A : partner1 (ptA : Pt m) = ptX 2 := by
  simp [partner1, ptA, ptX]

theorem partner1_X2 : partner1 (ptX 2 : Pt m) = ptA := by
  simp [partner1, ptA, ptX]

theorem partner1_Y (t : ZMod m) (h2 : t ≠ 2) : partner1 (ptY t) = ptZ (3 - t) := by
  refine Prod.ext ?_ ?_ <;> simp [partner1, ptY, ptZ, h2] <;> ring

theorem partner1_Z (t : ZMod m) (h1 : t ≠ 1) : partner1 (ptZ t) = ptY (3 - t) := by
  have h2 : (3 : ZMod m) - t ≠ 2 := fun h => h1 (by linear_combination -h)
  refine Prod.ext ?_ ?_ <;> simp [partner1, ptY, ptZ, h2] <;> ring

theorem partner1_B : partner1 (ptB : Pt m) = ptY 3 := by
  have hc := consts h6
  simp [partner1, ptB, ptY, hc]; norm_num

theorem partner1_C : partner1 (ptC : Pt m) = ptY 1 := by
  have hc := consts h6
  simp [partner1, ptC, ptY, hc]; norm_num

theorem partner1_Y0 : partner1 (ptY 0 : Pt m) = ptZ 3 := by
  have hc := consts h6
  simp [partner1, ptZ, ptY, hc]; norm_num

theorem partner1_Y1 : partner1 (ptY 1 : Pt m) = ptC := by
  have hc := consts h6
  simp [partner1, ptC, ptY, hc]; norm_num

theorem partner1_Y3 : partner1 (ptY 3 : Pt m) = ptB := by
  have hc := consts h6
  simp [partner1, ptB, ptY, hc]; norm_num

theorem partner1_Z3 : partner1 (ptZ 3 : Pt m) = ptY 0 := by
  have hc := consts h6
  simp [partner1, ptZ, ptY, hc]; norm_num

/-! The composite. -/

theorem NJ1_A : NJ1 (ptA : Pt m) = ptC := by rw [NJ1, j1_A h6, partner1_Y1 h6]
theorem NJ1_C : NJ1 (ptC : Pt m) = ptY 0 := by rw [NJ1, j1_C h6, partner1_Z3 h6]
theorem NJ1_B : NJ1 (ptB : Pt m) = ptX 2 := by rw [NJ1, j1_B h6, partner1_A h6]
theorem NJ1_X2 : NJ1 (ptX 2 : Pt m) = ptY 1 := by rw [NJ1, j1_X2 h6, partner1_C h6]
theorem NJ1_Y1 : NJ1 (ptY 1 : Pt m) = ptZ 3 := by rw [NJ1, j1_Y1 h6, partner1_Y0 h6]
theorem NJ1_Y3 : NJ1 (ptY 3 : Pt m) = ptA := by rw [NJ1, j1_Y3 h6, partner1_X2 h6]

theorem NJ1_Y0 : NJ1 (ptY 0 : Pt m) = ptZ 4 := by
  rw [NJ1, j1_Y0 h6, partner1_Y h6 (-1)]
  · congr 1; ring
  · have := neg_cast_ne_cast (m := m) (k := 1) (c := 2) (by omega) (by omega)
    simpa using this

theorem NJ1_Y (t : ZMod m) (h0 : t ≠ 0) (h1 : t ≠ 1) (h2 : t ≠ 2) (h3 : t ≠ 3) :
    NJ1 (ptY t) = ptZ (4 - t) := by
  rw [NJ1, j1_Y h6 t h0 h1 h2 h3, partner1_Y h6 (t - 1) (fun h => h3 (by linear_combination h))]
  congr 1; ring

theorem NJ1_Z (t : ZMod m) (h0 : t ≠ 0) (h1 : t ≠ 1) (h2 : t ≠ 2) :
    NJ1 (ptZ t) = ptY (2 - t) := by
  rw [NJ1, j1_Z h6 t h0 h1 h2, partner1_Z h6 (t + 1) (fun h => h0 (by linear_combination h))]
  congr 1; ring

end colour1

/-! ### Cast bookkeeping for the generic families -/

theorem natCast_ne_natCast_of_not_dvd {a b : ℕ} (hab : b ≤ a) (h : ¬ m ∣ a - b) :
    ((a : ℕ) : ZMod m) ≠ ((b : ℕ) : ZMod m) := by
  intro hab'
  rw [ZMod.natCast_eq_natCast_iff'] at hab'
  exact h (Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hab'))

theorem cast_succ_not_small {k : ℕ} (hk : 1 ≤ k) (h0 : ¬ m ∣ k + 1) (h1 : ¬ m ∣ k)
    (h2 : ¬ m ∣ k - 1) :
    ((k + 1 : ℕ) : ZMod m) ≠ 0 ∧ ((k + 1 : ℕ) : ZMod m) ≠ 1 ∧ ((k + 1 : ℕ) : ZMod m) ≠ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using natCast_ne_natCast_of_not_dvd (m := m) (a := k + 1) (b := 0) (by omega)
      (by simpa using h0)
  · simpa using natCast_ne_natCast_of_not_dvd (m := m) (a := k + 1) (b := 1) (by omega)
      (by simpa using h1)
  · simpa using natCast_ne_natCast_of_not_dvd (m := m) (a := k + 1) (b := 2) (by omega)
      (by rwa [show k + 1 - 2 = k - 1 by omega])

theorem two_sub_cast_not_small {k : ℕ} (hk : 2 ≤ k) (h2 : ¬ m ∣ k - 2) (h1 : ¬ m ∣ k - 1)
    (h0 : ¬ m ∣ k) (h3 : ¬ m ∣ k + 1) :
    (2 : ZMod m) - (k : ZMod m) ≠ 0 ∧ (2 : ZMod m) - (k : ZMod m) ≠ 1 ∧
    (2 : ZMod m) - (k : ZMod m) ≠ 2 ∧ (2 : ZMod m) - (k : ZMod m) ≠ 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    exact natCast_ne_natCast_of_not_dvd (m := m) (a := k) (b := 2) hk h2
      (by push_cast; linear_combination -h)
  · intro h
    exact natCast_ne_natCast_of_not_dvd (m := m) (a := k) (b := 1) (by omega) h1
      (by push_cast; linear_combination -h)
  · intro h
    exact natCast_ne_natCast_of_not_dvd (m := m) (a := k) (b := 0) (by omega) (by simpa using h0)
      (by push_cast; linear_combination -h)
  · intro h
    exact natCast_ne_natCast_of_not_dvd (m := m) (a := k + 1) (b := 0) (by omega)
      (by simpa using h3) (by push_cast; linear_combination -h)

theorem ptZ_zero : (ptZ (0 : ZMod m) : Pt m) = ptB := by simp [ptZ, ptB]

/-- The `2m`-cycle of `N_1 ∘ j_1` through `B_1`, indexed by position. -/
def pos1 (m : ℕ) (k : ℕ) : Pt m :=
  if k = 0 then ptA
  else if k = 1 then ptC
  else if k = 2 then ptY 0
  else if k ≤ m - 2 then
    (if k % 2 = 1 then ptZ ((k + 1 : ℕ) : ZMod m) else ptY (2 - (k : ZMod m)))
  else if k = m - 1 then ptB
  else if k = m then ptX 2
  else if k = m + 1 then ptY 1
  else if k = m + 2 then ptZ 3
  else if k ≤ 2 * m - 2 then
    (if k % 2 = 1 then ptY (2 - (k : ZMod m)) else ptZ ((k + 1 : ℕ) : ZMod m))
  else ptY 3

section cycle1

variable (h6 : 6 ≤ m) (hm : Even m)
include h6 hm

theorem pos1_zero : pos1 m 0 = ptA := by simp [pos1]
theorem pos1_one : pos1 m 1 = ptC := by simp [pos1]
theorem pos1_two : pos1 m 2 = ptY 0 := by simp [pos1]

theorem pos1_low_odd {k : ℕ} (h1 : 3 ≤ k) (h2 : k ≤ m - 2) (hodd : k % 2 = 1) :
    pos1 m k = ptZ ((k + 1 : ℕ) : ZMod m) := by
  have hk0 : k ≠ 0 := by omega
  have hk1 : k ≠ 1 := by omega
  have hk2 : k ≠ 2 := by omega
  simp [pos1, hk0, hk1, hk2, h2, hodd]

theorem pos1_low_even {k : ℕ} (h1 : 3 ≤ k) (h2 : k ≤ m - 2) (heven : k % 2 = 0) :
    pos1 m k = ptY (2 - (k : ZMod m)) := by
  have hk0 : k ≠ 0 := by omega
  have hk1 : k ≠ 1 := by omega
  have hk2 : k ≠ 2 := by omega
  simp [pos1, hk0, hk1, hk2, h2, heven]

theorem pos1_m1 : pos1 m (m - 1) = ptB := by
  have h0 : m - 1 ≠ 0 := by omega
  have h1 : m - 1 ≠ 1 := by omega
  have h2 : m - 1 ≠ 2 := by omega
  have h3 : ¬ (m - 1 ≤ m - 2) := by omega
  simp [pos1, h0, h1, h2, h3]

theorem pos1_m : pos1 m m = ptX 2 := by
  have h0 : m ≠ 0 := by omega
  have h1 : m ≠ 1 := by omega
  have h2 : m ≠ 2 := by omega
  have h3 : ¬ (m ≤ m - 2) := by omega
  have h4 : m ≠ m - 1 := by omega
  simp [pos1, h0, h1, h2, h3, h4]

theorem pos1_m_add_one : pos1 m (m + 1) = ptY 1 := by
  have h0 : m + 1 ≠ 0 := by omega
  have h1 : m + 1 ≠ 1 := by omega
  have h2 : m + 1 ≠ 2 := by omega
  have h3 : ¬ (m + 1 ≤ m - 2) := by omega
  have h4 : m + 1 ≠ m - 1 := by omega
  have h5 : m + 1 ≠ m := by omega
  have hm0 : m ≠ 0 := by omega
  simp [pos1, h0, h1, h2, h3, h4, h5, hm0]

theorem pos1_m_add_two : pos1 m (m + 2) = ptZ 3 := by
  have h0 : m + 2 ≠ 0 := by omega
  have h1 : m + 2 ≠ 1 := by omega
  have h2 : m + 2 ≠ 2 := by omega
  have h3 : ¬ (m + 2 ≤ m - 2) := by omega
  have h4 : m + 2 ≠ m - 1 := by omega
  have h5 : m + 2 ≠ m := by omega
  have h6' : m + 2 ≠ m + 1 := by omega
  have hm0 : m ≠ 0 := by omega
  simp [pos1, h0, h1, h2, h3, h4, h5, h6', hm0]

theorem pos1_high_odd {k : ℕ} (h1 : m + 3 ≤ k) (h2 : k ≤ 2 * m - 2) (hodd : k % 2 = 1) :
    pos1 m k = ptY (2 - (k : ZMod m)) := by
  have hk0 : k ≠ 0 := by omega
  have hk1 : k ≠ 1 := by omega
  have hk2 : k ≠ 2 := by omega
  have hk3 : ¬ (k ≤ m - 2) := by omega
  have hk4 : k ≠ m - 1 := by omega
  have hk5 : k ≠ m := by omega
  have hk6 : k ≠ m + 1 := by omega
  have hk7 : k ≠ m + 2 := by omega
  simp [pos1, hk0, hk1, hk2, hk3, hk4, hk5, hk6, hk7, h2, hodd]

theorem pos1_high_even {k : ℕ} (h1 : m + 3 ≤ k) (h2 : k ≤ 2 * m - 2) (heven : k % 2 = 0) :
    pos1 m k = ptZ ((k + 1 : ℕ) : ZMod m) := by
  have hk0 : k ≠ 0 := by omega
  have hk1 : k ≠ 1 := by omega
  have hk2 : k ≠ 2 := by omega
  have hk3 : ¬ (k ≤ m - 2) := by omega
  have hk4 : k ≠ m - 1 := by omega
  have hk5 : k ≠ m := by omega
  have hk6 : k ≠ m + 1 := by omega
  have hk7 : k ≠ m + 2 := by omega
  simp [pos1, hk0, hk1, hk2, hk3, hk4, hk5, hk6, hk7, h2, heven]

theorem pos1_last : pos1 m (2 * m - 1) = ptY 3 := by
  have hk0 : 2 * m - 1 ≠ 0 := by omega
  have hk1 : 2 * m - 1 ≠ 1 := by omega
  have hk2 : 2 * m - 1 ≠ 2 := by omega
  have hk3 : ¬ (2 * m - 1 ≤ m - 2) := by omega
  have hk4 : 2 * m - 1 ≠ m - 1 := by omega
  have hk5 : 2 * m - 1 ≠ m := by omega
  have hk6 : 2 * m - 1 ≠ m + 1 := by omega
  have hk7 : 2 * m - 1 ≠ m + 2 := by omega
  have hk8 : ¬ (2 * m - 1 ≤ 2 * m - 2) := by omega
  simp [pos1, hk0, hk1, hk2, hk3, hk4, hk5, hk6, hk7, hk8]

theorem four_not_small :
    (4 : ZMod m) ≠ 0 ∧ (4 : ZMod m) ≠ 1 ∧ (4 : ZMod m) ≠ 2 ∧ (4 : ZMod m) ≠ 3 := by
  have hc := consts h6
  exact ⟨hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem NJ1_pos1_succ {k : ℕ} (hk : k < 2 * m - 1) : NJ1 (pos1 m k) = pos1 m (k + 1) := by
  have hm' := hm
  obtain ⟨r, hr⟩ := hm'
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · interval_cases k
    · rw [pos1_zero h6 hm, NJ1_A h6, pos1_one h6 hm]
    · rw [pos1_one h6 hm, NJ1_C h6, pos1_two h6 hm]
    · rw [pos1_two h6 hm, NJ1_Y0 h6, pos1_low_odd h6 hm (by omega) (by omega) (by omega)]
      congr 1
  by_cases hlow : k ≤ m - 3
  · rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · have hns := two_sub_cast_not_small (m := m) (k := k) (by omega)
        (not_dvd_of_lt_of_lt (by omega) (by omega)) (not_dvd_of_lt_of_lt (by omega) (by omega))
        (not_dvd_of_lt_of_lt (by omega) (by omega)) (not_dvd_of_lt_of_lt (by omega) (by omega))
      rw [pos1_low_even h6 hm hk3 (by omega) (by omega), NJ1_Y h6 _ hns.1 hns.2.1 hns.2.2.1 hns.2.2.2,
        pos1_low_odd h6 hm (by omega) (by omega) (by omega)]
      congr 1; push_cast; ring
    · have hns := cast_succ_not_small (m := m) (k := k) (by omega)
        (not_dvd_of_lt_of_lt (by omega) (by omega)) (not_dvd_of_lt_of_lt (by omega) (by omega))
        (not_dvd_of_lt_of_lt (by omega) (by omega))
      rw [pos1_low_odd h6 hm hk3 (by omega) (by omega), NJ1_Z h6 _ hns.1 hns.2.1 hns.2.2,
        pos1_low_even h6 hm (by omega) (by omega) (by omega)]
  by_cases hk2 : k = m - 2
  · subst hk2
    rw [pos1_low_even h6 hm (by omega) (by omega) (by omega), cast_sub_self (by omega)]
    have h4 : (2 : ZMod m) - -((2 : ℕ) : ZMod m) = 4 := by push_cast; ring
    have hf := four_not_small h6 hm
    rw [h4, NJ1_Y h6 4 hf.1 hf.2.1 hf.2.2.1 hf.2.2.2, show m - 2 + 1 = m - 1 by omega,
      pos1_m1 h6 hm, show (4 : ZMod m) - 4 = 0 by ring, ptZ_zero]
  by_cases hk1 : k = m - 1
  · subst hk1
    rw [pos1_m1 h6 hm, NJ1_B h6, show m - 1 + 1 = m by omega, pos1_m h6 hm]
  by_cases hkm : k = m
  · subst hkm
    rw [pos1_m h6 hm, NJ1_X2 h6, pos1_m_add_one h6 hm]
  by_cases hkm1 : k = m + 1
  · subst hkm1
    rw [pos1_m_add_one h6 hm, NJ1_Y1 h6, pos1_m_add_two h6 hm]
  by_cases hkm2 : k = m + 2
  · subst hkm2
    have hc := consts h6
    rw [pos1_m_add_two h6 hm, NJ1_Z h6 3 hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.1
      hc.2.2.2.2.2.2.2.2.2.2.2.1, pos1_high_odd h6 hm (by omega) (by omega) (by omega)]
    congr 1; push_cast; simp
  by_cases hhigh : k ≤ 2 * m - 3
  · rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · have hns := cast_succ_not_small (m := m) (k := k) (by omega)
        (not_dvd_of_between (by omega) (by omega)) (not_dvd_of_between (by omega) (by omega))
        (not_dvd_of_between (by omega) (by omega))
      rw [pos1_high_even h6 hm (by omega) (by omega) (by omega), NJ1_Z h6 _ hns.1 hns.2.1 hns.2.2,
        pos1_high_odd h6 hm (by omega) (by omega) (by omega)]
    · have hns := two_sub_cast_not_small (m := m) (k := k) (by omega)
        (not_dvd_of_between (by omega) (by omega)) (not_dvd_of_between (by omega) (by omega))
        (not_dvd_of_between (by omega) (by omega)) (not_dvd_of_between (by omega) (by omega))
      rw [pos1_high_odd h6 hm (by omega) (by omega) (by omega),
        NJ1_Y h6 _ hns.1 hns.2.1 hns.2.2.1 hns.2.2.2,
        pos1_high_even h6 hm (by omega) (by omega) (by omega)]
      congr 1; push_cast; ring
  · have hk' : k = 2 * m - 2 := by omega
    subst hk'
    rw [pos1_high_even h6 hm (by omega) (by omega) (by omega), show 2 * m - 2 + 1 = 2 * m - 1 by omega,
      cast_two_mul_sub (by omega)]
    have hns := neg_cast_not_small (m := m) (k := 1) (not_dvd_of_lt_of_lt (by omega) (by omega))
      (not_dvd_of_lt_of_lt (by omega) (by omega)) (not_dvd_of_lt_of_lt (by omega) (by omega))
    rw [NJ1_Z h6 _ hns.1 hns.2.1 hns.2.2, pos1_last h6 hm]
    congr 1; push_cast; ring

theorem NJ1_pos1_wrap : NJ1 (pos1 m (2 * m - 1)) = pos1 m 0 := by
  rw [pos1_last h6 hm, NJ1_Y3 h6, pos1_zero h6 hm]

theorem NJ1_iterate {k : ℕ} (hk : k ≤ 2 * m - 1) : NJ1^[k] (ptA : Pt m) = pos1 m k := by
  induction k with
  | zero => simp [pos1_zero h6 hm]
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega), NJ1_pos1_succ h6 hm (by omega)]

/-- Every point of `B_1` is on the cycle. -/
theorem exists_pos1 {q : Pt m} (hq : fam1 q) : ∃ k, k ≤ 2 * m - 1 ∧ pos1 m k = q := by
  have hm' := hm
  obtain ⟨r, hr⟩ := hm'
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | ⟨ha, hb0, hb1, hb2⟩ | ⟨hab, ha0, ha1, ha2⟩
  · exact ⟨0, by omega, pos1_zero h6 hm⟩
  · exact ⟨m - 1, by omega, pos1_m1 h6 hm⟩
  · exact ⟨1, by omega, pos1_one h6 hm⟩
  · exact ⟨m, by omega, pos1_m h6 hm⟩
  · exact ⟨2, by omega, pos1_two h6 hm⟩
  · exact ⟨m + 1, by omega, pos1_m_add_one h6 hm⟩
  · rcases q with ⟨a, b⟩
    simp only at ha hb0 hb1 hb2
    subst ha
    have hv : ((b.val : ℕ) : ZMod m) = b := ZMod.natCast_zmod_val b
    have hvlt : b.val < m := ZMod.val_lt b
    have hv0 : b.val ≠ 0 := fun h => hb0 (by rw [← hv, h]; simp)
    have hv1 : b.val ≠ 1 := fun h => hb1 (by rw [← hv, h]; simp)
    have hv2 : b.val ≠ 2 := fun h => hb2 (by rw [← hv, h]; simp)
    by_cases hv3 : b.val = 3
    · refine ⟨2 * m - 1, le_rfl, ?_⟩
      rw [pos1_last h6 hm, ← hv, hv3]
      simp [ptY]
    rcases Nat.even_or_odd b.val with ⟨j, hj⟩ | ⟨j, hj⟩
    · refine ⟨m + 2 - b.val, by omega, ?_⟩
      rw [pos1_low_even h6 hm (by omega) (by omega) (by omega)]
      have hk : ((m + 2 - b.val : ℕ) : ZMod m) = 2 - b := by
        rw [Nat.cast_sub (by omega), hv]; push_cast; simp
      rw [hk]; simp [ptY]
    · refine ⟨2 * m + 2 - b.val, by omega, ?_⟩
      rw [pos1_high_odd h6 hm (by omega) (by omega) (by omega)]
      have hk : ((2 * m + 2 - b.val : ℕ) : ZMod m) = 2 - b := by
        rw [Nat.cast_sub (by omega), hv]; push_cast; simp
      rw [hk]; simp [ptY]
  · rcases q with ⟨a, b⟩
    simp only at hab ha0 ha1 ha2
    have hb : b = 3 - a := by linear_combination hab
    subst hb
    have hv : ((a.val : ℕ) : ZMod m) = a := ZMod.natCast_zmod_val a
    have hvlt : a.val < m := ZMod.val_lt a
    have hv0 : a.val ≠ 0 := fun h => ha0 (by rw [← hv, h]; simp)
    have hv1 : a.val ≠ 1 := fun h => ha1 (by rw [← hv, h]; simp)
    have hv2 : a.val ≠ 2 := fun h => ha2 (by rw [← hv, h]; simp)
    by_cases hv3 : a.val = 3
    · refine ⟨m + 2, by omega, ?_⟩
      rw [pos1_m_add_two h6 hm, ← hv, hv3]
      simp [ptZ]
    rcases Nat.even_or_odd a.val with ⟨j, hj⟩ | ⟨j, hj⟩
    · refine ⟨a.val - 1, by omega, ?_⟩
      rw [pos1_low_odd h6 hm (by omega) (by omega) (by omega), Nat.sub_add_cancel (by omega), hv]
      rfl
    · refine ⟨m + a.val - 1, by omega, ?_⟩
      rw [pos1_high_even h6 hm (by omega) (by omega) (by omega), Nat.sub_add_cancel (by omega),
        Nat.cast_add, ZMod.natCast_self, zero_add, hv]
      rfl

/-- The orbit of `A` under `N_1 ∘ j_1` is all of `B_1`. -/
theorem NJ1_orbit_covers {q : Pt m} (hq : inB 1 q) : ∃ k, NJ1^[k] (ptA : Pt m) = q := by
  obtain ⟨k, hk, hpos⟩ := exists_pos1 h6 hm (fam1_of_inB h6 hq)
  exact ⟨k, by rw [NJ1_iterate h6 hm hk, hpos]⟩

/-! ### Fibres of `ℓ_1 = b` -/

theorem partner1_inB {q : Pt m} (hq : inB 1 q) : inB 1 (partner1 q) := by
  have hc := consts h6
  apply inB_of_fam1 h6
  rcases fam1_of_inB h6 hq with rfl | rfl | rfl | rfl | rfl | rfl | ⟨ha, hb0, hb1, hb2⟩ |
    ⟨hab, ha0, ha1, ha2⟩
  · rw [partner1_A h6]; simp [fam1]
  · rw [partner1_B h6]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨rfl, hc.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2.2.1⟩))))))
  · rw [partner1_C h6]; simp [fam1]
  · rw [partner1_X2 h6]; simp [fam1]
  · rw [partner1_Y0 h6]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨by simp [ptZ], hc.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2.2.1⟩))))))
  · rw [partner1_Y1 h6]; simp [fam1]
  · rcases q with ⟨a, b⟩
    simp only at ha hb0 hb1 hb2
    subst ha
    rw [show ((1 : ZMod m), b) = ptY b from rfl, partner1_Y h6 b hb2]
    by_cases hb3 : b = 3
    · subst hb3
      rw [show (3 : ZMod m) - 3 = 0 by ring, ptZ_zero]; simp [fam1]
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by simp [ptZ],
        fun h => hb3 (by have h' : (3 : ZMod m) - b = 0 := h; linear_combination -h'),
        fun h => hb2 (by have h' : (3 : ZMod m) - b = 1 := h; linear_combination -h'),
        fun h => hb1 (by have h' : (3 : ZMod m) - b = 2 := h; linear_combination -h')⟩))))))
  · rcases q with ⟨a, b⟩
    simp only at hab ha0 ha1 ha2
    have hb : b = 3 - a := by linear_combination hab
    subst hb
    rw [show ((a, (3 : ZMod m) - a) : Pt m) = ptZ a from rfl, partner1_Z h6 a ha1]
    by_cases ha3 : a = 3
    · subst ha3
      rw [show (3 : ZMod m) - 3 = 0 by ring]; simp [fam1]
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,
        fun h => ha3 (by have h' : (3 : ZMod m) - a = 0 := h; linear_combination -h'),
        fun h => ha2 (by have h' : (3 : ZMod m) - a = 1 := h; linear_combination -h'),
        fun h => ha1 (by have h' : (3 : ZMod m) - a = 2 := h; linear_combination -h')⟩))))))

theorem partner1_ne {q : Pt m} (hq : inB 1 q) : partner1 q ≠ q := by
  have hc := consts h6
  rcases fam1_of_inB h6 hq with rfl | rfl | rfl | rfl | rfl | rfl | ⟨ha, hb0, hb1, hb2⟩ |
    ⟨hab, ha0, ha1, ha2⟩
  · rw [partner1_A h6]; simp [ptA, ptX, hc]
  · rw [partner1_B h6]; simp [ptB, ptY, hc]
  · rw [partner1_C h6]; simp [ptC, ptY, hc]
  · rw [partner1_X2 h6]; simp [ptA, ptX, hc]
  · rw [partner1_Y0 h6]; simp [ptZ, ptY, hc]
  · rw [partner1_Y1 h6]; simp [ptC, ptY, hc]
  · rcases q with ⟨a, b⟩
    simp only at ha hb0 hb1 hb2
    subst ha
    rw [show ((1 : ZMod m), b) = ptY b from rfl, partner1_Y h6 b hb2]
    intro h
    have := congrArg Prod.fst h
    simp [ptZ, ptY] at this
    exact hb2 (by linear_combination -this)
  · rcases q with ⟨a, b⟩
    simp only at hab ha0 ha1 ha2
    have hb : b = 3 - a := by linear_combination hab
    subst hb
    rw [show ((a, (3 : ZMod m) - a) : Pt m) = ptZ a from rfl, partner1_Z h6 a ha1]
    intro h
    have := congrArg Prod.fst h
    simp [ptZ, ptY] at this
    exact ha1 this.symm

theorem fibre1_exists (v : ZMod m) : ∃ q : Pt m, inB 1 q ∧ q.2 = v := by
  by_cases h0 : v = 0
  · exact ⟨ptY 0, inB_of_fam1 h6 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))),
      by simp [ptY, h0]⟩
  by_cases h1 : v = 1
  · exact ⟨ptY 1, inB_of_fam1 h6 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))),
      by simp [ptY, h1]⟩
  by_cases h2 : v = 2
  · exact ⟨ptA, inB_of_fam1 h6 (Or.inl rfl), by simp [ptA, h2]⟩
  · exact ⟨ptY v, inB_of_fam1 h6 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨rfl, h0, h1, h2⟩))))))), rfl⟩

/-- The families grouped by second coordinate. -/
theorem fam1_classes {q : Pt m} (hq : fam1 q) :
    (q.2 = 0 ∧ (q = ptY 0 ∨ q = ptZ 3)) ∨ (q.2 = 1 ∧ (q = ptY 1 ∨ q = ptC)) ∨
    (q.2 = 2 ∧ (q = ptA ∨ q = ptX 2)) ∨ (q.2 = 3 ∧ (q = ptY 3 ∨ q = ptB)) ∨
    (q.2 ≠ 0 ∧ q.2 ≠ 1 ∧ q.2 ≠ 2 ∧ q.2 ≠ 3 ∧ (q = ptY q.2 ∨ q = ptZ (3 - q.2))) := by
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | ⟨ha, hb0, hb1, hb2⟩ | ⟨hab, ha0, ha1, ha2⟩
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩)))
  · exact Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩))
  · exact Or.inl ⟨rfl, Or.inl rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)
  · rcases q with ⟨a, b⟩
    simp only at ha hb0 hb1 hb2
    subst ha
    by_cases hb3 : b = 3
    · subst hb3
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hb0, hb1, hb2, hb3, Or.inl rfl⟩)))
  · rcases q with ⟨a, b⟩
    simp only at hab ha0 ha1 ha2
    have hb : b = 3 - a := by linear_combination hab
    subst hb
    by_cases ha3 : a = 3
    · subst ha3
      exact Or.inl ⟨by simp, Or.inr (by simp [ptZ])⟩
    · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, ?_, Or.inr (by simp [ptZ])⟩)))
      · exact fun h => ha3 (by linear_combination -h)
      · exact fun h => ha2 (by linear_combination -h)
      · exact fun h => ha1 (by linear_combination -h)
      · exact fun h => ha0 (by linear_combination -h)

theorem fam1_snd_zero {q : Pt m} (hq : fam1 q) (h : q.2 = 0) : q = ptY 0 ∨ q = ptZ 3 := by
  have hc := consts h6
  rcases fam1_classes h6 hm hq with ⟨ha, hq1⟩ | ⟨ha, hq1⟩ | ⟨ha, hq1⟩ | ⟨ha, hq1⟩ |
    ⟨ha0, ha1, ha2, ha3, hq1⟩
  · exact hq1
  · exact absurd (ha.symm.trans h) hc.2.1
  · exact absurd (ha.symm.trans h) hc.2.2.2.1
  · exact absurd (ha.symm.trans h) hc.2.2.2.2.2.1
  · exact absurd h ha0

theorem fam1_snd_one {q : Pt m} (hq : fam1 q) (h : q.2 = 1) : q = ptY 1 ∨ q = ptC := by
  have hc := consts h6
  rcases fam1_classes h6 hm hq with ⟨ha, hq1⟩ | ⟨ha, hq1⟩ | ⟨ha, hq1⟩ | ⟨ha, hq1⟩ |
    ⟨ha0, ha1, ha2, ha3, hq1⟩
  · exact absurd (ha.symm.trans h) hc.1
  · exact hq1
  · exact absurd (ha.symm.trans h) hc.2.2.2.2.2.2.2.1
  · exact absurd (ha.symm.trans h) hc.2.2.2.2.2.2.2.2.2.1
  · exact absurd h ha1

theorem fam1_snd_two {q : Pt m} (hq : fam1 q) (h : q.2 = 2) : q = ptA ∨ q = ptX 2 := by
  have hc := consts h6
  rcases fam1_classes h6 hm hq with ⟨ha, hq1⟩ | ⟨ha, hq1⟩ | ⟨ha, hq1⟩ | ⟨ha, hq1⟩ |
    ⟨ha0, ha1, ha2, ha3, hq1⟩
  · exact absurd (ha.symm.trans h) hc.2.2.1
  · exact absurd (ha.symm.trans h) hc.2.2.2.2.2.2.1
  · exact hq1
  · exact absurd (ha.symm.trans h) hc.2.2.2.2.2.2.2.2.2.2.2.1
  · exact absurd h ha2

theorem fam1_snd_three {q : Pt m} (hq : fam1 q) (h : q.2 = 3) : q = ptY 3 ∨ q = ptB := by
  have hc := consts h6
  rcases fam1_classes h6 hm hq with ⟨ha, hq1⟩ | ⟨ha, hq1⟩ | ⟨ha, hq1⟩ | ⟨ha, hq1⟩ |
    ⟨ha0, ha1, ha2, ha3, hq1⟩
  · exact absurd (ha.symm.trans h) hc.2.2.2.2.1
  · exact absurd (ha.symm.trans h) hc.2.2.2.2.2.2.2.2.1
  · exact absurd (ha.symm.trans h) hc.2.2.2.2.2.2.2.2.2.2.1
  · exact hq1
  · exact absurd h ha3

theorem fam1_snd_other {q : Pt m} (hq : fam1 q) (h0 : q.2 ≠ 0) (h1 : q.2 ≠ 1) (h2 : q.2 ≠ 2)
    (h3 : q.2 ≠ 3) : q = ptY q.2 ∨ q = ptZ (3 - q.2) := by
  rcases fam1_classes h6 hm hq with ⟨ha, hq1⟩ | ⟨ha, hq1⟩ | ⟨ha, hq1⟩ | ⟨ha, hq1⟩ |
    ⟨ha0, ha1, ha2, ha3, hq1⟩
  · exact absurd ha h0
  · exact absurd ha h1
  · exact absurd ha h2
  · exact absurd ha h3
  · exact hq1

theorem fibre1_unique {q q' : Pt m} (hq : inB 1 q) (hq' : inB 1 q') (h : q'.2 = q.2) :
    q' = q ∨ q' = partner1 q := by
  have hc := consts h6
  have hf := fam1_of_inB h6 hq
  have hf' := fam1_of_inB h6 hq'
  rcases fam1_classes h6 hm hf with ⟨ha, hq1⟩ | ⟨ha, hq1⟩ | ⟨ha, hq1⟩ | ⟨ha, hq1⟩ |
    ⟨ha0, ha1, ha2, ha3, hq1⟩
  · rcases fam1_snd_zero h6 hm hf' (h.trans ha) with rfl | rfl <;> rcases hq1 with rfl | rfl <;>
      simp [partner1_Y0 h6, partner1_Z3 h6]
  · rcases fam1_snd_one h6 hm hf' (h.trans ha) with rfl | rfl <;> rcases hq1 with rfl | rfl <;>
      simp [partner1_Y1 h6, partner1_C h6]
  · rcases fam1_snd_two h6 hm hf' (h.trans ha) with rfl | rfl <;> rcases hq1 with rfl | rfl <;>
      simp [partner1_A h6, partner1_X2 h6]
  · rcases fam1_snd_three h6 hm hf' (h.trans ha) with rfl | rfl <;> rcases hq1 with rfl | rfl <;>
      simp [partner1_Y3 h6, partner1_B h6]
  · have h0' : q'.2 ≠ 0 := by rw [h]; exact ha0
    have h1' : q'.2 ≠ 1 := by rw [h]; exact ha1
    have h2' : q'.2 ≠ 2 := by rw [h]; exact ha2
    have h3' : q'.2 ≠ 3 := by rw [h]; exact ha3
    have hne1 : (3 : ZMod m) - q.2 ≠ 1 := fun h' => ha2 (by linear_combination -h')
    rcases fam1_snd_other h6 hm hf' h0' h1' h2' h3' with hq2 | hq2 <;>
      rcases hq1 with hq1 | hq1 <;> rw [h] at hq2
    · left; rw [hq2, ← hq1]
    · right
      rw [hq2]
      conv_rhs => rw [hq1]
      rw [partner1_Z h6 _ hne1]
      congr 1; ring
    · right
      rw [hq2]
      conv_rhs => rw [hq1]
      rw [partner1_Y h6 _ ha2]
    · left; rw [hq2, ← hq1]

/-- `j_1` maps `B_1` into itself. -/
theorem jmap1_inB {q : Pt m} (hq : inB 1 q) : inB 1 (jmap 1 q) := by
  have hc := consts h6
  apply inB_of_fam1 h6
  have hn1 := neg_cast_not_small (m := m) (k := 1) (not_dvd_of_lt_of_lt (by omega) (by omega))
    (not_dvd_of_lt_of_lt (by omega) (by omega)) (not_dvd_of_lt_of_lt (by omega) (by omega))
  simp only [Nat.cast_one] at hn1
  rcases fam1_of_inB h6 hq with rfl | rfl | rfl | rfl | rfl | rfl | ⟨ha, hb0, hb1, hb2⟩ |
    ⟨hab, ha0, ha1, ha2⟩
  · rw [j1_A h6]; simp [fam1]
  · rw [j1_B h6]; simp [fam1]
  · rw [j1_C h6]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨by simp [ptZ], hc.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2.2.1⟩))))))
  · rw [j1_X2 h6]; simp [fam1]
  · rw [j1_Y0 h6]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨rfl, hn1.1, hn1.2.1, hn1.2.2⟩))))))
  · rw [j1_Y1 h6]; simp [fam1]
  · rcases q with ⟨a, b⟩
    simp only at ha hb0 hb1 hb2
    subst ha
    by_cases hb3 : b = 3
    · subst hb3
      rw [show ((1 : ZMod m), (3 : ZMod m)) = ptY 3 from rfl, j1_Y3 h6]; simp [fam1]
    · rw [show ((1 : ZMod m), b) = ptY b from rfl, j1_Y h6 b hb0 hb1 hb2 hb3]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,
        fun h => hb1 (by have h' : b - 1 = 0 := h; linear_combination h'),
        fun h => hb2 (by have h' : b - 1 = 1 := h; linear_combination h'),
        fun h => hb3 (by have h' : b - 1 = 2 := h; linear_combination h')⟩))))))
  · rcases q with ⟨a, b⟩
    simp only at hab ha0 ha1 ha2
    have hb : b = 3 - a := by linear_combination hab
    subst hb
    rw [show ((a, (3 : ZMod m) - a) : Pt m) = ptZ a from rfl, j1_Z h6 a ha0 ha1 ha2]
    by_cases ham : a = -1
    · subst ham
      rw [show (-1 : ZMod m) + 1 = 0 by ring, ptZ_zero]; simp [fam1]
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by simp [ptZ],
        fun h => ham (by have h' : a + 1 = 0 := h; linear_combination h'),
        fun h => ha0 (by have h' : a + 1 = 1 := h; linear_combination h'),
        fun h => ha1 (by have h' : a + 1 = 2 := h; linear_combination h')⟩))))))

theorem NJ1_inB {q : Pt m} (hq : inB 1 q) : inB 1 (NJ1 q) :=
  partner1_inB h6 hm (jmap1_inB h6 hm hq)

end cycle1

end D5
end TorusEven
